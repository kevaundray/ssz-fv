"""Default-limit certificates for the complete linked ARM codec image.

Expected instructions come from ELF bytes, never from Lean instruction words.
Legacy sparse providers supply only their requested PCs; their words are looked
up in the ELF text at independently resolved symbol addresses.
"""
from __future__ import annotations

import re
from pathlib import Path

from decoder_arm_binding import _EMIT_IMAGE_ORDER, _ordered_image_declarations
from sha_binding import LIST_BINDING_HEADER, list_binding


FUNCTIONS = (
    "serialize", "measure", "emit", "deserialize", "measure_parts",
    "measure_child", "emit_parts", "is_fixed", "measure_fixed", "decode_fixed",
    "decode_offsets", "decode_list", "read_offset", "bounded", "nat_cmp_usize",
    "plan_singleton", "decode_struct_values",
)
ROOT = Path(__file__).resolve().parents[1]
LINKED = "SszArm.Codec.Linked"
CHUNK_SIZE = 64
IMPORTS = (
    "SszArm.CodecLinked", "SszArm.CodecLinkedBranches", "SszArm.CodecSimd",
    "ProofAudit",
)


def _stem(name):
    return "".join(part.title() for part in name.split("_"))


def _require(condition, message):
    if not condition:
        raise ValueError(message)


def _symbol(image, fragment):
    found = [symbol["address"] for symbol in image["symbols"]
             if symbol["name"] == fragment or fragment in symbol["name"]]
    _require(len(found) == 1, f"non-unique ARM linked symbol: {fragment}")
    return found[0]


def _word(image, address):
    offset = address - image["textAddress"]
    text = image["textRaw"]
    _require(offset >= 0 and offset % 4 == 0 and 2 * (offset + 4) <= len(text),
             f"ARM word outside linked text: {address}")
    return int.from_bytes(bytes.fromhex(text[2 * offset:2 * (offset + 4)]), "little")


def _rows(image, name):
    body = image["functions"][name]
    raw = bytes.fromhex(body["raw"])
    _require(len(raw) == body["size"] and len(raw) % 4 == 0,
             f"incomplete ARM function extent: {name}")
    rows = [{"pc": pc, "encoding": f"{int.from_bytes(raw[pc:pc + 4], 'little'):08x}"}
            for pc in range(0, len(raw), 4)]
    _require(len(rows) == len(body["rows"]), f"incomplete ARM rows: {name}")
    for expected, row in zip(rows, body["rows"]):
        word = int(expected["encoding"], 16)
        _require(row["pc"] == expected["pc"] and row["width"] == 4
                 and int(row["encoding"], 16) == word
                 and _word(image, body["address"] + row["pc"]) == word,
                 f"ARM bytes/rows disagree: {name}+{expected['pc']}")
    _require(_symbol(image, body["symbol"]) == body["address"],
             f"ARM entry/symbol disagreement: {name}")
    return rows


def _branch_declarations(image):
    declarations, panic_calls = [], []
    for name in FUNCTIONS:
        body = image["functions"][name]
        for row in body["rows"]:
            word = _word(image, body["address"] + row["pc"])
            opcode = word >> 26
            if opcode not in (5, 37):
                continue
            immediate = word & ((1 << 26) - 1)
            if immediate & (1 << 25):
                immediate -= 1 << 26
            address = body["address"] + row["pc"]
            target = address + 4 * immediate
            if opcode == 5 and body["address"] <= target < body["address"] + body["size"]:
                continue
            _require(row.get("targetAddress") == target,
                     f"ARM encoded branch target disagreement: {name}+{row['pc']}")
            effect = f"w .PC (bias + {target}#64) s"
            if opcode == 37:
                effect = f"w (.GPR 30#5) (bias + {address + 4}#64) ({effect})"
            declarations.append(f"""
example (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None) (entry : read_pc s = bias + {address}#64)
    (fetched : s.program.find? (bias + {address}#64) = some 0x{word:08x}#32) :
    stepi s = {effect} :=
  {LINKED}.Branches.{name}_p{row['pc']} s bias error entry fetched
""")
            targets = row.get("targetSymbols", [])
            if any("panic" in symbol or "slice_index_fail" in symbol for symbol in targets):
                panic_calls.append((address, target))
    for declaration, values, element_type in (
            ("panicCalls", [f"({address}, {target})" for address, target in panic_calls],
             "(Nat × Nat)"),
            ("panicAddresses", [str(address) for address in sorted({t for _, t in panic_calls})],
             "Nat")):
        _require(values, "ARM panic symbol metadata is missing")
        parts, _ = list_binding(f"actual{declaration.title()}", element_type,
                                f"{LINKED}.{declaration}", values)
        declarations.extend(parts)
    return declarations


def _simd_effect(word):
    """Decode the actual retained Q/SIMD forms, preserving all 128 data bits."""
    rt, rn = word & 31, (word >> 5) & 31
    if word & 0xffffffe0 == 0x6f00e400:
        return f"w (.SFP {rt}#5) 0#128 s"
    if word & 0xff800000 == 0x3d800000:
        address = f"(r (.GPR {rn}#5) s + {((word >> 10) & 4095) * 16}#64)"
        if word & (1 << 22):
            return f"w (.SFP {rt}#5) (read_mem_bytes 16 {address} s) s"
        return f"write_mem_bytes 16 {address} (r (.SFP {rt}#5) s) s"
    if word & 0xff800000 == 0xad000000:
        rt2, immediate = (word >> 10) & 31, (word >> 15) & 127
        if immediate & 64:
            immediate -= 128
        address = f"(r (.GPR {rn}#5) s + {immediate * 16}#64)"
        if word & (1 << 22):
            memory = f"(read_mem_bytes 32 {address} s)"
            return (f"w (.SFP {rt2}#5) ({memory}.extractLsb' 128 128) "
                    f"(w (.SFP {rt}#5) ({memory}.extractLsb' 0 128) s)")
        return (f"write_mem_bytes 32 {address} "
                f"((r (.SFP {rt2}#5) s) ++ (r (.SFP {rt}#5) s)) s")
    raise ValueError(f"unsupported retained ARM SIMD instruction: {word:08x}")


def _simd_declarations(image):
    words = set()
    for body in image["functions"].values():
        for row in body["rows"]:
            if re.search(r"\b[qv]\d+", row["asm"]):
                words.add(_word(image, body["address"] + row["pc"]))
    declarations = []
    for word in sorted(words):
        effect = _simd_effect(word)
        declarations.append(f"""
example : (decode_raw_inst 0x{word:08x}#32).isSome = true := by decide
example (s : ArmState) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0x{word:08x}#32) :
    stepi s = w .PC (read_pc s + 4#64) ({effect}) :=
  {LINKED}.Simd.word_{word:08x} s error aligned fetched
""")
    return declarations


def _legacy_addresses(image):
    addresses = {name: body["address"] for name, body in image["functions"].items()}
    for name, fragment in (
            ("compare", "3nat3Nat7compare17"), ("fromU128", "3nat3Nat9from_u12817"),
            ("add", "3nat3Nat3add17"), ("division", "3nat3Nat13div_rem_small17"),
            ("mul", "3nat3Nat3mul17"), ("mulWord", "3nat3Nat8mul_word17"),
            ("exactLeaf", "5codec5exact17"), ("toU128", "3nat3Nat7to_u12817"),
            ("delimited", "5codec16decode_delimited17"), ("memcpy", "memcpy"),
            ("memset", "memset"), ("udiv", "__udivti3")):
        addresses[name] = _symbol(image, fragment)
    return addresses


def _layout_declarations(addresses):
    fields = [(name, f"{LINKED}.{_stem(name)}.CodeAt", name) for name in FUNCTIONS]
    fields += [
        ("legacySerialize", "SszArm.Serialize.CodeAt", "serialize"),
        ("dispatch", "SszArm.Dispatch.CodeAt", "deserialize"),
        ("byteView", "SszArm.ByteView.CodeAt", "deserialize"),
        ("boolBody", "SszArm.BoolCodec.CodeAt", "deserialize"),
        ("uintBody", "SszArm.UintCodec.CodeAt", "deserialize"),
        ("bitVector", "SszArm.BitVector.JointCodeAt", "deserialize"),
        ("bitList", "SszArm.BitList.JointCodeAt", "deserialize"),
        ("compare", "SszArm.NatCompare.CodeAt", "compare"),
        ("fromU128", "SszArm.NatFromU128.CodeAt", "fromU128"),
        ("add", "SszArm.NatAdd.CodeAt", "add"),
        ("division", "SszArm.NatDivision.JointCodeAt", "division"),
        ("mul", "SszArm.NatMul.JointCodeAt", "mul"),
        ("mulWord", "SszArm.NatMulWord.CodeAt", "mulWord"),
        ("exactLeaf", "SszArm.NatExact.CodeAt", "exactLeaf"),
        ("toU128", "SszArm.NatToU128.CodeAt", "toU128"),
        ("delimited", "SszArm.Delimited.CodeAt", "delimited"),
        ("memcpy", "SszArm.CodeAt", "memcpy"),
    ]
    types = [f"{predicate} s (bias + {addresses[key]}#64)" +
             (" SszArm.Memcpy.program" if field == "memcpy" else "")
             for field, predicate, key in fields]
    names = [f"h{i}" for i in range(len(fields))]
    declarations = [f"""
theorem aggregateLayout (s : ArmState) (bias : BitVec 64) :
    {LINKED}.CodeAt s bias ↔
    {' ∧ '.join(types)} := by
  constructor
  · intro code
    exact ⟨{', '.join('code.' + field for field, _, _ in fields)}⟩
  · rintro ⟨{', '.join(names)}⟩
    exact ⟨{', '.join(names)}⟩
"""]
    for namespace, offset, source, target, natural in (
            ("Serialize", "measureOffset", "serialize", "measure", False),
            ("Serialize", "emitOffset", "serialize", "emit", False),
            ("Measure", "compareOffset", "measure", "compare", False),
            ("Measure", "fromU128Offset", "measure", "fromU128", False),
            ("Measure", "memcpyOffset", "measure", "memcpy", False),
            ("Emit", "memcpyOffset", "emit", "memcpy", True),
            ("ByteView", "memcpyOffset", "deserialize", "memcpy", True),
            ("UintCodec", "memcpyOffset", "deserialize", "memcpy", True),
            ("BitVector", "divisionOffset", "deserialize", "division", False),
            ("BitVector", "addOffset", "deserialize", "add", False),
            ("BitVector", "exactOffset", "deserialize", "exactLeaf", False),
            ("BitVector", "toU128Offset", "deserialize", "toU128", False),
            ("BitVector", "memcpyOffset", "deserialize", "memcpy", False),
            ("BitList", "delimitedOffset", "deserialize", "delimited", False),
            ("Delimited", "compareOffset", "delimited", "compare", False),
            ("NatDivision", "udivOffset", "division", "udiv", True),
            ("NatMul", "wordOffset", "mul", "mulWord", False),
            ("NatMul", "memsetOffset", "mul", "memset", False)):
        expression = f"SszArm.{namespace}.{offset}"
        if natural:
            expression = f"BitVec.ofNat 64 {expression}"
        declarations.append(
            f"example : {addresses[source]}#64 + {expression} = "
            f"{addresses[target]}#64 := by decide")
    return declarations


def _literal_pcs(module, declarations):
    """Read requested locations, not words; the ELF is the only byte oracle."""
    text = (ROOT / "backends/arm/SszArm" / f"{module}.lean").read_text()
    text = re.sub(r"--[^\n]*", "", text)
    result = []
    for name in declarations:
        pattern = (r"\bdef\s+" + name +
                   r"\s*:\s*List\s*\(Nat\s*×\s*BitVec\s+32\)\s*:=\s*\[(.*?)\]")
        matches = re.findall(pattern, text, re.S)
        _require(matches, f"missing ARM sparse literal selector: {module}.{name}")
        for match in matches:
            pcs = [int(pc) for pc in re.findall(r"\(\s*(\d+)\s*,", match)]
            _require(pcs, f"empty ARM sparse literal selector: {module}.{name}")
            result.extend(pcs)
    _require(len(result) == len(set(result)), f"duplicate sparse ARM PCs: {module}")
    return result


def _legacy_declarations(image, addresses):
    declarations = []
    specs = [
        ("SerializeImpl", "Serialize", "bodyProgram", ["bodyWords\\d+"], "serialize"),
        ("MeasureImpl", "Measure", "bodyProgram", ["bodyWords\\d+"], "measure"),
        ("EmitImpl", "Emit", "bodyProgram", ["bodyProgram"], "emit"),
        ("DispatchImpl", "Dispatch", "program", ["program"], "deserialize"),
        ("ByteViewImpl", "ByteView", "bodyProgram", ["bodyProgram"], "deserialize"),
        ("BoolImpl", "BoolCodec", "program", ["program"], "deserialize"),
        ("UintImpl", "UintCodec", "bodyProgram", ["bodyProgram"], "deserialize"),
        ("BitVectorImpl", "BitVector", "program", ["program"], "deserialize"),
        ("BitListImpl", "BitList", "program", ["program"], "deserialize"),
        ("NatCompareImpl", "NatCompare", "program", ["program"], "compare"),
        ("NatFromU128Impl", "NatFromU128", "program", ["program"], "fromU128"),
        ("NatAddImpl", "NatAdd", "program", ["program"], "add"),
        ("NatDivisionImpl", "NatDivision", "program", ["program"], "division"),
        ("NatMulImpl", "NatMul", "program", ["program"], "mul"),
        ("NatMulWordImpl", "NatMulWord", "program", ["program"], "mulWord"),
        ("NatExactImpl", "NatExact", "program", ["program"], "exactLeaf"),
        ("NatToU128Impl", "NatToU128", "program", ["program"], "toU128"),
        ("DelimitedImpl", "Delimited", "program", ["program"], "delimited"),
        ("ByteViewImpl", "ByteView", "memcpyProgram", ["memcpyProgram"], "memcpy"),
        ("UintImpl", "UintCodec", "memcpyProgram", ["memcpyProgram"], "memcpy"),
    ]
    for module, namespace, program, selectors, key in specs:
        pcs = _literal_pcs(module, selectors)
        expected = [f"({pc}, 0x{_word(image, addresses[key] + pc):08x}#32)" for pc in pcs]
        generated, _ = list_binding(f"legacy{namespace}{program.title()}", "Row",
                                    f"SszArm.{namespace}.{program}", expected)
        declarations.extend(generated)
    for namespace, key, count in (("Memcpy", "memcpy", 14), ("Memset", "memset", 13),
                                  ("Udivti3", "udiv", 65)):
        expected = [f"0x{_word(image, addresses[key] + 4 * i):08x}#32" for i in range(count)]
        generated, _ = list_binding(f"legacy{namespace}Words", "(BitVec 32)",
                                    f"SszArm.{namespace}.program", expected)
        declarations.extend(generated)
    for namespace in ("Emit", "ByteView", "UintCodec"):
        base = addresses["emit" if namespace == "Emit" else "deserialize"]
        offset = addresses["memcpy"] - base
        declarations.append(f"""
example : SszArm.{namespace}.program =
    SszArm.{namespace}.bodyProgram ++
      (SszArm.Memcpy.program.zipIdx.map
        (fun (word, index) => ({offset} + 4 * index, word))) := by rfl
""")
    for namespace in (
            "Emit", "Dispatch", "ByteView", "BoolCodec", "UintCodec", "BitVector",
            "BitList", "NatCompare", "NatFromU128", "NatAdd", "NatDivision",
            "NatMul", "NatMulWord", "NatExact", "NatToU128", "Delimited"):
        declarations.append(f"""
example (s : ArmState) (base : BitVec 64) :
    SszArm.{namespace}.CodeAt s base ↔
      {LINKED}.WordsAt SszArm.{namespace}.program s base := Iff.rfl
""")
    declarations.extend(_nested_layout_declarations(addresses))
    return declarations


def _nested_layout_declarations(addresses):
    def at(predicate, source, target, suffix=""):
        offset = addresses[target] - addresses[source]
        return f"{predicate} s (base + ({offset}#64)){suffix}"

    specifications = [
        ("Serialize", "CodeAt", [
            ("body", f"{LINKED}.WordsAt SszArm.Serialize.bodyProgram s base"),
            ("measure", at("SszArm.Measure.CodeAt", "serialize", "measure")),
            ("emit", at("SszArm.Emit.CodeAt", "serialize", "emit"))]),
        ("Measure", "CodeAt", [
            ("body", f"{LINKED}.WordsAt SszArm.Measure.bodyProgram s base"),
            ("compare", at("SszArm.NatCompare.CodeAt", "measure", "compare")),
            ("fromU128", at("SszArm.NatFromU128.CodeAt", "measure", "fromU128")),
            ("memcpy", at("SszArm.CodeAt", "measure", "memcpy", " SszArm.Memcpy.program"))]),
        ("BitVector", "JointCodeAt", [
            ("body", "SszArm.BitVector.CodeAt s base"),
            ("division", at("SszArm.NatDivision.JointCodeAt", "deserialize", "division")),
            ("add", at("SszArm.NatAdd.CodeAt", "deserialize", "add")),
            ("exactLeaf", at("SszArm.NatExact.CodeAt", "deserialize", "exactLeaf")),
            ("toU128", at("SszArm.NatToU128.CodeAt", "deserialize", "toU128")),
            ("memcpy", at("SszArm.CodeAt", "deserialize", "memcpy", " SszArm.Memcpy.program"))]),
        ("BitList", "JointCodeAt", [
            ("body", "SszArm.BitList.CodeAt s base"),
            ("delimited", at("SszArm.Delimited.CodeAt", "deserialize", "delimited")),
            ("compare", "SszArm.NatCompare.CodeAt s "
             f"(base + ({addresses['delimited'] - addresses['deserialize']}#64) + "
             f"({addresses['compare'] - addresses['delimited']}#64))")]),
        ("NatMul", "JointCodeAt", [
            ("body", "SszArm.NatMul.CodeAt s base"),
            ("word", at("SszArm.NatMulWord.CodeAt", "mul", "mulWord")),
            ("memset", at("SszArm.CodeAt", "mul", "memset", " SszArm.Memset.program"))]),
    ]
    declarations = []
    for namespace, predicate, fields in specifications:
        names = [f"h{i}" for i in range(len(fields))]
        declarations.append(f"""
example (s : ArmState) (base : BitVec 64) :
    SszArm.{namespace}.{predicate} s base ↔
      {' ∧ '.join(kind for _, kind in fields)} := by
  constructor
  · intro code
    exact ⟨{', '.join('code.' + field for field, _ in fields)}⟩
  · rintro ⟨{', '.join(names)}⟩
    exact ⟨{', '.join(names)}⟩
""")
    declarations.append(f"""
example (s : ArmState) (base : BitVec 64) :
    SszArm.NatDivision.JointCodeAt s base ↔
      SszArm.NatDivision.CodeAt s base ∧
      {at('SszArm.Udivti3.CodeAt', 'division', 'udiv')} := Iff.rfl
example (s : ArmState) (base : BitVec 64) :
    SszArm.Udivti3.CodeAt s base ↔
      SszArm.CodeAt s base SszArm.Udivti3.program := Iff.rfl
""")
    return declarations


def source(image: dict) -> str:
    """Return certificates binding every full codec body and linked provider."""
    _require(set(image["functions"]) == set(FUNCTIONS), "ARM codec function set changed")
    groups = []
    for name in FUNCTIONS:
        stem = _stem(name)
        groups.append((stem, _rows(image, name), image["functions"][name]["address"],
                       f"{LINKED}.{stem}.program"))
    groups.sort(key=lambda group: group[2])
    declarations = _ordered_image_declarations(
        groups, chunked_programs={group[3] for group in groups}, part_size=CHUNK_SIZE)
    declarations.append(LIST_BINDING_HEADER)
    for stem, rows, address, program in groups:
        namespace = f"{LINKED}.{stem}"
        for index in range((len(rows) + CHUNK_SIZE - 1) // CHUNK_SIZE):
            declarations.append(
                f"example : {stem.lower()}Part{index} = {namespace}.chunk{index} := by decide")
        declarations.append(f"""
example : {namespace}.address = {address} := by decide
example : {namespace}.byteSize = {4 * len(rows)} := by decide
theorem bound{stem}CodeAt (s : ArmState) :
    {namespace}.CodeAt {{s with program := bound}} {address}#64 := by
  change ∀ row ∈ {program},
    bound.find? ({address}#64 + BitVec.ofNat 64 row.1) = some row.2
  rw [← actual{stem}_eq]
  exact {stem.lower()}_lookup
""")
    declarations.extend(_branch_declarations(image))
    declarations.extend(_simd_declarations(image))
    addresses = _legacy_addresses(image)
    declarations.extend(_layout_declarations(addresses))
    declarations.extend(_legacy_declarations(image, addresses))
    declarations.append("end SszArm.CodecBinding\naudit_native\n")
    imports = "\n".join(f"import {module}" for module in IMPORTS)
    header = _EMIT_IMAGE_ORDER.replace("import SszArm.EmitImpl", imports +
                                      "\nnamespace SszArm.CodecBinding", 1)
    return header + "\n".join(declarations)
