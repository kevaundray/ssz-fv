"""Translate and bind actual x86 decoder instruction images.

Disassembly-to-AST translation is trusted, as for the existing runtime bindings.
Unknown forms fail; the unbound bounds-panic label is not an executable noop.
"""
import json
import re

CONDITIONAL = {"je", "jne", "jb", "ja", "jae", "jbe", "jl", "jle"}
REG64 = {"rax", "rbx", "rcx", "rdx", "rsi", "rdi", "rbp", "rsp"} | {f"r{i}" for i in range(8, 16)}
REG32 = {f"e{name[1:]}": name for name in REG64 if not name[1:].isdigit()}
REG32.update({f"r{i}d": f"r{i}" for i in range(8, 16)})
REG8 = {"al": "rax", "bl": "rbx", "cl": "rcx", "dl": "rdx",
        "sil": "rsi", "dil": "rdi", "bpl": "rbp", "spl": "rsp"}
REG8.update({f"r{i}b": f"r{i}" for i in range(8, 16)})
ALIASES = {1580: "boolScope", 2663: "boolZero", 2674: "boolBad", 7773: "boundsPanic"}
NOPS = {
    ("nop", "", "90"),
    ("xchgw", "%ax,%ax", "6690"),
    ("cs", "nopw0x0(%rax,%rax,1)", "662e0f1f840000000000"),
    ("nopl", "0x0(%rax)", "0f1f4000"),
    ("nopl", "(%rax)", "0f1f00"),
    ("nopl", "0x0(%rax)", "0f1f8000000000"),
    ("nopw", "0x0(%rax,%rax,1)", "660f1f440000"),
    ("nopl", "0x0(%rax,%rax,1)", "0f1f440000"),
    ("nopw", "0x0(%rax,%rax,1)", "660f1f840000000000"),
}


def labels(rows, label_prefix=""):
    targets = {row["target"] for row in rows if row["asm"].split()[0] in CONDITIONAL}
    preferred = [pc for pc in (1580, 2663, 2674) if pc in targets]
    return [(label_prefix + ALIASES.get(pc, f"u{pc}"), pc)
            for pc in preferred + sorted(targets - set(preferred))]


def expression(row, label_prefix=""):
    parts = row["asm"].split(None, 1)
    mnemonic, operands = parts[0], re.sub(r"\s+", "", parts[1]) if len(parts) == 2 else ""
    encoded = bytes.fromhex(row["encoding"])
    if len(encoded) != row["width"]:
        raise ValueError(f"instruction extent mismatch: {row}")
    if mnemonic == "addr32":
        # LLD's GOT-call relaxation keeps a six-byte encoding. Address-size
        # override has no effect on a direct near CALL in 64-bit mode.
        inner = parts[1].split(None, 1)
        if len(inner) != 2 or inner[0] != "callq" or len(encoded) != 6 or encoded[:2] != b"\x67\xe8":
            raise ValueError(f"unsupported address-size override: {row}")
        mnemonic, operands = inner[0], re.sub(r"\s+", "", inner[1])
    if mnemonic in CONDITIONAL:
        name = label_prefix + ALIASES.get(row["target"], f"u{row['target']}")
        return f"parse({json.dumps(mnemonic + ' ' + name)})"
    if mnemonic == "jmpq" and operands.startswith("*"):
        registers = {"*%rax": ("rax", b"\xff\xe0"),
                     "*%rcx": ("rcx", b"\xff\xe1"),
                     "*%rdx": ("rdx", b"\xff\xe2")}
        form = registers.get(operands)
        if form is None or encoded != form[1]:
            raise ValueError(f"unsupported indirect dispatcher jump: {row}")
        return f"[.instr (.regular .W64 .W64 (.jmp (.reg .{form[0]})))]"
    if mnemonic in ("jmp", "jmpq", "call", "callq"):
        operation = "call" if mnemonic.startswith("call") else "jmp"
        if operation == "call" and not row.get("callee"):
            raise ValueError(f"call lacks an extracted callee binding: {row}")
        delta = row["target"] - row["pc"] - row["width"]
        return f"[.instr (.regular .W64 .W64 (.{operation} (.rel (.int64 ({delta})))))]"
    if mnemonic in ("cs", "nop", "nopl", "nopw", "xchgw"):
        if (mnemonic, operands, encoded.hex()) not in NOPS:
            raise ValueError(f"unrecognized architectural nop: {row}")
        return f"[.instr (.regular .W64 .W64 (.nop {row['width']}))]"
    if mnemonic == "incl":
        if operands != "%edi" or encoded != b"\xff\xc7":
            raise ValueError(f"unsupported increment encoding: {row}")
        return "[.instr (.regular .W64 .W32 (.inc (.reg (.low .rdi .W32))))]"
    if mnemonic == "movzbl":
        registers = re.fullmatch(r"%([a-z0-9]+),%([a-z0-9]+)", operands)
        if registers is not None:
            src, dst = registers.groups()
            if src not in REG8 or dst not in REG32:
                raise ValueError(f"unsupported byte-extension registers: {row}")
            return (f"[.instr (.regular .W64 .W32 (.movzx "
                    f"(.reg (.low .{REG32[dst]} .W32)) (.reg (.low .{REG8[src]} .W8))))]")
        match = re.fullmatch(r"(-?0x[0-9a-f]+|-?[0-9]+)?\(%([a-z0-9]+)(?:,%([a-z0-9]+)(?:,(1|2|4|8))?)?\),%([a-z0-9]+)", operands)
        if match is None:
            raise ValueError(f"unsupported byte load: {row}")
        disp, base, index, scale, dst = match.groups()
        if base not in REG64 or (index is not None and index not in REG64) or dst not in REG32:
            raise ValueError(f"unsupported byte-load registers: {row}")
        idx = "none" if index is None else f"some ⟨.{index}, .W{8 * int(scale or '1')}⟩"
        address = f"{{ base := some (.reg .{base}), idx := {idx}, disp := .int64 ({int(disp or '0', 0)}) }}"
        return f"[.instr (.regular .W64 .W32 (.movzx (.reg (.low .{REG32[dst]} .W32)) (.mem (w := .W8) {address})))]"
    if mnemonic == "incq":
        if operands[1:] not in REG64 or not operands.startswith("%"):
            raise ValueError(f"unsupported increment: {row}")
        return f"[.instr (.regular .W64 .W64 (.inc (.reg (.low .{operands[1:]} .W64))))]"
    if mnemonic in ("cmovbq", "cmoveq"):
        match = re.fullmatch(r"%([a-z0-9]+),%([a-z0-9]+)", operands)
        if match is None or any(reg not in REG64 for reg in match.groups()):
            raise ValueError(f"unsupported conditional move: {row}")
        src, dst = match.groups()
        condition = "c" if mnemonic == "cmovbq" else "z"
        return f"[.instr (.regular .W64 .W64 (.cmovcc .{condition} (.low .{dst} .W64) (.reg (.low .{src} .W64))))]"
    if mnemonic == "movslq":
        forms = {
            "(%rcx,%rax,4),%rax": ("rcx", "rax", b"\x48\x63\x04\x81"),
            "(%rdx,%rcx,4),%rcx": ("rdx", "rcx", b"\x48\x63\x0c\x8a"),
            "(%rdi,%rdx,4),%rdx": ("rdi", "rdx", b"\x48\x63\x14\x97"),
        }
        form = forms.get(operands)
        if form is None or encoded != form[2]:
            raise ValueError(f"unsupported signed dispatcher table load: {row}")
        base, target, _ = form
        return (f"[.instr (.regular .W64 .W64 (.movsx (.reg .{target}) "
                f"(.mem (w := .W32) {{base := some (.reg .{base}), idx := some ⟨.{target}, .W32⟩}})))]")
    if mnemonic == "leaq" and "%rip" in operands:
        match = re.fullmatch(r"(-?0x[0-9a-f]+|-?[0-9]+)\(%rip\),%(rcx|rdx|rdi)(?:#[0-9a-f]+<[^>]+>)?", operands)
        if match is None or len(encoded) != 7:
            raise ValueError(f"unsupported RIP-relative dispatcher address: {row}")
        displacement, target = int(match[1], 0), match[2]
        prefix = {"rcx": b"\x48\x8d\x0d", "rdx": b"\x48\x8d\x15", "rdi": b"\x48\x8d\x3d"}[target]
        if encoded[:3] != prefix:
            raise ValueError(f"RIP-relative destination disagrees with bytes: {row}")
        if displacement != int.from_bytes(encoded[3:], "little", signed=True):
            raise ValueError(f"RIP-relative displacement disagrees with bytes: {row}")
        return (f"[.instr (.regular .W64 .W64 (.lea .{target} "
                f"{{base := some .rip, idx := none, disp := .int64 ({displacement})}}))]")
    if mnemonic == "leaq" and "(," in operands:
        match = re.fullmatch(r"(-?0x[0-9a-f]+|-?[0-9]+)?\(,%([a-z0-9]+),8\),%([a-z0-9]+)", operands)
        if match is None or match[2] not in REG64 or match[3] not in REG64:
            raise ValueError(f"unsupported base-less address: {row}")
        address = f"{{ base := none, idx := some ⟨.{match[2]}, .W64⟩, disp := .int64 ({int(match[1] or '0', 0)}) }}"
        return f"[.instr (.regular .W64 .W64 (.lea (.low .{match[3]} .W64) {address}))]"
    if mnemonic in {"cmovaq", "cmovneq", "cmovaeq"}:
        # Kraken infers the width from the registers, after the condition code.
        mnemonic = mnemonic[:-1]
    if mnemonic in {"cmpq", "cmpb", "cmpl", "movq", "movl", "movw", "movb", "testq", "testl", "testb",
                    "addq", "addl", "subq", "andq", "andl", "andb", "orq", "orb", "xorq", "xorl", "xorb",
                    "shlq", "shll", "shlb", "shrq", "shrb", "shldq", "shrdq", "leaq", "leal", "decq", "popq", "retq", "setb", "sete", "setne",
                    "seta", "sbbb", "sbbq", "pushq", "shrl", "movabsq", "adcq", "cmova", "setl",
                    "negq", "notb", "setae", "cmovne", "cmovae", "imulq", "mulq"}:
        if not re.fullmatch(r"[%a-z0-9(),$x+-]*", operands):
            raise ValueError(f"unsupported operand syntax: {row}")
        return f"parse({json.dumps(mnemonic + ' ' + operands)})"
    raise ValueError(f"unsupported decoder instruction: {row}")


def _byte_segments(raw):
    # Bound each literal's code-generation depth without altering any gap byte.
    return [
        f"[(.byteArray (ByteArray.mk #[{','.join(map(str, raw[at:at + 256]))}]), {len(raw[at:at + 256])})]"
        for at in range(0, len(raw), 256)
    ]


def _image_parts(rows, raw, label_prefix=""):
    names = labels(rows, label_prefix)
    expressions = []
    selected = {}
    end = 0
    for row in rows:
        pc, width = row["pc"], row["width"]
        if pc < end or raw[pc:pc + width] != bytes.fromhex(row["encoding"]):
            raise ValueError(f"overlapping or mismatched instruction bytes: {row}")
        operation = expression(row, label_prefix)
        expressions.append(f"({pc}, {width}, {operation})")
        selected[pc] = (operation, width)
        end = pc + width
    # Flatten typed segments to avoid expensive elaboration of deeply nested appends.
    pieces, cursor = [], 0
    for pc in sorted(set(selected) | {pc for _, pc in names}):
        if pc < cursor or pc >= len(raw):
            raise ValueError(f"label inside instruction or outside image: {pc}")
        if cursor < pc:
            pieces.extend(_byte_segments(raw[cursor:pc]))
        pieces.extend(f"[(.label {json.dumps(name)}, 0)]" for name, address in names if address == pc)
        cursor = pc
        if pc in selected:
            operation, width = selected[pc]
            pieces.append(f"({operation} : Program).map (fun d => (d, {width}))")
            cursor += width
    if cursor < len(raw):
        pieces.extend(_byte_segments(raw[cursor:]))
    return names, expressions, pieces


def _image_source(rows, raw, module, namespace, constants, label_prefix="", *, tail_pieces=()):
    names, expressions, pieces = _image_parts(rows, raw, label_prefix)
    pieces.extend(tail_pieces)
    label_literal = ', '.join(f'({json.dumps(name)}, {pc})' for name, pc in names)
    constant_proofs = "\n".join(
        f"example : {namespace}.{name} = {value} := by decide"
        for name, value in constants.items())
    return f'''import {module}
open Kraken.X64.Parser
set_option maxRecDepth 16384
set_option maxHeartbeats 32000000

def actual : List (Nat × Nat × Program) := [{', '.join(expressions)}]
example : actual = {namespace}.program := by decide
{constant_proofs}
example : {namespace}.labels = [{label_literal}] := by decide

noncomputable def bound : Executable := (0, List.flatten [{', '.join(pieces)}])
example : {namespace}.CodeAt bound 0 := by
  constructor
  · have h : {namespace}.program.all (fun row =>
        decide (bound.directivesAtAddress (0 + Int64.ofNat row.1) =
          {namespace}.directives row)) = true := by
      simp (config := {{maxSteps := 1000000}}) [bound, Kraken.Executable.directivesAtAddress,
        Kraken.Executable.withAddresses, {namespace}.program,
        {namespace}.directives, {namespace}.labels]
    intro row hr
    exact of_decide_eq_true (List.all_eq_true.mp h row hr)
  · have h : {namespace}.labels.all (fun item =>
        decide (bound.labels.label item.1 = 0 + Int64.ofNat item.2)) = true := by
      dsimp (config := {{instances := true}}) [Executable.labels]
      simp (config := {{maxSteps := 1000000}}) [bound, Kraken.Executable.withAddresses, {namespace}.labels]
    intro item hi
    exact of_decide_eq_true (List.all_eq_true.mp h item hi)
'''


def uint_source(rows, entry, raw, frontier, callees):
    if entry != 1131 or frontier != [7773] or callees:
        raise ValueError("unexpected integer entry, frontier, or callee set")
    return _image_source(rows, raw, "SszX86.UintImpl", "SszX86.UintCodec",
                         {"entry": entry, "boundsPanic": frontier[0]})


def byte_view_source(rows, entries, raw, frontier, callees):
    if entries != [45, 1131, 750, 824] or frontier != [7773] or callees or len(rows) != 327:
        raise ValueError("unexpected byte-view entries, frontier, callees, or row count")
    return _image_source(rows, raw, "SszX86.ByteViewImpl", "SszX86.ByteView",
                         {"vectorEntry": entries[2], "listEntry": entries[3],
                          "boundsPanic": frontier[0]})


def nat_compare_source(rows, entries, raw, frontier, callees):
    if entries != [0] or frontier or callees or len(rows) != 107 or len(raw) != 373:
        raise ValueError("unexpected Nat comparison entry, frontier, callees, or image extent")
    return _image_source(rows, raw, "SszX86.NatCompareImpl", "SszX86.NatCompare",
                         {"entry": 0}, label_prefix="natCompare_")

def nat_add_source(rows, entries, raw, frontier, callees):
    if entries != [0] or frontier or callees or len(rows) != 383 or len(raw) != 1474:
        raise ValueError("unexpected Nat addition entry, frontier, callees, or image extent")
    return _image_source(rows, raw, "SszX86.NatAddImpl", "SszX86.NatAdd",
                         {"entry": 0}, label_prefix="natAdd_")


def nat_exact_source(rows, entries, raw, frontier, callees):
    if entries != [0] or frontier or callees or len(rows) != 53 or len(raw) != 190:
        raise ValueError("unexpected exact-size entry, frontier, callees, or image extent")
    return _image_source(rows, raw, "SszX86.NatExactImpl", "SszX86.NatExact",
                         {"entry": 0}, label_prefix="natExact_")


def nat_to_u128_source(rows, entries, raw, frontier, callees):
    if entries != [0] or frontier or callees or len(rows) != 39 or len(raw) != 119:
        raise ValueError("unexpected Nat.to_u128 entry, frontier, callees, or image extent")
    return _image_source(rows, raw, "SszX86.NatToU128Impl", "SszX86.NatToU128",
                         {"entry": 0}, label_prefix="natToU128_")


def nat_from_u128_source(rows, entries, raw, frontier, callees):
    if entries != [0] or frontier or callees or len(rows) != 47 or len(raw) != 177:
        raise ValueError("unexpected Nat.from_u128 entry, frontier, callees, or image extent")
    return _image_source(rows, raw, "SszX86.NatFromU128Impl", "SszX86.NatFromU128",
                         {"entry": 0}, label_prefix="natFromU128_")



def delimited_source(body, comparison, linked):
    rows, entries, raw, frontier, callees = body
    compare_rows, compare_entries, compare_raw, compare_frontier, compare_callees = comparison
    origin, span = linked
    if (entries != [0] or frontier or len(callees) != 1 or
            compare_entries != [0] or compare_frontier or compare_callees or
            len(rows) != 184 or len(raw) != 841 or
            len(compare_rows) != 107 or len(compare_raw) != 373 or origin != -59232):
        raise ValueError("unexpected delimited decoder or comparison image")
    callee = next(iter(callees.values()))
    if (callee["offset"] != origin or callee["raw"] != compare_raw.hex() or
            callee["size"] != len(compare_raw) or
            span[:len(compare_raw)] != compare_raw or span[-origin:] != raw):
        raise ValueError("delimited/comparison linked-image mismatch")
    names, expressions, pieces = _image_parts(compare_rows, compare_raw, "natCompare_")
    pieces.extend(_byte_segments(span[len(compare_raw):-origin]))
    body_names, body_expressions, body_pieces = _image_parts(rows, raw, "delimited_")
    pieces.extend(body_pieces)
    definitions, witnesses = [], []
    for suffix, namespace, base, row_expressions, image_labels in (
            ("Compare", "SszX86.NatCompare", 0, expressions, names),
            ("Delimited", "SszX86.Delimited", -origin, body_expressions, body_names)):
        label_literal = ', '.join(f'({json.dumps(name)}, {pc})' for name, pc in image_labels)
        definitions.append(f'''
def actual{suffix} : List (Nat × Nat × Program) := [{', '.join(row_expressions)}]
example : actual{suffix} = {namespace}.program := by decide
example : {namespace}.labels = [{label_literal}] := by decide
''')
        witnesses.append(f'''
example : {namespace}.CodeAt bound {base} := by
  constructor
  · have h : {namespace}.program.all (fun row =>
        decide (bound.directivesAtAddress ({base} + Int64.ofNat row.1) =
          {namespace}.directives row)) = true := by
      simp (config := {{maxSteps := 1000000}}) [bound, Kraken.Executable.directivesAtAddress,
        Kraken.Executable.withAddresses, {namespace}.program,
        {namespace}.directives, {namespace}.labels]
    intro row hr
    exact of_decide_eq_true (List.all_eq_true.mp h row hr)
  · have h : {namespace}.labels.all (fun item =>
        decide (bound.labels.label item.1 = {base} + Int64.ofNat item.2)) = true := by
      dsimp (config := {{instances := true}}) [Executable.labels]
      simp (config := {{maxSteps := 1000000}}) [bound, Kraken.Executable.withAddresses, {namespace}.labels]
    intro item hi
    exact of_decide_eq_true (List.all_eq_true.mp h item hi)
''')
    return f'''import SszX86.DelimitedImpl
import SszX86.NatCompareImpl
open Kraken.X64.Parser
set_option maxRecDepth 16384
set_option maxHeartbeats 32000000
{''.join(definitions)}
example : SszX86.Delimited.entry = 0 := by decide
example : SszX86.Delimited.compareOffset = {origin} := by decide
example : ({-origin} : Int64) + Int64.ofInt SszX86.Delimited.compareOffset = 0 := by decide
-- This image is a kernel-reduced proof witness, not a runtime executable generator.
noncomputable def bound : Executable := (0, List.flatten [{', '.join(pieces)}])
{''.join(witnesses)}
'''


def nat_division_source(body, linked):
    rows, entries, raw, frontier, callees = body
    origin, span = linked
    if entries != [0] or frontier or set(callees) != {"__udivti3"}:
        raise ValueError("unexpected Nat division entry, frontier, or callees")
    callee = callees["__udivti3"]
    kernel = bytes.fromhex(callee["raw"])
    if (len(rows) != 221 or len(raw) != 817 or origin != 0 or
            callee["offset"] != 160352 or callee["size"] != 197 or len(kernel) != 197 or
            len(span) != 160549 or span[:len(raw)] != raw or span[160352:] != kernel):
        raise ValueError("unexpected Nat division/runtime linked image")
    if [row["pc"] for row in rows if row.get("callee")] != [261, 783]:
        raise ValueError("unexpected Nat division callsites")
    names, expressions, pieces = _image_parts(rows, raw, "natDivision_")
    pieces.extend(_byte_segments(span[len(raw):160352]))
    pieces.append("(SszX86.Udivti3.executable 160352).2")
    label_literal = ", ".join(f"({json.dumps(name)}, {pc})" for name, pc in names)
    return f'''import SszX86.NatDivisionImpl
import SszX86.Udivti3Embedded
open Kraken.X64.Parser
set_option maxRecDepth 16384
set_option maxHeartbeats 32000000
def actualCaller : List (Nat × Nat × Program) := [{', '.join(expressions)}]
example : actualCaller = SszX86.NatDivision.program := by decide
example : SszX86.NatDivision.labels = [{label_literal}] := by decide
example : SszX86.NatDivision.entry = 0 := by decide
example : SszX86.NatDivision.udivOffset = 160352 := by decide
-- The kernel's actual bytes/AST/layout are checked separately before this witness.
-- Preserve every real intervening byte; no invented executable padding.
noncomputable def bound : Executable := (0, List.flatten [{', '.join(pieces)}])
example : SszX86.NatDivision.CodeAt bound 0 := by
  constructor
  · have h : SszX86.NatDivision.program.all (fun row =>
        decide (bound.directivesAtAddress (0 + Int64.ofNat row.1) =
          SszX86.NatDivision.directives row)) = true := by
      simp (config := {{maxSteps := 1000000}}) [bound, Kraken.Executable.directivesAtAddress,
        Kraken.Executable.withAddresses, SszX86.NatDivision.program,
        SszX86.NatDivision.directives, SszX86.NatDivision.labels,
        SszX86.Udivti3.executable, SszX86.Udivti3.program,
        Kraken.Layout.apply]
    intro row hr
    exact of_decide_eq_true (List.all_eq_true.mp h row hr)
  · have h : SszX86.NatDivision.labels.all (fun item =>
        decide (bound.labels.label item.1 = 0 + Int64.ofNat item.2)) = true := by
      dsimp (config := {{instances := true}}) [Executable.labels]
      simp (config := {{maxSteps := 1000000}}) [bound, Kraken.Executable.withAddresses,
        SszX86.NatDivision.labels, SszX86.Udivti3.executable,
        SszX86.Udivti3.program, Kraken.Layout.apply]
    intro item hi
    exact of_decide_eq_true (List.all_eq_true.mp h item hi)
example : SszX86.Udivti3.Embedded.CodeAt bound 160352 := by
  apply SszX86.Udivti3.Embedded.CodeAt.of_rows
  · have h : (SszX86.Udivti3.executable 160352).withAddresses.all (fun row =>
        decide (bound.directivesAtAddress row.1 =
          (SszX86.Udivti3.executable 160352).directivesAtAddress row.1)) = true := by
      dsimp (config := {{instances := true}})
        [SszX86.Udivti3.executable, SszX86.Udivti3.layout, Kraken.Layout.apply]
      simp (config := {{instances := true, maxSteps := 1000000}}) [bound, Kraken.Executable.directivesAtAddress,
        Kraken.Executable.withAddresses, SszX86.Udivti3.executable,
        SszX86.Udivti3.layout, SszX86.Udivti3.program, Kraken.Layout.apply]
    intro row hr
    exact of_decide_eq_true (List.all_eq_true.mp h row hr)
  · have h : SszX86.Udivti3.Embedded.usedLabels.all (fun name =>
        decide (bound.labels.label name =
          (SszX86.Udivti3.executable 160352).labels.label name)) = true := by
      dsimp (config := {{instances := true}})
        [Executable.labels, SszX86.Udivti3.executable, SszX86.Udivti3.layout,
          Kraken.Layout.apply]
      simp (config := {{instances := true, maxSteps := 1000000}}) [bound, Kraken.Executable.withAddresses,
        SszX86.Udivti3.Embedded.usedLabels, SszX86.Udivti3.executable,
        SszX86.Udivti3.layout, SszX86.Udivti3.program, Kraken.Layout.apply]
    intro name hn
    exact of_decide_eq_true (List.all_eq_true.mp h name hn)
'''


def emit_source(rows, entries, raw, frontiers, callees, *, linked_bytes,
                memcpy_rows, memcpy_raw, table_bytes):
    expected_frontiers = [1615, 1625, 1638, 1653, 1666, 1675, 1683, 1694]
    if (entries != [0, 256, 414] or frontiers != expected_frontiers
            or len(rows) != 276 or len(raw) != 1705 or set(callees) != {"memcpy"}):
        raise ValueError("unexpected primitive emitter entries, frontiers, or image extent")
    helper = callees["memcpy"]
    if (helper["offset"] != 110736 or helper["size"] != 57
            or len(memcpy_rows) != 19 or len(memcpy_raw) != 57
            or memcpy_raw != bytes.fromhex(helper["raw"])
            or len(linked_bytes) != 110793 or linked_bytes[:len(raw)] != raw
            or linked_bytes[110736:] != memcpy_raw):
        raise ValueError("unexpected linked emitter memcpy image")
    if table_bytes != bytes.fromhex("806b01001e6c0100b36b0100db6b0100"):
        raise ValueError("unexpected primitive emitter jump-table bytes")
    labels, _, helper_pieces = _image_parts(memcpy_rows, memcpy_raw, "copy_")
    if labels != [("copy_u9", 9), ("copy_u33", 33), ("copy_u38", 38), ("copy_u56", 56)]:
        raise ValueError("unexpected memcpy control-flow labels")
    for pc, name in ((9, "bulk"), (33, "tail"), (38, "byte"), (56, "done")):
        helper_pieces = [piece.replace(f"copy_u{pc}", f"copy_{name}")
                         for piece in helper_pieces]
    tail = _byte_segments(linked_bytes[len(raw):110736]) + helper_pieces
    source = _image_source(
        rows, raw, "SszX86.EmitMemcpyEmbedded", "SszX86.Emit",
        {"entry": 0, "memcpyOffset": 110736, "tableOffset": -92800},
        "emit_", tail_pieces=tail)
    return source + f'''
example : SszX86.Emit.tableBytes = [{', '.join(map(str, table_bytes))}] := by decide
def actualCopy : List (Directive × Nat) := List.flatten [{', '.join(helper_pieces)}]
example : actualCopy = (SszX86.memcpyExecutable 0).2 := by decide
example : SszX86.Emit.MemcpyCodeAt bound 110736 := by
  apply SszX86.Emit.MemcpyCodeAt.of_rows
  · have checked : (SszX86.memcpyExecutable 110736).withAddresses.all (fun row =>
        decide (bound.directivesAtAddress row.1 =
          (SszX86.memcpyExecutable 110736).directivesAtAddress row.1)) = true := by
      simp (config := {{instances := true, maxSteps := 1000000}}) [bound, Kraken.Executable.directivesAtAddress,
        Kraken.Executable.withAddresses, SszX86.memcpyExecutable, SszX86.memcpyLayout,
        SszX86.memcpyProgram, Kraken.Layout.apply]
    intro row member
    exact of_decide_eq_true (List.all_eq_true.mp checked row member)
  · have checked : SszX86.Emit.memcpyLabels.all (fun name =>
        decide (bound.labels.label name =
          (SszX86.memcpyExecutable 110736).labels.label name)) = true := by
      dsimp (config := {{instances := true}}) [Executable.labels]
      simp (config := {{instances := true, maxSteps := 1000000}}) [bound, Kraken.Executable.withAddresses,
        SszX86.Emit.memcpyLabels, SszX86.memcpyExecutable, SszX86.memcpyLayout,
        SszX86.memcpyProgram, Kraken.Layout.apply]
    intro name member
    exact of_decide_eq_true (List.all_eq_true.mp checked name member)
'''


def _component_witness(stem, base, image_labels, expressions, *, chunked=False,
                       split_fetch=False):
    """Bound fetch decisions shared by linked measure and serialize images."""
    namespace = f"SszX86.{stem}"
    label_literal = ", ".join(
        f"({json.dumps(name)}, {pc})" for name, pc in image_labels)
    declarations, witnesses, chunks = [], [], []
    for number, at in enumerate(range(0, len(expressions), 64)):
        chunk = f"actual{stem}Chunk{number}"
        chunks.append(chunk)
        declarations.append(
            f"def {chunk} : List (Nat × Nat × Program) := "
            f"[{', '.join(expressions[at:at + 64])}]\n")
        if chunked:
            declarations.append(
                f"theorem {chunk}_eq : {chunk} = {namespace}.programChunk{number}"
                " := by decide\n")
    declarations.append(
        f"def actual{stem} : List (Nat × Nat × Program) := {' ++ '.join(chunks)}\n")
    if chunked:
        equalities = ", ".join(f"{chunk}_eq" for chunk in chunks)
        equality_proof = (
            f"by\n  simp only [actual{stem}, {namespace}.program, {equalities}]")
    else:
        equality_proof = "by decide"
    declarations.append(
        f"theorem actual{stem}_eq : actual{stem} = {namespace}.program := "
        f"{equality_proof}\n"
        f"example : {namespace}.labels = [{label_literal}] := by decide\n"
        f"example : {namespace}.entry = 0 := by decide\n")

    # Opaque top-level certificates keep large lookup proofs out of CodeAt.
    chunk_checks = []
    for number, chunk in enumerate(chunks):
        check = f"bound{stem}Chunk{number}Fetch"
        chunk_checks.append(check)
        parts = ((f"{check}First", f"({chunk}.take 32)"),
                 (f"{check}Rest", f"({chunk}.drop 32)")) if split_fetch else ((check, chunk),)
        for part_check, part_rows in parts:
            witnesses.append(f'''theorem {part_check} : {part_rows}.all (fun row =>
    decide (bound.directivesAtAddress ({base} + Int64.ofNat row.1) =
      {namespace}.directives row)) = true := by
  simp (config := {{maxSteps := 1000000}}) [bound, Kraken.Executable.directivesAtAddress,
    Kraken.Executable.withAddresses, {chunk},
    {namespace}.directives, {namespace}.labels]
''')
        if split_fetch:
            witnesses.append(f'''theorem {check} : {chunk}.all (fun row =>
    decide (bound.directivesAtAddress ({base} + Int64.ofNat row.1) =
      {namespace}.directives row)) = true := by
  rw [← List.take_append_drop 32 {chunk}, List.all_append,
    {check}First, {check}Rest]
  rfl
''')
    if len(chunk_checks) == 1:
        fetch_proof = f"exact {chunk_checks[0]}"
    else:
        fetch_proof = (
            f"simp only [actual{stem}, List.all_append, "
            f"{', '.join(chunk_checks)}, Bool.and_true]")
    witnesses.append(f'''theorem bound{stem}Targets : {namespace}.labels.all (fun item =>
    decide (bound.labels.label item.1 = {base} + Int64.ofNat item.2)) = true := by
  dsimp (config := {{instances := true}}) [Executable.labels]
  simp (config := {{maxSteps := 1000000}}) [bound, Kraken.Executable.withAddresses,
    {namespace}.labels]

theorem bound{stem}CodeAt : {namespace}.CodeAt bound {base} := by
  constructor
  · have checked : actual{stem}.all (fun row =>
        decide (bound.directivesAtAddress ({base} + Int64.ofNat row.1) =
          {namespace}.directives row)) = true := by
      {fetch_proof}
    intro row member
    rw [← actual{stem}_eq] at member
    exact of_decide_eq_true (List.all_eq_true.mp checked row member)
  · intro item member
    exact of_decide_eq_true (List.all_eq_true.mp bound{stem}Targets item member)
''')
    return declarations, witnesses


def measure_source(bodies, span, *, origin, table_bytes=None):
    """Bind primitive measurement and both helpers in their real linked image."""
    from decoder_binding import FUNCTIONS

    members = (
        ("nat_compare", "NatCompare", "natCompare_", -32880, 107, 373),
        ("nat_from_u128", "NatFromU128", "natFromU128_", -14704, 47, 177),
        ("measure", "Measure", "measure_", 0, 476, 3528),
    )
    if set(bodies) != {member[0] for member in members}:
        raise ValueError("unexpected primitive measurement helper closure")
    rows, entries, raw, frontiers, callees = bodies["measure"]
    helper_symbols = {FUNCTIONS[key]["x86"] for key in ("nat_compare", "nat_from_u128")}
    if (entries != [0, 46, 795, 529, 616, 82, 879, 929]
            or frontiers or set(callees) != helper_symbols
            or origin != -32880 or len(span) != 36408):
        raise ValueError("unexpected primitive measurement entries, callees, or linked layout")
    expected_table = bytes.fromhex(
        "125d0100ff5f0100f55e01004c5f0100365d01005360010085600100"
        "a25f0100e66001006e5e0100b5600100245d01008c5d0100")
    if table_bytes != expected_table:
        raise ValueError("unexpected primitive measurement jump-table bytes")
    table_offset = -89316
    destinations = [
        table_offset + int.from_bytes(table_bytes[at:at + 4], "little", signed=True)
        for at in range(0, len(table_bytes), 4)
    ]
    if destinations != [46, 795, 529, 616, 82, 879, 929, 702, 1026, 394, 977, 64, 168]:
        raise ValueError("unexpected primitive measurement jump-table destinations")
    dispatch = [row for row in rows if row["pc"] == 44]
    if (len(dispatch) != 1 or dispatch[0]["width"] != 2
            or bytes.fromhex(dispatch[0]["encoding"]) != b"\xff\xe2"):
        raise ValueError("primitive measurement lacks its actual indirect dispatcher")
    for row in rows:
        if row.get("callee"):
            if (row["callee"] not in callees
                    or row["target"] != callees[row["callee"]]["offset"]):
                raise ValueError(f"primitive measurement helper target mismatch: {row}")

    # Check all component extents before constructing any proof declarations.
    for key, _, _, offset, count, size in members:
        body_rows, body_entries, body_raw, body_frontiers, body_callees = bodies[key]
        base = offset - origin
        if (len(body_rows) != count or len(body_raw) != size
                or span[base:base + size] != body_raw):
            raise ValueError(f"unexpected linked primitive measurement component: {key}")
        if key != "measure":
            helper = callees[FUNCTIONS[key]["x86"]]
            if (body_entries != [0] or body_frontiers or body_callees
                    or helper["offset"] != offset or helper["size"] != size
                    or bytes.fromhex(helper["raw"]) != body_raw):
                raise ValueError(f"primitive measurement helper ABI mismatch: {key}")

    declarations, witnesses, pieces = [], [], []
    cursor = 0
    for key, stem, prefix, offset, _, _ in members:
        body_rows, _, body_raw, _, _ = bodies[key]
        base = offset - origin
        image_labels, expressions, body_pieces = _image_parts(body_rows, body_raw, prefix)
        pieces.extend(_byte_segments(span[cursor:base]))
        pieces.extend(body_pieces)
        cursor = base + len(body_raw)
        component_declarations, component_witnesses = _component_witness(
            stem, base, image_labels, expressions, chunked=key == "measure")
        declarations.extend(component_declarations)
        witnesses.extend(component_witnesses)
    pieces.extend(_byte_segments(span[cursor:]))
    return f'''import SszX86.MeasureImpl
import SszX86.NatCompareImpl
import SszX86.NatFromU128Impl
open Kraken.X64.Parser
set_option maxRecDepth 16384
set_option maxHeartbeats 32000000

{''.join(declarations)}
example : SszX86.Measure.compareOffset = -32880 := by decide
example : SszX86.Measure.fromU128Offset = -14704 := by decide
example : (32880 : Int64) + Int64.ofInt SszX86.Measure.compareOffset = 0 := by decide
example : (32880 : Int64) + Int64.ofInt SszX86.Measure.fromU128Offset = 18176 := by decide
example : SszX86.Measure.tableOffset = {table_offset} := by decide
example : SszX86.Measure.tableAddress 32880 =
    ((32880 : Int64) + Int64.ofInt SszX86.Measure.tableOffset).toBitVec := by decide
example : SszX86.Measure.tableBytes = [{', '.join(map(str, table_bytes))}] := by decide
example : SszX86.Measure.tableBytes.length = 52 := by decide
example : SszX86.Measure.tableDestinations = [{', '.join(map(str, destinations))}] := by decide

-- Preserve every real gap byte; all three CodeAt witnesses use this one image.
noncomputable def bound : Executable := (0, List.flatten [{', '.join(pieces)}])
{''.join(witnesses)}
'''


def serialize_source(bodies, span, *, origin, table_bytes=None):
    """Bind the actual serialize wrapper and its full primitive helper closure."""
    from hashlib import sha256
    from decoder_binding import FUNCTIONS

    # Offsets are relative to the wrapper, not rebased component-local PCs.
    members = (
        ("nat_compare", "NatCompare", "natCompare_", -66368, 107, 373),
        ("nat_from_u128", "NatFromU128", "natFromU128_", -48192, 47, 177),
        ("measure", "Measure", "measure_", -33488, 476, 3528),
        ("emit", "Emit", "emit_", -29952, 276, 1705),
        ("serialize", "Serialize", "serialize_", 0, 99, 424),
        ("memcpy", "Memcpy", "copy_", 80784, 19, 57),
    )
    if (set(bodies) != {member[0] for member in members}
            or origin != -66368 or len(span) != 147209):
        raise ValueError("unexpected serialize closure or linked image extent")
    # Pin the complete extracted image, including all otherwise unselected gap
    # bytes. Component equality alone cannot detect mutations in those gaps.
    if sha256(span).hexdigest() != "b5fbd27cc6f2263803d7a3f81ccdb58d4a2662738977817247bb11b56d6d44df":
        raise ValueError("serialize linked image bytes differ from the pinned image")
    expected_tables = {
        "measure": bytes.fromhex(
            "125d0100ff5f0100f55e01004c5f0100365d01005360010085600100"
            "a25f0100e66001006e5e0100b5600100245d01008c5d0100"),
        "emit": bytes.fromhex("806b01001e6c0100b36b0100db6b0100"),
    }
    if table_bytes != expected_tables:
        raise ValueError("unexpected serialize readonly jump tables")
    entries = {
        "measure": [0, 46, 795, 529, 616, 82, 879, 929],
        "emit": [0, 256, 414],
    }
    emit_frontiers = [1615, 1625, 1638, 1653, 1666, 1675, 1683, 1694]
    graph = {
        "serialize": ("measure", "emit"),
        "measure": ("nat_compare", "nat_from_u128"),
        "emit": ("memcpy",),
    }
    offsets = {key: offset for key, _, _, offset, _, _ in members}
    selected = {}
    for key, _, _, offset, count, size in members:
        rows, body_entries, raw, frontiers, callees = bodies[key]
        base = offset - origin
        expected_callees = {FUNCTIONS[child]["x86"]: child
                            for child in graph.get(key, ())}
        if (body_entries != entries.get(key, [0])
                or frontiers != (emit_frontiers if key == "emit" else [])
                or set(callees) != set(expected_callees)
                or len(rows) != count or len(raw) != size
                or span[base:base + size] != raw):
            raise ValueError(f"unexpected serialize component contract: {key}")
        for symbol, child in expected_callees.items():
            helper = callees[symbol]
            child_raw = bodies[child][2]
            if (helper["offset"] != offsets[child] - offset
                    or helper["size"] != len(child_raw)
                    or bytes.fromhex(helper["raw"]) != child_raw):
                raise ValueError(f"serialize callee metadata mismatch: {key}/{child}")
        for row in rows:
            if row.get("callee") and (
                    row["callee"] not in callees
                    or row.get("target") != callees[row["callee"]]["offset"]):
                raise ValueError(f"serialize linked call target mismatch: {key}/{row}")
        # Normalize assembler whitespace/address annotations through the existing
        # translator, but pin every selected PC, width, operation and branch/call.
        selected[key] = [[row["pc"], row["width"], expression(row),
                          row.get("target"), row.get("callee")] for row in rows]
    selection = json.dumps(selected, sort_keys=True, separators=(",", ":")).encode()
    if sha256(selection).hexdigest() != "e4c5ac121fc03c544fcf3ade6e547036f9b307f4a751f7d62c361587cc8e768f":
        raise ValueError("serialize selected instruction rows differ from the pinned closure")

    declarations, witnesses, pieces = [], [], []
    cursor = 0
    for key, stem, prefix, offset, _, _ in members:
        rows, _, raw, _, _ = bodies[key]
        base = offset - origin
        image_labels, expressions, body_pieces = _image_parts(rows, raw, prefix)
        pieces.extend(_byte_segments(span[cursor:base]))
        if key == "memcpy":
            if image_labels != [("copy_u9", 9), ("copy_u33", 33),
                                ("copy_u38", 38), ("copy_u56", 56)]:
                raise ValueError("unexpected serialize memcpy labels")
            for pc, name in ((9, "bulk"), (33, "tail"), (38, "byte"), (56, "done")):
                body_pieces = [piece.replace(f"copy_u{pc}", f"copy_{name}")
                               for piece in body_pieces]
            declarations.append(
                f"def actualCopy : List (Directive × Nat) := List.flatten "
                f"[{', '.join(body_pieces)}]\n"
                "theorem actualCopy_eq : actualCopy = (SszX86.memcpyExecutable 0).2"
                " := by decide\n")
        else:
            component_declarations, component_witnesses = _component_witness(
                stem, base, image_labels, expressions,
                chunked=key in ("measure", "serialize"), split_fetch=key == "serialize")
            declarations.extend(component_declarations)
            witnesses.extend(component_witnesses)
        pieces.extend(body_pieces)
        cursor = base + len(raw)
    pieces.extend(_byte_segments(span[cursor:]))
    table_literals = "\n".join(
        f"example : SszX86.{key.title()}.tableBytes = "
        f"[{', '.join(map(str, raw))}] := by decide"
        for key, raw in table_bytes.items())
    return f'''import SszX86.SerializeImpl
open Kraken.X64.Parser
set_option maxRecDepth 16384
set_option maxHeartbeats 32000000

{''.join(declarations)}
{table_literals}
example : SszX86.Serialize.measureOffset = -33488 := by decide
example : SszX86.Serialize.emitOffset = -29952 := by decide
example : SszX86.Serialize.compareOffset = -66368 := by decide
example : SszX86.Serialize.fromU128Offset = -48192 := by decide
example : SszX86.Serialize.memcpyOffset = 80784 := by decide
example : (32880 : Int64) + Int64.ofInt SszX86.Measure.compareOffset = 0 := by decide
example : (32880 : Int64) + Int64.ofInt SszX86.Measure.fromU128Offset = 18176 := by decide
example : (36416 : Int64) + Int64.ofNat SszX86.Emit.memcpyOffset = 147152 := by decide
example : SszX86.Serialize.measureTableOffset = -122804 := by decide
example : SszX86.Serialize.emitTableOffset = -122752 := by decide
example : SszX86.Serialize.measureOffset + SszX86.Measure.tableOffset =
    SszX86.Serialize.measureTableOffset := by decide
example : SszX86.Serialize.emitOffset + SszX86.Emit.tableOffset =
    SszX86.Serialize.emitTableOffset := by decide
example : SszX86.Measure.tableAddress 32880 =
    ((66368 : Int64) + Int64.ofInt SszX86.Serialize.measureTableOffset).toBitVec := by decide
example : SszX86.Emit.tableAddress 36416 =
    ((66368 : Int64) + Int64.ofInt SszX86.Serialize.emitTableOffset).toBitVec := by decide

def signedTableDestinations (offset : Int) (bytes : List UInt8) : List Int :=
  (List.range (bytes.length / 4)).map fun i =>
    let displacement := (bytes.getD (4 * i) 0).toNat +
      256 * (bytes.getD (4 * i + 1) 0).toNat +
      65536 * (bytes.getD (4 * i + 2) 0).toNat +
      16777216 * (bytes.getD (4 * i + 3) 0).toNat
    offset + (if displacement < 2147483648 then Int.ofNat displacement
      else Int.ofNat displacement - 4294967296)

theorem boundMeasureTableDestinations :
    signedTableDestinations SszX86.Measure.tableOffset SszX86.Measure.tableBytes =
      SszX86.Measure.tableDestinations.map Int.ofNat := by decide
theorem boundEmitTableDestinations :
    signedTableDestinations SszX86.Emit.tableOffset SszX86.Emit.tableBytes =
      [256, 414, 307, 347] := by decide

-- One image; every real gap byte is retained. Readonly tables remain data, not code.
noncomputable def bound : Executable := (0, List.flatten [{', '.join(pieces)}])
{''.join(witnesses)}
theorem boundMemcpyFetch :
    (SszX86.memcpyExecutable 147152).withAddresses.all (fun row =>
      decide (bound.directivesAtAddress row.1 =
        (SszX86.memcpyExecutable 147152).directivesAtAddress row.1)) = true := by
  simp (config := {{instances := true, maxSteps := 1000000}}) [bound,
    Kraken.Executable.directivesAtAddress, Kraken.Executable.withAddresses,
    SszX86.memcpyExecutable, SszX86.memcpyLayout, SszX86.memcpyProgram, Kraken.Layout.apply]

theorem boundMemcpyTargets : SszX86.Emit.memcpyLabels.all (fun name =>
    decide (bound.labels.label name =
      (SszX86.memcpyExecutable 147152).labels.label name)) = true := by
  dsimp (config := {{instances := true}}) [Executable.labels]
  simp (config := {{instances := true, maxSteps := 1000000}}) [bound,
    Kraken.Executable.withAddresses, SszX86.Emit.memcpyLabels,
    SszX86.memcpyExecutable, SszX86.memcpyLayout, SszX86.memcpyProgram, Kraken.Layout.apply]

theorem boundMemcpyCodeAt : SszX86.Emit.MemcpyCodeAt bound 147152 := by
  apply SszX86.Emit.MemcpyCodeAt.of_rows
  · intro row member
    exact of_decide_eq_true (List.all_eq_true.mp boundMemcpyFetch row member)
  · intro name member
    exact of_decide_eq_true (List.all_eq_true.mp boundMemcpyTargets name member)

theorem boundSerializeClosureAt : SszX86.Serialize.ClosureAt bound 66368 := by
  refine ⟨boundSerializeCodeAt, ?_, ?_, ?_, ?_, ?_⟩
  · exact boundMeasureCodeAt
  · exact boundEmitCodeAt
  · exact boundNatCompareCodeAt
  · exact boundNatFromU128CodeAt
  · exact boundMemcpyCodeAt
'''
