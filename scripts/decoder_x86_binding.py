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
    ("xchgw", "%ax,%ax", "6690"),
    ("cs", "nopw0x0(%rax,%rax,1)", "662e0f1f840000000000"),
    ("nopl", "0x0(%rax)", "0f1f4000"),
    ("nopl", "(%rax)", "0f1f00"),
    ("nopl", "0x0(%rax)", "0f1f8000000000"),
    ("nopw", "0x0(%rax,%rax,1)", "660f1f440000"),
    ("nopl", "0x0(%rax,%rax,1)", "0f1f440000"),
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
    if mnemonic in ("jmp", "jmpq", "call", "callq"):
        operation = "call" if mnemonic.startswith("call") else "jmp"
        if operation == "call" and not row.get("callee"):
            raise ValueError(f"call lacks an extracted callee binding: {row}")
        delta = row["target"] - row["pc"] - row["width"]
        return f"[.instr (.regular .W64 .W64 (.{operation} (.rel (.int64 ({delta})))))]"
    if mnemonic in ("cs", "nopl", "nopw", "xchgw"):
        if (mnemonic, operands, encoded.hex()) not in NOPS:
            raise ValueError(f"unrecognized architectural nop: {row}")
        return f"[.instr (.regular .W64 .W64 (.nop {row['width']}))]"
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
    if mnemonic == "leaq" and "(," in operands:
        match = re.fullmatch(r"(-?0x[0-9a-f]+|-?[0-9]+)?\(,%([a-z0-9]+),8\),%([a-z0-9]+)", operands)
        if match is None or match[2] not in REG64 or match[3] not in REG64:
            raise ValueError(f"unsupported base-less address: {row}")
        address = f"{{ base := none, idx := some ⟨.{match[2]}, .W64⟩, disp := .int64 ({int(match[1] or '0', 0)}) }}"
        return f"[.instr (.regular .W64 .W64 (.lea (.low .{match[3]} .W64) {address}))]"
    if mnemonic in {"cmovaq", "cmovneq"}:
        # Kraken infers the width from the registers, after the condition code.
        mnemonic = mnemonic[:-1]
    if mnemonic in {"cmpq", "cmpb", "cmpl", "movq", "movl", "movw", "movb", "testq", "testl", "testb",
                    "addq", "subq", "andq", "andl", "andb", "orq", "orb", "xorq", "xorl", "xorb",
                    "shlq", "shrq", "leaq", "leal", "decq", "popq", "retq", "setb", "sete", "setne",
                    "seta", "sbbb", "pushq", "shrl", "movabsq", "adcq", "cmova", "setl",
                    "negq", "setae", "cmovne", "imulq", "mulq"}:
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


def _image_source(rows, raw, module, namespace, constants, label_prefix=""):
    names, expressions, pieces = _image_parts(rows, raw, label_prefix)
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

def bound : Executable := (0, List.flatten [{', '.join(pieces)}])
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
