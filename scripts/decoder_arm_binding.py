#!/usr/bin/env python3
"""Generate Lean binding witnesses for ARM decoder sparse programs."""
from __future__ import annotations

MEMCPY_OFFSET = 104240
ENTRY = 148
BOUNDS_PANIC = 9880


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def _parse_hex_bytes(text: str) -> bytes:
    text = text.strip()
    _require(len(text) % 2 == 0, "malformed hex byte string")
    return bytes.fromhex(text)


def _word_le(chunk: bytes) -> int:
    _require(len(chunk) == 4, "expected 4 bytes per word")
    return int.from_bytes(chunk, "little")


def _encoding_bytes(word_hex: str) -> bytes:
    _require(len(word_hex) == 8, f"malformed ARM encoding width: {word_hex!r}")
    return int(word_hex, 16).to_bytes(4, "little")


def _validate_rows(rows, raw_bytes: bytes) -> None:
    last_end = 0
    for row in rows:
        _require(isinstance(row.get("pc"), int), f"row pc must be an int: {row!r}")
        _require(row.get("width") == 4, f"unexpected row width: {row!r}")
        encoding = row.get("encoding")
        _require(isinstance(encoding, str), f"row encoding must be a string: {row!r}")
        encoded = _encoding_bytes(encoding)
        pc = row["pc"]
        end = pc + row["width"]
        _require(pc >= last_end, f"rows not in nondecreasing order: {row!r}")
        _require(end <= len(raw_bytes), f"row past raw extent: {row!r}")
        _require(raw_bytes[pc:end] == encoded, f"raw/encoding mismatch at pc {pc}: {row!r}")
        last_end = end


def _rows_expr(rows) -> str:
    return ", ".join(f"({row['pc']}, 0x{row['encoding']}#32)" for row in rows)


def _memcpy_rows_expr(raw_hex: str) -> str:
    raw = _parse_hex_bytes(raw_hex)
    _require(len(raw) == 56, f"unexpected memcpy raw length {len(raw)}; expected 56")
    _require(len(raw) % 4 == 0, "memcpy raw length must be a multiple of 4")
    rows = []
    for index in range(0, len(raw), 4):
        rows.append((index, _word_le(raw[index:index + 4])))
    _require(len(rows) == 14, f"unexpected memcpy word count {len(rows)}; expected 14")
    return ", ".join(f"({pc}, 0x{word:08x}#32)" for pc, word in rows)


def _image_source(rows, raw, callees, module, namespace, constants) -> str:
    _require(set(callees) == {"memcpy"}, f"unsupported callees: {sorted(callees)}")
    _validate_rows(rows, raw)

    memcpy = callees["memcpy"]
    _require(memcpy.get("offset") == MEMCPY_OFFSET, f"unexpected memcpy offset {memcpy.get('offset')}"
             f"; expected {MEMCPY_OFFSET}")
    _require(memcpy.get("size") == 56, f"unexpected memcpy size {memcpy.get('size')}; expected 56")
    memcpy_rows = _memcpy_rows_expr(memcpy["raw"])

    body_rows = _rows_expr(rows)
    constant_proofs = "\n".join(
        f"example : {namespace}.{name} = {value} := by decide"
        for name, value in constants.items())

    return f'''import {module}

set_option maxRecDepth 16384
set_option maxHeartbeats 16000000

open BitVec


def actualBody : List (Nat × BitVec 32) := [{body_rows}]
theorem actualBody_eq : actualBody = {namespace}.bodyProgram := by decide

/-- Linked memcpy rows, relative to the callee entry. -/
def actualMemcpy : List (Nat × BitVec 32) := [{memcpy_rows}]
theorem actualMemcpy_eq : actualMemcpy = {namespace}.memcpyProgram := by decide
example : actualMemcpy.map Prod.snd = SszArm.Memcpy.program := by decide

{constant_proofs}
example : {namespace}.memcpyOffset = {MEMCPY_OFFSET} := by decide

def actualProgram : List (Nat × BitVec 32) :=
  actualBody ++ actualMemcpy.map (fun row => ({MEMCPY_OFFSET} + row.1, row.2))
theorem actualProgram_eq : actualProgram = {namespace}.program := by decide

def bound : Program := actualProgram.map (fun row => (BitVec.ofNat 64 row.1, row.2))

example (s : ArmState) : {namespace}.CodeAt {{s with program := bound}} 0 := by
  change ∀ row ∈ {namespace}.program,
    bound.find? (0 + BitVec.ofNat 64 row.1) = some row.2
  rw [← actualProgram_eq]
  have h : actualProgram.all (fun row =>
      decide (bound.find? (0 + BitVec.ofNat 64 row.1) = some row.2)) = true := by decide
  intro row hr
  exact of_decide_eq_true (List.all_eq_true.mp h row hr)
'''


def uint_source(rows, entry, raw, frontier, callees) -> str:
    _require(entry == ENTRY, f"unexpected entry {entry}; expected {ENTRY}")
    _require(frontier == [BOUNDS_PANIC], f"unexpected frontier {frontier}; expected [{BOUNDS_PANIC}]")
    _require(len(rows) == 359, f"unexpected body row count {len(rows)}; expected 359")
    return _image_source(rows, raw, callees, "SszArm.UintImpl", "SszArm.UintCodec",
                         {"entry": entry, "boundsPanic": frontier[0]})


def byte_view_source(rows, entries, raw, frontier, callees) -> str:
    _require(entries == [604, 148, 1972, 688], f"unexpected byte-view entries {entries}")
    _require(frontier == [BOUNDS_PANIC], f"unexpected byte-view frontier {frontier}")
    _require(len(rows) == 513, f"unexpected byte-view body row count {len(rows)}; expected 513")
    return _image_source(rows, raw, callees, "SszArm.ByteViewImpl", "SszArm.ByteView",
                         {"vectorEntry": entries[2], "listEntry": entries[3],
                          "boundsPanic": frontier[0]})


def nat_compare_source(rows, entries, raw, frontier, callees) -> str:
    _require(entries == [0] and not frontier and not callees,
             "unexpected Nat comparison entry, frontier, or callees")
    _require(len(rows) == 178 and len(raw) == 712,
             "unexpected Nat comparison instruction count or image extent")
    return _leaf_source(rows, raw, "SszArm.NatCompareImpl", "SszArm.NatCompare")


def nat_add_source(rows, entries, raw, frontier, callees) -> str:
    _require(entries == [0] and not frontier and not callees,
             "unexpected Nat addition entry, frontier, or callees")
    _require(len(rows) == 603 and len(raw) == 2412,
             "unexpected Nat addition instruction count or image extent")
    return _leaf_source(rows, raw, "SszArm.NatAddImpl", "SszArm.NatAdd")


def nat_exact_source(rows, entries, raw, frontier, callees) -> str:
    _require(entries == [0] and not frontier and not callees,
             "unexpected exact-size entry, frontier, or callees")
    _require(len(rows) == 74 and len(raw) == 296,
             "unexpected exact-size instruction count or image extent")
    return _leaf_source(rows, raw, "SszArm.NatExactImpl", "SszArm.NatExact")


def nat_to_u128_source(rows, entries, raw, frontier, callees) -> str:
    _require(entries == [0] and not frontier and not callees,
             "unexpected Nat.to_u128 entry, frontier, or callees")
    _require(len(rows) == 96 and len(raw) == 384,
             "unexpected Nat.to_u128 instruction count or image extent")
    return _leaf_source(rows, raw, "SszArm.NatToU128Impl", "SszArm.NatToU128")


def nat_from_u128_source(rows, entries, raw, frontier, callees) -> str:
    _require(entries == [0] and not frontier and not callees,
             "unexpected Nat.from_u128 entry, frontier, or callees")
    _require(len(rows) == 105 and len(raw) == 420,
             "unexpected Nat.from_u128 instruction count or image extent")
    return _leaf_source(rows, raw, "SszArm.NatFromU128Impl", "SszArm.NatFromU128")


def _leaf_source(rows, raw, module, namespace) -> str:
    _validate_rows(rows, raw)
    return f'''import {module}

set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
open BitVec

def actualProgram : List (Nat × BitVec 32) := [{_rows_expr(rows)}]
theorem actualProgram_eq : actualProgram = {namespace}.program := by decide
example : {namespace}.entry = 0 := by decide

def bound : Program := actualProgram.map (fun row => (BitVec.ofNat 64 row.1, row.2))
example (s : ArmState) : {namespace}.CodeAt {{s with program := bound}} 0 := by
  change ∀ row ∈ {namespace}.program,
    bound.find? (0 + BitVec.ofNat 64 row.1) = some row.2
  rw [← actualProgram_eq]
  have h : actualProgram.all (fun row =>
      decide (bound.find? (0 + BitVec.ofNat 64 row.1) = some row.2)) = true := by decide
  intro row hr
  exact of_decide_eq_true (List.all_eq_true.mp h row hr)
'''


def delimited_source(body, comparison, linked) -> str:
    rows, entries, raw, frontier, callees = body
    compare_rows, compare_entries, compare_raw, compare_frontier, compare_callees = comparison
    origin, span = linked
    _require(entries == [0] and not frontier and len(callees) == 1,
             "unexpected delimited decoder entry, frontier, or callees")
    _require(compare_entries == [0] and not compare_frontier and not compare_callees,
             "unexpected Nat comparison entry, frontier, or callees")
    _require(len(rows) == 253 and len(raw) == 1012 and len(compare_rows) == 178
             and len(compare_raw) == 712 and origin == -69940,
             "unexpected delimited decoder or comparison image extent")
    _validate_rows(rows, raw)
    _validate_rows(compare_rows, compare_raw)
    callee = next(iter(callees.values()))
    _require(callee["offset"] == origin and callee["raw"] == compare_raw.hex()
             and callee["size"] == len(compare_raw)
             and span[:len(compare_raw)] == compare_raw and span[-origin:] == raw,
             "delimited/comparison linked-image mismatch")
    witnesses = []
    for suffix, namespace, base in (("Compare", "SszArm.NatCompare", 0),
                                     ("Delimited", "SszArm.Delimited", -origin)):
        witnesses.append(f'''
example (s : ArmState) : {namespace}.CodeAt {{s with program := bound}} {base} := by
  change ∀ row ∈ {namespace}.program,
    bound.find? ({base} + BitVec.ofNat 64 row.1) = some row.2
  rw [← actual{suffix}_eq]
  have h : actual{suffix}.all (fun row =>
      decide (bound.find? ({base} + BitVec.ofNat 64 row.1) = some row.2)) = true := by decide
  intro row hr
  exact of_decide_eq_true (List.all_eq_true.mp h row hr)
''')
    return f'''import SszArm.DelimitedImpl
import SszArm.NatCompareImpl
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
open BitVec
def actualCompare : List (Nat × BitVec 32) := [{_rows_expr(compare_rows)}]
theorem actualCompare_eq : actualCompare = SszArm.NatCompare.program := by decide
def actualDelimited : List (Nat × BitVec 32) := [{_rows_expr(rows)}]
theorem actualDelimited_eq : actualDelimited = SszArm.Delimited.program := by decide
example : SszArm.Delimited.entry = 0 := by decide
example : SszArm.Delimited.compareOffset = BitVec.ofInt 64 ({origin}) := by decide
example : ({-origin} : BitVec 64) + SszArm.Delimited.compareOffset = 0 := by decide
def bound : Program :=
  (actualCompare ++ actualDelimited.map (fun (row : Nat × BitVec 32) => ({-origin} + row.1, row.2))).map
    (fun (row : Nat × BitVec 32) => (BitVec.ofNat 64 row.1, row.2))
{''.join(witnesses)}
'''


def nat_division_source(body, linked) -> str:
    rows, entries, raw, frontier, callees = body
    origin, span = linked
    _require(entries == [0] and not frontier and set(callees) == {"__udivti3"},
             "unexpected Nat division entry, frontier, or callees")
    callee = callees["__udivti3"]
    kernel = bytes.fromhex(callee["raw"])
    _require(len(rows) == 282 and len(raw) == 1128 and origin == 0
             and callee["offset"] == 182664 and callee["size"] == 260
             and len(kernel) == 260 and len(span) == 182924
             and span[:len(raw)] == raw and span[182664:] == kernel,
             "unexpected Nat division/runtime linked image")
    _require([row["pc"] for row in rows if row.get("callee")] == [316, 360, 564, 636, 676],
             "unexpected Nat division callsites")
    _validate_rows(rows, raw)
    words = ", ".join(f"0x{_word_le(kernel[i:i + 4]):08x}#32"
                      for i in range(0, len(kernel), 4))
    return f'''import SszArm.NatDivisionImpl
import SszArm.Udivti3
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
open BitVec
def actualCaller : List (Nat × BitVec 32) := [{_rows_expr(rows)}]
theorem actualCaller_eq : actualCaller = SszArm.NatDivision.program := by decide
def actualKernel : List (BitVec 32) := [{words}]
theorem actualKernel_eq : actualKernel = SszArm.Udivti3.program := by decide
example : SszArm.NatDivision.entry = 0 := by decide
example : SszArm.NatDivision.udivOffset = 182664 := by decide
def bound : Program :=
  (actualCaller ++ actualKernel.mapIdx (fun i word => (182664 + 4 * i, word))).map
    (fun (row : Nat × BitVec 32) => (BitVec.ofNat 64 row.1, row.2))
example (s : ArmState) : SszArm.NatDivision.CodeAt {{s with program := bound}} 0 := by
  change ∀ row ∈ SszArm.NatDivision.program,
    bound.find? (0 + BitVec.ofNat 64 row.1) = some row.2
  rw [← actualCaller_eq]
  have h : actualCaller.all (fun row =>
      decide (bound.find? (0 + BitVec.ofNat 64 row.1) = some row.2)) = true := by decide
  intro row hr
  exact of_decide_eq_true (List.all_eq_true.mp h row hr)
example (s : ArmState) : SszArm.Udivti3.CodeAt {{s with program := bound}} 182664 := by
  change ∀ k (hk : k < SszArm.Udivti3.program.length),
    bound.find? (182664 + BitVec.ofNat 64 (4 * k)) = some SszArm.Udivti3.program[k]
  have h : ∀ k : Fin actualKernel.length,
      bound.find? (182664 + BitVec.ofNat 64 (4 * k.val)) = some actualKernel[k.val] := by decide
  intro k hk
  have actualBound : k < actualKernel.length := by simpa only [actualKernel_eq] using hk
  simpa only [actualKernel_eq] using h ⟨k, actualBound⟩
'''


def emit_source(rows, entries, raw, frontiers, callees) -> str:
    """Bind primitive emitter words and real memcpy without deep flat lookups."""
    _require(entries == [0] and len(rows) == 336 and len(raw) == 1996,
             "unexpected primitive emitter image")
    _require(frontiers == [740, 1916, 1928, 1944, 1960, 1972, 1984],
             "unexpected primitive emitter frontiers")
    _require(set(callees) == {"memcpy"}, "unexpected primitive emitter callees")
    _validate_rows(rows, raw)
    callee = callees["memcpy"]
    copy_bytes = _parse_hex_bytes(callee["raw"])
    _require(callee["offset"] == 118996 and callee["size"] == 56 and len(copy_bytes) == 56,
             "unexpected linked emitter memcpy layout")
    copy_rows = ", ".join(
        f"({118996 + i}, 0x{_word_le(copy_bytes[i:i + 4]):08x}#32)"
        for i in range(0, len(copy_bytes), 4))
    # Each suffix equality unfolds at most 64 cons cells. A whole-image
    # equality or one flat lookup per word exceeds the default recursion bound.
    parts = [rows[i:i + 64] for i in range(0, len(rows), 64)]
    declarations = []
    for index, part in enumerate(parts):
        declarations.append(f"def part{index} : List Row := [{_rows_expr(part)}]")
        declarations.append(f"def tail{index} : List Row := [{_rows_expr(rows[index * 64:])}]")
    for index in range(len(parts) - 1):
        declarations.append(
            f"theorem split{index} : tail{index} = part{index} ++ tail{index + 1} := by rfl")
    declarations.append(f"def copyRows : List Row := [{copy_rows}]")
    declarations.append("def actualProgram : List Row := tail0 ++ copyRows")
    declarations.append("theorem actualProgram_eq : actualProgram = SszArm.Emit.program := by rfl")
    declarations.append("example : SszArm.Emit.entry = 0 := by rfl")
    declarations.append(f"example : SszArm.Emit.frontiers = {frontiers} := by rfl")
    for index, part in enumerate(parts):
        lo, hi = part[0]["pc"], part[-1]["pc"] + 4
        declarations.append(f"""theorem segment{index} : Segment part{index} {lo} {hi} := by
  refine ⟨by decide, by decide, ?_⟩
  have checked : part{index}.all (fun row => decide ({lo} ≤ key row ∧ key row < {hi})) = true := by decide
  intro row member
  exact of_decide_eq_true (List.all_eq_true.mp checked row member)
""")
    declarations.append("""theorem copySegment : Segment copyRows 118996 119052 := by
  refine ⟨by decide, by decide, ?_⟩
  have checked : copyRows.all (fun row => decide (118996 ≤ key row ∧ key row < 119052)) = true := by decide
  intro row member
  exact of_decide_eq_true (List.all_eq_true.mp checked row member)
""")
    end = rows[-1]["pc"] + 4
    for index in reversed(range(len(parts))):
        proof = (f"  exact segment{index}" if index == len(parts) - 1 else
                 f"  rw [split{index}]\n  exact join segment{index} suffix{index + 1} (by decide)")
        declarations.append(
            f"theorem suffix{index} : Segment tail{index} {parts[index][0]['pc']} {end} := by\n{proof}")
    return _EMIT_IMAGE_ORDER + "\n".join(declarations) + """
theorem all_ordered : Ordered actualProgram := (join suffix0 copySegment (by decide)).2.1
def bound : Program := actualProgram.map (fun row => (BitVec.ofNat 64 row.1, row.2))
example (s : ArmState) : SszArm.Emit.CodeAt {s with program := bound} 0 := by
  change ∀ row ∈ SszArm.Emit.program, bound.find? (0 + BitVec.ofNat 64 row.1) = some row.2
  rw [← actualProgram_eq]
  intro row member
  simpa only [bound, show (0 : BitVec 64) = 0#64 by decide, BitVec.zero_add] using
    lookup actualProgram all_ordered row member
"""


_EMIT_IMAGE_ORDER = """import SszArm.EmitImpl
open BitVec
abbrev Row := Nat × BitVec 32
def key (row : Row) : Nat := (BitVec.ofNat 64 row.1).toNat
abbrev Ordered (rows : List Row) : Prop := rows.Pairwise (fun x y => key x < key y)
def Segment (rows : List Row) (lo hi : Nat) : Prop :=
  lo ≤ hi ∧ Ordered rows ∧ ∀ row ∈ rows, lo ≤ key row ∧ key row < hi
theorem join {xs ys : List Row} {a b c d : Nat}
    (left : Segment xs a b) (right : Segment ys c d) (gap : b ≤ c) :
    Segment (xs ++ ys) a d := by
  refine ⟨Nat.le_trans left.1 (Nat.le_trans gap right.1),
    List.pairwise_append.mpr ⟨left.2.1, right.2.1, ?_⟩, ?_⟩
  · intro x hx y hy
    have lx := left.2.2 x hx
    have ry := right.2.2 y hy
    exact Nat.lt_of_lt_of_le lx.2 (Nat.le_trans gap ry.1)
  · intro row member
    rcases List.mem_append.mp member with h | h
    · have bounds := left.2.2 row h
      exact ⟨bounds.1, Nat.lt_of_lt_of_le bounds.2 (Nat.le_trans gap right.1)⟩
    · have bounds := right.2.2 row h
      exact ⟨Nat.le_trans left.1 (Nat.le_trans gap bounds.1), bounds.2⟩
theorem lookup (rows : List Row) (ordered : Ordered rows) (row : Row) (member : row ∈ rows) :
    Map.find? (rows.map (fun r => (BitVec.ofNat 64 r.1, r.2))) (BitVec.ofNat 64 row.1) =
      some row.2 := by
  induction rows with
  | nil => cases member
  | cons first rest ih =>
    have pieces := List.pairwise_cons.mp ordered
    rcases List.mem_cons.mp member with same | inside
    · subst row
      simp only [List.map_cons, Map.find?, ↓reduceIte]
    · have different : BitVec.ofNat 64 first.1 ≠ BitVec.ofNat 64 row.1 := by
        intro same
        have less := pieces.1 row inside
        unfold key at less
        rw [same] at less
        exact Nat.lt_irrefl _ less
      simp only [List.map_cons, Map.find?, if_neg different]
      exact ih pieces.2 inside
"""



def _ordered_image_declarations(groups, *, chunked_programs=(), flat_programs=(), part_size=100):
    """Share bounded word equalities and ordered lookup for linked ARM images."""
    declarations = ["""
def shiftRows (base : Nat) (rows : List Row) : List Row :=
  rows.map (fun row => (base + row.1, row.2))
theorem shiftRows_append (base : Nat) (xs ys : List Row) :
    shiftRows base (xs ++ ys) = shiftRows base xs ++ shiftRows base ys := by
  exact List.map_append
theorem append_eq {xs xs' ys ys' : List Row}
    (left : xs = xs') (right : ys = ys') : xs ++ ys = xs' ++ ys' := by
  rw [left, right]
"""]

    def join_proofs(proofs):
        result = proofs[-1]
        for proof in reversed(proofs[:-1]):
            result = f"(join {proof} {result} (by decide))"
        return result

    def append_rows(names):
        result = names[-1]
        for name in reversed(names[:-1]):
            result = f"({name} ++ {result})"
        return result

    for name, group_rows, base, program in groups:
        # Preserve literal module chunk boundaries where required; flat programs
        # may use smaller blocks to keep equality checks within default limits.
        parts = [group_rows[i:i + part_size] for i in range(0, len(group_rows), part_size)]
        part_names = []
        part_proofs = []
        for index, part in enumerate(parts):
            part_name = f"{name.lower()}Part{index}"
            half_size = (part_size + 1) // 2
            halves = [part[i:i + half_size] for i in range(0, len(part), half_size)]
            half_names = []
            half_proofs = []
            for half_index, half in enumerate(halves):
                half_name = f"{part_name}_{half_index}"
                half_names.append(half_name)
                half_proofs.append(f"{half_name}_segment")
                lo, hi = base + half[0]["pc"], base + half[-1]["pc"] + 4
                declarations.append(f"def {half_name} : List Row := [{_rows_expr(half)}]")
                declarations.append(f"""theorem {half_name}_segment :
    Segment (shiftRows {base} {half_name}) {lo} {hi} := by
  refine ⟨by decide, by decide, ?_⟩
  have checked : (shiftRows {base} {half_name}).all
      (fun row => decide ({lo} ≤ key row ∧ key row < {hi})) = true := by decide
  intro row member
  exact of_decide_eq_true (List.all_eq_true.mp checked row member)
""")
            declarations.append(f"def {part_name} : List Row := {append_rows(half_names)}")
            half_rewrites = ", shiftRows_append" if len(half_names) > 1 else ""
            declarations.append(f"""theorem {part_name}_segment :
    Segment (shiftRows {base} {part_name})
      {base + part[0]["pc"]} {base + part[-1]["pc"] + 4} := by
  simp only [{part_name}{half_rewrites}]
  exact {join_proofs(half_proofs)}
""")
            part_names.append(part_name)
            part_proofs.append(f"{part_name}_segment")
        declarations.append(f"def actual{name} : List Row := {append_rows(part_names)}")
        if program is not None:
            equality = "(by rfl)"
            for _ in (parts[:-1] if program in chunked_programs else []):
                equality = f"(append_eq (by rfl) {equality})"
            normalization = (
                f"  conv =>\n    rhs\n    unfold {program}\n    simp only [List.append_assoc]\n"
                if program in chunked_programs else "")
            if program in flat_programs:
                # Check finite prefixes, then compose take/drop identities.
                # Comparing two long literal suffixes directly exceeds kernel depth.
                tails = [f"{name.lower()}Tail{i}" for i in range(len(parts))]
                for index, tail in enumerate(tails):
                    source = program if index == 0 else (
                        f"{tails[index - 1]}.drop {len(parts[index - 1])}")
                    declarations.append(f"def {tail} : List Row := {source}")
                    declarations.append(
                        f"theorem {tail}_head : {tail}.take {len(parts[index])} = "
                        f"{part_names[index]} := by decide")
                for index in reversed(range(len(parts))):
                    tail, count = tails[index], len(parts[index])
                    if index + 1 < len(parts):
                        suffix = f"{tails[index + 1]}_eq"
                        proof = f"append_eq {tail}_head {suffix}"
                    else:
                        proof = (f"(append_eq {tail}_head (show {tail}.drop {count} = [] "
                                 f"from by decide)).trans (List.append_nil _)")
                    declarations.append(
                        f"theorem {tail}_eq : {tail} = {append_rows(part_names[index:])} :=\n"
                        f"  (List.take_append_drop {count} {tail}).symm.trans ({proof})")
                normalization = ""
                equality = f"{tails[0]}_eq.symm"
            declarations.append(
                f"theorem actual{name}_eq : actual{name} = {program} := by\n"
                f"{normalization}  exact {equality}")
        part_rewrites = ", shiftRows_append" if len(part_names) > 1 else ""
        declarations.append(f"""theorem actual{name}_segment :
    Segment (shiftRows {base} actual{name})
      {base + group_rows[0]["pc"]} {base + group_rows[-1]["pc"] + 4} := by
  simp only [actual{name}{part_rewrites}]
  exact {join_proofs(part_proofs)}
""")

    declarations.append(
        "def actualProgram : List Row := " +
        append_rows([f"shiftRows {base} actual{name}" for name, _, base, _ in groups]))
    declarations.append(
        "theorem all_ordered : Ordered actualProgram :=\n  " +
        f"{join_proofs([f'actual{name}_segment' for name, _, _, _ in groups])}.2.1")
    declarations.append("""
def bound : Program := actualProgram.map (fun row => (BitVec.ofNat 64 row.1, row.2))
theorem lookup_shifted (base : Nat) (rows : List Row)
    (included : ∀ row ∈ shiftRows base rows, row ∈ actualProgram)
    (row : Row) (member : row ∈ rows) :
    bound.find? (BitVec.ofNat 64 base + BitVec.ofNat 64 row.1) = some row.2 := by
  have inside : (base + row.1, row.2) ∈ shiftRows base rows :=
    List.mem_map.mpr ⟨row, member, rfl⟩
  have found := lookup actualProgram all_ordered (base + row.1, row.2)
    (included _ inside)
  simpa only [bound, BitVec.ofNat_add] using found
""")
    for index, (name, _, base, _) in enumerate(groups):
        included = "member" if index == len(groups) - 1 else "(Or.inl member)"
        for _ in range(index):
            included = f"(Or.inr {included})"
        declarations.append(f"""theorem {name.lower()}_lookup (row : Row)
    (member : row ∈ actual{name}) :
    bound.find? ({base}#64 + BitVec.ofNat 64 row.1) = some row.2 := by
  apply lookup_shifted {base} actual{name} ?_ row member
  intro other member
  simp only [actualProgram, List.mem_append]
  exact {included}
""")
    return declarations


def measure_source(bodies, span, *, origin, table_bytes=None) -> str:
    """Bind the selected measurement body and all helpers in one linked program."""
    _require(set(bodies) == {"measure", "nat_compare", "nat_from_u128", "memcpy"},
             "unexpected measurement function set")
    _require(origin == -40272 and len(span) == 163676 and table_bytes is None,
             "unexpected ARM measurement span, origin, or table")
    rows, entries, raw, frontiers, callees = bodies["measure"]
    _require(entries == [0] and len(rows) == 1030 and len(raw) == 4352
             and frontiers == [1092, 3108],
             "unexpected primitive measurement image")
    helpers = (
        ("nat_compare", "_ZN13ssz_fv_native3nat3Nat7compare17h066191a25a9f736bE",
         -40272, 178, 712, "Compare", "SszArm.NatCompare.program"),
        ("nat_from_u128", "_ZN13ssz_fv_native3nat3Nat9from_u12817h73292f97725c3b7dE",
         -15748, 105, 420, "FromU128", "SszArm.NatFromU128.program"),
        ("memcpy", "memcpy", 123348, 14, 56, "Memcpy", None),
    )
    _require(set(callees) == {helper[1] for helper in helpers},
             "unexpected primitive measurement callees")
    _validate_rows(rows, raw)
    caller_base = -origin
    _require(span[caller_base:caller_base + len(raw)] == raw,
             "measurement caller does not match linked span")
    groups = []
    for key, symbol, offset, count, size, name, program in helpers:
        helper_rows, helper_entries, helper_raw, helper_frontiers, helper_callees = bodies[key]
        _require(helper_entries == [0] and not helper_frontiers and not helper_callees
                 and len(helper_rows) == count and len(helper_raw) == size,
                 f"unexpected measurement {key} image")
        _validate_rows(helper_rows, helper_raw)
        _require([row["pc"] for row in helper_rows] == list(range(0, size, 4)),
                 f"incomplete measurement {key} image")
        callee = callees[symbol]
        base = caller_base + offset
        _require(callee["offset"] == offset and callee["size"] == size
                 and _parse_hex_bytes(callee["raw"]) == helper_raw
                 and span[base:base + size] == helper_raw,
                 f"measurement {key} linked-image mismatch")
        groups.append((name, helper_rows, base, program))
    groups.insert(2, ("Body", rows, caller_base, "SszArm.Measure.bodyProgram"))
    declarations = _ordered_image_declarations(
        groups, chunked_programs={"SszArm.Measure.bodyProgram"})
    declarations.append("""
example : SszArm.Measure.entry = 0 := by rfl
example : SszArm.Measure.frontiers = [1092, 3108] := by rfl
example : SszArm.Measure.compareOffset = -40272#64 := by rfl
example : SszArm.Measure.fromU128Offset = -15748#64 := by rfl
example : SszArm.Measure.memcpyOffset = 123348#64 := by rfl

theorem measure_codeAt (s : ArmState) :
    SszArm.Measure.CodeAt {s with program := bound} 40272#64 := by
  constructor
  · change ∀ row ∈ SszArm.Measure.bodyProgram,
      bound.find? (40272#64 + BitVec.ofNat 64 row.1) = some row.2
    rw [← actualBody_eq]
    exact body_lookup
  · change ∀ row ∈ SszArm.NatCompare.program,
      bound.find? (0#64 + BitVec.ofNat 64 row.1) = some row.2
    rw [← actualCompare_eq]
    exact compare_lookup
  · change ∀ row ∈ SszArm.NatFromU128.program,
      bound.find? (24524#64 + BitVec.ofNat 64 row.1) = some row.2
    rw [← actualFromU128_eq]
    exact fromu128_lookup
  · change ∀ k (hk : k < SszArm.Memcpy.program.length),
      bound.find? (163620#64 + BitVec.ofNat 64 (4 * k)) = some SszArm.Memcpy.program[k]
    have checked : ∀ k : Fin 14,
        (4 * k.val, SszArm.Memcpy.program[k.val]) ∈ actualMemcpy := by decide
    intro k hk
    exact memcpy_lookup _ (checked ⟨k, hk⟩)
""")
    return _EMIT_IMAGE_ORDER.replace(
        "import SszArm.EmitImpl", "import SszArm.MeasureImpl", 1
    ) + "\n".join(declarations)


def serialize_source(bodies, span, *, origin, table_bytes=None) -> str:
    """Bind the actual serialize wrapper and primitive closure in one ARM image."""
    from hashlib import sha256

    # Relative to the original standalone serialize entry, not a synthetic root.
    specs = (
        ("nat_compare", -78380, 712, ((0, 712),), [],
         "51111a14f3070af5098217e615c08827975cf452846ba01826748c2e5655262e",
         "Compare", "SszArm.NatCompare.program"),
        ("nat_from_u128", -53856, 420, ((0, 420),), [],
         "129949dabc6c440892c7db8dfb189bb12566f21934f687e1bab4b9a5b5f2ffee",
         "FromU128", "SszArm.NatFromU128.program"),
        ("measure", -38108, 4352, ((0, 1092), (1156, 2900), (2984, 3108), (3116, 4276)),
         [1092, 3108],
         "16b518576779f284f22f4c7609e23ef1a3555c708c08497ac6b1650faaff0fd5",
         "Measure", "SszArm.Measure.bodyProgram"),
        ("emit", -33756, 1996, ((0, 740), (796, 868), (896, 1368), (1484, 1536),
                                  (1580, 1588)),
         [740, 1916, 1928, 1944, 1960, 1972, 1984],
         "edfe46a25130ea88eac1c200663c66a1ee7a1567ed41af36c7fecfb5265455ef",
         "Emit", "SszArm.Emit.bodyProgram"),
        ("serialize", 0, 692, ((0, 692),), [],
         "661a9170dc1854f25887cff67f9a7c138297fbc223c7433d369356b28ff058db",
         "Serialize", "SszArm.Serialize.bodyProgram"),
        ("memcpy", 85240, 56, ((0, 56),), [],
         "7f5022cb240032194b2b2f50db5c0b19896edef3b68e5598d8d509be82acc6af",
         "Memcpy", "SszArm.Emit.memcpyProgram"),
    )
    symbols = {
        "nat_compare": "_ZN13ssz_fv_native3nat3Nat7compare17h066191a25a9f736bE",
        "nat_from_u128": "_ZN13ssz_fv_native3nat3Nat9from_u12817h73292f97725c3b7dE",
        "measure": "_ZN13ssz_fv_native5codec7measure17h6f170d30c3984362E",
        "emit": "_ZN13ssz_fv_native5codec4emit17h0c79599762be27eaE",
        "memcpy": "memcpy",
    }
    calls = {
        "serialize": {48: "measure", 668: "emit"},
        "measure": {160: "nat_compare", 1052: "nat_compare", 1728: "nat_compare",
                    1912: "nat_from_u128", 1940: "memcpy"},
        "emit": {648: "memcpy", 856: "memcpy", 1252: "memcpy"},
        "nat_compare": {}, "nat_from_u128": {}, "memcpy": {},
    }
    _require(set(bodies) == {spec[0] for spec in specs},
             "unexpected ARM serialize function set")
    _require(type(origin) is int and origin == -78380 and len(span) == 163676
             and table_bytes is None,
             "unexpected ARM serialize origin, span extent, or table")
    # Pin the full extracted extent, including unselected bytes. The witness below
    # owns selected executable rows only; it makes no claim about their execution.
    _require(sha256(span).hexdigest()
             == "b93bb296fa7e2876d862067191f9f5552463f797c5d2c2e2478d7671ab4e6897",
             "ARM serialize linked span bytes changed")
    offsets = {spec[0]: spec[1] for spec in specs}
    sizes = {spec[0]: spec[2] for spec in specs}
    groups = []
    for key, offset, size, ranges, expected_frontiers, digest, name, program in specs:
        rows, entries, raw, frontiers, callees = bodies[key]
        selected = [pc for start, end in ranges for pc in range(start, end, 4)]
        _require(entries == [0] and frontiers == expected_frontiers
                 and all(type(pc) is int for pc in entries + frontiers)
                 and len(raw) == size and sha256(raw).hexdigest() == digest,
                 f"unexpected ARM serialize {key} entry, frontier, or bytes")
        _validate_rows(rows, raw)
        _require([row["pc"] for row in rows] == selected
                 and all(type(row["pc"]) is int for row in rows),
                 f"unexpected ARM serialize {key} selected rows")
        base = offset - origin
        _require(span[base:base + size] == raw,
                 f"ARM serialize {key} does not match linked span")
        expected_calls = calls[key]
        _require(set(callees) == {symbols[callee] for callee in expected_calls.values()},
                 f"unexpected ARM serialize {key} callees")
        for callee_key in set(expected_calls.values()):
            metadata = callees[symbols[callee_key]]
            _require(type(metadata.get("offset")) is int
                     and metadata["offset"] == offsets[callee_key] - offset
                     and type(metadata.get("size")) is int
                     and metadata["size"] == sizes[callee_key]
                     and _parse_hex_bytes(metadata["raw"]) == bodies[callee_key][2],
                     f"ARM serialize {key}/{callee_key} linked metadata mismatch")
        for row in rows:
            word = int(row["encoding"], 16)
            pc = row["pc"]
            callee_key = expected_calls.get(pc)
            _require(row.get("callee") == (symbols[callee_key] if callee_key else None)
                     and (word & 0xfc000000 == 0x94000000) == (callee_key is not None),
                     f"ARM serialize {key} callsite mismatch at {pc}")
            # Validate the decoder's branch metadata against the actual immediate,
            # including the linked BL targets and primitive frontier branches.
            if word & 0x7c000000 == 0x14000000:
                immediate, bits = word & 0x03ffffff, 26
            elif (word & 0xff000010 == 0x54000000
                  or word & 0x7e000000 == 0x34000000):
                immediate, bits = (word >> 5) & 0x7ffff, 19
            elif word & 0x7e000000 == 0x36000000:
                immediate, bits = (word >> 5) & 0x3fff, 14
            else:
                _require("target" not in row,
                         f"ARM serialize {key} nonbranch target metadata at {pc}")
                continue
            signed = immediate - (1 << bits) if immediate & (1 << (bits - 1)) else immediate
            target = pc + 4 * signed
            _require(type(row.get("target")) is int and row["target"] == target,
                     f"ARM serialize {key} branch target mismatch at {pc}")
            if callee_key is not None:
                _require(target == offsets[callee_key] - offset,
                         f"ARM serialize {key} linked call target mismatch at {pc}")
        groups.append((name, rows, base, program))

    declarations = _ordered_image_declarations(
        groups, chunked_programs={"SszArm.Measure.bodyProgram", "SszArm.Serialize.bodyProgram"},
        flat_programs={"SszArm.Emit.bodyProgram"})
    declarations.append("""
example : SszArm.Serialize.entry = 0 := by rfl
example : SszArm.Serialize.frontiers = [] := by rfl
example : SszArm.Serialize.measureOffset = -38108#64 := by rfl
example : SszArm.Serialize.emitOffset = -33756#64 := by rfl
example : SszArm.Measure.entry = 0 := by rfl
example : SszArm.Measure.frontiers = [1092, 3108] := by rfl
example : SszArm.Measure.compareOffset = -40272#64 := by rfl
example : SszArm.Measure.fromU128Offset = -15748#64 := by rfl
example : SszArm.Measure.memcpyOffset = 123348#64 := by rfl
example : SszArm.Emit.entry = 0 := by rfl
example : SszArm.Emit.frontiers = [740, 1916, 1928, 1944, 1960, 1972, 1984] := by rfl
example : SszArm.Emit.memcpyOffset = 118996 := by rfl

theorem compare_codeAt (s : ArmState) :
    SszArm.NatCompare.CodeAt {s with program := bound} 0#64 := by
  change ∀ row ∈ SszArm.NatCompare.program,
    bound.find? (0#64 + BitVec.ofNat 64 row.1) = some row.2
  rw [← actualCompare_eq]
  exact compare_lookup

theorem fromU128_codeAt (s : ArmState) :
    SszArm.NatFromU128.CodeAt {s with program := bound} 24524#64 := by
  change ∀ row ∈ SszArm.NatFromU128.program,
    bound.find? (24524#64 + BitVec.ofNat 64 row.1) = some row.2
  rw [← actualFromU128_eq]
  exact fromu128_lookup

theorem memcpy_codeAt (s : ArmState) :
    SszArm.CodeAt {s with program := bound} 163620#64 SszArm.Memcpy.program := by
  change ∀ k (hk : k < SszArm.Memcpy.program.length),
    bound.find? (163620#64 + BitVec.ofNat 64 (4 * k)) = some SszArm.Memcpy.program[k]
  have checked : ∀ k : Fin 14,
      (4 * k.val, SszArm.Memcpy.program[k.val]) ∈ actualMemcpy := by decide
  intro k hk
  exact memcpy_lookup _ (checked ⟨k, hk⟩)

theorem measure_codeAt (s : ArmState) :
    SszArm.Measure.CodeAt {s with program := bound} 40272#64 := by
  constructor
  · change ∀ row ∈ SszArm.Measure.bodyProgram,
      bound.find? (40272#64 + BitVec.ofNat 64 row.1) = some row.2
    rw [← actualMeasure_eq]
    exact measure_lookup
  · exact compare_codeAt s
  · exact fromU128_codeAt s
  · exact memcpy_codeAt s

theorem emit_codeAt (s : ArmState) :
    SszArm.Emit.CodeAt {s with program := bound} 44624#64 := by
  intro row member
  change row ∈ SszArm.Emit.bodyProgram ++
    SszArm.Emit.memcpyProgram.map (fun r => (SszArm.Emit.memcpyOffset + r.1, r.2)) at member
  rcases List.mem_append.mp member with body | copy
  · rw [← actualEmit_eq] at body
    exact emit_lookup row body
  · rcases List.mem_map.mp copy with ⟨localRow, inside, rfl⟩
    rw [← actualMemcpy_eq] at inside
    change bound.find? (44624#64 + BitVec.ofNat 64 (118996 + localRow.1)) = some localRow.2
    have baseSum : 44624#64 + 118996#64 = 163620#64 := by decide
    simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, baseSum] using
      memcpy_lookup localRow inside

theorem serialize_codeAt (s : ArmState) :
    SszArm.Serialize.CodeAt {s with program := bound} 78380#64 := by
  constructor
  · change ∀ row ∈ SszArm.Serialize.bodyProgram,
      bound.find? (78380#64 + BitVec.ofNat 64 row.1) = some row.2
    rw [← actualSerialize_eq]
    exact serialize_lookup
  · exact measure_codeAt s
  · exact emit_codeAt s
""")
    return _EMIT_IMAGE_ORDER.replace(
        "import SszArm.EmitImpl", "import SszArm.SerializeImpl", 1
    ) + "\n".join(declarations)


def nat_mul_source(bodies, span, *, origin) -> str:
    """Bind both multiplication entries and real memset in one linked program."""
    from decoder_binding import validate_nat_mul_image

    validate_nat_mul_image("arm", bodies, span, origin)
    groups = []
    for key, name, base, program in (
            ("nat_mul", "NatMul", 0, "SszArm.NatMul.program"),
            ("nat_mul_word", "NatMulWord", 1544, "SszArm.NatMulWord.program"),
            ("memset", "Memset", 167060, None)):
        rows, _, raw, _, _ = bodies[key]
        _validate_rows(rows, raw)
        groups.append((name, rows, base, program))
    declarations = _ordered_image_declarations(
        groups, flat_programs={"SszArm.NatMul.program", "SszArm.NatMulWord.program"},
        part_size=50)
    declarations.append("""
example : SszArm.NatMul.entry = 0 := by rfl
example : SszArm.NatMulWord.entry = 0 := by rfl
example : SszArm.NatMul.wordOffset = 1544#64 := by rfl
example : SszArm.NatMul.memsetOffset = 167060#64 := by rfl

theorem boundNatMulCodeAt (s : ArmState) :
    SszArm.NatMul.CodeAt {s with program := bound} 0#64 := by
  change ∀ row ∈ SszArm.NatMul.program,
    bound.find? (0#64 + BitVec.ofNat 64 row.1) = some row.2
  rw [← actualNatMul_eq]
  exact natmul_lookup

theorem boundNatMulWordCodeAt (s : ArmState) :
    SszArm.NatMulWord.CodeAt {s with program := bound} 1544#64 := by
  change ∀ row ∈ SszArm.NatMulWord.program,
    bound.find? (1544#64 + BitVec.ofNat 64 row.1) = some row.2
  rw [← actualNatMulWord_eq]
  exact natmulword_lookup

theorem boundMemsetCodeAt (s : ArmState) :
    SszArm.CodeAt {s with program := bound} 167060#64 SszArm.Memset.program := by
  change ∀ k (hk : k < SszArm.Memset.program.length),
    bound.find? (167060#64 + BitVec.ofNat 64 (4 * k)) = some SszArm.Memset.program[k]
  have checked : ∀ k : Fin 13,
      (4 * k.val, SszArm.Memset.program[k.val]) ∈ actualMemset := by decide
  intro k hk
  exact memset_lookup _ (checked ⟨k, hk⟩)

theorem SszArm.NatMulBinding.closureAt (s : ArmState) :
    SszArm.NatMul.JointCodeAt {s with program := bound} 0#64 :=
  ⟨boundNatMulCodeAt s, boundNatMulWordCodeAt s, boundMemsetCodeAt s⟩
audit_native
""")
    return _EMIT_IMAGE_ORDER.replace(
        "import SszArm.EmitImpl", "import SszArm.NatMulCalls\nimport ProofAudit", 1
    ) + "\n".join(declarations)
