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
