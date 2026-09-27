#!/usr/bin/env python3
"""Bind the shipped postdispatch Boolean blocks, not a reconstructed function.

Disassembly/AST translation is trusted, as in check-runtime-binding.py. Lean
checks offsets, widths, branch operands, ARM words and concrete CodeAt witnesses.
This is artifact binding and decoder coverage, NOT a whole-block execution proof.
Unselected x86 bytes remain actual opaque byte arrays, never synthetic padding.
"""
import json
from pathlib import Path
import re
import tempfile

from native_build import ROOT
from decoder_binding import extract, output

ENTRIES = {"x86": ".LBB93_1", "arm": ".LBB93_28"}


def x86_source(rows, entry, raw):
    conditional = [row for row in rows if row["asm"].split()[0] in ("je", "jne")]
    names = ("boolScope", "boolZero", "boolBad")
    if len(conditional) != len(names):
        raise ValueError("unexpected Boolean conditional-branch topology")
    branches = {row["pc"]: name for row, name in zip(conditional, names)}
    labels = [(name, row["target"]) for row, name in zip(conditional, names)]
    expressions = []
    for row in rows:
        parts = row["asm"].split(None, 1)
        mnemonic, operands = parts[0], parts[1] if len(parts) == 2 else ""
        if mnemonic in ("je", "jne"):
            expression = f"parse({json.dumps(mnemonic + ' ' + branches[row['pc']])})"
        elif mnemonic in ("jmp", "jmpq"):
            delta = row["target"] - row["pc"] - row["width"]
            expression = f"[.instr (.regular .W64 .W64 (.jmp (.rel (.int64 ({delta})))))]"
        elif mnemonic == "movzbl" and re.sub(r"\s+", "", operands) == "(%rdx),%eax":
            expression = "[.instr (.regular .W64 .W32 (.movzx (.reg .eax) (.mem (w := .W8) { base := some (.reg .rdx), idx := none })))]"
        elif mnemonic in ("cmpq", "movq", "movl", "movw", "cmpl", "testl", "addq", "popq", "retq"):
            if not re.fullmatch(r"[%a-z0-9(),$x\s+-]*", operands):
                raise ValueError(f"unsupported Boolean operand: {row}")
            text = mnemonic + " " + re.sub(r"\s+", "", operands)
            expression = f"parse({json.dumps(text)})"
        else:
            raise ValueError(f"unsupported Boolean instruction: {row}")
        expressions.append(f"({row['pc']}, {row['width']}, {expression})")
    pieces, cursor = [], 0
    for index, row in enumerate(rows):
        if cursor < row["pc"]:
            gap = raw[cursor:row["pc"]]
            pieces.append(f"[(.byteArray (ByteArray.mk #[{','.join(map(str, gap))}]), {len(gap)})]")
        for name, pc in labels:
            if pc == row["pc"]:
                pieces.append(f"[(.label {json.dumps(name)}, 0)]")
        pieces.append(f"(actual[{index}]!).2.2.map (fun d => (d, {row['width']}))")
        cursor = row["pc"] + row["width"]
    if cursor < len(raw):
        gap = raw[cursor:]
        pieces.append(f"[(.byteArray (ByteArray.mk #[{','.join(map(str, gap))}]), {len(gap)})]")
    label_literal = ", ".join(f"({json.dumps(name)}, {pc})" for name, pc in labels)
    return f'''import SszX86.BoolImpl
open Kraken.X64.Parser
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000

def actual : List (Nat × Nat × Program) := [{', '.join(expressions)}]
example : actual = SszX86.BoolCodec.program := by decide
example : SszX86.BoolCodec.entry = {entry} := by decide
example : SszX86.BoolCodec.labels = [{label_literal}] := by decide

def bound : Executable := (0, {' ++ '.join(pieces)})
example : SszX86.BoolCodec.CodeAt bound 0 := by
  constructor
  · have h : SszX86.BoolCodec.program.all (fun row =>
        decide (bound.directivesAtAddress (0 + Int64.ofNat row.1) =
          SszX86.BoolCodec.directives row)) = true := by
      simp [bound, actual, Kraken.Executable.directivesAtAddress,
        Kraken.Executable.withAddresses, SszX86.BoolCodec.program,
        SszX86.BoolCodec.directives, SszX86.BoolCodec.labels]
    intro row hr
    exact of_decide_eq_true (List.all_eq_true.mp h row hr)
  · have h : SszX86.BoolCodec.labels.all (fun item =>
        decide (bound.labels.label item.1 = 0 + Int64.ofNat item.2)) = true := by
      dsimp (config := {{instances := true}}) [Executable.labels]
      simp [bound, actual, Kraken.Executable.withAddresses, SszX86.BoolCodec.labels]
    intro item hi
    exact of_decide_eq_true (List.all_eq_true.mp h item hi)
'''


def arm_source(rows, entry):
    words = ", ".join(f"({row['pc']}, 0x{row['encoding']}#32)" for row in rows)
    return f'''import SszArm.BoolImpl
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000

def actual : List (Nat × BitVec 32) := [{words}]
theorem actual_eq : actual = SszArm.BoolCodec.program := by decide
example : SszArm.BoolCodec.entry = {entry} := by decide

def bound : Program := actual.map (fun row => (BitVec.ofNat 64 row.1, row.2))
example (s : ArmState) : SszArm.BoolCodec.CodeAt {{s with program := bound}} 0 := by
  change ∀ row ∈ SszArm.BoolCodec.program,
    bound.find? (0 + BitVec.ofNat 64 row.1) = some row.2
  rw [← actual_eq]
  have h : actual.all (fun row =>
      decide (bound.find? (0 + BitVec.ofNat 64 row.1) = some row.2)) = true := by decide
  intro row hr
  exact of_decide_eq_true (List.all_eq_true.mp h row hr)
'''


def main():
    with tempfile.TemporaryDirectory(prefix="ssz-bool-binding-") as directory:
        temp = Path(directory)
        for arch, namespace in (("x86", "SszX86"), ("arm", "SszArm")):
            backend = ROOT / f"backends/{arch}"
            output("lake", "--log-level=error", "build", f"{namespace}.BoolImpl", cwd=backend)
            rows, (entry,), raw, _, _ = extract(temp, arch, "deserialize", [(ENTRIES[arch], 0)])
            source = x86_source(rows, entry, raw) if arch == "x86" else arm_source(rows, entry)
            proof = temp / f"{arch}.lean"
            proof.write_text(source)
            output("lake", "env", "lean", str(proof), cwd=backend)
            print(f"{arch} Boolean body: {len(rows)} actual instructions, offsets and targets bound; "
                  "CodeAt witness checked (not an execution proof)", flush=True)


if __name__ == "__main__":
    main()
