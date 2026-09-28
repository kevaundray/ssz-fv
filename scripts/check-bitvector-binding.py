#!/usr/bin/env python3
"""Bind the real BitVector body and every reachable callee, not their execution."""
from pathlib import Path
import json
import runpy
import tempfile

from decoder_binding import FUNCTIONS, extract, linked_span, output
from decoder_x86_binding import _image_parts, _byte_segments
from decoder_arm_binding import _rows_expr, _validate_rows, _word_le
from native_build import ROOT

MEMBERS = (
    ("nat_div_rem_small", "NatDivision", "natDivision_"),
    ("nat_add", "NatAdd", "natAdd_"),
    ("deserialize", "BitVector", "bitVector_"),
    ("nat_exact", "NatExact", "natExact_"),
    ("nat_to_u128", "NatToU128", "natToU128_"),
)
OFFSETS = {"x86": [0, 8304, 63168, 77952, 78144],
           "arm": [0, 11156, 78088, 95516, 95812]}


def closure(temp, arch):
    entries = [(".LBB93_6", 0)] if arch == "x86" else [(".LBB93_21", 16)]
    calls = [FUNCTIONS[name][arch] for name, _, _ in MEMBERS if name != "deserialize"]
    if arch == "arm":
        calls.append("memcpy")
    vector = extract(temp, arch, "deserialize", entries, calls=calls)
    expected = (228, 115, 7825) if arch == "x86" else (239, 428, 9940)
    if (len(vector[0]), vector[1][0], len(vector[2])) != expected or vector[3]:
        raise ValueError(f"{arch}: unexpected BitVector body extent or frontier")
    if set(vector[4]) != set(calls):
        raise ValueError(f"{arch}: incomplete BitVector call closure")
    bodies = {"deserialize": vector}
    for name, _, _ in MEMBERS:
        if name != "deserialize":
            bodies[name] = extract(temp, arch, name, [(FUNCTIONS[name][arch], 0)],
                                   calls=("__udivti3",) if name == "nat_div_rem_small" else ())
    division = bodies["nat_div_rem_small"]
    origin, span = linked_span(temp, arch, "nat_div_rem_small", division[2], division[4])
    if origin != 0:
        raise ValueError(f"{arch}: unexpected linked-image origin")
    vector_base = OFFSETS[arch][2]
    for (name, _, _), base in zip(MEMBERS, OFFSETS[arch]):
        body = bodies[name]
        if body[3] or (name != "deserialize" and body[1] != [0]):
            raise ValueError(f"{arch}: invalid helper entry or frontier: {name}")
        if span[base:base + len(body[2])] != body[2]:
            raise ValueError(f"{arch}: linked helper/body bytes disagree: {name}")
        if name != "deserialize":
            callee = vector[4][FUNCTIONS[name][arch]]
            if (callee["offset"] != base - vector_base or
                    bytes.fromhex(callee["raw"]) != body[2] or callee["size"] != len(body[2])):
                raise ValueError(f"{arch}: direct callee binding mismatch: {name}")
    kernel = division[4]["__udivti3"]
    kernel_base = 160352 if arch == "x86" else 182664
    kernel_size = 197 if arch == "x86" else 260
    if (kernel["offset"] != kernel_base or kernel["size"] != kernel_size or
            len(span) != kernel_base + kernel_size or
            span[kernel_base:] != bytes.fromhex(kernel["raw"])):
        raise ValueError(f"{arch}: transitive division runtime binding mismatch")
    if arch == "arm":
        copy = vector[4]["memcpy"]
        if (copy["offset"] != 104240 or copy["size"] != 56 or
                span[182328:182384] != bytes.fromhex(copy["raw"])):
            raise ValueError("arm: memcpy binding mismatch")
    return bodies, span


def x86_source(bodies, span):
    declarations, witnesses, pieces = [], [], []
    addresses = []
    cursor = 0
    for (name, stem, prefix), base in zip(MEMBERS, OFFSETS["x86"]):
        rows, entries, raw, _, _ = bodies[name]
        labels, expressions, body_pieces = _image_parts(rows, raw, prefix)
        if base < cursor:
            raise ValueError("overlapping x86 components")
        addresses.extend(range(cursor, base, 256))
        at = base
        selected = {row["pc"]: row["width"] for row in rows}
        for pc in sorted(set(selected) | {pc for _, pc in labels}):
            addresses.extend(range(at, base + pc, 256))
            addresses.extend(base + pc for _, location in labels if location == pc)
            at = base + pc
            if pc in selected:
                addresses.append(at)
                at += selected[pc]
        addresses.extend(range(at, base + len(raw), 256))
        pieces.extend(_byte_segments(span[cursor:base]))
        pieces.extend(body_pieces)
        cursor = base + len(raw)
        namespace = f"SszX86.{stem}"
        label_literal = ", ".join(f"({json.dumps(label)}, {pc})" for label, pc in labels)
        declarations.append(f'''def actual{stem} : List (Nat × Nat × Program) := [{', '.join(expressions)}]
example : actual{stem} = {namespace}.program := by decide
example : {namespace}.labels = [{label_literal}] := by decide
example : {namespace}.entry = {entries[0]} := by decide
''')
        witnesses.append(f'''example : {namespace}.CodeAt bound {base} := by
  constructor
  · have h : {namespace}.program.all (fun row =>
        decide (bound.directivesAtAddress ({base} + Int64.ofNat row.1) =
          {namespace}.directives row)) = true := by
      simp only [Kraken.Executable.directivesAtAddress, addressTable_eq]
      simp (config := {{instances := true}}) only [addressTable, SszX86.Udivti3.executable,
        SszX86.Udivti3.program, SszX86.Udivti3.layout, Kraken.Layout.apply]
      decide
    intro row hr
    exact of_decide_eq_true (List.all_eq_true.mp h row hr)
  · have h : {namespace}.labels.all (fun item =>
        decide (bound.labels.label item.1 = {base} + Int64.ofNat item.2)) = true := by
      dsimp (config := {{instances := true}}) [Executable.labels]
      rw [addressTable_eq]
      simp (config := {{instances := true}}) only [addressTable, SszX86.Udivti3.executable,
        SszX86.Udivti3.program, SszX86.Udivti3.layout, Kraken.Layout.apply]
      decide
    intro item hi
    exact of_decide_eq_true (List.all_eq_true.mp h item hi)
''')
    addresses.extend(range(cursor, 160352, 256))
    pieces.extend(_byte_segments(span[cursor:160352]))
    pieces.append("(SszX86.Udivti3.executable 160352).2")
    return f'''import SszX86.BitVectorImpl
import SszX86.Udivti3Embedded
open Kraken.X64.Parser
set_option maxRecDepth 16384
set_option maxHeartbeats 32000000
{''.join(declarations)}
example : SszX86.BitVector.divisionOffset = -63168 := by decide
example : SszX86.BitVector.addOffset = -54864 := by decide
example : SszX86.BitVector.exactOffset = 14784 := by decide
example : SszX86.BitVector.toU128Offset = 14976 := by decide
example : SszX86.NatDivision.udivOffset = 160352 := by decide
noncomputable def bound : Executable := (0, List.flatten [{', '.join(pieces)}])
noncomputable def kernelAddresses : List (Int64 × Directive × Nat) :=
  (SszX86.Udivti3.executable 160352).2.mapIdx (fun i row =>
    (160352 + Int64.ofNat (((SszX86.Udivti3.executable 160352).2.take i).map Prod.snd).sum, row))
theorem kernelAddresses_eq :
    (SszX86.Udivti3.executable 160352).withAddresses = kernelAddresses := by
  simp (config := {{instances := true, maxSteps := 1000000}}) [kernelAddresses,
    SszX86.Udivti3.executable, SszX86.Udivti3.layout, SszX86.Udivti3.program,
    Kraken.Layout.apply, Kraken.Executable.withAddresses]
-- Check the generated address table once, before expanding finite row lookups.
-- Its equality to the actual executable is proved, not assumed.
noncomputable def addressTable : List (Int64 × Directive × Nat) :=
  List.zip [{', '.join(map(str, addresses))}] (bound.2.take {len(addresses)}) ++
    kernelAddresses
theorem addressTable_eq : bound.withAddresses = addressTable := by
  simp (config := {{instances := true, maxSteps := 1000000}}) [bound, addressTable, kernelAddresses,
    Kraken.Executable.withAddresses, SszX86.Udivti3.executable,
    SszX86.Udivti3.program, SszX86.Udivti3.layout, Kraken.Layout.apply]
{''.join(witnesses)}
example : SszX86.Udivti3.Embedded.CodeAt bound 160352 := by
  apply SszX86.Udivti3.Embedded.CodeAt.of_rows
  · have h : (SszX86.Udivti3.executable 160352).withAddresses.all (fun row =>
        decide (bound.directivesAtAddress row.1 =
          (SszX86.Udivti3.executable 160352).directivesAtAddress row.1)) = true := by
      simp only [Kraken.Executable.directivesAtAddress, addressTable_eq, kernelAddresses_eq]
      simp (config := {{instances := true}}) only [addressTable, kernelAddresses,
        SszX86.Udivti3.executable, SszX86.Udivti3.layout, SszX86.Udivti3.program, Kraken.Layout.apply]
      decide
    intro row hr
    exact of_decide_eq_true (List.all_eq_true.mp h row hr)
  · have h : SszX86.Udivti3.Embedded.usedLabels.all (fun name =>
        decide (bound.labels.label name =
          (SszX86.Udivti3.executable 160352).labels.label name)) = true := by
      dsimp (config := {{instances := true}}) [Executable.labels]
      simp only [addressTable_eq, kernelAddresses_eq]
      simp (config := {{instances := true}}) only [addressTable, kernelAddresses,
        SszX86.Udivti3.executable, SszX86.Udivti3.layout, SszX86.Udivti3.program, Kraken.Layout.apply]
      decide
    intro name hn
    exact of_decide_eq_true (List.all_eq_true.mp h name hn)
'''


def arm_source(bodies, span):
    declarations, components, witnesses = [], [], []
    for (name, stem, _), base in zip(MEMBERS, OFFSETS["arm"]):
        rows, entries, raw, _, _ = bodies[name]
        _validate_rows(rows, raw)
        namespace = f"SszArm.{stem}"
        declarations.append(f'''def actual{stem} : List (Nat × BitVec 32) := [{_rows_expr(rows)}]
theorem actual{stem}_eq : actual{stem} = {namespace}.program := by decide
example : {namespace}.entry = {entries[0]} := by decide
''')
        components.append(f"actual{stem}.map (fun (row : Nat × BitVec 32) => ({base} + row.1, row.2))")
        witnesses.append(f'''example (s : ArmState) : {namespace}.CodeAt {{s with program := bound}} {base} := by
  change ∀ row ∈ {namespace}.program,
    bound.find? ({base} + BitVec.ofNat 64 row.1) = some row.2
  rw [← actual{stem}_eq]
  have h : actual{stem}.all (fun row =>
      decide (bound.find? ({base} + BitVec.ofNat 64 row.1) = some row.2)) = true := by decide
  intro row hr
  exact of_decide_eq_true (List.all_eq_true.mp h row hr)
''')
    for stem, base, size in (("Memcpy", 182328, 56), ("Udivti3", 182664, 260)):
        raw = span[base:base + size]
        words = ", ".join(f"0x{_word_le(raw[i:i + 4]):08x}#32" for i in range(0, size, 4))
        namespace = f"SszArm.{stem}"
        declarations.append(f'''def actual{stem} : List (BitVec 32) := [{words}]
theorem actual{stem}_eq : actual{stem} = {namespace}.program := by decide
''')
        components.append(f"actual{stem}.mapIdx (fun i word => ({base} + 4 * i, word))")
        code = (f"SszArm.CodeAt {{s with program := bound}} {base} {namespace}.program"
                if stem == "Memcpy" else f"{namespace}.CodeAt {{s with program := bound}} {base}")
        witnesses.append(f'''example (s : ArmState) : {code} := by
  change ∀ k (hk : k < {namespace}.program.length),
    bound.find? ({base} + BitVec.ofNat 64 (4 * k)) = some {namespace}.program[k]
  have h : ∀ k : Fin actual{stem}.length,
      bound.find? ({base} + BitVec.ofNat 64 (4 * k.val)) = some actual{stem}[k.val] := by decide
  intro k hk
  have actualBound : k < actual{stem}.length := by simpa only [actual{stem}_eq] using hk
  simpa only [actual{stem}_eq] using h ⟨k, actualBound⟩
''')
    return f'''import SszArm.BitVectorImpl
import SszArm.Memcpy
import SszArm.Udivti3
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
open BitVec
{''.join(declarations)}
example : SszArm.BitVector.divisionOffset = BitVec.ofInt 64 (-78088) := by decide
example : SszArm.BitVector.addOffset = BitVec.ofInt 64 (-66932) := by decide
example : SszArm.BitVector.exactOffset = 17428 := by decide
example : SszArm.BitVector.toU128Offset = 17724 := by decide
example : SszArm.BitVector.memcpyOffset = 104240 := by decide
example : SszArm.NatDivision.udivOffset = 182664 := by decide
def bound : Program := ({' ++ '.join(components)}).map
  (fun (row : Nat × BitVec 32) => (BitVec.ofNat 64 row.1, row.2))
{''.join(witnesses)}
'''


def main():
    runtime = runpy.run_path(str(ROOT / "scripts/check-runtime-binding.py"))
    with tempfile.TemporaryDirectory(prefix="ssz-bitvector-binding-") as directory:
        temp = Path(directory)
        for arch, namespace, target, generate in (
            ("x86", "SszX86", "x86_64-unknown-linux-gnu", x86_source),
            ("arm", "SszArm", "aarch64-unknown-linux-gnu", arm_source),
        ):
            backend = ROOT / f"backends/{arch}"
            modules = [f"{namespace}.BitVectorImpl"]
            if arch == "x86":
                modules.append("SszX86.Udivti3Embedded")
            output("lake", "--log-level=error", "build", *modules, cwd=backend)
            bodies, span = closure(temp, arch)
            for name in (["udivti3"] if arch == "x86" else ["udivti3", "memcpy"]):
                obj = temp / f"{arch}-{name}.o"
                output("clang-18", f"--target={target}", "-c", f"asm/{arch}/{name}.s",
                       "-o", str(obj))
                rows, size = runtime["instructions"](arch, obj, name)
                raw = b"".join(bytes.fromhex(row[2]) if arch == "x86"
                               else int(row[2], 16).to_bytes(4, "little") for row in rows)
                callee = (bodies["nat_div_rem_small"][4]["__udivti3"] if name == "udivti3"
                          else bodies["deserialize"][4]["memcpy"])
                if raw.hex() != callee["raw"]:
                    raise ValueError(f"{arch}: linked {name} differs from its runtime object")
                runtime[f"bind_{arch}"](temp, rows, size, name)
            proof = temp / f"{arch}-bitvector-joint.lean"
            proof.write_text(generate(bodies, span))
            output("lake", "env", "lean", str(proof), cwd=backend)
            print(f"{arch} BitVector: {len(bodies['deserialize'][0])} body instructions, "
                  "four Nat helpers and transitive runtime jointly bound "
                  "(not a BitVector execution refinement)", flush=True)


if __name__ == "__main__":
    main()
