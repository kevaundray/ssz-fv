#!/usr/bin/env python3
"""Bind private decoder entry instructions, primitive frontiers, and real x86 table data.

Body/callee closures are checked by the existing primitive binding checks.
This check binds the preceding dispatcher, not its execution refinement.
"""
from pathlib import Path
import json
import tempfile

from decoder_binding import FUNCTIONS, extract, output
from decoder_x86_binding import _image_parts
from decoder_arm_binding import _rows_expr, _validate_rows
from native_build import ROOT

KINDS = ("bool", "uint", "byteVector", "byteList", "bitVector", "bitList", "progressiveBitList")
ENTRIES = {"x86": [45, 1131, 750, 824, 115, 1192, 1240],
           "arm": [604, 148, 1972, 688, 428, 2052, 564]}


def image(temp, arch):
    symbol = FUNCTIONS["deserialize"][arch]
    stops = [43] if arch == "x86" else [52, 236, *ENTRIES[arch]]
    rows, entries, raw, reached, callees = extract(
        temp, arch, "deserialize", [(symbol, 0)], [(symbol, pc) for pc in stops])
    if entries != [0] or reached != sorted(stops) or callees:
        raise ValueError(f"{arch}: unexpected dispatcher entry or frontier")
    if arch == "arm":
        if len(rows) != 24 or len(raw) != 9940:
            raise ValueError("arm: unexpected dispatcher extent")
        _validate_rows(rows, raw)
        return rows, raw, None
    if len(rows) != 14 or len(raw) != 7825 or raw[43:45] != b"\xff\xe0":
        raise ValueError("x86: unexpected dispatcher or indirect JMP bytes")
    # This exact two-byte instruction is the indirect frontier itself, not a
    # fabricated direct jump to a selected body. Its target is proved from data.
    rows.append({"pc": 43, "width": 2, "encoding": raw[43:45].hex(), "asm": "jmpq *%rax"})
    elf = temp / "x86.elf"
    symbols = [line.split() for line in output("llvm-nm-18", "-S", "--defined-only", str(elf)).splitlines()]

    def address(name):
        matches = [item for item in symbols if item[-1] == name]
        if len(matches) != 1:
            raise ValueError(f"x86: missing or ambiguous dispatcher symbol {name}")
        return int(matches[0][0], 16)

    root, table = address(symbol), address(".LJTI93_0")
    if table - root != -106520:
        raise ValueError("x86: unexpected read-only jump-table location")
    headers = json.loads(output("llvm-readobj-18", "--sections", "--elf-output-style=JSON", str(elf)))
    sections = [item["Section"] for item in headers[0]["Sections"]
                if item["Section"]["Address"] <= table
                and table + 52 <= item["Section"]["Address"] + item["Section"]["Size"]]
    if len(sections) != 1 or sections[0]["Name"]["Name"] != ".rodata":
        raise ValueError("x86: jump table is not wholly in the linked read-only section")
    section = sections[0]
    position = section["Offset"] + table - section["Address"]
    data = elf.read_bytes()[position:position + 52]
    destinations = [table - root + int.from_bytes(data[i:i + 4], "little", signed=True)
                    for i in range(0, 52, 4)]
    if destinations != [*ENTRIES["x86"], 937, 1522, 708, 1275, 86, 294]:
        raise ValueError("x86: actual signed table entries disagree with body frontiers")
    return rows, raw, data


def frontiers(namespace, arch):
    return "\n".join(f"example : {namespace}.Kind.entry .{kind} = {pc} := by decide"
                     for kind, pc in zip(KINDS, ENTRIES[arch]))


def x86_source(rows, raw, table):
    labels, expressions, pieces = _image_parts(rows, raw, "dispatch_")
    if labels:
        raise ValueError("x86: indirect dispatcher unexpectedly gained direct labels")
    return f'''import SszX86.DispatchImpl
open Kraken.X64.Parser
set_option maxRecDepth 16384
set_option maxHeartbeats 32000000
def actual : List (Nat × Nat × Program) := [{', '.join(expressions)}]
example : actual = SszX86.Dispatch.program := by decide
example : SszX86.Dispatch.labels = [] := by decide
example : SszX86.Dispatch.tableOffset = -106520 := by decide
example : SszX86.Dispatch.tableBytes = [{', '.join(map(str, table))}] := by decide
{frontiers('SszX86.Dispatch', 'x86')}
noncomputable def bound : Executable := (0, List.flatten [{', '.join(pieces)}])
example : SszX86.Dispatch.CodeAt bound 0 := by
  constructor
  have h : SszX86.Dispatch.program.all (fun row =>
      decide (bound.directivesAtAddress (0 + Int64.ofNat row.1) =
        SszX86.Dispatch.directives row)) = true := by
    simp (config := {{maxSteps := 1000000}}) [bound, Kraken.Executable.directivesAtAddress,
      Kraken.Executable.withAddresses, SszX86.Dispatch.program, SszX86.Dispatch.directives]
  intro row hr
  exact of_decide_eq_true (List.all_eq_true.mp h row hr)
'''


def arm_source(rows, raw, table):
    return f'''import SszArm.DispatchImpl
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
open BitVec
def actual : List (Nat × BitVec 32) := [{_rows_expr(rows)}]
theorem actual_eq : actual = SszArm.Dispatch.program := by decide
{frontiers('SszArm.Dispatch', 'arm')}
def bound : Program := actual.map (fun (row : Nat × BitVec 32) => (BitVec.ofNat 64 row.1, row.2))
example (s : ArmState) : SszArm.Dispatch.CodeAt {{s with program := bound}} 0 := by
  change ∀ row ∈ SszArm.Dispatch.program,
    bound.find? (0 + BitVec.ofNat 64 row.1) = some row.2
  rw [← actual_eq]
  have h : actual.all (fun row =>
      decide (bound.find? (0 + BitVec.ofNat 64 row.1) = some row.2)) = true := by decide
  intro row hr
  exact of_decide_eq_true (List.all_eq_true.mp h row hr)
'''


def main():
    with tempfile.TemporaryDirectory(prefix="ssz-dispatch-binding-") as directory:
        temp = Path(directory)
        for arch, namespace, generate in (("x86", "SszX86", x86_source),
                                          ("arm", "SszArm", arm_source)):
            backend = ROOT / f"backends/{arch}"
            output("lake", "--log-level=error", "build", f"{namespace}.DispatchImpl", cwd=backend)
            rows, raw, table = image(temp, arch)
            proof = temp / f"{arch}-dispatch.lean"
            proof.write_text(generate(rows, raw, table))
            output("lake", "env", "lean", str(proof), cwd=backend)
            print(f"{arch} decoder dispatcher: {len(rows)} actual entry instructions, "
                  f"seven primitive frontiers{', 52 actual read-only table bytes' if table else ''} bound "
                  "(not an execution refinement)", flush=True)


if __name__ == "__main__":
    main()
