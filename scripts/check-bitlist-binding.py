#!/usr/bin/env python3
"""Bind both bit-list wrappers, their real tail calls, and the complete helper closure."""
from pathlib import Path
import json
import tempfile

from decoder_binding import FUNCTIONS, extract, linked_span, output
from decoder_x86_binding import _image_parts, _byte_segments
from decoder_arm_binding import _rows_expr, _validate_rows
from native_build import ROOT

MEMBERS = (("nat_compare", "NatCompare", "natCompare_"),
           ("deserialize", "BitList", "bitList_"),
           ("decode_delimited", "Delimited", "delimited_"))
BASES = {"x86": (0, 50272, 59232), "arm": (0, 59380, 69940)}
ENTRIES = {"x86": [(".LBB93_49", 0), (".LBB93_50", 0)],
           "arm": [(".LBB93_87", 0), (".LBB93_27", 0)]}


def closure(temp, arch):
    helper_symbol = FUNCTIONS["decode_delimited"][arch]
    compare_symbol = FUNCTIONS["nat_compare"][arch]
    caller = extract(temp, arch, "deserialize", ENTRIES[arch], calls=(helper_symbol,))
    helper = extract(temp, arch, "decode_delimited", [(helper_symbol, 0)],
                     calls=(compare_symbol,))
    compare = extract(temp, arch, "nat_compare", [(compare_symbol, 0)])
    expected = ([1192, 1240], 30, 7825, 1270, 60073) if arch == "x86" else (
        [2052, 564], 26, 9940, 600, 70952)
    entries, count, size, tail_pc, total = expected
    if (caller[1] != entries or len(caller[0]) != count or len(caller[2]) != size or
            caller[3] or set(caller[4]) != {helper_symbol} or
            helper[1] != [0] or helper[3] or set(helper[4]) != {compare_symbol} or
            compare[1] != [0] or compare[3] or compare[4]):
        raise ValueError(f"{arch}: unexpected bit-list call closure")
    tails = [row for row in caller[0] if row.get("tail_call")]
    if len(tails) != 1 or tails[0]["pc"] != tail_pc or tails[0]["callee"] != helper_symbol:
        raise ValueError(f"{arch}: actual progressive tail call is missing")
    direct, nested = caller[4][helper_symbol], helper[4][compare_symbol]
    if (bytes.fromhex(direct["raw"]) != helper[2] or direct["size"] != len(helper[2]) or
            bytes.fromhex(nested["raw"]) != compare[2] or nested["size"] != len(compare[2])):
        raise ValueError(f"{arch}: helper bytes disagree with their linked callees")
    callees = {helper_symbol: direct,
               compare_symbol: dict(nested, offset=direct["offset"] + nested["offset"])}
    origin, span = linked_span(temp, arch, "deserialize", caller[2], callees)
    if ((0, -origin, direct["offset"] - origin) != BASES[arch] or
            direct["offset"] + nested["offset"] != origin or len(span) != total):
        raise ValueError(f"{arch}: unexpected joint linked-image layout")
    bodies = {"nat_compare": compare, "deserialize": caller, "decode_delimited": helper}
    for (name, _, _), base in zip(MEMBERS, BASES[arch]):
        raw = bodies[name][2]
        if span[base:base + len(raw)] != raw:
            raise ValueError(f"{arch}: linked component mismatch: {name}")
    return bodies, span


def x86_source(bodies, span):
    declarations, witnesses, pieces = [], [], []
    cursor = 0
    for (name, stem, prefix), base in zip(MEMBERS, BASES["x86"]):
        rows, _, raw, _, _ = bodies[name]
        labels, expressions, body_pieces, _ = _image_parts(rows, raw, prefix)
        pieces.extend(_byte_segments(span[cursor:base]))
        pieces.extend(body_pieces)
        cursor = base + len(raw)
        namespace = f"SszX86.{stem}"
        literal = ", ".join(f"({json.dumps(label)}, {pc})" for label, pc in labels)
        declarations.append(f'''def actual{stem} : List (Nat × Nat × Program) := [{', '.join(expressions)}]
example : actual{stem} = {namespace}.program := by decide
example : {namespace}.labels = [{literal}] := by decide
''')
        witness = f'''example : {namespace}.CodeAt bound {base} := by
  constructor
  · have h : {namespace}.program.all (fun row =>
        decide (bound.directivesAtAddress ({base} + Int64.ofNat row.1) =
          {namespace}.directives row)) = true := by
      simp (config := {{maxSteps := 1000000}}) [bound, Kraken.Executable.directivesAtAddress,
        Kraken.Executable.withAddresses, {namespace}.program,
        {namespace}.directives, {namespace}.labels]
    intro row hr
    exact of_decide_eq_true (List.all_eq_true.mp h row hr)
'''
        if stem != "BitList":
            witness += f'''  · have h : {namespace}.labels.all (fun item =>
        decide (bound.labels.label item.1 = {base} + Int64.ofNat item.2)) = true := by
      dsimp (config := {{instances := true}}) [Executable.labels]
      simp (config := {{maxSteps := 1000000}}) [bound, Kraken.Executable.withAddresses, {namespace}.labels]
    intro item hi
    exact of_decide_eq_true (List.all_eq_true.mp h item hi)
'''
        witnesses.append(witness)
    return f'''import SszX86.BitListImpl
open Kraken.X64.Parser
set_option maxRecDepth 16384
set_option maxHeartbeats 32000000
{''.join(declarations)}
example : SszX86.BitList.listEntry = 1192 := by decide
example : SszX86.BitList.progressiveEntry = 1240 := by decide
example : SszX86.BitList.delimitedOffset = 8960 := by decide
example : SszX86.Delimited.compareOffset = -59232 := by decide
noncomputable def bound : Executable := (0, List.flatten [{', '.join(pieces)}])
{''.join(witnesses)}
'''


def arm_source(bodies, span):
    declarations, witnesses, components = [], [], []
    for (name, stem, _), base in zip(MEMBERS, BASES["arm"]):
        rows, _, raw, _, _ = bodies[name]
        _validate_rows(rows, raw)
        namespace = f"SszArm.{stem}"
        declarations.append(f'''def actual{stem} : List (Nat × BitVec 32) := [{_rows_expr(rows)}]
theorem actual{stem}_eq : actual{stem} = {namespace}.program := by decide
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
    return f'''import SszArm.BitListImpl
import SszArm.NatCompareImpl
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
open BitVec
{''.join(declarations)}
example : SszArm.BitList.listEntry = 2052 := by decide
example : SszArm.BitList.progressiveEntry = 564 := by decide
example : SszArm.BitList.delimitedOffset = 10560#64 := by decide
example : SszArm.Delimited.compareOffset = BitVec.ofInt 64 (-69940) := by decide
def bound : Program :=
  ({' ++ '.join(components)}).map
    (fun (row : Nat × BitVec 32) => (BitVec.ofNat 64 row.1, row.2))
{''.join(witnesses)}
'''


def main():
    with tempfile.TemporaryDirectory(prefix="ssz-bitlist-binding-") as directory:
        temp = Path(directory)
        for arch, namespace, generate in (("x86", "SszX86", x86_source),
                                           ("arm", "SszArm", arm_source)):
            backend = ROOT / f"backends/{arch}"
            output("lake", "--log-level=error", "build", f"{namespace}.BitListImpl", cwd=backend)
            bodies, span = closure(temp, arch)
            proof = temp / f"{arch}-bitlist-joint.lean"
            proof.write_text(generate(bodies, span))
            output("lake", "env", "lean", str(proof), cwd=backend)
            print(f"{arch} BitList/ProgressiveBitList: {len(bodies['deserialize'][0])} wrapper instructions, "
                  "real tail call, Delimited and NatCompare jointly bound "
                  "(not a wrapper execution refinement)", flush=True)


if __name__ == "__main__":
    main()
