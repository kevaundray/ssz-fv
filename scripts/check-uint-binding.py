#!/usr/bin/env python3
"""Bind integer decoder blocks and their real linked runtime calls.

The explicit bounds-panic frontiers still require machine-level unreachability
proofs. Artifact binding and decoder coverage alone are not codec refinement.
"""
from pathlib import Path
import tempfile

from decoder_binding import extract, output
from native_build import ROOT
from decoder_x86_binding import uint_source as x86_source
from decoder_arm_binding import uint_source as arm_source


def main():
    configurations = (
        ("x86", "SszX86", [(".LBB93_1", 0), (".LBB93_44", 0)],
         (".LBB93_318",), (), x86_source),
        ("arm", "SszArm", [(".LBB93_28", 0), (".LBB93_5", 20)],
         (".LBB93_319",), ("memcpy",), arm_source),
    )
    with tempfile.TemporaryDirectory(prefix="ssz-uint-binding-") as directory:
        temp = Path(directory)
        for arch, namespace, entries, terminals, calls, generate in configurations:
            backend = ROOT / f"backends/{arch}"
            output("lake", "--log-level=error", "build", f"{namespace}.UintImpl", cwd=backend)
            rows, (_, entry), raw, frontier, callees = extract(temp, arch, "deserialize", entries, terminals, calls)
            proof = temp / f"{arch}.lean"
            proof.write_text(generate(rows, entry, raw, frontier, callees))
            output("lake", "env", "lean", str(proof), cwd=backend)
            print(f"{arch} integer decoder: {len(rows)} linked body instructions, "
                  f"{len(callees)} runtime callees, and CodeAt witness checked; "
                  f"unreachable-frontier obligation {frontier} (not a refinement proof)", flush=True)


if __name__ == "__main__":
    main()
