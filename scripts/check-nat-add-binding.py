#!/usr/bin/env python3
"""Bind both complete native Nat.add images, without claiming execution refinement."""
from pathlib import Path
import tempfile

from decoder_binding import FUNCTIONS, extract, output
from decoder_x86_binding import nat_add_source as x86_source
from decoder_arm_binding import nat_add_source as arm_source
from native_build import ROOT


def main():
    with tempfile.TemporaryDirectory(prefix="ssz-nat-add-binding-") as directory:
        temp = Path(directory)
        for arch, namespace, generate in (("x86", "SszX86", x86_source),
                                           ("arm", "SszArm", arm_source)):
            backend = ROOT / f"backends/{arch}"
            output("lake", "--log-level=error", "build", f"{namespace}.NatAddImpl", cwd=backend)
            rows, entries, raw, frontier, callees = extract(
                temp, arch, "nat_add", [(FUNCTIONS["nat_add"][arch], 0)])
            proof = temp / f"{arch}.lean"
            proof.write_text(generate(rows, entries, raw, frontier, callees))
            output("lake", "env", "lean", str(proof), cwd=backend)
            print(f"{arch} Nat.add: {len(rows)} linked instructions, complete leaf image, "
                  "and CodeAt witness checked (not an execution refinement)", flush=True)


if __name__ == "__main__":
    main()
