#!/usr/bin/env python3
"""Bind exact-size and Nat conversion images; no execution-refinement claim."""
from pathlib import Path
import tempfile

from decoder_binding import FUNCTIONS, extract, output
import decoder_x86_binding as x86
import decoder_arm_binding as arm
from native_build import ROOT


def main():
    with tempfile.TemporaryDirectory(prefix="ssz-nat-conversion-binding-") as directory:
        temp = Path(directory)
        for arch, namespace, generate in (("x86", "SszX86", x86),
                                           ("arm", "SszArm", arm)):
            backend = ROOT / f"backends/{arch}"
            for name, stem, source in (
                ("nat_exact", "NatExact", generate.nat_exact_source),
                ("nat_to_u128", "NatToU128", generate.nat_to_u128_source),
                ("nat_from_u128", "NatFromU128", generate.nat_from_u128_source),
            ):
                output("lake", "--log-level=error", "build", f"{namespace}.{stem}Impl", cwd=backend)
                body = extract(temp, arch, name, [(FUNCTIONS[name][arch], 0)])
                proof = temp / f"{arch}-{name}.lean"
                proof.write_text(source(*body))
                output("lake", "env", "lean", str(proof), cwd=backend)
                print(f"{arch} {name}: {len(body[0])} linked instructions, complete leaf image, "
                      "and CodeAt witness checked (not an execution refinement)", flush=True)


if __name__ == "__main__":
    main()
