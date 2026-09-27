#!/usr/bin/env python3
"""Bind native delimited decoders and Nat.compare in one image per ISA.

Joint CodeAt witnesses are instruction bindings, not refinement proofs.
"""
from pathlib import Path
import tempfile

from decoder_binding import FUNCTIONS, extract, linked_span, output
from decoder_x86_binding import delimited_source as x86_source
from decoder_arm_binding import delimited_source as arm_source
from native_build import ROOT


def main():
    with tempfile.TemporaryDirectory(prefix="ssz-delimited-binding-") as directory:
        temp = Path(directory)
        for arch, namespace, generate in (("x86", "SszX86", x86_source),
                                           ("arm", "SszArm", arm_source)):
            backend = ROOT / f"backends/{arch}"
            output("lake", "--log-level=error", "build", f"{namespace}.DelimitedImpl",
                   f"{namespace}.NatCompareImpl", cwd=backend)
            body = extract(temp, arch, "decode_delimited",
                           [(FUNCTIONS["decode_delimited"][arch], 0)],
                           calls=(FUNCTIONS["nat_compare"][arch],))
            linked = linked_span(temp, arch, "decode_delimited", body[2], body[4])
            comparison = extract(temp, arch, "nat_compare",
                                 [(FUNCTIONS["nat_compare"][arch], 0)])
            proof = temp / f"{arch}.lean"
            proof.write_text(generate(body, comparison, linked))
            output("lake", "env", "lean", str(proof), cwd=backend)
            print(f"{arch} delimited decoder: {len(body[0])} linked instructions, "
                  f"{len(comparison[0])} Nat.compare instructions, and joint CodeAt "
                  "witnesses checked (not a refinement proof)", flush=True)


if __name__ == "__main__":
    main()
