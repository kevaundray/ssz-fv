#!/usr/bin/env python3
"""Bind both native multiplication entries and their actual runtime memset."""
from pathlib import Path
import tempfile

from decoder_binding import FUNCTIONS, extract, linked_span, output
from native_build import ROOT


def closure(temp, arch):
    bodies = {}
    for key in ("nat_mul_word", "memset", "nat_mul"):
        symbol = FUNCTIONS[key][arch]
        frontier = ([814, 817] if arch == "x86" else [1536]) if key == "nat_mul" else []
        callees = [FUNCTIONS[child][arch] for child in ("nat_mul_word", "memset")] if key == "nat_mul" else []
        bodies[key] = extract(temp, arch, key, [(symbol, 0)],
                              [(symbol, pc) for pc in frontier], callees)
    origin, span = linked_span(temp, arch, "nat_mul", bodies["nat_mul"][2],
                               bodies["nat_mul"][4])
    return bodies, span, origin


def main():
    import decoder_arm_binding
    import decoder_x86_binding

    with tempfile.TemporaryDirectory(prefix="ssz-nat-mul-binding-") as directory:
        temp = Path(directory)
        for arch, generate, targets in (
                ("x86", decoder_x86_binding.nat_mul_source,
                 ("SszX86.NatMulMemsetEmbedded", "SszX86.NatMulWordImpl",
                  "SszX86.LinkedImage", "SszX86.LinkedImageSequential")),
                ("arm", decoder_arm_binding.nat_mul_source, ("SszArm.NatMulCalls",))):
            backend = ROOT / f"backends/{arch}"
            output("lake", "--log-level=error", "build", "ProofAudit", *targets, cwd=backend)
            bodies, span, origin = closure(temp, arch)
            proof = temp / f"{arch}-nat-mul.lean"
            proof.write_text(generate(bodies, span, origin=origin))
            output("lake", "env", "lean", "-DwarningAsError=true", str(proof), cwd=backend)
            count = sum(len(body[0]) for body in bodies.values())
            print(f"{arch} multiplication: {count} instructions in one linked image "
                  "(not an execution refinement)", flush=True)


if __name__ == "__main__":
    main()
