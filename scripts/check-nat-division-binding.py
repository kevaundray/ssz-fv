#!/usr/bin/env python3
"""Bind native division and its proved runtime callee in one linked image."""
from pathlib import Path
import runpy
import tempfile

from decoder_binding import FUNCTIONS, extract, linked_span, output
from decoder_x86_binding import nat_division_source as x86_source
from decoder_arm_binding import nat_division_source as arm_source
from native_build import ROOT


def main():
    runtime = runpy.run_path(str(ROOT / "scripts/check-runtime-binding.py"))
    with tempfile.TemporaryDirectory(prefix="ssz-nat-division-binding-") as directory:
        temp = Path(directory)
        for arch, namespace, target, generate in (
                ("x86", "SszX86", "x86_64-unknown-linux-gnu", x86_source),
                ("arm", "SszArm", "aarch64-unknown-linux-gnu", arm_source)):
            backend = ROOT / f"backends/{arch}"
            modules = [f"{namespace}.NatDivisionImpl"]
            if arch == "x86":
                modules.append("SszX86.Udivti3Embedded")
            output("lake", "--log-level=error", "build", *modules, cwd=backend)
            body = extract(temp, arch, "nat_div_rem_small",
                           [(FUNCTIONS["nat_div_rem_small"][arch], 0)], calls=("__udivti3",))
            linked = linked_span(temp, arch, "nat_div_rem_small", body[2], body[4])
            obj = temp / f"{arch}-udivti3.o"
            output("clang-18", f"--target={target}", "-c", "asm/" + arch + "/udivti3.s",
                   "-o", str(obj))
            rows, size = runtime["instructions"](arch, obj, "udivti3")
            raw = b"".join(bytes.fromhex(row[2]) if arch == "x86"
                           else int(row[2], 16).to_bytes(4, "little") for row in rows)
            if raw.hex() != body[4]["__udivti3"]["raw"]:
                raise ValueError(f"{arch}: linked divider differs from the bound runtime object")
            runtime[f"bind_{arch}"](temp, rows, size, "udivti3")
            proof = temp / f"{arch}-joint.lean"
            proof.write_text(generate(body, linked))
            output("lake", "env", "lean", str(proof), cwd=backend)
            print(f"{arch} Nat.div_rem_small: {len(body[0])} caller instructions, "
                  f"{len(rows)} runtime instructions, joint CodeAt witnesses checked "
                  "(not a Nat-division execution refinement)", flush=True)


if __name__ == "__main__":
    main()
