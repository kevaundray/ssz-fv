"""Pinned, freestanding, whole-library SSZ assembly generation (not a proof)."""
from __future__ import annotations

import os
from pathlib import Path
import subprocess

from lower_arm import lower as lower_arm
from lower_x86 import lower as lower_x86

ROOT = Path(__file__).resolve().parents[1]
TARGETS = (("x86", "x86_64-unknown-none"), ("arm", "aarch64-unknown-none"))


def emit(target: str, assembly: Path, target_dir: Path) -> None:
    """Emit the lowered fat-LTO module."""
    env = os.environ.copy()
    env.pop("RUSTFLAGS", None)
    flags = [f"--remap-path-prefix={ROOT}=/ssz-fv"]
    if target.startswith("aarch64"):
        # Keep supported SIMD memory operations. LLVM auto-vectorization also
        # emits widening, comparisons, and lane operations missing from LNSym;
        # disable those passes, not SIMD itself. BR/BLR are also unimplemented.
        flags.extend(["-Cjump-tables=no", "-Cno-vectorize-loops", "-Cno-vectorize-slp"])
    env["CARGO_ENCODED_RUSTFLAGS"] = "\x1f".join(flags)
    subprocess.run(
        ["cargo", "+1.94.0", "rustc", "--manifest-path", str(ROOT / "native-ffi/Cargo.toml"),
         "--release", "--locked", "--target", target, "--target-dir", str(target_dir),
         "--", f"--emit=asm={assembly}"],
        cwd=ROOT, env=env, check=True,
    )
    lowering = lower_arm if target.startswith("aarch64") else lower_x86
    assembly.write_text(lowering(assembly.read_text()))
