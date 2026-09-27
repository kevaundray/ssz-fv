#!/usr/bin/env python3
"""Regenerate complete SSZ candidate assembly; no ISA proof is implied."""
from pathlib import Path
import shutil
import tempfile

from native_build import ROOT, TARGETS, emit


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="ssz-assembly-") as directory:
        temp = Path(directory)
        for architecture, target in TARGETS:
            candidate = temp / f"{architecture}.s"
            emit(target, candidate, temp / "cargo")
            destination = ROOT / "asm" / architecture / "ssz.s"
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(candidate, destination)
            print(f"{target}: wrote {destination.relative_to(ROOT)} ({destination.stat().st_size} bytes)", flush=True)


if __name__ == "__main__":
    main()
