#!/usr/bin/env python3
"""Compare the native SSZ candidate with the pinned Python oracle on eight seeded corpora.

The generator and seeds are the upstream parity suite's; no fixtures are synthesized
from the candidate's own answers. All corpus files are temporary. This is execution
evidence, not an ISA refinement proof.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
SPEC = ROOT / "vendor/ssz-specs"


def oracle(destination: Path) -> None:
    sys.path.insert(0, str(SPEC / "tests"))
    from parity.corpus import Corpus
    from parity.draw import Draw

    for seed in range(8):
        corpus = Corpus.drawn(Draw.seeded(seed), f"seed{seed}", cases=120, pairs=60)
        (destination / f"seed{seed}.json").write_text(json.dumps(corpus.to_json()))


def main() -> None:
    if len(sys.argv) == 3 and sys.argv[1] == "--oracle":
        oracle(Path(sys.argv[2]))
        return
    if len(sys.argv) != 1:
        raise SystemExit("usage: check-native-parity.py")
    subprocess.run(
        ["cargo", "build", "--release", "--example", "conformance", "--manifest-path", str(ROOT / "native/Cargo.toml")],
        cwd=ROOT, check=True,
    )
    env = os.environ.copy()
    env["UV_PROJECT_ENVIRONMENT"] = ".venv312"
    env["SSZ_PARANOID_ROOTS"] = "1"
    with tempfile.TemporaryDirectory(prefix="ssz-native-parity-") as directory:
        destination = Path(directory)
        subprocess.run(
            ["uv", "run", "--python", "/usr/bin/python3.12", "--locked", "--group", "test", "python",
             str(Path(__file__).resolve()), "--oracle", str(destination)],
            cwd=SPEC, env=env, check=True,
        )
        for seed in range(8):
            print(f"Python/native differential seed {seed}: 120 values, 60 compatibility pairs", flush=True)
            subprocess.run(
                [str(ROOT / "native/target/release/examples/conformance"), "--diff", str(destination / f"seed{seed}.json")],
                cwd=ROOT, check=True,
            )
    print("native differential: 960 generated values and 480 compatibility pairs passed")


if __name__ == "__main__":
    main()
