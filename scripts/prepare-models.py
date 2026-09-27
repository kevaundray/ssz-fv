#!/usr/bin/env python3
"""Prepare the pinned LNSym model with its source-locked Rn31 correction."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
BACKEND = ROOT / "backends/arm"
PACKAGE = BACKEND / ".lake/packages/lnsym"


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def prepare():
    model = json.loads((ROOT / "sources.lock.json").read_text())["arm-model"]
    correction = model["patch"]
    patch = ROOT / correction["path"]
    patch_hash = sha256(patch)
    if patch_hash != correction["sha256"]:
        raise ValueError(
            f"patch hash mismatch for {patch}: expected {correction['sha256']}, "
            f"found {patch_hash}; refusing to prepare the model"
        )

    # Never update an existing checkout: it may contain unrelated user changes.
    if not PACKAGE.exists():
        subprocess.run(["lake", "update", "lnsym"], cwd=BACKEND, check=True)

    head = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=PACKAGE, check=True,
        capture_output=True, text=True,
    ).stdout.strip()
    if head != model["rev"]:
        raise ValueError(
            f"LNSym base revision mismatch: expected {model['rev']}, found {head}; "
            "the existing checkout was not changed"
        )

    changed = subprocess.run(
        ["git", "diff", "--name-only", "-z", "HEAD", "--"], cwd=PACKAGE, check=True,
        capture_output=True, text=True,
    ).stdout.split("\0")
    unexpected = sorted(set(filter(None, changed)) - {correction["target"]})
    if unexpected:
        raise ValueError(
            f"unrecorded LNSym changes outside the approved patch: {unexpected}; "
            "the existing checkout was not changed"
        )

    target = PACKAGE / correction["target"]
    source_hash = sha256(target)
    before = correction["before_sha256"]
    after = correction["after_sha256"]
    if source_hash == after:
        state = "already applied"
    elif source_hash == before:
        subprocess.run(
            ["git", "apply", "--check", "--", str(patch)], cwd=PACKAGE, check=True,
        )
        subprocess.run(
            ["git", "apply", "--", str(patch)], cwd=PACKAGE, check=True,
        )
        state = "applied"
    else:
        raise ValueError(
            f"unexpected LNSym source drift in {target}: expected pristine SHA256 "
            f"{before} or corrected SHA256 {after}, found {source_hash}; "
            "the existing checkout was not changed"
        )

    actual = sha256(target)
    if actual != after:
        raise ValueError(
            f"corrected source hash mismatch for {target}: expected {after}, "
            f"found {actual}; inspect the checkout before continuing"
        )
    print(f"arm-model: {model['url']} @ {head}", flush=True)
    print(f"  patch: {correction['path']} SHA256 {patch_hash} ({state})", flush=True)
    print(f"  source: {correction['target']} SHA256 {actual}", flush=True)


def main():
    try:
        prepare()
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        print(f"prepare-models: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
