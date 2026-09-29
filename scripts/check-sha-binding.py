#!/usr/bin/env python3
"""Check the actual SHA code/data image; this is not an execution refinement."""
import argparse
import copy
from pathlib import Path
import tempfile

from decoder_binding import output
from native_build import ROOT
from sha_binding import extract_image, validate


def rejected(arch, image, mutate):
    changed = copy.deepcopy(image)
    mutate(changed)
    try:
        validate(arch, changed)
    except ValueError:
        return
    raise AssertionError(f"{arch}: accepted a changed SHA image")


def negative_checks(arch, image):
    body = "sha_finalize"
    rejected(arch, image, lambda data: data.__setitem__("origin", data["origin"] + 1))
    rejected(arch, image, lambda data: data.__setitem__("span", "00" + data["span"][2:]))
    rejected(arch, image, lambda data: data["bodies"][body]["rows"][0].__setitem__("pc", 1))
    rejected(arch, image, lambda data: data["bodies"][body]["frontiers"].clear())
    rejected(arch, image, lambda data: data["bodies"]["memcpy"].__setitem__(
        "offset", data["bodies"]["memcpy"]["offset"] + 4))
    rejected(arch, image, lambda data: data["bodies"][body]["rows"][0].__setitem__(
        "asm", data["bodies"][body]["rows"][0]["asm"] + " invalid"))
    regions = sorted((item["offset"] - image["origin"],
                      item["offset"] - image["origin"] + len(bytes.fromhex(item["raw"])))
                     for item in image["bodies"].values())
    gap = next(end for (_, end), (start, _) in zip(regions, regions[1:]) if end < start)

    def corrupt_gap(data):
        span = bytearray.fromhex(data["span"])
        span[gap] ^= 1
        data["span"] = span.hex()

    def move_call(data):
        callee = next(iter(data["bodies"][body]["callees"].values()))
        callee["offset"] += 4

    rejected(arch, image, corrupt_gap)
    rejected(arch, image, move_call)
    for name in ("initial", "rounds"):
        rejected(arch, image, lambda data, name=name: data["tables"][name].__setitem__(
            "offset", data["tables"][name]["offset"] + 4))
        rejected(arch, image, lambda data, name=name: data["tables"][name].__setitem__(
            "raw", "00" + data["tables"][name]["raw"][2:]))
    if arch == "x86":
        from decoder_x86_binding import expression
        for function in image["bodies"].values():
            for row in function["rows"]:
                if not row["asm"].lstrip().startswith("bswap"):
                    continue
                changed = dict(row)
                changed["encoding"] = row["encoding"][:-2] + "00"
                try:
                    expression(changed)
                except ValueError:
                    continue
                raise AssertionError("accepted a corrupt BSWAP encoding")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--arch", choices=("x86", "arm"), nargs="+", default=("x86", "arm"))
    args = parser.parse_args()
    import decoder_arm_binding
    import decoder_x86_binding

    with tempfile.TemporaryDirectory(prefix="ssz-sha-binding-") as directory:
        temp = Path(directory)
        for arch in args.arch:
            backend = ROOT / f"backends/{arch}"
            generator, targets = (
                (decoder_x86_binding.sha_source,
                 ("SszX86.HashContracts", "SszX86.LinkedImage", "SszX86.LinkedImageSequential"))
                if arch == "x86" else (decoder_arm_binding.sha_source, ("SszArm.HashImage",)))
            output("lake", "--log-level=error", "build", "ProofAudit", *targets, cwd=backend)
            image = extract_image(temp, arch)
            negative_checks(arch, image)
            proof = temp / f"{arch}-sha.lean"
            proof.write_text(generator(image))
            output("lake", "env", "lean", "-DwarningAsError=true", str(proof), cwd=backend)
            count = sum(len(body["rows"]) for body in image["bodies"].values())
            print(f"{arch} SHA: {count} instructions, full linked span, IV/round tables, "
                  "and rejected image mutations (not an execution refinement)", flush=True)


if __name__ == "__main__":
    main()
