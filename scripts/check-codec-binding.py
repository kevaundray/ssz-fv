#!/usr/bin/env python3
"""Certify complete recursive codec images; image binding is not execution refinement."""
import argparse
import copy
from pathlib import Path
import tempfile

from codec_binding import NAMES, extract_image, selected_rows, validate
from decoder_binding import output
from native_build import ROOT


def rejected(arch, image, mutate):
    changed = copy.deepcopy(image)
    mutate(changed)
    try:
        validate(arch, changed)
    except ValueError:
        return
    raise AssertionError(f"{arch}: accepted a changed recursive codec image")


def negative_checks(arch, image):
    rejected(arch, image, lambda data: data.__setitem__("textAddress", data["textAddress"] + 1))
    rejected(arch, image, lambda data: data["functions"].pop("decode_struct_values"))
    rejected(arch, image, lambda data: data["functions"]["serialize"].__setitem__(
        "address", data["functions"]["serialize"]["address"] + 1))
    rejected(arch, image, lambda data: data["functions"]["measure"].__setitem__(
        "size", data["functions"]["measure"]["size"] - 1))
    rejected(arch, image, lambda data: data["functions"]["emit"]["rows"][0].__setitem__("asm", "nop"))
    rejected(arch, image, lambda data: data["symbols"][0].__setitem__(
        "address", data["symbols"][0]["address"] + 1))

    def corrupt_gap(data):
        intervals = sorted((body["offset"], body["offset"] + body["size"])
                           for body in data["functions"].values())
        gap = next(end for (_, end), (start, _) in zip(intervals, intervals[1:]) if end < start)
        text = bytearray.fromhex(data["textRaw"])
        text[gap] ^= 1
        data["textRaw"] = text.hex()

    def move_callee(data):
        row = next(row for body in data["functions"].values() for row in body["rows"] if "callee" in row)
        row["targetAddress"] += 4

    def change_constant(data):
        section = next(section for section in data["constants"].values() if section["raw"])
        raw = bytearray.fromhex(section["raw"])
        raw[0] ^= 1
        section["raw"] = raw.hex()

    rejected(arch, image, corrupt_gap)
    rejected(arch, image, move_callee)
    rejected(arch, image, change_constant)
    if arch == "x86":
        body = copy.deepcopy(image["functions"]["decode_list"])
        fault = next(row for row in body["rows"] if row["pc"] == 1195)
        fault["encoding"] = "90 90 90"
        try:
            selected_rows(arch, "decode_list", body)
        except ValueError:
            pass
        else:
            raise AssertionError("accepted a changed original DIV fault instruction")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--arch", choices=("x86", "arm"), nargs="+", default=("x86", "arm"))
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="ssz-codec-binding-") as directory:
        temp = Path(directory)
        for arch in args.arch:
            backend = ROOT / f"backends/{arch}"
            if arch == "x86":
                from codec_x86_binding import source
                targets = ["SszX86.Codec" + "".join(word.title() for word in name.split("_")) + "Impl"
                           for name in NAMES]
                targets.extend(("SszX86.LinkedImage", "SszX86.LinkedImageSequential"))
            else:
                from codec_arm_binding import source
                targets = ["SszArm.CodecLinked", "SszArm.CodecLinkedBranches", "SszArm.CodecSimd"]
            output("lake", "--log-level=error", "build", "ProofAudit", *targets, cwd=backend)
            image = extract_image(temp, arch)
            validate(arch, image)
            negative_checks(arch, image)
            proof = temp / f"{arch}-codec.lean"
            proof.write_text(source(image))
            output("lake", "env", "lean", "-DwarningAsError=true", str(proof), cwd=backend)
            total = sum(len(body["rows"]) for body in image["functions"].values())
            selected = sum(len(selected_rows(arch, name, body)) for name, body in image["functions"].items())
            print(f"{arch} recursive codec: 17 complete functions, {total} instruction rows, "
                  f"{selected} executable selections, full linked bytes and rejected mutations "
                  "(not an execution refinement)", flush=True)


if __name__ == "__main__":
    main()
