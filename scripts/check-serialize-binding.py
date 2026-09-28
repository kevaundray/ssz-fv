#!/usr/bin/env python3
"""Bind the native serializer's primitive call graph in one image, not execution."""
from pathlib import Path
import importlib.util
import tempfile

from decoder_binding import FUNCTIONS, extract, linked_span, output
from native_build import ROOT


def load_check(name, filename):
    """Reuse the existing CLI extraction APIs without invoking their main checks."""
    spec = importlib.util.spec_from_file_location(name, ROOT / "scripts" / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def closure(temp, arch):
    measure = load_check("_serialize_measure_check", "check-measure-binding.py")
    emit = load_check("_serialize_emit_check", "check-emit-binding.py")
    bodies, _, _, measure_table = measure.closure(temp, arch)
    bodies["emit"] = emit.image(temp, arch)
    if "memcpy" not in bodies:
        bodies["memcpy"] = extract(temp, arch, "memcpy", [("memcpy", 0)])
    symbol = FUNCTIONS["serialize"][arch]
    bodies["serialize"] = extract(
        temp, arch, "serialize", [(symbol, 0)], [],
        [FUNCTIONS[key][arch] for key in ("measure", "emit")])
    caller = bodies["serialize"]
    expected = (99, 424) if arch == "x86" else (173, 692)
    if (caller[1] != [0] or caller[3]
            or (len(caller[0]), len(caller[2])) != expected
            or set(caller[4]) != {FUNCTIONS[key][arch] for key in ("measure", "emit")}):
        raise ValueError(f"{arch}: unexpected complete serializer wrapper")
    combined = dict(caller[4])
    for key in ("measure", "emit"):
        component = caller[4][FUNCTIONS[key][arch]]
        if component["size"] != len(bodies[key][2]) or bytes.fromhex(component["raw"]) != bodies[key][2]:
            raise ValueError(f"{arch}: serializer callee image mismatch: {key}")
        for name, metadata in bodies[key][4].items():
            shifted = dict(metadata, offset=component["offset"] + metadata["offset"])
            if name in combined and combined[name] != shifted:
                raise ValueError(f"{arch}: inconsistent shared serializer helper: {name}")
            combined[name] = shifted
    origin, span = linked_span(temp, arch, "serialize", caller[2], combined)
    expected_span = (-66368, 147209) if arch == "x86" else (-78380, 163676)
    if (origin, len(span)) != expected_span:
        raise ValueError(f"{arch}: unexpected joint serializer image extent")
    tables = ({"measure": measure_table, "emit": emit.table_bytes(temp)}
              if arch == "x86" else None)
    return bodies, span, origin, tables


def main():
    import decoder_arm_binding
    import decoder_x86_binding

    with tempfile.TemporaryDirectory(prefix="ssz-serialize-binding-") as directory:
        temp = Path(directory)
        for arch, namespace, generate in (
                ("x86", "SszX86", decoder_x86_binding.serialize_source),
                ("arm", "SszArm", decoder_arm_binding.serialize_source)):
            backend = ROOT / f"backends/{arch}"
            output("lake", "--log-level=error", "build", f"{namespace}.SerializeImpl", cwd=backend)
            bodies, span, origin, tables = closure(temp, arch)
            source = generate(bodies, span, origin=origin, table_bytes=tables)
            proof = temp / f"{arch}-serialize.lean"
            proof.write_text(source)
            output("lake", "env", "lean", "-DwarningAsError=true", str(proof), cwd=backend)
            count = sum(len(body[0]) for body in bodies.values())
            print(f"{arch} primitive serializer: {len(bodies['serialize'][0])} wrapper instructions, "
                  f"{count} total instructions in one linked image "
                  "(not an execution refinement)", flush=True)


if __name__ == "__main__":
    main()
