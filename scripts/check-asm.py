#!/usr/bin/env python3
"""Check uint64 model programs against compiled Rust and shipped assembly.

This checker and the disassemblers are trusted for artifact binding. They do not
prove ISA semantics or replace the Lean proof build. Only literal two-instruction
uint64 programs are accepted; no normalization drops instructions or operands.
"""
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
SYMBOLS = {"ssz_load_u64": "loadProgram", "ssz_store_u64": "storeProgram"}


def output(*args):
    return subprocess.check_output(args, cwd=ROOT, text=True)


def x86_instruction(line):
    parts = line.strip().split(None, 1)
    mnemonic = parts[0]
    operands = re.sub(r"\s+", "", parts[1]) if len(parts) == 2 else ""
    if mnemonic in ("ret", "retq") and not operands:
        return "retq"
    if mnemonic == "movq" and operands in ("(%rdi),%rax", "%rsi,(%rdi)"):
        return mnemonic + " " + operands
    raise ValueError(f"unsupported x86 instruction: {line!r}")


def model(isa, name):
    if isa == "x86":
        path = ROOT / "backends/x86/SszX86/Impl.lean"
        match = re.search(
            rf'\bdef\s+{name}\s*:\s*Program\s*:=\s*parse\s*\(\s*"([^"\\]*)"\s*\)',
            path.read_text(),
        )
        if match is None:
            raise ValueError(f"missing literal {name} in {path}")
        return [x86_instruction(line) for line in match[1].splitlines() if line.strip()]
    path = ROOT / "backends/arm/SszArm/Impl.lean"
    match = re.search(
        rf"\bdef\s+{name}\s*:\s*List\s*\(BitVec\s+32\)\s*:=\s*\[([^\]]*)\]",
        re.sub(r"--[^\n]*", "", path.read_text()),
    )
    if match is None:
        raise ValueError(f"missing literal {name} in {path}")
    words = [word.strip() for word in match[1].split(",") if word.strip()]
    if not all(re.fullmatch(r"0x[0-9a-fA-F]{8}#32", word) for word in words):
        raise ValueError(f"nonliteral instruction words in {name}")
    return [int(word[2:-3], 16) for word in words]


def disassemble(isa, obj, symbol):
    if isa == "x86":
        text = output("objdump", "-d", "-M", "att,suffix", "--insn-width=15",
                      "--disassemble-zeroes", f"--disassemble={symbol}", str(obj))
        pattern = r"^\s*[0-9a-f]+:\s+((?:[0-9a-f]{2}\s+)+)(\S.*)$"
    else:
        text = output("llvm-objdump-18", "-d", f"--disassemble-symbols={symbol}", str(obj))
        pattern = r"^\s*[0-9a-f]+:\s+([0-9a-f]{8})\s+(\S.*)$"
    instructions = []
    for line in text.splitlines():
        if re.match(r"^\s*[0-9a-f]+:", line):
            match = re.fullmatch(pattern, line)
            if match is None:
                raise ValueError(f"unparsed instruction: {line}")
            instructions.append(x86_instruction(match[2]) if isa == "x86" else int(match[1], 16))
    if len(instructions) != 2:
        raise ValueError(f"expected exactly two instructions for {symbol}: {instructions}")
    return instructions


def main():
    with tempfile.TemporaryDirectory(prefix="ssz-bind-") as directory:
        temp = Path(directory)
        for isa, target in (("x86", "x86_64-unknown-linux-gnu"), ("arm", "aarch64-unknown-linux-gnu")):
            compiled = temp / f"{isa}-rust.o"
            assembled = temp / f"{isa}-asm.o"
            output("rustc", "+1.94.0", "--crate-type=lib", "-C", "opt-level=3", "--target", target,
                   "--emit=obj", "-o", str(compiled), "impl/uint64.rs")
            output("clang-18", f"--target={target}", "-c", f"asm/{isa}/uint64.s", "-o", str(assembled))
            for symbol, name in SYMBOLS.items():
                expected = model(isa, name)
                for obj in (compiled, assembled):
                    actual = disassemble(isa, obj, symbol)
                    if actual != expected:
                        raise SystemExit(f"{isa} {symbol}: {obj.name}: {actual} != model {expected}")
                print(f"{isa} {symbol}: Rust object = assembled artifact = model program", flush=True)


if __name__ == "__main__":
    main()
