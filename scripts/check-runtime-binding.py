#!/usr/bin/env python3
"""Bind runtime instruction streams and layouts to the imported ISA models.

Disassemblers and this byte-to-instruction translation are trusted for artifact
binding. Lean checks the x86 AST/layout equality and raw ARM instruction words;
these checks do not replace execution proofs.
"""
from pathlib import Path
import json
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def output(*args, cwd=ROOT):
    try:
        return subprocess.check_output(args, cwd=cwd, text=True)
    except subprocess.CalledProcessError as error:
        print(error.output, end="", flush=True)
        raise


def lean(temp, arch, name, source, execute=False):
    path = temp / f"{arch}-{name}.lean"
    path.write_text(source)
    args = ["lake", "env", "lean"]
    if execute:
        args.append("--run")
    return output(*args, str(path), cwd=ROOT / f"backends/{arch}")


def instructions(arch, obj, kernel):
    symbol = "__udivti3" if kernel == "udivti3" else kernel
    symbols = output("llvm-nm-18", "-S", "--defined-only", str(obj))
    matches = re.findall(rf"^([0-9a-f]+)\s+([0-9a-f]+)\s+T\s+{symbol}$", symbols, re.M)
    if len(matches) != 1:
        raise ValueError(f"expected one sized {symbol} function: {symbols}")
    start, size = (int(value, 16) for value in matches[0])
    if start != 0 or size == 0:
        raise ValueError(f"unexpected {kernel} object extent: {start}, {size}")
    if arch == "x86":
        text = output("objdump", "-d", "-M", "att,suffix", "--insn-width=15",
                      "--disassemble-zeroes", f"--disassemble={symbol}", str(obj))
        pattern = r"\s*([0-9a-f]+):\s+((?:[0-9a-f]{2}\s+)+)(\S.*)"
    else:
        text = output("llvm-objdump-18", "-d", "--disassemble-zeroes",
                      f"--disassemble-symbols={symbol}", str(obj))
        pattern = r"\s*([0-9a-f]+):\s+([0-9a-f]{8})\s+(\S.*)"
    rows = []
    end = 0
    for line in text.splitlines():
        if not re.match(r"\s*[0-9a-f]+:", line):
            continue
        match = re.fullmatch(pattern, line)
        if match is None:
            raise ValueError(f"unparsed instruction: {line}")
        pc = int(match[1], 16)
        width = len(match[2].split()) if arch == "x86" else 4
        if pc != end or width == 0:
            raise ValueError(f"noncontiguous instruction at {pc}, expected {end}")
        rows.append((pc, width, match[2].strip(), match[3].strip()))
        end += width
    if end != size:
        raise ValueError(f"decoded {end} bytes, function symbol contains {size}")
    return rows, size


def bind_x86(temp, rows, size, kernel):
    model = kernel.capitalize()
    symbol = "__udivti3" if kernel == "udivti3" else kernel
    if kernel == "udivti3":
        executable = "SszX86.Udivti3.executable"
        layout = "SszX86.Udivti3.layout"
    else:
        executable = f"SszX86.{kernel}Executable"
        layout = f"SszX86.{kernel}Layout"
    metadata = json.loads(lean(temp, "x86", f"{kernel}-labels", f'''import SszX86.{model}Impl
import Lean
open Lean

def main : IO Unit := do
  let executable := {executable} 0
  let mut labels : Array Json := #[]
  for (pc, directive, _) in Kraken.Executable.withAddresses executable do
    match directive with
    | .label name => labels := labels.push (Json.arr #[toJson pc.toInt, toJson name])
    | .instr _ => pure ()
    | .byteArray _ => throw (IO.userError "noninstruction model directive")
  IO.println (Json.compress (Json.mkObj [
    ("start", toJson executable.1.toInt), ("labels", Json.arr labels)]))
''', execute=True))
    if metadata["start"] != 0:
        raise ValueError("binding requires the model's relative layout at origin zero")
    labels = {}
    names = set()
    boundaries = {pc for pc, _, _, _ in rows} | {size}
    for pc, name in metadata["labels"]:
        if pc not in boundaries or name in names or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", name):
            raise ValueError(f"invalid model label: {pc}, {name!r}")
        labels.setdefault(pc, []).append(name)
        names.add(name)
    expressions = []
    sizes = []
    branch_aliases = {"jb": "jb", "jc": "jb", "jnae": "jb",
                      "jae": "jae", "jnb": "jae", "jnc": "jae",
                      "ja": "ja", "jnbe": "ja", "jbe": "jbe", "jna": "jbe",
                      "je": "jz", "jz": "jz", "jne": "jnz", "jnz": "jnz",
                      "jmp": "jmp", "jmpq": "jmp"}
    for pc, width, _, instruction in rows:
        for label in labels.get(pc, []):
            expressions.append(f"parse({json.dumps(label + ':')})")
            sizes.append(0)
        parts = instruction.split(None, 1)
        mnemonic, operands = parts[0], parts[1] if len(parts) == 2 else ""
        expression = None
        if mnemonic in branch_aliases:
            target = re.fullmatch(rf"([0-9a-f]+)\s+<{symbol}(?:[+-]0x[0-9a-f]+)?>", operands)
            if target is None:
                raise ValueError(f"unsupported branch operand: {instruction}")
            target_labels = labels.get(int(target[1], 16), [])
            if len(target_labels) != 1:
                raise ValueError(f"branch target lacks a unique model label: {instruction}")
            instruction = branch_aliases[mnemonic] + " " + target_labels[0]
        elif mnemonic in ("ret", "retq") and not operands:
            instruction = "retq"
        elif mnemonic == "movzbl" and operands.startswith("("):
            # The pinned AST supports this real operation, but its text parser
            # only accepts register-source MOVZX. Keep the actual memory load.
            memory = re.fullmatch(r"\(%([a-z0-9]+)\),%([a-z0-9]+)", re.sub(r"\s+", "", operands))
            if memory is None:
                raise ValueError(f"unsupported MOVZX address: {instruction}")
            base, destination = memory.groups()
            expression = (
                f"[.instr (.regular .W64 .W32 (.movzx (.reg .{destination}) "
                f"(.mem (w := .W8) {{ base := some (.reg .{base}), idx := none }})))]")
        elif mnemonic in ("movq", "movl", "movb", "movzbl", "movabsq", "imulq",
                          "cmpq", "addq", "adcq", "subq", "sbbq", "testq", "xorl", "subl"):
            if not re.fullmatch(r"[%a-z0-9(),$x\s+-]+", operands):
                raise ValueError(f"unsupported operands: {instruction}")
            instruction = mnemonic + " " + re.sub(r"\s+", "", operands)
        else:
            raise ValueError(f"unsupported instruction: {instruction}")
        expressions.append(expression or f"parse({json.dumps(instruction)})")
        sizes.append(width)
    for label in labels.get(size, []):
        expressions.append(f"parse({json.dumps(label + ':')})")
        sizes.append(0)
    literal = " ++\n  ".join(expressions)
    source = f'''import SszX86.{model}Impl

open Kraken.X64.Parser
def actual : Program :=
  {literal}
def actualSizes : List Nat := {sizes}
example : actual.length = actualSizes.length := by decide
example (base : Int64) : (base, actual.zip actualSizes) = {executable} base := by
  have body : actual.zip actualSizes = ({executable} 0).2 := by decide
  dsimp (config := {{instances := true}})
    [{executable}, {layout}, Kraken.Layout.apply] at body ⊢
  exact congrArg (fun instructions => (base, instructions)) body
'''
    lean(temp, "x86", f"{kernel}-binding", source)
    print(f"x86 {kernel}: all {len(rows)} instructions and {size} encoded bytes match the model layout", flush=True)


def bind_arm(temp, rows, size, kernel):
    model = kernel.capitalize()
    words = ", ".join(f"0x{word}#32" for _, _, word, _ in rows)
    lean(temp, "arm", f"{kernel}-binding", f'''import SszArm.{model}

example : ([{words}] : List (BitVec 32)) = SszArm.{model}.program := by decide
''')
    print(f"arm {kernel}: all {len(rows)} instruction words and {size} encoded bytes match the model", flush=True)


def main():
    with tempfile.TemporaryDirectory(prefix="ssz-runtime-binding-") as directory:
        temp = Path(directory)
        for arch, target, namespace, suffix, bind in (
                ("x86", "x86_64-unknown-linux-gnu", "SszX86", "Impl", bind_x86),
                ("arm", "aarch64-unknown-linux-gnu", "SszArm", "", bind_arm)):
            kernels = ("memcpy", "memset", "memcmp", "memmove", "udivti3")
            modules = [f"{namespace}.{kernel.capitalize()}{suffix}" for kernel in kernels]
            output("lake", "build", *modules, cwd=ROOT / f"backends/{arch}")
            for kernel in kernels:
                obj = temp / f"{arch}-{kernel}.o"
                output("clang-18", f"--target={target}", "-c", f"asm/{arch}/{kernel}.s", "-o", str(obj))
                bind(temp, *instructions(arch, obj, kernel), kernel)


if __name__ == "__main__":
    main()
