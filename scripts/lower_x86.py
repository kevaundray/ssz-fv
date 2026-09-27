"""Prepare AT&T x86 assembly for the pinned Kraken scalar model.

BSF/BSR (16/32/64 bits) become bounded shift loops; only their defined ZF
is reproduced. A zero source retains the architecturally undefined destination;
a nonzero 32-bit result is zero-extended. BT becomes a rotate loop,
retaining incoming ZF and producing CF. Register aliases, signed memory
bit offsets, and stack-relative operands are handled before any output write.
SHLD/SHRD are NOT gaps: Kraken/X64/{Syntax,Semantics,Parser/Basic}.lean
explicitly implement them. CLTQ is MOVSX, not an arithmetic shift sequence.

REP MOVS uses a bounded straight-line MOV/LEA copy when its count is proved
constant (at most 16 elements). This preserves every flag and forward overlap
order. Otherwise a conservative CFG walk must prove all arithmetic flags dead
before any use. Returns may discard flags under SysV; unknown calls, indirect
exits and unknown instructions block that proof. DF must be clear, as required
at SysV ABI boundaries. No CLD or unmodeled flag-save instruction is introduced.

Sign predicates become signed-less predicates under must-proved OF=0; overflow
predicates become carry predicates under must-proved OF=CF (MUL/IMUL). Another
sign lowering retests a still-available, known producer result, but only after
proving the old flags dead on BOTH predicate exits. Facts intersect at joins;
every label admits an unknown indirect entry, and unknown instructions
invalidate facts. Inverse signed conditions use supported inverse branches,
with unconditional memory reads and 32-bit zero extension for CMOV.
With dead flags, REP BSF uses the baseline expansion of TZCNT: nonzero results
coincide; a zero result is exact for BMI1 and a permitted refinement of baseline
BSF's undefined destination. This is NOT all-state equality with baseline BSF.

All spills are allocated before use, strictly below the incoming RSP. The
allocated 8-byte words must be mapped ordinary memory, disjoint from operand
memory and accessible without wraparound. No red zone is used. RSP-relative
addresses are rebased. Scratch registers are caller-saved and never overlap
any operand register. RSP is restored before leaving an expansion, except
when the original instruction explicitly writes SP/ESP/RSP. Such a write is
delayed until after all scratch-register restores. Existing CFI is retained;
RSP-based CFA offsets track the temporary allocation. Register-based CFAs
must not use scratch registers. No source-level memory fault behavior is
claimed outside these frame/memory preconditions.

Unsigned DIVW/DIVL/DIVQ snapshot their divisor before changing RAX/RDX, then
check high<divisor. On that valid-division domain a bounded restoring-division
loop computes the exact quotient/remainder, preserving all other registers.
This includes nonzero high halves, operand aliases, and 16/32-bit write rules.
The complementary domain includes zero divisors and quotient overflow: restore
the complete frame and execute the ORIGINAL DIV to retain genuine #DE.
Arithmetic flags after successful DIV are undefined. Precise fault flag context,
fault timing and duplicate fault-path memory reads are not claimed; operand
memory must be stable ordinary memory under the frame preconditions above.
The retained fault DIV still requires an unreachability/domain proof for Kraken.
An explicit fault-boundary comment preserves that original DIV on repeated
lowering; the marker is metadata, not evidence that its guard is unreachable.
Byte DIV, signed IDIV and genuine traps remain unchanged model blockers.
CPU-dependent REP BSF/BSR and sign/overflow predicates without the required
facts are rejected, not silently weakened. Explicit TZCNT/LZCNT reproduce
defined zero/result/CF/ZF behavior. No ADX/BMI instruction is introduced. The
returned assembly is candidate preparation, not a refinement proof or a
promise that Kraken's narrower text parser accepts all aliases
(e.g. its Operation.movsx supports forms its AT&T parser does not).
"""

from __future__ import annotations

import re
from dataclasses import dataclass


_REG_ROWS = (
    ("rax", "eax", "ax", "al"), ("rbx", "ebx", "bx", "bl"),
    ("rcx", "ecx", "cx", "cl"), ("rdx", "edx", "dx", "dl"),
    ("rsi", "esi", "si", "sil"), ("rdi", "edi", "di", "dil"),
    ("rbp", "ebp", "bp", "bpl"), ("rsp", "esp", "sp", "spl"),
) + tuple((f"r{i}", f"r{i}d", f"r{i}w", f"r{i}b") for i in range(8, 16))
_REGS = {"%" + name: row for row in _REG_ROWS for name in row}
_CALLER_SAVED = ("r11", "r10", "r9", "r8", "rax", "rcx", "rdx", "rsi", "rdi")
_WIDTH_INDEX = {"q": 0, "l": 1, "w": 2, "b": 3}
_FLAGS = frozenset(("cf", "pf", "af", "zf", "sf", "of"))
_DIV_FAULT_MARKER = "ssz-lowering: original DIV fault boundary"
_CONDITIONS = {
    "z": {"zf"}, "e": {"zf"}, "nz": {"zf"}, "ne": {"zf"},
    "b": {"cf"}, "c": {"cf"}, "nae": {"cf"},
    "ae": {"cf"}, "nc": {"cf"}, "nb": {"cf"},
    "a": {"cf", "zf"}, "nbe": {"cf", "zf"},
    "be": {"cf", "zf"}, "na": {"cf", "zf"},
    "l": {"sf", "of"}, "nge": {"sf", "of"},
    "ge": {"sf", "of"}, "nl": {"sf", "of"},
    "le": {"sf", "of", "zf"}, "ng": {"sf", "of", "zf"},
    "g": {"sf", "of", "zf"}, "nle": {"sf", "of", "zf"},
    "s": {"sf"}, "ns": {"sf"}, "o": {"of"}, "no": {"of"},
    "p": {"pf"}, "pe": {"pf"}, "np": {"pf"}, "po": {"pf"},
}
_MODELED_CONDITIONS = {"z", "e", "nz", "ne", "b", "c", "nae", "ae", "nc", "nb", "a", "nbe", "be", "na", "l", "nge", "le", "ng"}
_INVERSE_CONDITIONS = {"g": "le", "nle": "le", "ge": "l", "nl": "l"}


def _reg(base: str, width: str = "q") -> str:
    return "%" + _REGS["%" + base][_WIDTH_INDEX[width]]


def _base(reg: str) -> str:
    try:
        return _REGS[reg][0]
    except KeyError as exc:
        raise ValueError(f"unsupported general register {reg}") from exc


def _split_operands(text: str) -> list[str]:
    parts, start, depth = [], 0, 0
    for pos, char in enumerate(text):
        if char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
        elif char == "," and depth == 0:
            parts.append(text[start:pos].strip())
            start = pos + 1
    if depth != 0:
        raise ValueError(f"unbalanced operand parentheses: {text}")
    if text[start:].strip():
        parts.append(text[start:].strip())
    return parts


def _instruction(line: str) -> tuple[str, str] | None:
    code = line.split("#", 1)[0].strip()
    if not code or code.startswith(".") or code.endswith(":"):
        return None
    # The compiler writes REP;MOVSQ and REP BSF as a single instruction line.
    code = re.sub(r"^rep(?:e|z)?\s*;\s*", "rep ", code)
    fields = code.split(None, 1)
    return fields[0].lower(), fields[1].strip() if len(fields) == 2 else ""


def _condition(mnemonic: str) -> tuple[str, str, str] | None:
    if mnemonic.startswith("cmov"):
        suffix = mnemonic[4:]
        if suffix in _CONDITIONS:
            return "cmov", suffix, ""
        if suffix[-1:] in "wlq" and suffix[:-1] in _CONDITIONS:
            return "cmov", suffix[:-1], suffix[-1]
    elif mnemonic.startswith("set") and mnemonic[3:] in _CONDITIONS:
        return "set", mnemonic[3:], ""
    elif mnemonic.startswith("j") and mnemonic[1:] in _CONDITIONS:
        return "j", mnemonic[1:], ""
    return None


def _effects(mnemonic: str, operands: str) -> tuple[set[str], set[str]] | None:
    condition = _condition(mnemonic)
    if condition:
        return set(_CONDITIONS[condition[1]]), set()
    if re.fullmatch(r"(?:mov\w*|lea[wlq]?|push[wlq]?|pop[wlq]?|not[bwlq]?|bswap[lq]?|nop\w*|cltq)", mnemonic):
        return set(), set()
    if re.fullmatch(r"(?:add|sub|cmp|neg|test|and|or|xor|mul|imul|div|idiv|bsf|bsr|tzcnt|lzcnt)[bwlq]?", mnemonic):
        return set(), set(_FLAGS)
    if re.fullmatch(r"(?:adc|sbb)[bwlq]?", mnemonic):
        return {"cf"}, set(_FLAGS)
    if re.fullmatch(r"(?:inc|dec)[bwlq]?", mnemonic):
        return set(), set(_FLAGS - {"cf"})
    if re.fullmatch(r"bt[wlq]?", mnemonic):
        return set(), set(_FLAGS - {"zf"})
    if re.fullmatch(r"(?:shl|sal|shr|sar|shld|shrd|rol|ror|rcl|rcr)[bwlq]?", mnemonic):
        args = _split_operands(operands)
        count = args[0] if len(args) > 1 else "$1"
        reads = {"cf"} if mnemonic.startswith(("rcl", "rcr")) else set()
        if not re.fullmatch(r"\$-?(?:0x[0-9a-fA-F]+|[0-9]+)", count):
            return reads, set()  # Variable count can be zero.
        mask = 63 if mnemonic.endswith("q") else 31
        amount = int(count[1:], 0) & mask
        if mnemonic.startswith(("rol", "ror")) and mnemonic[-1] in "bw":
            amount %= {"b": 8, "w": 16}[mnemonic[-1]]
        if mnemonic.startswith(("rcl", "rcr")) and mnemonic[-1] in "bw":
            amount %= {"b": 9, "w": 17}[mnemonic[-1]]
        return reads, (set() if amount == 0 else {"cf", "of"} if mnemonic.startswith("r") else set(_FLAGS))
    if mnemonic == "rep" and re.match(r"movs[bwlq](?:\s|$)", operands):
        return set(), set()
    return None


def _flags_dead(lines: list[str], origin: int, predicate_exits: bool = False) -> bool:
    """Prove flags dead after an instruction, optionally on both predicate exits."""
    labels = {}
    for index, line in enumerate(lines):
        code = line.split("#", 1)[0].strip()
        if code.endswith(":"):
            labels[code[:-1]] = index + 1
    pending = [(origin + 1, _FLAGS)]
    if predicate_exits:
        instruction = _instruction(lines[origin])
        condition = _condition(instruction[0]) if instruction else None
        if condition and condition[0] == "j":
            target = instruction[1]
            if target not in labels:
                return False
            pending.append((labels[target], _FLAGS))
    visited = set()
    while pending:
        index, flags = pending.pop()
        state = (index, flags)
        if not flags or state in visited:
            continue
        visited.add(state)
        while index < len(lines):
            line = lines[index].split("#", 1)[0].strip()
            # Falling out of a function or into a new section is not an ABI return.
            if line.startswith((".size", ".section", ".cfi_endproc")):
                return False
            instruction = _instruction(lines[index])
            if instruction:
                break
            index += 1
        if index == len(lines):
            return False
        mnemonic, operands = instruction
        if mnemonic in {"ret", "retq"}:
            continue  # SysV ABI does not expose outgoing arithmetic flags.
        if mnemonic in {"jmp", "jmpq"}:
            if operands not in labels:
                return False
            pending.append((labels[operands], flags))
            continue
        condition = _condition(mnemonic)
        effects = _effects(mnemonic, operands)
        if effects is None or effects[0] & flags:
            return False
        remaining = flags - effects[1]
        if condition and condition[0] == "j":
            if operands not in labels:
                return False
            pending.append((labels[operands], remaining))
        pending.append((index + 1, remaining))
    return True


def _written_registers(mnemonic: str, operands: str) -> set[str]:
    """Registers possibly written by an instruction with known flag effects."""
    args = _split_operands(operands)
    condition = _condition(mnemonic)
    if mnemonic.startswith(("cmp", "test", "bt")) or (condition and condition[0] == "j"):
        return set()
    if mnemonic == "cltq":
        return {"rax"}
    if mnemonic == "rep":
        return {"rsi", "rdi", "rcx"}
    if re.fullmatch(r"(?:mul|div|idiv)[bwlq]?|imul[bwlq]?", mnemonic) and len(args) == 1:
        return {"rax", "rdx"}
    written = {"rsp"} if mnemonic.startswith(("push", "pop")) else set()
    if not mnemonic.startswith(("push", "nop")) and args:
        register = args[-1]
        if register in _REGS:
            written.add(_base(register))
        elif register in {"%ah", "%bh", "%ch", "%dh"}:
            written.add("r" + register[1] + "x")
    return written




def _transfer_facts(mnemonic: str, operands: str, incoming: frozenset[str]) -> frozenset[str]:
    effects = _effects(mnemonic, operands)
    if effects is None:
        return frozenset()
    args = _split_operands(operands)
    written = _written_registers(mnemonic, operands)
    facts = {fact for fact in incoming if not (":" in fact and fact.split(":", 1)[1] in _REGS and _base(fact.split(":", 1)[1]) in written)}
    if "rcx" in written:
        facts = {fact for fact in facts if not fact.startswith("count:")}
    changed = effects[1]
    # _effects reports definite writes for liveness. Must-facts require MAY
    # writes instead: a variable shift can either preserve or replace flags.
    if re.fullmatch(r"(?:shl|sal|shr|sar|shld|shrd|rol|ror|rcl|rcr)[bwlq]?", mnemonic):
        changed = set(_FLAGS)
    if "of" in changed:
        facts.discard("of_zero")
    if {"of", "cf"} & changed:
        facts.discard("of_cf")
    if "sf" in changed:
        facts = {fact for fact in facts if not fact.startswith("sign:")}
    if re.fullmatch(r"(?:test|and|or|xor)[bwlq]?", mnemonic):
        facts.add("of_zero")
    if re.fullmatch(r"(?:mul|imul)[bwlq]?", mnemonic):
        facts.add("of_cf")
    if mnemonic.startswith("cmp") and len(args) == 2 and args[0] in {"$0", "$0x0"}:
        facts.add("of_zero")
    if args and args[-1] in _REGS and "sf" in effects[1] and re.fullmatch(
        r"(?:add|adc|sub|sbb|inc|dec|neg|shl|sal|shr|sar)[bwlq]?", mnemonic
    ):
        facts.add("sign:" + args[-1])
    if (
        len(args) == 2 and args[1] in {"%rcx", "%ecx"} and mnemonic.startswith("mov")
        and re.fullmatch(r"\$-?(?:0x[0-9a-fA-F]+|[0-9]+)", args[0])
    ):
        width = 64 if args[1] == "%rcx" else 32
        facts.add("count:" + str(int(args[0][1:], 0) % (1 << width)))
    return frozenset(facts)


def _facts_at(lines: list[str]) -> dict[int, frozenset[str]]:
    """Forward must-facts; intersect at joins and forget facts at unknown code.

    Every label is additionally treated as an unknown indirect-entry point.
    This intentionally sacrifices cross-label facts rather than assuming an
    incomplete direct-edge CFG accounts for the compiler's jump tables.
    Facts retain the exact register width of a sign-producing result.
    """
    nodes = {i: ins for i, line in enumerate(lines) if (ins := _instruction(line))}
    next_node, labels, roots = {}, {}, set()
    following = None
    for i in range(len(lines) - 1, -1, -1):
        next_node[i] = following
        if i in nodes:
            following = i
        code = lines[i].split("#", 1)[0].strip()
        if code.endswith(":") and following is not None:
            labels[code[:-1]] = following
            roots.add(following)
    if nodes:
        roots.add(min(nodes))
    states = {i: frozenset() for i in roots}
    pending = list(roots)
    while pending:
        i = pending.pop()
        mnemonic, operands = nodes[i]
        condition = _condition(mnemonic)
        if mnemonic in {"ret", "retq", "ud2", "ud1", "ud0", "hlt", "int3"}:
            continue
        incoming = states[i]
        outgoing = incoming if mnemonic in {"jmp", "jmpq"} else _transfer_facts(mnemonic, operands, incoming)
        successors = []
        if mnemonic in {"jmp", "jmpq"}:
            successors.append((labels.get(operands), outgoing))
        else:
            successors.append((next_node[i], outgoing))
            if condition and condition[0] == "j":
                successors.append((labels.get(operands), outgoing))
        for target, facts in successors:
            if target is None:
                continue
            merged = states[target] & facts if target in states else facts
            if target not in states or merged != states[target]:
                states[target] = merged
                pending.append(target)
    return states


@dataclass
class _Cfi:
    active: bool = False
    register: str = "rsp"
    supported: bool = True

    def consume(self, line: str) -> None:
        code = line.split("#", 1)[0].strip()
        if code.startswith(".cfi_startproc"):
            self.active, self.register = True, "unknown" if "simple" in code.split() else "rsp"
            self.supported = True
        elif code.startswith(".cfi_endproc"):
            self.active = False
        elif code.startswith((".cfi_def_cfa_register ", ".cfi_def_cfa_register\t", ".cfi_def_cfa ", ".cfi_def_cfa\t")):
            value = code.split(None, 1)[1].split(",", 1)[0].strip()
            dwarf = ("rax", "rdx", "rcx", "rbx", "rsi", "rdi", "rbp", "rsp") + tuple(f"r{i}" for i in range(8, 16))
            self.register = dwarf[int(value)] if value.isdecimal() and int(value) < 16 else value.lstrip("%")
            if "%" + self.register not in _REGS:
                self.register = "unknown"
        elif code.startswith((".cfi_def_cfa_expression", ".cfi_escape", ".cfi_remember_state", ".cfi_restore_state", ".cfi_register", ".cfi_same_value", ".cfi_expression", ".cfi_val_expression")):
            # Custom unwind register locations need more than a CFA adjustment.
            self.supported = False


class _Frame:
    def __init__(self, operands: str, count: int, cfi: _Cfi, sp_output: bool = False):
        used = {_base(reg) for reg in re.findall(r"%[a-z][a-z0-9]*", operands) if reg in _REGS}
        used.add(cfi.register)
        self.temps = [reg for reg in _CALLER_SAVED if reg not in used][:count]
        if len(self.temps) != count:
            raise ValueError("not enough non-aliasing caller-saved scratch registers")
        if cfi.active and (cfi.register == "unknown" or not cfi.supported):
            raise ValueError("cannot lower inside custom or unknown CFI register/CFA state")
        self.size = 8 * (count + int(sp_output))
        self.sp_output = sp_output
        self.adjust_cfa = cfi.active and cfi.register == "rsp"

    def begin(self) -> list[str]:
        lines = [f"\tleaq -{self.size}(%rsp), %rsp"]
        if self.adjust_cfa:
            lines.append(f"\t.cfi_adjust_cfa_offset {self.size}")
        lines += [f"\tmovq %{reg}, {8 * i}(%rsp)" for i, reg in enumerate(self.temps)]
        if self.sp_output:
            lines += [f"\tleaq {self.size}(%rsp), %{self.temps[0]}", f"\tmovq %{self.temps[0]}, {self.size - 8}(%rsp)"]
        return lines

    def end(self) -> list[str]:
        lines = [f"\tmovq {8 * i}(%rsp), %{reg}" for i, reg in enumerate(self.temps)]
        if self.sp_output:
            lines.append(f"\tmovq {self.size - 8}(%rsp), %rsp")
        else:
            lines.append(f"\tleaq {self.size}(%rsp), %rsp")
        if self.adjust_cfa:
            lines.append(f"\t.cfi_adjust_cfa_offset -{self.size}")
        return lines

    def address(self, operand: str) -> str:
        if re.search(r"%[a-z]+:", operand):
            raise ValueError("segment-relative operands are not modeled")
        if re.fullmatch(r"(?:[+-]?(?:0x[0-9a-fA-F]+|\d+))?\(%rip\)", operand):
            raise ValueError("numeric RIP-relative operands require instruction-address binding")
        if "(" in operand and re.search(r"\(\s*%[re]sp\b", operand):
            displacement, rest = operand.split("(", 1)
            return f"{displacement + '+' if displacement else ''}{self.size}({rest}"
        return operand

    def load(self, operand: str, temp: str, width: str) -> list[str]:
        if operand.startswith("%") and operand in _REGS and _base(operand) == "rsp":
            result = [f"\tleaq {self.size}(%rsp), %{temp}"]
            if width == "l":
                result.append(f"\tmovl {_reg(temp, 'l')}, {_reg(temp, 'l')}")
            return result
        return [f"\tmov{width} {self.address(operand)}, {_reg(temp, width)}"]


def _divide(mnemonic: str, operands: str, label: str, cfi: _Cfi) -> list[str]:
    """Unsigned double-width / single-width division; retain real #DE on faults."""
    args = _split_operands(operands)
    if len(args) != 1 or args[0].startswith("$"):
        raise ValueError("DIV requires exactly one register/memory divisor")
    source = args[0]
    width = mnemonic[-1]
    if source in _REGS and source != _reg(_base(source), width):
        raise ValueError("DIV divisor width mismatch")
    frame = _Frame(operands + ", %rax, %rdx", 3, cfi)
    divisor, numerator, counter = frame.temps
    divisor_reg, numerator_reg = _reg(divisor, width), _reg(numerator, width)
    quotient, remainder = _reg("rax", width), _reg("rdx", width)
    bits = {"w": 16, "l": 32, "q": 64}[width]
    lines = frame.begin() + frame.load(source, divisor, width)
    # high >= divisor is exactly unsigned quotient overflow, including divisor
    # zero. RAX/RDX and source-address registers are still original here.
    lines += [f"\tcmp{width} {divisor_reg}, {remainder}", f"\tjb {label}_valid"]
    lines += frame.end()
    lines += [f"\t{mnemonic} {operands} # {_DIV_FAULT_MARKER}", f"\tjmp {label}_done", f"{label}_valid:"]
    if frame.adjust_cfa:
        # The valid branch bypasses the fault-path restore. Describe its still
        # allocated frame rather than inheriting the preceding textual CFA.
        lines.append(f"\t.cfi_adjust_cfa_offset {frame.size}")
    lines += [
        f"\tmov{width} {quotient}, {numerator_reg}",
        f"\tmovq ${bits}, %{counter}",
        f"\tmov{width} $0, {quotient}",
        f"{label}_loop:",
        f"\tshl{width} $1, {quotient}",
        f"\tshl{width} $1, {numerator_reg}",
        f"\tadc{width} {remainder}, {remainder}",
        f"\tjb {label}_subtract",
        f"\tcmp{width} {divisor_reg}, {remainder}",
        f"\tjb {label}_next",
        f"{label}_subtract:",
        f"\tsub{width} {divisor_reg}, {remainder}",
        f"\tor{width} $1, {quotient}",
        f"{label}_next:",
        f"\tdecq %{counter}",
        f"\tjne {label}_loop",
    ]
    return lines + frame.end() + [f"{label}_done:"]


def _scan(mnemonic: str, operands: str, label: str, cfi: _Cfi) -> list[str]:
    args = _split_operands(operands)
    if len(args) != 2 or args[1] not in _REGS:
        raise ValueError("bit scan requires a register destination and one register/memory source")
    source, destination = args
    width = mnemonic[-1]
    if width not in "wlq" or destination != _reg(_base(destination), width):
        raise ValueError("bit-scan operand width mismatch")
    if source.startswith("$") or (source in _REGS and source != _reg(_base(source), width)):
        raise ValueError("invalid bit-scan source")
    kind, bits = mnemonic[:-1], {"w": 16, "l": 32, "q": 64}[width]
    counted = kind in {"tzcnt", "lzcnt"}
    reverse = kind in {"bsr", "lzcnt"}
    frame = _Frame(operands, 2, cfi, _base(destination) == "rsp")
    work, index = frame.temps
    wr, ix = _reg(work, width), _reg(index, width)
    output = f"{frame.size - 8}(%rsp)" if frame.sp_output else destination
    lines = frame.begin() + frame.load(source, work, width)
    lines += [f"\ttest{width} {wr}, {wr}", f"\tje {label}_zero", f"\tmovq ${-1 if reverse else 0}, %{index}", f"{label}_loop:"]
    if reverse:
        lines += [f"\tincq %{index}", f"\tshr{width} $1, {wr}", f"\tjne {label}_loop"]
        if counted:
            lines += [f"\tnegq %{index}", f"\tleaq {bits - 1}(%{index}), %{index}"]
    else:
        lines += [f"\ttest{width} $1, {wr}", f"\tjne {label}_found", f"\tshr{width} $1, {wr}", f"\tincq %{index}", f"\tjmp {label}_loop", f"{label}_found:"]
    if frame.sp_output and width == "l":
        lines.append(f"\tmovq $0, {output}")
    lines.append(f"\tmov{width} {ix}, {output}")
    # TEST produces CF=0, ZF=(result==0), as defined for nonzero TZ/LZCNT.
    lines.append(f"\ttestq %{index}, %{index}" if counted else f"\tcmpq $-1, %{index}")
    lines += [f"\tjmp {label}_done", f"{label}_zero:"]
    if counted:
        if frame.sp_output and width == "l":
            lines.append(f"\tmovq $0, {output}")
        lines += [f"\tmov{width} ${bits}, {output}", f"\tcmp{width} $1, {wr}"]  # 0-1: CF=1, ZF=0.
    lines += [f"{label}_done:"] + frame.end()
    return lines


def _bit_test(mnemonic: str, operands: str, label: str, cfi: _Cfi) -> list[str]:
    args = _split_operands(operands)
    if len(args) != 2 or mnemonic[-1] not in "wlq":
        raise ValueError("BT requires explicitly sized index and register/memory operands")
    offset, source = args
    width = mnemonic[-1]
    bits = {"w": 16, "l": 32, "q": 64}[width]
    if source in _REGS and source != _reg(_base(source), width):
        raise ValueError("BT source width mismatch")
    if not offset.startswith("$") and (offset not in _REGS or offset != _reg(_base(offset), width)):
        raise ValueError("BT offset must be an immediate or matching-width register")
    frame = _Frame(operands, 3, cfi)
    work, count, zf = frame.temps
    lines = frame.begin() + [f"\tsete {_reg(zf, 'b')}"]
    immediate = offset.startswith("$")
    if not immediate and source not in _REGS:
        lines += frame.load(offset, count, width)
        if width != "q":
            lines.append(f"\tmovs{width}q {_reg(count, width)}, %{count}")
        lines += [f"\tsarq ${bits.bit_length() - 1}, %{count}", f"\tleaq {frame.address(source)}, %{work}", f"\tleaq (%{work},%{count},{bits // 8}), %{work}", f"\tmov{width} (%{work}), {_reg(work, width)}"]
    else:
        lines += frame.load(source, work, width)
    if immediate:
        try:
            amount = int(offset[1:], 0)
        except ValueError as exc:
            raise ValueError("symbolic BT immediates require relocation evaluation") from exc
        if not -128 <= amount <= 255:
            raise ValueError("BT immediate is outside its encoded byte range")
        lines.append(f"\tmovq ${amount & (bits - 1)}, %{count}")
    else:
        lines += frame.load(offset, count, width)
        lines.append(f"\tandq ${bits - 1}, %{count}")
    lines += [f"\tcmpq $0, %{count}", f"\tje {label}_ready", f"{label}_loop:", f"\tror{width} $1, {_reg(work, width)}", f"\tdecq %{count}", f"\tjne {label}_loop", f"{label}_ready:", f"\tcmpb $1, {_reg(zf, 'b')}", f"\tror{width} $1, {_reg(work, width)}"]
    return lines + frame.end()


def _rep_movs(operands: str, label: str, cfi: _Cfi, count: int | None = None) -> list[str]:
    fields = operands.split(None, 1)
    mnemonic = fields[0]
    if not re.fullmatch(r"movs[bwlq]", mnemonic):
        raise ValueError("only REP MOVS is lowerable")
    if len(fields) > 1 and re.sub(r"\s+", "", fields[1]) not in {"(%rsi),%es:(%rdi)", "(%rsi),(%rdi)"}:
        raise ValueError("REP MOVS requires its standard 64-bit RSI/RDI addressing form")
    width = mnemonic[-1]
    size = {"b": 1, "w": 2, "l": 4, "q": 8}[width]
    frame = _Frame("%rsi, %rdi, %rcx", 1, cfi)
    temp = _reg(frame.temps[0], width)
    if count is not None:
        if not 0 <= count <= 16:
            raise ValueError("flag-preserving REP MOVS requires a proved count from 0 through 16")
        copy = [f"\tmov{width} (%rsi), {temp}", f"\tmov{width} {temp}, (%rdi)", f"\tleaq {size}(%rsi), %rsi", f"\tleaq {size}(%rdi), %rdi"]
        return frame.begin() + copy * count + ["\tmovq $0, %rcx"] + frame.end()
    return frame.begin() + [f"\ttestq %rcx, %rcx", f"\tje {label}_done", f"{label}_loop:", f"\tmov{width} (%rsi), {temp}", f"\tmov{width} {temp}, (%rdi)", f"\tleaq {size}(%rsi), %rsi", f"\tleaq {size}(%rdi), %rdi", "\tdecq %rcx", f"\tjne {label}_loop", f"{label}_done:"] + frame.end()


def _inverse_condition(condition: tuple[str, str, str], operands: str, label: str, cfi: _Cfi) -> list[str]:
    family, code, width = condition
    inverse = _INVERSE_CONDITIONS[code]
    if family == "j":
        return [f"\tj{inverse} {label}_done", f"\tjmp {operands}", f"{label}_done:"]
    if family == "set":
        return [f"\tj{inverse} {label}_false", f"\tmovb $1, {operands}", f"\tjmp {label}_done", f"{label}_false:", f"\tmovb $0, {operands}", f"{label}_done:"]
    args = _split_operands(operands)
    if len(args) != 2 or args[1] not in _REGS:
        raise ValueError("conditional move requires a register destination")
    if not width:
        width = next(w for w in "wlq" if args[1] == _reg(_base(args[1]), w))
    frame = None
    source, destination = args
    lines = []
    if source not in _REGS:
        if source.startswith("$"):
            raise ValueError("conditional move cannot use an immediate source")
        frame = _Frame(operands, 1, cfi, _base(destination) == "rsp")
        lines = frame.begin() + frame.load(source, frame.temps[0], width)
        source = _reg(frame.temps[0], width)
        if frame.sp_output:
            destination = f"{frame.size - 8}(%rsp)"
            if width == "l":
                lines.append(f"\tmovl $0, {frame.size - 4}(%rsp)")
    lines += [f"\tj{inverse} {label}_false", f"\tmov{width} {source}, {destination}", f"\tjmp {label}_done", f"{label}_false:"]
    if width == "l" and not (frame and frame.sp_output):
        lines.append(f"\tmovl {destination}, {destination}")
    lines.append(f"{label}_done:")
    return lines + (frame.end() if frame else [])


def lower(text: str) -> str:
    """Lower supported gaps deterministically, or report every residual by line."""
    lines = text.splitlines()
    prefix = ".Lssz_x86_lower"
    while prefix in text:
        prefix += "_"
    result, failures = [], []
    facts = _facts_at(lines)
    cfi = _Cfi()
    for index, line in enumerate(lines):
        cfi.consume(line)
        instruction = _instruction(line)
        if instruction is None:
            result.append(line)
            continue
        mnemonic, operands = instruction
        label = f"{prefix}_{index}"
        try:
            if mnemonic in {"bsf", "bsr", "tzcnt", "lzcnt", "bt"}:
                args = _split_operands(operands)
                candidates = [arg for arg in reversed(args) if arg in _REGS]
                if not candidates:
                    if mnemonic != "bt":
                        raise ValueError("cannot infer bit-scan operand width")
                    width = "l"  # GAS's default for an unsized immediate BT.
                else:
                    width = next((w for w in "wlq" if candidates[0] == _reg(_base(candidates[0]), w)), None)
                    if width is None:
                        raise ValueError("bit operations require 16/32/64-bit operands")
                mnemonic += width
            expansion = None
            if re.fullmatch(r"(?:bsf|bsr|tzcnt|lzcnt)[wlq]", mnemonic):
                expansion = _scan(mnemonic, operands, label, cfi)
            elif re.fullmatch(r"bt[wlq]", mnemonic):
                expansion = _bit_test(mnemonic, operands, label, cfi)
            elif re.fullmatch(r"div[wlq]", mnemonic):
                if line.partition("#")[2].strip() != _DIV_FAULT_MARKER:
                    expansion = _divide(mnemonic, operands, label, cfi)
            elif mnemonic == "cltq":
                if operands:
                    raise ValueError("CLTQ takes no explicit operands")
                expansion = ["\tmovslq %eax, %rax"]
            elif mnemonic == "rep":
                if re.match(r"bs[fr][wlq](?:\s|$)", operands):
                    scan, scan_operands = operands.split(None, 1)
                    if scan.startswith("bsr"):
                        raise ValueError("REP BSR differs from LZCNT even for nonzero sources")
                    if not _flags_dead(lines, index):
                        raise ValueError("REP BSF CPU-dependent CF/ZF are not proved dead")
                    expansion = _scan("tzcnt" + scan[-1], scan_operands, label, cfi)
                else:
                    count = next((int(fact[6:]) for fact in facts.get(index, ()) if fact.startswith("count:")), None)
                    if count is not None and count <= 16:
                        expansion = _rep_movs(operands, label, cfi, count)
                    else:
                        if not _flags_dead(lines, index):
                            raise ValueError("REP MOVS needs a bounded known count or provably dead arithmetic flags")
                        expansion = _rep_movs(operands, label, cfi)
            else:
                condition = _condition(mnemonic)
                if condition and condition[1] not in _MODELED_CONDITIONS:
                    family, code, width = condition
                    known = facts.get(index, ())
                    prefix_instructions = []
                    if code in {"s", "ns"} and "of_zero" in known:
                        condition = family, "l" if code == "s" else "ge", width
                    elif code in {"o", "no"} and "of_cf" in known:
                        condition = family, "c" if code == "o" else "nc", width
                    elif code in {"s", "ns"}:
                        producer = next((fact[5:] for fact in known if fact.startswith("sign:")), None)
                        if producer and _flags_dead(lines, index, predicate_exits=True):
                            producer_width = next(w for w in "bwlq" if producer == _reg(_base(producer), w))
                            prefix_instructions = [f"\ttest{producer_width} {producer}, {producer}"]
                            condition = family, "l" if code == "s" else "ge", width
                    if condition[1] in _INVERSE_CONDITIONS:
                        expansion = _inverse_condition(condition, operands, label, cfi)
                    elif condition[1] in _MODELED_CONDITIONS:
                        family, code, width = condition
                        expansion = [f"\t{family}{code}{width} {operands}"]
                    else:
                        raise ValueError("condition lacks a proved flag relation or an available sign result with dead flags")
                    expansion = prefix_instructions + expansion
                elif re.fullmatch(r"(?:popcnt|bts|btr|btc)[wlq]?|(?:repne|repnz|repe|repz)|(?:movs|stos|lods|scas|cmps)[bwlq]|(?:lahf|sahf|pushf[qwl]?|popf[qwl]?|cld|std)", mnemonic):
                    raise ValueError("unsupported instruction family has no implemented lowering")
            if expansion is None:
                result.append(line)
            else:
                result.append(f"\t# lowered: {line.strip()}")
                result.extend(expansion)
        except ValueError as exc:
            failures.append(f"line {index + 1}: {line.strip()}: {exc}")
    if failures:
        raise ValueError("x86 lowering residuals:\n" + "\n".join(failures))
    return "\n".join(result) + ("\n" if text.endswith("\n") else "")
