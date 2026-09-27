"""Prepare AArch64 assembly for the pinned LNSym instruction subset.

This is a semantics-preserving candidate preparation pass, NOT a refinement
proof or a claim that all input instructions are modeled.  BRK is deliberately
retained: proving a valid call cannot reach a panic/trap remains an obligation.
Supported SIMD instructions are left alone.  Known unsupported normal SIMD or
control instructions fail closed rather than being replaced by a fake result.

Preconditions for expansions: little-endian ordinary, nonvolatile memory; an
aligned, non-wrapping SP; and caller-available writable stack below SP, disjoint
from live data addressed through other registers.  No red zone is permitted.
At most 64 bytes hold saved caller-saved GPRs; memory addressing may additionally
reserve up to 512 bytes to keep these saves below a negative SP-relative access.
The original memory accesses must be valid (fault timing and atomicity are not
preserved).  All non-destination GPRs and NZCV are preserved, except CCMP/CCMN
and flag-setting extended arithmetic which produce the original defined flags.
Only x0..x17 are borrowed, never the CFA register or a named operand.  SP is
restored on every path, except an original instruction's explicit SP update.

CFI is tracked through remember/restore-state and SP/frame-pointer CFA changes.
Temporary SP changes adjust an SP-based CFA; frame-pointer CFAs remain fixed.
No call is introduced and no callee-saved register's unwind rule is changed.
Assembler directives, labels, relocations and data are retained.  This pass
expects ordinary compiler assembly (one instruction per line, not macros).
The exact emitted bytes must still be checked against the fixed model: notably
LNSym's GPR LDUR/STUR, halfword/sign-extending immediate memory and ZR memory
semantics are not interchangeable with its supported LDR/STR operand forms.
"""
from __future__ import annotations

import re
from dataclasses import dataclass, field


_GPR = re.compile(r"(?:[wx](?:[0-9]|[12][0-9]|30)|[wx]zr|w?sp)$")
_MEM = re.compile(r"(ldr(?:b|h|sb|sh|sw)?|str(?:b|h)?|ldur(?:b|h|sb|sh|sw)?|stur(?:b|h)?|ldp|stp|ldpsw)$")
_CONDS = {"eq", "ne", "cs", "hs", "cc", "lo", "mi", "pl", "vs", "vc", "hi", "ls", "ge", "lt", "gt", "le", "al", "nv"}
_EXTENSIONS = {"uxtb": 8, "uxth": 16, "uxtw": 32, "uxtx": 64,
               "sxtb": 8, "sxth": 16, "sxtw": 32, "sxtx": 64}


def _operands(text: str) -> list[str]:
    return [part.strip() for part in re.split(r",(?![^\[\]]*\])(?![^{}]*})", text)]


def _x(reg: str) -> str:
    if reg in {"sp", "wsp", "31"}:
        return "sp"
    if reg.isdecimal():
        return "x" + reg
    if reg.startswith(("w", "x")):
        return "x" + reg[1:]
    return reg


def _w(reg: str) -> str:
    return "wsp" if reg == "sp" else "w" + reg[1:]


def _width(reg: str) -> int:
    return 32 if reg.startswith("w") else 64


def _num(text: str) -> int:
    value = text.removeprefix("#")
    # LLVM sometimes emits decimal constants with leading zeroes.
    return int(value, 16 if "0x" in value.lower() else 10)


def _ins(op: str, *args: str) -> str:
    return "\t" + op + ("\t" + ", ".join(args) if args else "")


def _add_const(dst: str, src: str, value: int) -> list[str]:
    if value == 0 and dst == src:
        return []
    op = "add" if value >= 0 else "sub"
    value = abs(value)
    if value > 0xffffff:
        raise ValueError("address adjustment exceeds two immediate instructions")
    low, high = value & 4095, value >> 12
    result = []
    if high:
        result.append(_ins(op, dst, src, f"#{high}", "lsl #12"))
        src = dst
    if low or not high:
        result.append(_ins(op, dst, src, f"#{low}"))
    return result


@dataclass
class _CFI:
    active: bool = False
    reg: str = "sp"
    offset: int = 0
    stack: list[tuple[str, int]] = field(default_factory=list)

    def consume(self, line: str) -> None:
        fields = line.strip().split(None, 1)
        op = fields[0] if fields else ""
        args = _operands(fields[1]) if len(fields) == 2 else []
        if op == ".cfi_startproc":
            self.active, self.reg, self.offset = True, "sp", 0
            self.stack.clear()
        elif op == ".cfi_endproc":
            self.active = False
        elif op == ".cfi_def_cfa":
            self.reg, self.offset = _x(args[0]), _num(args[1])
        elif op == ".cfi_def_cfa_register":
            self.reg = _x(args[0])
        elif op == ".cfi_def_cfa_offset":
            self.offset = _num(args[0])
        elif op == ".cfi_adjust_cfa_offset":
            self.offset += _num(args[0])
        elif op == ".cfi_remember_state":
            self.stack.append((self.reg, self.offset))
        elif op == ".cfi_restore_state":
            if not self.stack:
                raise ValueError("unbalanced .cfi_restore_state")
            self.reg, self.offset = self.stack.pop()
        elif op in {".cfi_escape", ".cfi_def_cfa_expression"}:
            raise ValueError("opaque CFA expressions cannot be updated safely")

    def adjust(self, amount: int) -> list[str]:
        if self.active and self.reg == "sp" and amount:
            return [f"\t.cfi_adjust_cfa_offset {amount}"]
        return []


class _Spill:
    def __init__(self, ctx: _Lower, args: list[str], count: int, reserve: int = 0):
        used = {_x(reg) for arg in args for reg in re.findall(r"\b(?:[wx](?:\d+|zr)|w?sp)\b", arg)}
        used.add(ctx.cfi.reg)
        pool = [f"x{i}" for i in (*range(9, 18), *range(9)) if f"x{i}" not in used]
        if len(pool) < count:
            raise ValueError("not enough non-operand caller-saved spill registers")
        if not 0 <= reserve <= 512:
            raise ValueError("SP-relative spill exclusion exceeds 512 bytes")
        self.regs = pool[:count]
        self.size = ((count * 8 + reserve + 15) // 16) * 16
        self.ctx = ctx

    def enter(self) -> list[str]:
        result = [_ins("sub", "sp", "sp", f"#{self.size}")]
        result += self.ctx.cfi.adjust(self.size)
        result += [_ins("str", reg, f"[sp, #{i * 8}]") for i, reg in enumerate(self.regs)]
        return result

    def leave(self) -> list[str]:
        result = [_ins("ldr", reg, f"[sp, #{i * 8}]") for i, reg in reversed(list(enumerate(self.regs)))]
        result += [_ins("add", "sp", "sp", f"#{self.size}")]
        return result + self.ctx.cfi.adjust(-self.size)

    def leave_to_sp(self, result: str, anchor: str) -> list[str]:
        # The final self-addressed load restores the last borrowed register
        # after SP has acquired its original instruction's result.
        code = [_ins("mov", anchor, "sp")]
        cfi = self.ctx.cfi
        if cfi.active and cfi.reg == "sp":
            code += ["\t.cfi_remember_state", f"\t.cfi_def_cfa {anchor}, {cfi.offset + self.size}"]
        code.append(_ins("mov", "wsp" if result.startswith("w") else "sp", result))
        for i, reg in reversed(list(enumerate(self.regs))):
            if reg != anchor:
                code.append(_ins("ldr", reg, f"[{anchor}, #{i * 8}]"))
        code.append(_ins("ldr", anchor, f"[{anchor}, #{self.regs.index(anchor) * 8}]"))
        if cfi.active and cfi.reg == "sp":
            code += ["\t.cfi_restore_state"] + cfi.adjust(-self.size)
        return code


class _Lower:
    def __init__(self, text: str):
        self.cfi = _CFI()
        self.serial = 0
        self.prefix = ".Llower_arm_"
        while self.prefix in text:
            self.prefix += "_"

    def label(self) -> str:
        self.serial += 1
        return f"{self.prefix}{self.serial}"

    def spill(self, args: list[str], count: int, reserve: int = 0) -> _Spill:
        return _Spill(self, args, count, reserve)

    def select(self, op: str, a: list[str]) -> list[str]:
        dst, cond = a[0], a[-1]
        if cond not in _CONDS:
            raise ValueError(f"unknown condition {cond}")
        zr = "wzr" if _width(dst) == 32 else "xzr"
        if dst == zr:
            # A discarded conditional-select result has no architectural effect.
            return [_ins("csel", dst, zr, zr, cond)]
        yes, done = self.label(), self.label()
        if op in {"cset", "csetm"}:
            false = [_ins("mov", dst, "#0")]
            true = [_ins("mov", dst, "#1" if op == "cset" else "#-1")]
        else:
            alias = op in {"cinc", "cinv", "cneg"}
            n, m = a[1], a[1] if alias else a[2]
            transform = op.removeprefix("cs") if not alias else op[1:]
            if transform == "inc":
                transformed = [_ins("mov", dst, "#1")] if m == zr else [_ins("add", dst, m, "#1")]
            elif transform == "inv":
                transformed = [_ins("mvn", dst, m)]
            else:
                transformed = [_ins("neg", dst, m)]
            false, true = ([_ins("mov", dst, n)], transformed) if alias else (transformed, [_ins("mov", dst, n)])
        return [_ins("b." + cond, yes)] + false + [_ins("b", done), yes + ":"] + true + [done + ":"]

    def bit_branch(self, op: str, a: list[str]) -> list[str]:
        src, bit, target = a
        n = _num(bit)
        if not 0 <= n < _width(src):
            raise ValueError("bit-test index outside register width")
        frame = self.spill(a, 1)
        tmp = frame.regs[0] if _width(src) == 64 else _w(frame.regs[0])
        taken, done = self.label(), self.label()
        code = frame.enter() + [_ins("and", tmp, src, f"#{1 << n}"), _ins("cbz" if op == "tbz" else "cbnz", tmp, taken)]
        code += frame.leave() + [_ins("b", done), taken + ":"]
        # The alternate edge still has the spill frame, unlike the textually
        # preceding fall-through edge.  Re-establish its CFI at this label.
        code += self.cfi.adjust(frame.size) + frame.leave()
        return code + [_ins("b", target), done + ":"]

    def bit_count(self, op: str, a: list[str]) -> list[str]:
        dst, src = a
        width = _width(dst)
        frame = self.spill(a, 2)
        value, result = [r if width == 64 else _w(r) for r in frame.regs]
        code = frame.enter() + [_ins("mov", value, src)]
        if op == "clz":
            loop, done = self.label(), self.label()
            code += [_ins("mov", result, f"#{width}"), _ins("cbz", value, done), loop + ":",
                     _ins("sub", result, result, "#1"), _ins("lsr", value, value, "#1"),
                     _ins("cbnz", value, loop), done + ":", _ins("mov", dst, result)]
        else:
            step = 1
            while step < width:
                mask = sum(((1 << step) - 1) << pos for pos in range(0, width, step * 2))
                code += [_ins("and", result, value, f"#{mask}"), _ins("lsr", value, value, f"#{step}"),
                         _ins("and", value, value, f"#{mask}"), _ins("orr", value, value, result, f"lsl #{step}")]
                step *= 2
            code.append(_ins("mov", dst, value))
        return code + frame.leave()

    def multiply(self, op: str, a: list[str]) -> list[str]:
        dst, n, m = a[:3]
        if op in {"umulh", "smulh"}:
            if any(_width(r) != 64 for r in a):
                raise ValueError("high multiplication requires 64-bit operands")
            frame = self.spill(a, 6)
            lo_n, hi_n, lo_m, hi_m, t, u = frame.regs
            code = frame.enter() + [
                _ins("mov", _w(lo_n), _w(n)), _ins("lsr", hi_n, n, "#32"),
                _ins("mov", _w(lo_m), _w(m)), _ins("lsr", hi_m, m, "#32"),
                _ins("mul", t, lo_n, lo_m), _ins("lsr", t, t, "#32"),
                _ins("madd", t, hi_n, lo_m, t), _ins("lsr", lo_m, t, "#32"),
                _ins("mov", _w(u), _w(t)), _ins("madd", u, lo_n, hi_m, u),
                _ins("lsr", u, u, "#32"), _ins("madd", t, hi_n, hi_m, lo_m),
                _ins("add", t, t, u)]
            if op == "smulh":
                code += [_ins("asr", lo_n, n, "#63"), _ins("and", lo_n, lo_n, m), _ins("sub", t, t, lo_n),
                         _ins("asr", lo_n, m, "#63"), _ins("and", lo_n, lo_n, n), _ins("sub", t, t, lo_n)]
            return code + [_ins("mov", dst, t)] + frame.leave()
        if op in {"msub", "mneg"}:
            frame = self.spill(a, 1)
            tmp = frame.regs[0] if _width(dst) == 64 else _w(frame.regs[0])
            accum = a[3] if op == "msub" else ("xzr" if _width(dst) == 64 else "wzr")
            return frame.enter() + [_ins("mul", tmp, n, m), _ins("sub", dst, accum, tmp)] + frame.leave()
        frame = self.spill(a, 2)
        left, right = frame.regs
        extend = "sbfx" if op.startswith("s") else "ubfx"
        code = frame.enter() + [_ins(extend, left, _x(n), "#0", "#32"), _ins(extend, right, _x(m), "#0", "#32")]
        accum = a[3] if len(a) == 4 else "xzr"
        if "sub" in op or "neg" in op:
            code += [_ins("mul", left, left, right), _ins("sub", dst, accum, left)]
        else:
            code += [_ins("madd", dst, left, right, accum)]
        return code + frame.leave()

    def extract(self, op: str, a: list[str]) -> list[str]:
        dst, n = a[:2]
        m, shift = (n, _num(a[2])) if op == "ror" else (a[2], _num(a[3]))
        width = _width(dst)
        if not 0 <= shift < width:
            raise ValueError("extract shift outside register width")
        if shift == 0:
            return [_ins("mov", dst, m)]
        frame = self.spill(a, 1)
        tmp = frame.regs[0] if width == 64 else _w(frame.regs[0])
        return frame.enter() + [_ins("lsr", tmp, m, f"#{shift}"), _ins("orr", dst, tmp, n, f"lsl #{width - shift}")] + frame.leave()

    def extend_arithmetic(self, op: str, a: list[str]) -> list[str]:
        compare = op in {"cmp", "cmn"}
        dst, n, m = (("wzr" if _width(a[0]) == 32 else "xzr"), a[0], a[1]) if compare else tuple(a[:3])
        width = _width(dst)
        mod = a[2:] if compare else a[3:]
        modifier = mod[0].split() if mod else ["lsl", "#0"]
        kind, shift = modifier[0], _num(modifier[1]) if len(modifier) > 1 else 0
        if not 0 <= shift <= 4:
            raise ValueError("extended-register arithmetic shift must be in 0..4")
        if kind not in _EXTENSIONS and kind != "lsl":
            raise ValueError(f"unsupported extended arithmetic modifier {kind}")
        frame = self.spill(a, 4 if _x(dst) == "sp" else 2)
        r = [reg if width == 64 else _w(reg) for reg in frame.regs]
        right, left = r[:2]
        code = frame.enter()
        if kind == "lsl" or _EXTENSIONS[kind] >= width:
            code.append(_ins("mov", right, m))
        else:
            source = _x(m) if width == 64 else _w(_x(m))
            code.append(_ins("sbfx" if kind.startswith("s") else "ubfx", right, source, "#0", f"#{_EXTENSIONS[kind]}"))
        if shift:
            code.append(_ins("lsl", right, right, f"#{shift}"))
        if _x(n) == "sp":
            code += _add_const(left, n, frame.size)
            n = left
        operation = {"cmp": "subs", "cmn": "adds"}.get(op, op)
        output = r[2] if _x(dst) == "sp" else dst
        code.append(_ins(operation, output, n, right))
        return code + (frame.leave_to_sp(output, frame.regs[3]) if _x(dst) == "sp" else frame.leave())

    def conditional_compare(self, op: str, a: list[str]) -> list[str]:
        n, m, flags, cond = a
        if cond not in _CONDS:
            raise ValueError(f"unknown condition {cond}")
        literal = _num(flags)
        if literal not in {0, 2, 3, 4, 6, 7, 8, 9, 10}:
            raise ValueError(f"NZCV literal #{literal} cannot be synthesized by modeled scalar arithmetic")
        frame = self.spill(a, 1)
        tmp = _w(frame.regs[0])
        true, done = self.label(), self.label()
        synth = {
            0: [_ins("mov", tmp, "#1"), _ins("adds", "wzr", tmp, "wzr")],
            2: [_ins("mov", tmp, "#1"), _ins("subs", "wzr", tmp, "wzr")],
            3: [_ins("mov", tmp, "#0x80000000"), _ins("subs", "wzr", tmp, "#1")],
            4: [_ins("adds", "wzr", "wzr", "wzr")],
            6: [_ins("subs", "wzr", "wzr", "wzr")],
            7: [_ins("mov", tmp, "#0x80000000"), _ins("adds", "wzr", tmp, tmp)],
            8: [_ins("mov", tmp, "#-1"), _ins("adds", "wzr", tmp, "wzr")],
            9: [_ins("mov", tmp, "#0x40000000"), _ins("adds", "wzr", tmp, tmp)],
            10: [_ins("mov", tmp, "#-1"), _ins("subs", "wzr", tmp, "wzr")],
        }
        compare = []
        if n.endswith("zr") and m.startswith("#"):
            n = frame.regs[0] if _width(n) == 64 else tmp
            compare.append(_ins("mov", n, "#0"))
        compare.append(_ins("cmp" if op == "ccmp" else "cmn", n, m))
        return (frame.enter() + [_ins("b." + cond, true)] + synth[literal]
                + [_ins("b", done), true + ":"] + compare + [done + ":"] + frame.leave())

    def unsigned_divide(self, a: list[str]) -> list[str]:
        dst, numerator, denominator = a
        width = _width(dst)
        frame = self.spill(a, 8)
        n, d, rem, quotient, diff, borrow, high, count = [r if width == 64 else _w(r) for r in frame.regs]
        loop, subtract, next_bit, done = (self.label() for _ in range(4))
        code = frame.enter() + [_ins("mov", n, numerator), _ins("mov", d, denominator),
            _ins("mov", quotient, "#0"), _ins("cbz", d, done), _ins("mov", rem, "#0"), _ins("mov", count, f"#{width}"), loop + ":",
            _ins("lsr", high, rem, f"#{width - 1}"), _ins("lsl", rem, rem, "#1"),
            _ins("orr", rem, rem, n, f"lsr #{width - 1}"), _ins("lsl", n, n, "#1"),
            _ins("lsl", quotient, quotient, "#1"), _ins("sub", diff, rem, d),
            _ins("cbnz", high, subtract),
            # Borrow of rem-d: (~rem & d) | (~(rem ^ d) & diff).
            _ins("bic", borrow, d, rem), _ins("eor", high, rem, d),
            _ins("bic", high, diff, high), _ins("orr", borrow, borrow, high),
            _ins("lsr", borrow, borrow, f"#{width - 1}"), _ins("cbnz", borrow, next_bit), subtract + ":",
            _ins("mov", rem, diff), _ins("orr", quotient, quotient, "#1"), next_bit + ":",
            _ins("sub", count, count, "#1"), _ins("cbnz", count, loop), done + ":", _ins("mov", dst, quotient)]
        return code + frame.leave()

    def address(self, dst: str, temp: str, parts: list[str], frame: _Spill) -> list[str]:
        base = parts[0]
        offset = parts[1] if len(parts) > 1 else "#0"
        if _GPR.fullmatch(offset):
            modifier = parts[2].split() if len(parts) > 2 else ["lsl", "#0"]
            kind, amount = modifier[0], _num(modifier[1]) if len(modifier) > 1 else 0
            if kind == "lsl" or kind in {"uxtx", "sxtx"}:
                code = [_ins("mov", dst, _x(offset))]
            elif kind in {"uxtw", "sxtw"}:
                code = [_ins("ubfx" if kind == "uxtw" else "sbfx", dst, _x(offset), "#0", "#32")]
            else:
                raise ValueError(f"unsupported memory extension {kind}")
            if not 0 <= amount <= 4:
                raise ValueError("memory register shift outside 0..4")
            if amount:
                code.append(_ins("lsl", dst, dst, f"#{amount}"))
            if base == "sp":
                code += _add_const(temp, "sp", frame.size)
                base = temp
            return code + [_ins("add", dst, base, dst)]
        code = _add_const(dst, base, frame.size if base == "sp" else 0)
        if ":lo12:" in offset:
            return code + [_ins("add", dst, dst, offset)]
        return code + _add_const(dst, dst, _num(offset))

    def memory(self, op: str, a: list[str]) -> list[str] | None:
        pair = op in {"ldp", "stp", "ldpsw"}
        ri = 2 if pair else 1
        if len(a) <= ri or not a[ri].startswith("["):
            raise ValueError("literal or unrecognized memory addressing is not lowered")
        regs = a[:ri]
        pre = a[ri].endswith("!")
        post = len(a) > ri + 1
        parts = [p.strip() for p in a[ri].strip("[]!").split(",")]
        base = parts[0]
        gpr = bool(_GPR.fullmatch(regs[0]))
        zero = any(r.endswith("zr") for r in regs)
        unscaled = op.startswith(("ldur", "stur"))
        canonical = op.replace("ldur", "ldr").replace("stur", "str")
        special = canonical in {"ldrh", "strh", "ldrsb", "ldrsh", "ldrsw"}
        indexed = len(parts) > 1 and bool(_GPR.fullmatch(parts[1]))
        # A negative or unaligned LDR/STR immediate may silently assemble to
        # scalar LDUR/STUR even when that mnemonic was not written explicitly.
        size = (4 if regs[0].startswith("w") else 8) if gpr else {"b": 1, "h": 2, "s": 4, "d": 8, "q": 16}[regs[0][0]]
        if canonical.endswith("b"):
            size = 1
        elif canonical.endswith("h"):
            size = 2
        elif canonical in {"ldrsw", "ldpsw"}:
            size = 4
        bad_immediate = False
        if len(parts) > 1 and parts[1].startswith("#") and not (pre or post or pair):
            offset = _num(parts[1])
            bad_immediate = offset < 0 or offset % size != 0 or offset // size > 4095
        if not (zero or special or indexed or (gpr and unscaled) or (gpr and bad_immediate) or (pre and not pair)):
            return None
        if (pre or post) and any(_x(r) == base and base != "sp" for r in regs):
            raise ValueError("constrained-unpredictable memory writeback aliases a data register")
        if pair and op.startswith("ld") and regs[0] == regs[1]:
            raise ValueError("constrained-unpredictable identical pair load destinations")
        # Fast pre-index normalization needs no scratch and preserves the
        # source because writeback/data-register aliasing was rejected above.
        if pre and not (zero or special or indexed or unscaled):
            delta = _num(parts[1])
            code = _add_const(base, base, delta)
            if base == "sp":
                code += self.cfi.adjust(-delta)
            code += [_ins(op, *regs, f"[{base}]")]
            if base == "sp":
                code += self.cfi.adjust(delta)
            return code
        delta = _num(a[ri + 1]) if post else (_num(parts[1]) if pre else 0)
        addressed = [base] if post else parts
        reserve = 0
        if base == "sp" and len(addressed) > 1 and addressed[1].startswith("#"):
            reserve = max(0, -_num(addressed[1]))
        halfword = canonical in {"ldrh", "ldrsh", "strh"}
        count = 3 if halfword else (2 if zero or special or (indexed and base == "sp") else 1)
        frame = self.spill(a, count, reserve)
        addr = frame.regs[0]
        value = frame.regs[1] if count > 1 else addr
        extra = frame.regs[2] if count > 2 else value
        code = frame.enter() + self.address(addr, value, addressed, frame)
        load = op.startswith("ld")
        if pair:
            for i, reg in enumerate(regs):
                target = (value if _width(reg) == 64 else _w(value)) if reg.endswith("zr") else reg
                if not load and reg.endswith("zr"):
                    code.append(_ins("mov", target, "#0"))
                if op == "ldpsw":
                    code += [_ins("ldr", _w(target), f"[{addr}, #{i * size}]"),
                             _ins("sxtw", target, _w(target))]
                else:
                    code.append(_ins("ldr" if load else "str", target, f"[{addr}, #{i * size}]"))
        elif canonical in {"ldrh", "ldrsh"}:
            target = _w(value)
            code += [_ins("ldrb", target, f"[{addr}]"), _ins("ldrb", _w(extra), f"[{addr}, #1]"),
                     _ins("orr", target, target, _w(extra), "lsl #8")]
            code.append(_ins("sxth", regs[0], target) if canonical == "ldrsh" else _ins("mov", regs[0], target))
        elif canonical == "strh":
            source = regs[0]
            if source.endswith("zr"):
                code.append(_ins("mov", _w(value), "#0"))
                source = _w(value)
            code += [_ins("lsr", _w(extra), source, "#8"), _ins("strb", source, f"[{addr}]"), _ins("strb", _w(extra), f"[{addr}, #1]")]
        elif canonical in {"ldrsb", "ldrsw"}:
            code += [_ins("ldrb" if canonical == "ldrsb" else "ldr", _w(value), f"[{addr}]"),
                     _ins("sxtb" if canonical == "ldrsb" else "sxtw", regs[0], _w(value))]
        else:
            reg = regs[0]
            if zero:
                reg = value if _width(reg) == 64 else _w(value)
                if not load:
                    code.append(_ins("mov", reg, "#0"))
            code.append(_ins(canonical, reg, f"[{addr}]"))
        code += frame.leave()
        if pre or post:
            code += _add_const(base, base, delta)
        return code

    def instruction(self, op: str, a: list[str]) -> list[str] | None:
        vector = any(re.search(r"\bv\d+\.", arg) for arg in a)
        if vector:
            if op in {"ushll", "ushll2", "sshll", "sshll2", "sli", "sri", "cmeq", "cmhi", "cmhs", "neg", "ushl", "sshl", "xtn", "xtn2", "uzp1", "uzp2", "zip1", "zip2", "mvn", "not", "uaddw", "uaddw2", "addp"} or (op == "ld1" and "]" in a[0]):
                raise ValueError(f"unsupported SIMD form {op}; supported vector instructions are retained")
            return None
        if _MEM.fullmatch(op):
            return self.memory(op, a)
        if op in {"cset", "csetm", "cinc", "cinv", "cneg", "csinc", "csinv", "csneg"}:
            return self.select(op, a)
        if op in {"tbz", "tbnz"}:
            return self.bit_branch(op, a)
        if op in {"clz", "rbit"}:
            return self.bit_count(op, a)
        if op in {"umulh", "smulh", "msub", "mneg", "smull", "umull", "smaddl", "umaddl", "smsubl", "umsubl", "smnegl", "umnegl"}:
            return self.multiply(op, a)
        if op == "extr" or (op == "ror" and a[-1].startswith("#")):
            return self.extract(op, a)
        if op in {"add", "adds", "sub", "subs", "cmp", "cmn"}:
            rhs = a[1] if op in {"cmp", "cmn"} else a[2]
            if any(re.match(r"[su]xt[bwhx]", arg) for arg in a) or (_GPR.fullmatch(rhs) and any(_x(arg) == "sp" for arg in a[:2])):
                return self.extend_arithmetic(op, a)
        if op in {"ccmp", "ccmn"}:
            return self.conditional_compare(op, a)
        if op == "udiv":
            return self.unsigned_divide(a)
        if op in {"br", "blr", "sdiv", "cls", "mrs", "msr", "svc", "hvc", "smc"}:
            raise ValueError(f"unsupported normal instruction {op}")
        return None


def lower(text: str) -> str:
    """Lower recognized unsupported forms, preserving all untouched lines.

    ValueError includes the input line and instruction when a recognized form
    cannot be lowered safely.  This is not an exhaustive machine-code decoder;
    final artifact checking is required even when this function succeeds.
    """
    ctx = _Lower(text)
    output = []
    for number, line in enumerate(text.splitlines(keepends=True), 1):
        stripped = line.strip()
        if not stripped or stripped.startswith(("//", "#")):
            output.append(line)
            continue
        if stripped.startswith("."):
            try:
                ctx.cfi.consume(stripped.split("//", 1)[0])
            except (ValueError, IndexError) as exc:
                raise ValueError(f"ARM lowering line {number}: {stripped}: {exc}") from exc
            output.append(line)
            continue
        if stripped.endswith(":"):
            output.append(line)
            continue
        code, _, comment = stripped.partition("//")
        parts = code.strip().split(None, 1)
        if not parts:
            output.append(line)
            continue
        op = parts[0].lower()
        args = _operands(parts[1]) if len(parts) == 2 else []
        try:
            replacement = ctx.instruction(op, args)
        except (ValueError, IndexError, KeyError) as exc:
            raise ValueError(f"ARM lowering line {number}: {code.strip()}: {exc}") from exc
        if replacement is None:
            output.append(line)
        else:
            if comment:
                replacement.insert(0, "\t//" + comment)
            output.append("\n".join(replacement) + ("\n" if line.endswith("\n") else ""))
    return "".join(output)
