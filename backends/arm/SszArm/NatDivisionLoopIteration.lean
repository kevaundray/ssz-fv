import SszArm.NatDivisionLoopStep

namespace SszArm.NatDivision

open Delimited (Span Protected MemoryFrame)

set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

def loopCallee (s : ArmState) (base : BitVec 64) : ArmState :=
  callResult .limb (loopPrepared s base) base

def loopIteration (s : ArmState) (base : BitVec 64) : ArmState :=
  loopFinished (loopCallee s base) base

def loopIterationFuel (s : ArmState) (base : BitVec 64) : Nat :=
  10 + callFuel .limb (loopPrepared s base) base + 12

def loopRoundWrites (s : ArmState) : List Span :=
  [((r (.GPR 31#5) s).toNat - 16, 16), ((loopAddress s).toNat, 8)]

@[simp] theorem loopPrepared_program (s : ArmState) (base : BitVec 64) :
    (loopPrepared s base).program = s.program := by
  simp [loopPrepared, loopSpill, state_simp_rules]

@[simp] theorem loopPrepared_error (s : ArmState) (base : BitVec 64) :
    read_err (loopPrepared s base) = read_err s := by
  simp [loopPrepared, loopSpill, state_simp_rules]

@[simp] theorem loopCallee_program (s : ArmState) (base : BitVec 64) :
    (loopCallee s base).program = s.program := by simp [loopCallee]

@[simp] theorem loopCallee_error (s : ArmState) (base : BitVec 64) :
    read_err (loopCallee s base) = read_err s := by simp [loopCallee]

theorem loopCallee_gpr (s : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (lo : 9 ≤ reg.toNat) (hi : reg.toNat ≤ 29) (h21 : reg ≠ 21#5) :
    r (.GPR reg) (loopCallee s base) = r (.GPR reg) s := by
  have h0 : reg ≠ 0#5 := by bv_omega
  have h2 : reg ≠ 2#5 := by bv_omega
  have h3 : reg ≠ 3#5 := by bv_omega
  rw [loopCallee, call_gpr _ _ _ reg lo hi]
  simp [loopPrepared, loopSpill, state_simp_rules, h0, h2, h3, h21]

@[simp] theorem loopCallee_sp (s : ArmState) (base : BitVec 64) :
    r (.GPR 31#5) (loopCallee s base) = r (.GPR 31#5) s := by
  simp [loopCallee, loopPrepared, loopSpill, state_simp_rules]

@[simp] theorem loopCallee_limb (s : ArmState) (base : BitVec 64) :
    r (.GPR 21#5) (loopCallee s base) = read_mem_bytes 8 (loopAddress s) s := by
  rw [loopCallee, call_gpr _ _ _ 21#5 (by decide) (by decide)]
  simp [loopPrepared, state_simp_rules]

theorem loopCallee_memory (s : ArmState) (base : BitVec 64) :
    (loopCallee s base).mem = (loopSpill s).mem := by
  simp [loopCallee, loopPrepared, state_simp_rules]

theorem loopFinished_gpr (s : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (h1 : reg ≠ 1#5) (h8 : reg ≠ 8#5) (h23 : reg ≠ 23#5) :
    r (.GPR reg) (loopFinished s base) = r (.GPR reg) s := by
  simp [loopFinished, loopStored, loopSpill, state_simp_rules, h1, h8, h23]

theorem loopFinished_remainder (s : ArmState) (base : BitVec 64) :
    r (.GPR 1#5) (loopFinished s base) =
      r (.GPR 21#5) s - r (.GPR 0#5) s * r (.GPR 20#5) s := by
  simp [loopFinished, state_simp_rules]

theorem loopFinished_read (s : ArmState) (base : BitVec 64) (n : Nat) (a : BitVec 64) :
    read_mem_bytes n a (loopFinished s base) = read_mem_bytes n a (loopStored s) := by
  simp [loopFinished, state_simp_rules]

theorem loopFinished_memory (s : ArmState) (base : BitVec 64) :
    (loopFinished s base).mem = (loopStored s).mem := by
  simp [loopFinished, state_simp_rules]

theorem loopFinished_error (s : ArmState) (base : BitVec 64) :
    read_err (loopFinished s base) = read_err s := by
  simp [loopFinished, loopStored, loopSpill, state_simp_rules]

theorem loopIteration_run (s : ArmState) (base : BitVec 64) (count i : Nat)
    (hc : JointCodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 524#64)
    (space : LoopSpace (r (.GPR 31#5) s) (r (.GPR 24#5) s) count)
    (hi : i < count) (index : r (.GPR 23#5) s = BitVec.ofNat 64 (8 * i))
    (hd : 0 < (r (.GPR 20#5) s).toNat) :
    run (loopIterationFuel s base) s = loopIteration s base := by
  have load := loop_load_run s base count i hc.1 he ha hp space hi index
  have preparedCode : JointCodeAt (loopPrepared s base) base := by
    simpa only [JointCodeAt, CodeAt, Udivti3.CodeAt, SszArm.CodeAt,
      loopPrepared_program] using hc
  have positive : 0 < Udivti3.divisor (loopPrepared s base) := by
    simpa [Udivti3.divisor, Udivti3.join, loopPrepared, loopSpill, state_simp_rules] using hd
  have call := call_run .limb (loopPrepared s base) base preparedCode (by simpa using he)
    (by simp [CallSite.offset, loopPrepared, state_simp_rules]) positive
  have calleeCode : CodeAt (loopCallee s base) base := by
    simpa only [CodeAt, loopCallee_program] using hc.1
  have calleeAligned : CheckSPAlignment (loopCallee s base) := by
    simpa only [CheckSPAlignment, state_simp_rules, loopCallee_sp] using ha
  have h24 := loopCallee_gpr s base 24#5 (by decide) (by decide) (by decide)
  have h23 := loopCallee_gpr s base 23#5 (by decide) (by decide) (by decide)
  have store := loop_store_run (loopCallee s base) base count i calleeCode
    (by simpa using he) calleeAligned
    (by simpa only [loopCallee, CallSite.offset] using
      (call_return .limb (loopPrepared s base) base positive))
    (by simpa only [loopCallee_sp, h24] using space) hi (by rw [h23]; exact index)
  rw [loopIterationFuel, run_plus, run_plus, load, call]
  exact store

theorem loopIteration_arithmetic (s : ArmState) (base divisor word : BitVec 64)
    (remainder : Nat) (hd : r (.GPR 20#5) s = divisor)
    (hw : read_mem_bytes 8 (loopAddress s) s = word)
    (hr : (r (.GPR 1#5) s).toNat = remainder)
    (bound : remainder < divisor.toNat) :
    r (.GPR 0#5) (loopIteration s base) =
      (SszNative.LimbDivision.step divisor remainder word).1 ∧
    (r (.GPR 1#5) (loopIteration s base)).toNat =
      (SszNative.LimbDivision.step divisor remainder word).2 := by
  have low : r (.GPR 0#5) (loopPrepared s base) = word := by
    simp [loopPrepared, state_simp_rules, hw]
  have high : (r (.GPR 1#5) (loopPrepared s base)).toNat = remainder := by
    simpa [loopPrepared, loopSpill, state_simp_rules] using hr
  have divisorLow : r (.GPR 2#5) (loopPrepared s base) = divisor := by
    simp [loopPrepared, state_simp_rules, hd]
  have divisorHigh : r (.GPR 3#5) (loopPrepared s base) = 0#64 := by
    simp [loopPrepared, state_simp_rules]
  have quotient := call_limb_quotient .limb (loopPrepared s base) base divisor word remainder
    low high divisorLow divisorHigh bound
  have remainderEq := call_limb_remainder .limb (loopPrepared s base) base divisor word remainder
    low high divisorLow divisorHigh bound
  have h20 := loopCallee_gpr s base 20#5 (by decide) (by decide) (by decide)
  constructor
  · change r (.GPR 0#5) (loopFinished (loopCallee s base) base) = _
    rw [loopFinished_gpr _ _ _ (by decide) (by decide) (by decide)]
    exact quotient.1
  · change (r (.GPR 1#5) (loopFinished (loopCallee s base) base)).toNat = _
    rw [loopFinished_remainder, loopCallee_limb, h20, hd, hw]
    exact remainderEq

@[simp] theorem loopIteration_index (s : ArmState) (base : BitVec 64) :
    r (.GPR 23#5) (loopIteration s base) = r (.GPR 23#5) s - 8#64 := by
  simp [loopIteration, loopFinished, state_simp_rules,
    loopCallee_gpr s base 23#5 (by decide) (by decide) (by decide)]

@[simp] theorem loopIteration_pc (s : ArmState) (base : BitVec 64) :
    read_pc (loopIteration s base) =
      if r (.GPR 23#5) s = 0#64 then base + 616#64 else base + 524#64 := by
  simp [loopIteration, loopFinished, state_simp_rules,
    loopCallee_gpr s base 23#5 (by decide) (by decide) (by decide)]

theorem loopIteration_frame (s : ArmState) (base : BitVec 64) (count i : Nat)
    (space : LoopSpace (r (.GPR 31#5) s) (r (.GPR 24#5) s) count)
    (hi : i < count) (index : r (.GPR 23#5) s = BitVec.ofNat 64 (8 * i)) :
    LoopFrame (loopRoundWrites s) s (loopIteration s base) := by
  have h24 := loopCallee_gpr s base 24#5 (by decide) (by decide) (by decide)
  have h23 := loopCallee_gpr s base 23#5 (by decide) (by decide) (by decide)
  have addr : loopAddress (loopCallee s base) = loopAddress s := by
    simp only [loopAddress, h24, h23]
  have physical : (loopAddress s).toNat + 8 ≤ 2^64 := by
    simp only [loopAddress, index, space.address hi]
    have := space.physical; omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [loopIteration, loopFinished, loopStored, loopSpill, state_simp_rules]
  · exact (loopFinished_error (loopCallee s base) base).trans (loopCallee_error s base)
  · intro reg lo h21 h23reg h30
    have h1 : reg ≠ 1#5 := by bv_omega
    have h8 : reg ≠ 8#5 := by bv_omega
    change r (.GPR reg) (loopFinished (loopCallee s base) base) = _
    rw [loopFinished_gpr _ _ reg h1 h8 h23reg]
    by_cases h31 : reg = 31#5
    · subst reg; exact loopCallee_sp s base
    · exact loopCallee_gpr s base reg lo (by have := reg.isLt; bv_omega) h21
  · intro reg
    simp [loopIteration, loopFinished, loopStored, loopSpill, loopCallee,
      loopPrepared, state_simp_rules]
  · intro a outside
    have slot := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [loopRoundWrites])
    have word := outside ((loopAddress s).toNat, 8) (by simp [loopRoundWrites])
    have first := (loopSpill_frame s space.stack) a (by simpa using slot)
    have second := (loopSpill_frame (loopCallee s base) (by simpa using space.stack)) a
      (by simpa using slot)
    have stored := BoolCodec.write_mem_bytes_frame (loopSpill (loopCallee s base))
      (loopAddress (loopCallee s base)) 8 (r (.GPR 0#5) (loopCallee s base)) a
      (by simpa only [addr] using physical) (by simpa only [addr] using word)
    rw [loopIteration, loopFinished_memory]
    exact stored.trans (second.trans ((congrFun (loopCallee_memory s base) a).trans first))

theorem loopIteration_word (s : ArmState) (base : BitVec 64) (count i : Nat)
    (space : LoopSpace (r (.GPR 31#5) s) (r (.GPR 24#5) s) count)
    (hi : i < count) (index : r (.GPR 23#5) s = BitVec.ofNat 64 (8 * i)) :
    read_mem_bytes 8 (loopAddress s) (loopIteration s base) =
      r (.GPR 0#5) (loopIteration s base) := by
  have h24 := loopCallee_gpr s base 24#5 (by decide) (by decide) (by decide)
  have h23 := loopCallee_gpr s base 23#5 (by decide) (by decide) (by decide)
  have addr : loopAddress (loopCallee s base) = loopAddress s := by
    simp only [loopAddress, h24, h23]
  have physical : (loopAddress s).toNat + 8 ≤ 2^64 := by
    simp only [loopAddress, index, space.address hi]
    have := space.physical; omega
  change read_mem_bytes 8 (loopAddress s) (loopFinished (loopCallee s base) base) =
    r (.GPR 0#5) (loopFinished (loopCallee s base) base)
  rw [loopFinished_read, loopFinished_gpr _ _ _ (by decide) (by decide) (by decide)]
  unfold loopStored
  rw [addr]
  exact BoolCodec.read_mem_bytes_write_mem_bytes_same (loopSpill (loopCallee s base)) 8
    (loopAddress s) (r (.GPR 0#5) (loopCallee s base)) physical

end SszArm.NatDivision
