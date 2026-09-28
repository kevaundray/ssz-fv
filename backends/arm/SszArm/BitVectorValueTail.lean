import SszArm.BitVectorValueGuard
import SszArm.BitVectorValueObservation

namespace SszArm.BitVector.ValueTail

open Delimited (MemoryFrame Protected)
open UintCodec (widthLoad)

def beforeStore (s : ArmState) (base : BitVec 64) : ArmState :=
  guardResult (loadResult s base) base

def result (s : ArmState) (base : BitVec 64) : ArmState :=
  storeResult (beforeStore s base) base

def fuel (s : ArmState) (base : BitVec 64) : Nat :=
  15 + ((roundFuel (loadResult s base) + (2 + (2 + 3))) + 14)

@[simp] theorem before_sp (s : ArmState) (base : BitVec 64) :
    r (.GPR 31#5) (beforeStore s base) = r (.GPR 31#5) s := by simp [beforeStore]

theorem before_register (s : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (r8 : reg ≠ 8#5) (r9 : reg ≠ 9#5) (r10 : reg ≠ 10#5)
    (r11 : reg ≠ 11#5) (r12 : reg ≠ 12#5) (rsp : reg ≠ 31#5) :
    r (.GPR reg) (beforeStore s base) = r (.GPR reg) s := by
  rw [beforeStore, guard_register _ _ _ r10 r11 r12,
    loaded_register _ _ _ r8 r9 r10 r11 rsp]

@[simp] theorem before_out (s : ArmState) (base : BitVec 64) :
    r (.GPR 23#5) (beforeStore s base) = r (.GPR 23#5) s :=
  before_register _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

@[simp] theorem before_source (s : ArmState) (base : BitVec 64) :
    r (.GPR 24#5) (beforeStore s base) = r (.GPR 24#5) s :=
  before_register _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

@[simp] theorem before_size (s : ArmState) (base : BitVec 64) :
    r (.GPR 20#5) (beforeStore s base) = r (.GPR 20#5) s :=
  before_register _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem before_space (s : ArmState) (base : BitVec 64) (space : Space s) :
    Space (beforeStore s base) := by
  obtain ⟨stackLow, stackHigh, output, separate⟩ := space
  constructor
  · simpa only [before_sp] using stackLow
  · simpa only [before_sp] using stackHigh
  · simpa only [before_out] using output
  · simpa only [before_sp, before_out] using separate

theorem before_frame (s : ArmState) (base : BitVec 64) (space : Space s) :
    MemoryFrame (writes s) s (beforeStore s base) := by
  intro address outside
  have spill := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [writes])
  change (guardResult (loadResult s base) base).mem address = _
  rw [guard_mem]
  apply loaded_frame s base space.stackLow address
  intro span member
  simp only [List.mem_singleton] at member
  subst span
  exact spill

@[simp] theorem before_writes (s : ArmState) (base : BitVec 64) :
    writes (beforeStore s base) = writes s := by simp only [writes, before_out, before_sp]

/-- The instruction trace reaches the existing common epilogue, including every
lowering spill and both data-dependent rounding alternatives. -/
theorem executes (s : ArmState) (base : BitVec 64) (count : BitVec 128)
    (space : Space s) (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 6592#64)
    (observed : SszNative.NatNarrow.U128ResultAt (widthLoad s)
      ((r (.GPR 31#5) s).toNat + 144) (some count))
    (scope : (r (.GPR 20#5) s).toNat = (count.toNat + 7) / 8) :
    run (fuel s base) s = result s base := by
  obtain ⟨tag, low, high⟩ := u128_observed s count observed
  have first := load_run s base code error aligned pc tag
  have loadedLow := (loaded_low s base space.stackLow space.stackHigh).trans low
  have loadedHigh := (loaded_high s base space.stackLow space.stackHigh).trans high
  have quotient : r (.GPR 10#5) (loadResult s base) =
      quotientWord (countLow count) (countHigh count) := by
    rw [loaded_quotient s base space.stackLow space.stackHigh, low, high]
  have size : r (.GPR 20#5) (loadResult s base) = r (.GPR 20#5) s :=
    loaded_register _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have narrowed : (r (.GPR 20#5) (loadResult s base)).toNat = (count.toNat + 7) / 8 := by
    simpa only [size] using scope
  have middle := guard_run (loadResult s base) base count
    (by simpa only [CodeAt, loaded_program] using code)
    (by simpa only [loaded_error] using error) (loaded_pc s base)
    loadedLow loadedHigh quotient narrowed
  have last := store_run (beforeStore s base) base
    (by simpa only [beforeStore, CodeAt, guard_program, loaded_program] using code)
    (by simpa only [beforeStore, guard_error, loaded_error] using error)
    (by simpa only [CheckSPAlignment, state_simp_rules, before_sp] using aligned)
    (guard_pc (loadResult s base) base count loadedLow loadedHigh quotient narrowed)
  change run _ (loadResult s base) = beforeStore s base at middle
  rw [fuel, run_plus, first, run_plus, middle, last]
  rfl

@[simp] theorem final_pc (s : ArmState) (base : BitVec 64) :
    read_pc (result s base) = base + 4732#64 := by simp [result]

@[simp] theorem final_error (s : ArmState) (base : BitVec 64) :
    read_err (result s base) = read_err s := by simp [result, beforeStore]

@[simp] theorem final_program (s : ArmState) (base : BitVec 64) :
    (result s base).program = s.program := by simp [result, beforeStore]

@[simp] theorem final_sp (s : ArmState) (base : BitVec 64) :
    r (.GPR 31#5) (result s base) = r (.GPR 31#5) s := by simp [result]

theorem final_register (s : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (low : 19 ≤ reg.toNat) (high : reg.toNat ≤ 30) :
    r (.GPR reg) (result s base) = r (.GPR reg) s := by
  have r8 : reg ≠ 8#5 := by bv_omega
  have r9 : reg ≠ 9#5 := by bv_omega
  have r10 : reg ≠ 10#5 := by bv_omega
  have r11 : reg ≠ 11#5 := by bv_omega
  have r12 : reg ≠ 12#5 := by bv_omega
  have rsp : reg ≠ 31#5 := by bv_omega
  rw [result, stored_register _ _ _ r9 r10 rsp,
    before_register _ _ _ r8 r9 r10 r11 r12 rsp]

@[simp] theorem final_vector (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.SFP reg) (result s base) = r (.SFP reg) s := by simp [result, beforeStore]

theorem final_frame (s : ArmState) (base : BitVec 64) (space : Space s) :
    MemoryFrame (writes s) s (result s base) := by
  apply (before_frame s base space).trans
  simpa only [result, before_writes] using
    stored_frame (beforeStore s base) base (before_space s base space)

theorem final_result (s : ArmState) (base : BitVec 64) (space : Space s)
    (count : BitVec 128) (data : Ssz.Bytes)
    (observed : SszNative.NatNarrow.U128ResultAt (widthLoad s)
      ((r (.GPR 31#5) s).toNat + 144) (some count))
    (size : (r (.GPR 20#5) s).toNat = data.size)
    (scope : (r (.GPR 20#5) s).toNat = (count.toNat + 7) / 8)
    (dataAt : SszNative.ByteView.BytesAt (widthLoad s) (r (.GPR 24#5) s).toNat data)
    (dataBound : (r (.GPR 24#5) s).toNat + data.size ≤ 2^64)
    (dataOwned : Protected (writes s) (r (.GPR 24#5) s).toNat data.size) :
    SszNative.BitVector.ResultAt (widthLoad (result s base))
      (r (.GPR 23#5) s).toNat (r (.GPR 24#5) s).toNat data (.ok count) := by
  obtain ⟨_, low, high⟩ := u128_observed s count observed
  have lower : r (.GPR 9#5) (beforeStore s base) = countLow count := by
    rw [beforeStore, guard_register _ _ _ (by decide) (by decide) (by decide)]
    exact (loaded_low s base space.stackLow space.stackHigh).trans low
  have upper : r (.GPR 8#5) (beforeStore s base) = countHigh count := by
    rw [beforeStore, guard_register _ _ _ (by decide) (by decide) (by decide)]
    exact (loaded_high s base space.stackLow space.stackHigh).trans high
  have bytes : SszNative.ByteView.BytesAt (widthLoad (beforeStore s base))
      (r (.GPR 24#5) (beforeStore s base)).toNat data := by
    rw [before_source]
    intro index within
    rw [(before_frame s base space).load _ 1 (by omega)
      (dataOwned.subspan index 1 (by omega))]
    exact dataAt index within
  have stored := stored_result (beforeStore s base) base (before_space s base space)
    count data lower upper (by simpa only [before_size] using size)
    (size.symm.trans scope) bytes
    (by simpa only [before_source] using dataBound)
    (by simpa only [before_source, before_writes] using dataOwned)
  simpa only [result, before_out, before_source] using stored

/-- Public arithmetic bridge: the numeric native-guard premise is a consequence
of shared Expected and the actual successful exact-helper observation. -/
theorem executes_of_scope (s : ArmState) (base : BitVec 64)
    (length expected : SszNative.NatOperand) (remainder : BitVec 64)
    (space : Space s) (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 6592#64)
    (arithmetic : SszNative.BitVector.Expected length expected remainder)
    (scope : SszNative.NatNarrow.runExact expected (r (.GPR 20#5) s) = true)
    (observed : SszNative.NatNarrow.U128ResultAt (widthLoad s)
      ((r (.GPR 31#5) s).toNat + 144) (SszNative.NatNarrow.toU128 length)) :
    run (fuel s base) s = result s base := by
  have narrowed := SszNative.BitVector.scope_narrows length expected remainder (r (.GPR 20#5) s)
    arithmetic scope
  apply executes s base (BitVec.ofNat 128 length.value) space code error aligned pc
  · simpa only [narrowed.2.1] using observed
  · exact narrowed.2.2

end SszArm.BitVector.ValueTail
