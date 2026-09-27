import SszArm.NatDivisionLoopMemory
import SszArm.NatDivisionArithmetic
import SszArm.NatDivisionExec

namespace SszArm.NatDivision

open Delimited (Span Protected MemoryFrame)
open NatCompare (read_spill_w spill_mem_w)

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def loopLoadOps : List Op :=
  [.p524, .p528, .p532, .p536, .p540, .p544, .p548, .p552, .p556, .p560]

def loopStoreOps : List Op :=
  [.p568, .p572, .p576, .p580, .p584, .p588, .p592, .p596, .p600, .p604, .p608, .p612]

/-- Concrete register and spill state immediately before the actual BL. -/
def loopPrepared (s : ArmState) (base : BitVec 64) : ArmState :=
  let word := read_mem_bytes 8 (loopAddress s) s
  w .PC (base + 564#64)
    (w (.GPR 0#5) word (w (.GPR 3#5) 0#64 (w (.GPR 2#5) (r (.GPR 20#5) s)
      (w (.GPR 21#5) word (loopSpill s)))))

def loopStored (s : ArmState) : ArmState :=
  write_mem_bytes 8 (loopAddress s) (r (.GPR 0#5) s) (loopSpill s)

/-- The final CMN overwrites the subtraction flags; its wrapped zero test is
exactly a test for the original byte index being zero. -/
def loopFinished (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (if r (.GPR 23#5) s = 0#64 then base + 616#64 else base + 524#64)
    (write_pstate (AddWithCarry (r (.GPR 23#5) s - 8#64) 8#64 0#1).2
      (w (.GPR 1#5) (r (.GPR 21#5) s - r (.GPR 0#5) s * r (.GPR 20#5) s)
        (w (.GPR 23#5) (r (.GPR 23#5) s - 8#64)
          (w (.GPR 8#5) (r (.GPR 0#5) s * r (.GPR 20#5) s) (loopStored s)))))

theorem loop_cmn_zero (index : BitVec 64) :
    (AddWithCarry (index - 8#64) 8#64 0#1).2.z = 1#1 ↔ index = 0#64 := by
  change (if (AddWithCarry (index - 8#64) 8#64 0#1).1 = 0#64 then 1#1 else 0#1) = 1#1 ↔ _
  rw [fst_AddWithCarry_eq_add, BitVec.sub_add_cancel]
  by_cases h : index = 0#64 <;> simp [h]

theorem loop_read_two_spills_w (s : ArmState) (f : StateField) (v : state_value f)
    (n k m : Nat) (addr dst₁ dst₂ : BitVec 64)
    (value₁ : BitVec (k * 8)) (value₂ : BitVec (m * 8)) :
    read_mem_bytes n addr (write_mem_bytes k dst₁ value₁
      (write_mem_bytes m dst₂ value₂ (w f v s))) =
    read_mem_bytes n addr (write_mem_bytes k dst₁ value₁
      (write_mem_bytes m dst₂ value₂ s)) :=
  (Memory.mem_eq_iff_read_mem_bytes_eq.mp
    (mem_write_mem_bytes_of_mem_eq (spill_mem_w s f v m dst₂ value₂)
      k dst₁ value₁)) n addr

theorem loop_load_run (s : ArmState) (base : BitVec 64) (count i : Nat)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 524#64)
    (space : LoopSpace (r (.GPR 31#5) s) (r (.GPR 24#5) s) count)
    (hi : i < count) (index : r (.GPR 23#5) s = BitVec.ofNat 64 (8 * i)) :
    run 10 s = loopPrepared s base := by
  have hrestore := loopSpill_read s space.stack
  have hload := loopSpill_word s count i space hi
  rw [← index] at hload
  simp only [loopSpill] at hrestore hload
  have hpc : r .PC s = base + 524#64 := hp
  have follows : Follows base loopLoadOps s := by
    simp [loopLoadOps, Follows, Op.row, Op.effect, put, next, state_simp_rules,
      hpc, BitVec.add_assoc]
  rw [show 10 = loopLoadOps.length from rfl, block_run base _ s hc he ha follows]
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro f
    cases f with
    | GPR reg =>
      by_cases h0 : reg = 0#5 <;> by_cases h2 : reg = 2#5 <;>
        by_cases h3 : reg = 3#5 <;> by_cases h9 : reg = 9#5 <;>
        by_cases h21 : reg = 21#5 <;> by_cases h31 : reg = 31#5 <;>
        (try subst reg) <;>
        simp_all (config := {decide := true, instances := true})
          [loopPrepared, loopSpill, loopAddress, loopLoadOps, block, Op.effect,
            put, next, state_simp_rules, read_spill_w, BitVec.sub_add_cancel, BitVec.add_assoc]
    | PC => simp [loopPrepared, loopLoadOps, block, Op.effect, put, next,
        state_simp_rules, hpc, BitVec.add_assoc]
    | SFP reg => simp [loopPrepared, loopSpill, loopLoadOps, block, Op.effect,
        put, next, state_simp_rules]
    | FLAG flag => simp [loopPrepared, loopSpill, loopLoadOps, block, Op.effect,
        put, next, state_simp_rules]
    | ERR => simp [loopPrepared, loopSpill, loopLoadOps, block, Op.effect,
        put, next, state_simp_rules]
  · simp [loopPrepared, loopSpill, loopLoadOps, block, Op.effect, put, next, state_simp_rules]
  · intro n addr
    simp [loopPrepared, loopSpill, loopLoadOps, block, Op.effect, put, next,
      state_simp_rules, read_spill_w]

theorem loop_store_run (s : ArmState) (base : BitVec 64) (count i : Nat)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 568#64)
    (space : LoopSpace (r (.GPR 31#5) s) (r (.GPR 24#5) s) count)
    (hi : i < count) (index : r (.GPR 23#5) s = BitVec.ofNat 64 (8 * i)) :
    run 12 s = loopFinished s base := by
  have address : (loopAddress s).toNat = (r (.GPR 24#5) s).toNat + 8 * i := by
    simpa only [loopAddress, index] using space.address hi
  have physical : (loopAddress s).toNat + 8 ≤ 2^64 := by
    rw [address]; have := space.physical; omega
  have apart : Protected [((loopAddress s).toNat, 8)]
      (r (.GPR 31#5) s - 16#64).toNat 8 := by
    right; intro span member
    simp only [List.mem_singleton] at member
    subst span
    have := space.apart
    have := space.stack
    simp only [Prod.fst, Prod.snd]
    rw [address]
    bv_omega
  have hrestore : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (loopStored s) =
      r (.GPR 9#5) s := by
    unfold loopStored
    rw [(Delimited.store_frame (loopSpill s) (loopAddress s) 8 _ physical).read _ 8
      (by have := space.stack; bv_omega) apart]
    exact loopSpill_read s space.stack
  simp only [loopStored, loopSpill, loopAddress] at hrestore
  have hpc : r .PC s = base + 568#64 := hp
  have follows : Follows base loopStoreOps s := by
    simp [loopStoreOps, Follows, Op.row, Op.effect, put, next, state_simp_rules,
      hpc, BitVec.add_assoc]
  rw [show 12 = loopStoreOps.length from rfl, block_run base _ s hc he ha follows]
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro f
    cases f with
    | GPR reg =>
      by_cases h1 : reg = 1#5 <;> by_cases h8 : reg = 8#5 <;>
        by_cases h9 : reg = 9#5 <;> by_cases h23 : reg = 23#5 <;>
        by_cases h31 : reg = 31#5 <;> (try subst reg) <;>
        simp_all (config := {decide := true, instances := true})
          [loopFinished, loopStored, loopSpill, loopAddress, loopStoreOps, block, Op.effect,
            put, next, state_simp_rules, read_spill_w, loop_read_two_spills_w,
            BitVec.sub_add_cancel, BitVec.add_assoc]
    | PC =>
      by_cases hz : r (.GPR 23#5) s = 0#64 <;>
        simp [loopFinished, loopStoreOps, block, Op.effect, put, next,
          state_simp_rules, loop_cmn_zero, hz] <;> decide
    | SFP reg => simp [loopFinished, loopStored, loopSpill, loopStoreOps, block, Op.effect,
        put, next, state_simp_rules]
    | FLAG flag => cases flag <;>
        simp [loopFinished, loopStored, loopSpill, loopStoreOps, block, Op.effect,
          put, next, state_simp_rules]
    | ERR => simp [loopFinished, loopStored, loopSpill, loopStoreOps, block, Op.effect,
        put, next, state_simp_rules]
  · simp [loopFinished, loopStored, loopSpill, loopStoreOps, block, Op.effect,
      put, next, state_simp_rules]
  · intro n addr
    simp [loopFinished, loopStored, loopSpill, loopAddress, loopStoreOps, block,
      Op.effect, put, next, state_simp_rules, read_spill_w, loop_read_two_spills_w, hrestore]

end SszArm.NatDivision
