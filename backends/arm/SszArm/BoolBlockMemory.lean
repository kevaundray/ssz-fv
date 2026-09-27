import SszArm.BoolBlocks
import SszArm.BoolResultMemory

namespace SszArm.BoolCodec

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/-- The output is separate from the largest temporary lowering frame. -/
def ScratchSeparated (s : ArmState) : Prop :=
  32 ≤ (r (.GPR 31#5) s).toNat ∧
  (r (.GPR 31#5) s).toNat + 368 ≤ 2^64 ∧
  (r (.GPR 0#5) s).toNat + 80 ≤ 2^64 ∧
  ((r (.GPR 0#5) s).toNat + 80 ≤ (r (.GPR 31#5) s).toNat - 32 ∨
    (r (.GPR 31#5) s).toNat ≤ (r (.GPR 0#5) s).toNat)

def zeroPairState (s : ArmState) (offset : Nat) : ArmState :=
  let out := r (.GPR 0#5) s + BitVec.ofNat 64 offset
  let sp := r (.GPR 31#5) s
  w .PC (read_pc s + 48#64)
    (write_mem_bytes 8 (out + 8#64) 0#64
      (write_mem_bytes 8 out 0#64
        (write_mem_bytes 8 (sp - 16#64 + 8#64) (r (.GPR 10#5) s)
          (write_mem_bytes 8 (sp - 16#64) (r (.GPR 9#5) s) s))))

theorem zeroPair_effect (s : ArmState) (op : StoreOp) (offset : Nat)
    (ho : (op, offset) ∈ [(StoreOp.addX9X9_16, 16), (.addX9X9_40, 40), (.addX9X9_56, 56)])
    (hs : ScratchSeparated s) :
    storeBlock (zeroPair op) s = zeroPairState s offset := by
  rcases hs with ⟨hlo, hhi, hout, hsep⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at ho
  rcases ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    apply state_eq_iff_components_eq.mpr
    refine ⟨?_, ?_, ?_⟩
    · intro field
      cases field <;>
        simp (config := {decide := true, instances := true})
          [storeBlock, zeroPair, StoreOp.effect, zeroPairState, state_simp_rules,
           BitVec.add_assoc] <;> try (simp only [r, w]; rfl)
      rename_i reg
      by_cases h9 : reg = 9#5
      · subst reg
        repeat' first
          | rw [read_mem_bytes_of_w]
          | rw [read_mem_bytes_write_mem_bytes_same _ 8 _ _ (by bv_omega)]
          | rw [read_mem_bytes_write_mem_bytes_disjoint _ 8 8 _ _ _
              (by bv_omega) (by bv_omega) (by bv_omega)]
        simp (config := {decide := true, instances := true}) [state_simp_rules]
      · by_cases h10 : reg = 10#5
        · subst reg
          repeat' first
            | rw [read_mem_bytes_of_w]
            | rw [read_mem_bytes_write_mem_bytes_same _ 8 _ _ (by bv_omega)]
            | rw [read_mem_bytes_write_mem_bytes_disjoint _ 8 8 _ _ _
                (by bv_omega) (by bv_omega) (by bv_omega)]
          simp (config := {decide := true, instances := true}) [state_simp_rules]
        · by_cases h31 : reg = 31#5
          · subst reg
            simp only [state_simp_rules]
            bv_omega
          · simp (disch := first | assumption | simp_all) [state_simp_rules]
    · simp [storeBlock, zeroPair, StoreOp.effect, zeroPairState, state_simp_rules]
    · apply Memory.mem_eq_iff_read_mem_bytes_eq.mp
      simp (config := {decide := true, instances := true})
        [storeBlock, zeroPair, StoreOp.effect, zeroPairState, state_simp_rules, BitVec.add_assoc]
      simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]

theorem zeroPairState_separated (s : ArmState) (offset : Nat) (hs : ScratchSeparated s) :
    ScratchSeparated (zeroPairState s offset) := by
  simpa (config := {decide := true}) [ScratchSeparated, zeroPairState, state_simp_rules] using hs

/-- Neither padding beyond the result nor bytes outside lowering scratch change. -/
theorem zeroPairState_frame (s : ArmState) (offset : Nat) (a : BitVec 64)
    (hs : ScratchSeparated s) (hoff : offset + 16 ≤ 76)
    (hout : a.toNat < (r (.GPR 0#5) s).toNat ∨ (r (.GPR 0#5) s).toNat + 76 ≤ a.toNat)
    (hstack : a.toNat < (r (.GPR 31#5) s).toNat - 32 ∨ (r (.GPR 31#5) s).toNat ≤ a.toNat) :
    (zeroPairState s offset).mem a = s.mem a := by
  rcases hs with ⟨hlo, hhi, hospace, hsep⟩
  simp only [zeroPairState, ArmState.mem_w_eq_mem]
  repeat' rw [write_mem_bytes_frame _ _ 8 _ a (by bv_omega) (by bv_omega)]

end SszArm.BoolCodec
