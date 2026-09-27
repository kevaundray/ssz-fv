import SszArm.NatDivisionScanLoad

namespace SszArm.NatDivision

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def copyStoreOps : List Op := [.p408, .p412, .p416, .p420, .p424, .p428, .p432, .p436]

def copyStoreResult (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 440#64)
    (write_mem_bytes 8 (r (.GPR 24#5) s + (r (.GPR 9#5) s <<< 3))
      (r (.GPR 10#5) s) (NatCompare.saved s 11#5))

private theorem copy_read_spill_w (s : ArmState) (f : StateField) (v : state_value f)
    (n m k : Nat) (addr first second : BitVec 64)
    (a : BitVec (m * 8)) (b : BitVec (k * 8)) :
    read_mem_bytes n addr (write_mem_bytes k second b (write_mem_bytes m first a (w f v s))) =
      read_mem_bytes n addr (write_mem_bytes k second b (write_mem_bytes m first a s)) :=
  (Memory.mem_eq_iff_read_mem_bytes_eq.mp
    (mem_write_mem_bytes_of_mem_eq (NatCompare.spill_mem_w s f v m first a) k second b)) n addr

/-- Eight lowered instructions perform precisely one quotient scratch store.
The store interval is disjoint from the saved X11 slot, so restoration is exact. -/
theorem copy_store_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 408#64)
    (hsp : 16 ≤ (r (.GPR 31#5) s).toNat)
    (hspace : (r (.GPR 24#5) s + (r (.GPR 9#5) s <<< 3)).toNat + 8 ≤ 2^64)
    (hsep : (r (.GPR 24#5) s + (r (.GPR 9#5) s <<< 3)).toNat + 8 ≤
        (r (.GPR 31#5) s).toNat - 16 ∨
      (r (.GPR 31#5) s).toNat ≤
        (r (.GPR 24#5) s + (r (.GPR 9#5) s <<< 3)).toNat) :
    run 8 s = copyStoreResult s base := by
  have hrestore : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64)
      (write_mem_bytes 8 (r (.GPR 24#5) s + (r (.GPR 9#5) s <<< 3))
        (r (.GPR 10#5) s) (NatCompare.saved s 11#5)) = r (.GPR 11#5) s := by
    rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 8 _ _ _
      (by bv_omega) hspace (by bv_omega)]
    exact BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ (by bv_omega)
  have hpc : r .PC s = base + 408#64 := hp
  have hf : Follows base copyStoreOps s := by
    simp [copyStoreOps, Follows, Op.row, Op.effect, put, next,
      state_simp_rules, hpc, BitVec.add_assoc]
  rw [show 8 = copyStoreOps.length by rfl, block_run base copyStoreOps s hc he ha hf]
  simp only [NatCompare.saved] at hrestore
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro f
    cases f with
    | GPR reg =>
      by_cases h11 : reg = 11#5 <;> by_cases h31 : reg = 31#5 <;>
        (try subst reg) <;>
        simp_all (config := {decide := true, instances := true})
          [copyStoreResult, copyStoreOps, block, Op.effect, put, next,
            NatCompare.saved, state_simp_rules, NatCompare.read_spill_w,
            copy_read_spill_w, BitVec.sub_add_cancel, BitVec.add_assoc]
    | PC =>
      simp [copyStoreResult, copyStoreOps, block, Op.effect, put, next,
        NatCompare.saved, state_simp_rules, hpc, BitVec.add_assoc]
    | SFP reg =>
      simp [copyStoreResult, copyStoreOps, block, Op.effect, put, next,
        NatCompare.saved, state_simp_rules]
    | FLAG flag =>
      simp [copyStoreResult, copyStoreOps, block, Op.effect, put, next,
        NatCompare.saved, state_simp_rules]
    | ERR =>
      simp [copyStoreResult, copyStoreOps, block, Op.effect, put, next,
        NatCompare.saved, state_simp_rules]
  · simp [copyStoreResult, copyStoreOps, block, Op.effect, put, next,
      NatCompare.saved, state_simp_rules]
  · intro n addr
    simp [copyStoreResult, copyStoreOps, block, Op.effect, put, next,
      NatCompare.saved, state_simp_rules, NatCompare.read_spill_w, copy_read_spill_w]

end SszArm.NatDivision
