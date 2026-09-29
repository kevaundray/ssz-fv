import SszArm.NatMulWordHighRun
import SszWordAutomation

namespace SszArm.NatMulWord

/-- The six stack slots use modular machine addresses; their physical
read-after-write safety is supplied separately by `NatMulSpill.six_reads`. -/
theorem high_spill_offset (sp : BitVec 64) (index : Fin 6) :
    sp - 48#64 + BitVec.ofNat 64 (8 * index.val) =
      sp - BitVec.ofNat 64 (48 - 8 * index.val) := by
  have bound := index.isLt
  arm_word_nf
  apply BitVec.eq_of_toNat_eq
  ssz_word

theorem high_spilled_read (site : HighSite) (s : ArmState) (index : Fin 6)
    (stack : 48 ≤ (r (.GPR 31#5) s).toNat) :
    read_mem_bytes 8 (r (.GPR 31#5) s - 48#64 + BitVec.ofNat 64 (8 * index.val))
      (site.spilled s) = r (.GPR site.saved[index.val]!) s := by
  rw [high_spill_offset]
  have observed := NatMulSpill.six_reads s (r (.GPR 31#5) s)
    (r (.GPR site.saved[0]!) s) (r (.GPR site.saved[1]!) s)
    (r (.GPR site.saved[2]!) s) (r (.GPR site.saved[3]!) s)
    (r (.GPR site.saved[4]!) s) (r (.GPR site.saved[5]!) s) stack
  rcases index with ⟨index, bound⟩
  have indices : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 := by
    omega
  rcases indices with rfl | rfl | rfl | rfl | rfl | rfl
  · exact observed.1
  · exact observed.2.1
  · exact observed.2.2.1
  · exact observed.2.2.2.1
  · exact observed.2.2.2.2.1
  · exact observed.2.2.2.2.2

end SszArm.NatMulWord
