import SszArm.DelimitedImpl
import SszArm.NatCompareProofs

namespace SszArm.Delimited

open UintCodec (widthLoad)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- The actual BL writes its link register and uses the signed linked target. -/
def compareCalled (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + compareOffset) (w (.GPR 30#5) (base + 400#64) s)

theorem compare_call_step (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None)
    (hp : read_pc s = base + 396#64) : stepi s = compareCalled s base := by
  have hf := hc (396, 0x97ffbb50#32) (by decide)
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he hp
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 396#64 := hp
  simp (config := {decide := true, instances := true})
    [exec_inst, compareCalled, compareOffset, state_simp_rules, bitvec_rules,
     minimal_theory, hpc, BitVec.add_assoc]

/-- Complete call/RET composition with the checked arbitrary-Nat comparison.
The compare code image is an instruction-memory premise supplied by the joint
binding; comparison semantics are obtained only by applying compare_correct. -/
theorem compare_call (s : ArmState) (base : BitVec 64) (actual limit : Nat)
    (hc : CodeAt s base)
    (compareCode : NatCompare.CodeAt s (base + compareOffset))
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 396#64)
    (left : SszNative.NatMemory.Pair (widthLoad s)
      (r (.GPR 0#5) s) (r (.GPR 1#5) s) actual)
    (right : SszNative.NatMemory.Pair (widthLoad s)
      (r (.GPR 2#5) s) (r (.GPR 3#5) s) limit)
    (leftOwned : NatCompare.Owned s (r (.GPR 0#5) s) (r (.GPR 1#5) s))
    (rightOwned : NatCompare.Owned s (r (.GPR 2#5) s) (r (.GPR 3#5) s)) :
    ∃ fuel t, run fuel s = t ∧ NatCompare.Frame (compareCalled s base) t ∧
      read_pc t = base + 400#64 ∧ read_err t = .None ∧
      r (.GPR 31#5) t = r (.GPR 31#5) s ∧
      (∀ reg : BitVec 5, 19 ≤ reg.toNat → reg.toNat ≤ 29 →
        r (.GPR reg) t = r (.GPR reg) s) ∧
      (r (.GPR 0#5) t).setWidth 8 = SszNative.NatABI.orderingByte (compare actual limit) ∧
      SszNative.NatMemory.Pair (widthLoad t)
        (r (.GPR 0#5) s) (r (.GPR 1#5) s) actual ∧
      SszNative.NatMemory.Pair (widthLoad t)
        (r (.GPR 2#5) s) (r (.GPR 3#5) s) limit := by
  let q := compareCalled s base
  have cq : NatCompare.CodeAt q (base + compareOffset) := by
    simpa [q, compareCalled, NatCompare.CodeAt, state_simp_rules] using compareCode
  have eq : read_err q = .None := by simpa [q, compareCalled, state_simp_rules] using he
  have aq : CheckSPAlignment q := by simpa [q, compareCalled, state_simp_rules] using ha
  have pq : read_pc q = base + compareOffset + BitVec.ofNat 64 NatCompare.entry := by
    simp [q, compareCalled, NatCompare.entry, state_simp_rules]
  have load : widthLoad q = widthLoad s := by
    funext address width
    simp [widthLoad, q, compareCalled, state_simp_rules]
  have lq : SszNative.NatMemory.Pair (widthLoad q)
      (r (.GPR 0#5) q) (r (.GPR 1#5) q) actual := by
    rw [load]
    simpa [q, compareCalled, state_simp_rules] using left
  have rq : SszNative.NatMemory.Pair (widthLoad q)
      (r (.GPR 2#5) q) (r (.GPR 3#5) q) limit := by
    rw [load]
    simpa [q, compareCalled, state_simp_rules] using right
  have loq : NatCompare.Owned q (r (.GPR 0#5) q) (r (.GPR 1#5) q) := by
    simpa [q, compareCalled, NatCompare.Owned, state_simp_rules] using leftOwned
  have roq : NatCompare.Owned q (r (.GPR 2#5) q) (r (.GPR 3#5) q) := by
    simpa [q, compareCalled, NatCompare.Owned, state_simp_rules] using rightOwned
  obtain ⟨fuel, t, ht, hf, hpc, herr, hsp, hsaved, horder, hl, hr⟩ :=
    NatCompare.compare_correct q (base + compareOffset) actual limit cq eq aq pq lq rq loq roq
  refine ⟨fuel + 1, t, ?_, hf, ?_, herr, ?_, ?_, horder, ?_, ?_⟩
  · rw [run, compare_call_step s base hc he hp]
    exact ht
  · simpa [q, compareCalled, state_simp_rules] using hpc
  · simpa [q, compareCalled, state_simp_rules] using hsp
  · intro reg low high
    have h := hsaved reg low (by omega)
    have ne : reg ≠ 30#5 := by bv_omega
    simpa [q, compareCalled, state_simp_rules, ne] using h
  · simpa [q, compareCalled, state_simp_rules] using hl
  · simpa [q, compareCalled, state_simp_rules] using hr

end SszArm.Delimited
