import SszArm.HashFinalizeDigest

namespace SszArm.Hash.Finalize

open Delimited (MemoryFrame)

theorem return_observe (s t : ArmState) (aligned : CheckSPAlignment s) (live : Live s t) :
    read_pc (returnState t) = r (.GPR 30#5) s ∧
    r (.GPR 31#5) (returnState t) = r (.GPR 31#5) s ∧
    r (.GPR 19#5) (returnState t) = r (.GPR 19#5) s ∧
    r (.GPR 20#5) (returnState t) = r (.GPR 20#5) s ∧
    r (.GPR 30#5) (returnState t) = r (.GPR 30#5) s := by
  have ta := live.toActivation.aligned aligned
  have link := live.saved.link
  have pair := live.saved.pair
  simp (config := {decide := true, instances := true})
    [returnState, effect, returnOps, p544, p548, p552, Op.effect, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, ta, live.sp, link, pair,
     bodySP, stackTop, BitVec.sub_eq_add_neg, BitVec.add_assoc]

theorem return_correct (s t : ArmState) (aligned : CheckSPAlignment s) (live : Live s t) :
    Returned s (returnState t) ∧ MemoryFrame (finalizeWrites s) s (returnState t) := by
  have ta := live.toActivation.aligned aligned
  have scalar := return_scalar t ta
  obtain ⟨pc, sp, x19, x20, x30⟩ := return_observe s t aligned live
  refine ⟨⟨pc, scalar.error.trans live.error, scalar.program.trans live.program, sp, ?_, ?_⟩, ?_⟩
  · intro reg lo hi
    by_cases h19 : reg = 19#5
    · simpa only [h19] using x19
    by_cases h20 : reg = 20#5
    · simpa only [h20] using x20
    by_cases h30 : reg = 30#5
    · simpa only [h30] using x30
    rw [scalar.registers reg (by simp only [List.mem_cons, List.mem_singleton]; bv_omega)]
    exact live.registers reg lo (by bv_omega) h19 h20
  · intro reg lo hi
    rw [scalar.vectors]
    exact live.vectors reg lo hi
  · intro address outside
    rw [return_memory t ta]
    exact live.frame address outside

theorem digest_return (s t : ArmState) (base : BitVec 64) (words : Vector UInt32 8)
    (code : CodeAt s base) (g : Geometry s) (aligned : CheckSPAlignment s)
    (live : Live s t) (chaining : ChainingAt t (statePtr s + 64#64) words)
    (pc : read_pc t = base + finalizeOffset + 216#64) :
    Returned s (run 85 t) ∧ BytesAt (run 85 t) (outputPtr s) (Ssz.Sha256.digest words) ∧
      MemoryFrame (finalizeWrites s) s (run 85 t) := by
  obtain ⟨u, execution, liveU, bytesU, pcU⟩ := digest_run s t base words code g aligned live chaining pc
  have ua := liveU.toActivation.aligned aligned
  have ret := return_correct s u aligned liveU
  have final : run 85 t = returnState u := by
    rw [show 85 = 82 + 3 by decide, run_plus, execution,
      return_run u base (liveU.toActivation.code code) liveU.error ua pcU]
  rw [final]
  refine ⟨ret.1, ?_, ret.2⟩
  intro i
  change (returnState u).mem _ = _
  rw [return_memory u ua]
  exact bytesU i

end SszArm.Hash.Finalize
