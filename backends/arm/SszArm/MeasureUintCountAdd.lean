import SszArm.MeasureUintCountDivide

namespace SszArm.Measure.Uint

def countAddOps (low : BitVec 64) (bits : Nat) : List CountOp :=
  [.p2256, .p2260, .p2264, .p2268] ++
    if (AddWithCarry low (BitVec.ofNat 64 bits) 0#1).2.c = 1#1 then [.p2280]
    else [.p2272, .p2276]

theorem count_add (s : ArmState) (base : BitVec 64) (bits : Nat)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 2256#64) (bitsBound : bits ≤ 64)
    (counter : r (.GPR 8#5) s = 64#64 - BitVec.ofNat 64 bits)
    (bound : pairValue (r (.GPR 10#5) s) (r (.GPR 9#5) s) + bits < 2^128) :
    ∃ fuel t, run fuel s = t ∧ NatNarrow.Frame s t ∧
      read_pc t = base + 2284#64 ∧
      pairValue (r (.GPR 8#5) t) (r (.GPR 9#5) t) =
        pairValue (r (.GPR 10#5) s) (r (.GPR 9#5) s) + bits := by
  let ops := countAddOps (r (.GPR 10#5) s) bits
  let t := countBlock base ops s
  have pc' : r .PC s = base + 2256#64 := pc
  have converted : (64#32 - (64#64 - BitVec.ofNat 64 bits).setWidth 32).setWidth 64 =
      BitVec.ofNat 64 bits := by bv_omega
  have follows : CountFollows base ops s := by
    by_cases carry : (AddWithCarry (r (.GPR 10#5) s) (BitVec.ofNat 64 bits) 0#1).2.c = 1#1 <;>
      simp [ops, countAddOps, CountFollows, CountOp.row, CountOp.effect, put, next,
        Emit.Dispatch.next, state_simp_rules, pc', counter, converted, carry, BitVec.add_assoc]
  have wordValue : (BitVec.ofNat 64 bits).toNat = bits := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have added := count_add_word (r (.GPR 10#5) s) (r (.GPR 9#5) s)
    (BitVec.ofNat 64 bits) (by simpa only [wordValue] using bound)
  refine ⟨ops.length, t, count_run base ops s code error aligned follows,
    count_pure_frame base ops s ?_, ?_, ?_⟩
  · dsimp only [ops, countAddOps]
    split <;> decide
  · by_cases carry : (AddWithCarry (r (.GPR 10#5) s) (BitVec.ofNat 64 bits) 0#1).2.c = 1#1 <;>
      simp [t, ops, countAddOps, countBlock, CountOp.effect, put, next,
        Emit.Dispatch.next, state_simp_rules, pc', counter, converted, carry, BitVec.add_assoc]
  · by_cases carry : (AddWithCarry (r (.GPR 10#5) s) (BitVec.ofNat 64 bits) 0#1).2.c = 1#1 <;>
      simpa [t, ops, countAddOps, countBlock, CountOp.effect, put, next,
        Emit.Dispatch.next, state_simp_rules, counter, converted, carry, wordValue] using added

end SszArm.Measure.Uint
