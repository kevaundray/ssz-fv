import SszArm.DelimitedBlocks
import SszNatABI

namespace SszArm.Delimited

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def prepareCompareOps : List Op := [.p364, .p368, .p372, .p376, .p380, .p384, .p388, .p392]

theorem prepare_compare_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 364#64) :
    run 8 s = block base prepareCompareOps s := by
  apply block_run base prepareCompareOps s hc he ha
  have hpc : r .PC s = base + 364#64 := hp
  simp [prepareCompareOps, Follows, Op.row, Op.effect, put, next,
    state_simp_rules, hpc, BitVec.add_assoc]

/-- The actual LDP and argument moves preserve the original output/input/length
in X27/X28/X29, and preserve both original cap words in X22/X21. -/
theorem prepare_compare_fields (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 364#64) :
    let t := block base prepareCompareOps s
    read_pc t = base + 396#64 ∧ t.mem = s.mem ∧
      r (.GPR 0#5) t = r (.GPR 20#5) s ∧ r (.GPR 1#5) t = r (.GPR 19#5) s ∧
      r (.GPR 2#5) t = read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s ∧
      r (.GPR 3#5) t = read_mem_bytes 8 (r (.GPR 1#5) s + 16#64) s ∧
      r (.GPR 22#5) t = read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s ∧
      r (.GPR 21#5) t = read_mem_bytes 8 (r (.GPR 1#5) s + 16#64) s ∧
      r (.GPR 27#5) t = r (.GPR 0#5) s ∧ r (.GPR 28#5) t = r (.GPR 2#5) s ∧
      r (.GPR 29#5) t = r (.GPR 3#5) s ∧ r (.GPR 31#5) t = r (.GPR 31#5) s := by
  have hpc : r .PC s = base + 364#64 := hp
  simp [block, prepareCompareOps, Op.effect, put, next, state_simp_rules, hpc, BitVec.add_assoc]

/-- Only Rust Ordering's low byte is inspected. SXTB first sign-extends that
byte to W8; B.LT takes both LT and EQ, and rejects exactly GT. -/
theorem compare_return_fields (s : ArmState) (base : BitVec 64) (order : Ordering)
    (result : (r (.GPR 0#5) s).setWidth 8 = SszNative.NatABI.orderingByte order) :
    let t := block base callReturnOps s
    read_pc t = (if order = .gt then base + 424#64 else base + 540#64) ∧
      t.mem = s.mem ∧ r (.GPR 0#5) t = r (.GPR 27#5) s ∧
      r (.GPR 2#5) t = r (.GPR 28#5) s ∧ r (.GPR 3#5) t = r (.GPR 29#5) s ∧
      r (.GPR 31#5) t = r (.GPR 31#5) s := by
  cases order <;>
    simp (config := {decide := true, instances := true})
      [block, callReturnOps, Op.effect, put, next, state_simp_rules,
       result, SszNative.NatABI.orderingByte, AddWithCarry, make_pstate, bitvec_rules]

end SszArm.Delimited
