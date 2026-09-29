import SszArm.CodecFixedBody

namespace SszArm.Codec.Fixed.IsFixed

open SszNative.Codec (DescTag)
open Dispatch.Block (next put save branch greater)

def gateOps : List Op := [.p12, .p16, .p20]

theorem gate_pcs (s : ArmState) (base : BitVec 64) (pc : read_pc s = base + 12#64) :
    PCs base gateOps s := by
  change r .PC s = _ at pc
  simp [gateOps, PCs, Op.row, Op.effect, next, put, branch, Udivti3.compare,
    Udivti3.next, state_simp_rules, pc, BitVec.add_assoc]

theorem gate_pc (s : ArmState) (base : BitVec 64) (tag : DescTag)
    (pc : read_pc s = base + 12#64)
    (stored : read_mem_bytes 8 (r (.GPR 0#5) s) s = tagWord tag) :
    read_pc (block gateOps s) = base + selectedEntry tag := by
  change r .PC s = _ at pc
  cases tag <;> simp (config := {decide := true}) [gateOps, selectedEntry, block,
    Op.effect, next, put, branch, Udivti3.compare, Udivti3.next, state_simp_rules,
    pc, stored, tagWord, BitVec.add_assoc, AddWithCarry, bitvec_rules, minimal_theory]

theorem gate_tag (s : ArmState) (tag : DescTag)
    (stored : read_mem_bytes 8 (r (.GPR 0#5) s) s = tagWord tag) :
    r (.GPR 8#5) (block gateOps s) = tagWord tag := by
  simp [gateOps, block, Op.effect, next, put, branch, Udivti3.compare,
    Udivti3.next, state_simp_rules, stored]

theorem gate_memory (s : ArmState) : (block gateOps s).mem = s.mem := by
  simp [gateOps, block, Op.effect, next, put, branch, Udivti3.compare,
    Udivti3.next, state_simp_rules]

theorem gate_register (s : ArmState) (reg : BitVec 5) (different : reg ≠ 8#5) :
    r (.GPR reg) (block gateOps s) = r (.GPR reg) s := by
  simp [gateOps, block, Op.effect, next, put, branch, Udivti3.compare,
    Udivti3.next, state_simp_rules, different]

theorem gate_run (s : ArmState) (base : BitVec 64) (code : CodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 12#64) : run 3 s = block gateOps s :=
  run_block gateOps s base code error aligned (gate_pcs s base pc)

theorem BodyContext.gate {source current : ArmState} (context : BodyContext source current) :
    BodyContext source (block gateOps current) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨(gate_register current 31#5 (by decide)).trans context.saved.sp, ?_, ?_, ?_⟩
    all_goals rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp (gate_memory current))]
    · exact context.saved.link
    · exact context.saved.first
    · exact context.saved.second
  · intro reg lower upper h19 h20 h30
    exact (gate_register current reg (by bv_omega)).trans
      (context.registers reg lower upper h19 h20 h30)
  · intro reg lower upper
    rw [block_vector]
    exact context.vectors reg lower upper

end SszArm.Codec.Fixed.IsFixed
