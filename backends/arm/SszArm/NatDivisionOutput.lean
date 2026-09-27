import SszArm.NatDivisionReturn

namespace SszArm.NatDivision

open Delimited (Span Protected MemoryFrame)
open BoolCodec
open UintCodec (widthLoad)
open UintCodec.Tail

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def smallHeadOps : List Op := [.p644, .p648, .p652]
def fastOutputOps : List Op :=
  [.p768, .p772, .p776, .p780, .p784, .p788, .p792, .p796, .p800, .p804, .p808]
def payloadOps : List Op := [.p800, .p804, .p808]

theorem small_head_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 644#64) :
    run 3 s = block base smallHeadOps s := by
  apply block_run base smallHeadOps s hc he ha
  have hpc : r .PC s = base + 644#64 := hp
  simp [smallHeadOps, Follows, Op.row, Op.effect, put, next, state_simp_rules,
    hpc, BitVec.add_assoc]

theorem small_head_data (s : ArmState) (base : BitVec 64) :
    let t := block base smallHeadOps s
    read_pc t = base + 768#64 ∧ r (.GPR 9#5) t = 0#64 ∧
      r (.GPR 10#5) t = r (.GPR 0#5) s ∧ t.mem = s.mem := by
  simp [block, smallHeadOps, Op.effect, put, next, state_simp_rules]

theorem fast_output_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 768#64) :
    run 11 s = block base fastOutputOps s := by
  apply block_run base fastOutputOps s hc he ha
  have hpc : r .PC s = base + 768#64 := hp
  simp [fastOutputOps, Follows, Op.row, Op.effect, put, next, state_simp_rules,
    hpc, BitVec.add_assoc]

theorem payload_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 800#64) :
    run 3 s = block base payloadOps s := by
  apply block_run base payloadOps s hc he ha
  have hpc : r .PC s = base + 800#64 := hp
  simp [payloadOps, Follows, Op.row, Op.effect, put, next, state_simp_rules,
    hpc, BitVec.add_assoc]

macro "division_output_expand" : tactic => `(tactic|
  simp (config := {decide := true, instances := true}) only
    [block, fastOutputOps, payloadOps, List.foldl_cons, List.foldl_nil, Op.effect, put, next,
     state_simp_rules, ArmState.mem_w_eq_mem, BitVec.add_assoc,
     BitVec.ofNat_eq_ofNat, BitVec.ofNat_add_ofNat, Nat.reduceAdd,
     BitVec.add_zero, BitVec.zero_add, BitVec.sub_add_cancel])

theorem fast_output_frame (s : ArmState) (base : BitVec 64) (space : ReturnSpace s) :
    MemoryFrame (returnWrites s) s (block base fastOutputOps s) := by
  rcases space with ⟨stackLow, stackHigh, outputHigh, separate⟩
  intro a ha
  have outsideOutput := ha ((r (.GPR 19#5) s).toNat, 68) (by simp [returnWrites])
  have outsideStack := ha ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [returnWrites])
  simp only [Prod.fst, Prod.snd] at outsideOutput outsideStack
  division_output_expand
  tail_reads
  simp (disch := tail_side) [write_mem_bytes_frame, ArmState.mem_w_eq_mem]

theorem fast_output_head (s : ArmState) (base : BitVec 64) (space : ReturnSpace s) :
    let t := block base fastOutputOps s
    read_mem_bytes 8 (r (.GPR 19#5) s) t = r (.GPR 9#5) s ∧
      read_mem_bytes 8 (r (.GPR 19#5) s + 8#64) t = r (.GPR 10#5) s := by
  rcases space with ⟨stackLow, stackHigh, outputHigh, separate⟩
  dsimp only
  constructor <;> division_output_expand <;> tail_reads

theorem fast_output_arguments (s : ArmState) (base : BitVec 64) (space : ReturnSpace s) :
    let t := block base fastOutputOps s
    read_pc t = base + 976#64 ∧
      r (.GPR 1#5) t = r (.GPR 22#5) s - r (.GPR 0#5) s * r (.GPR 20#5) s ∧
      r (.GPR 8#5) t = 0#64 ∧ r (.GPR 9#5) t = 16#64 ∧
      r (.GPR 19#5) t = r (.GPR 19#5) s ∧ r (.GPR 31#5) t = r (.GPR 31#5) s := by
  rcases space with ⟨stackLow, stackHigh, outputHigh, separate⟩
  division_output_expand

/-- This suffix is also used after normalizing a multi-limb quotient. -/
theorem payload_frame (s : ArmState) (base : BitVec 64) (space : ReturnSpace s) :
    MemoryFrame (returnWrites s) s (block base payloadOps s) := by
  have outputHigh := space.outputHigh
  intro a ha
  have outside := ha ((r (.GPR 19#5) s).toNat, 68) (by simp [returnWrites])
  simp only [Prod.fst, Prod.snd] at outside
  division_output_expand
  simp (disch := tail_side) [write_mem_bytes_frame, ArmState.mem_w_eq_mem]

theorem payload_head (s : ArmState) (base : BitVec 64) (space : ReturnSpace s) :
    let t := block base payloadOps s
    read_mem_bytes 8 (r (.GPR 19#5) s) t = read_mem_bytes 8 (r (.GPR 19#5) s) s ∧
      read_mem_bytes 8 (r (.GPR 19#5) s + 8#64) t = r (.GPR 10#5) s := by
  have outputHigh := space.outputHigh
  dsimp only
  constructor <;> division_output_expand <;> tail_reads

theorem payload_arguments (s : ArmState) (base : BitVec 64) :
    let t := block base payloadOps s
    read_pc t = base + 976#64 ∧ r (.GPR 1#5) t = r (.GPR 1#5) s ∧
      r (.GPR 8#5) t = r (.GPR 8#5) s ∧ r (.GPR 9#5) t = 16#64 ∧
      r (.GPR 19#5) t = r (.GPR 19#5) s ∧ r (.GPR 31#5) t = r (.GPR 31#5) s := by
  division_output_expand

end SszArm.NatDivision
