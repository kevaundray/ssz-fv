import SszArm.DelimitedTailMemory
import SszArm.DelimitedResults
import SszArm.DelimitedArenaArithmetic

namespace SszArm.Delimited

open BoolCodec
open UintCodec (widthLoad)
open UintCodec.Tail (write_pair_words)

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- The four straight-line output paths, ending immediately before the six
restore pairs. The dynamic-index stores are retained in `tagsOps`. -/
inductive TailPath where
  | invalid | scratch | overLimit | success

def TailPath.ops : TailPath → List Op
  | .invalid => invalidOps ++ [.p976]
  | .scratch => scratchOps ++ tagsOps
  | .overLimit => overLimitOps ++ tagsOps
  | .success => successOps

def TailPath.pc : TailPath → Nat
  | .invalid => 620
  | .scratch => 752
  | .overLimit => 424
  | .success => 596

def TailPath.steps : TailPath → Nat
  | .invalid => 17
  | .scratch => 57
  | .overLimit => 45
  | .success => 5

def tailBody (path : TailPath) (base : BitVec 64) (s : ArmState) : ArmState :=
  block base path.ops s

def tailResult (path : TailPath) (base : BitVec 64) (s : ArmState) : ArmState :=
  block base epilogueOps (tailBody path base s)

macro "delimited_tail_expand" : tactic => `(tactic|
  simp (config := {decide := true, instances := true}) only
    [tailBody, TailPath.ops, invalidOps, scratchOps, overLimitOps, successOps,
     tagsOps, List.cons_append, List.nil_append, block, List.foldl_cons,
     List.foldl_nil, Op.effect, put, next, state_simp_rules,
     ArmState.mem_w_eq_mem, BitVec.add_assoc, BitVec.ofNat_eq_ofNat,
     BitVec.ofNat_add_ofNat, Nat.reduceAdd, BitVec.add_zero,
     BitVec.zero_add, BitVec.sub_add_cancel, BitVec.reduceAppend, write_zero32, write_zero16])

macro "delimited_tail_reads" : tactic => `(tactic|
  simp (config := {decide := true, instances := true})
    (disch := delimited_side) only
    [state_simp_rules, ArmState.mem_w_eq_mem, BitVec.add_assoc,
     BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.zero_add,
     BitVec.ofNat_add_ofNat, Nat.reduceAdd, BitVec.setWidth_ofNat_of_le,
     BitVec.sub_add_cancel, BitVec.add_sub_cancel, write_pair_words,
     read_mem_bytes_write_mem_bytes_same, read_mem_bytes_write_mem_bytes_disjoint])

theorem tail_body_run (path : TailPath) (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 path.pc) :
    run path.steps s = tailBody path base s := by
  have length : path.ops.length = path.steps := by cases path <;> rfl
  rw [← length]
  apply block_run base path.ops s hc he ha
  have hpc : r .PC s = base + BitVec.ofNat 64 path.pc := hp
  cases path <;>
    simp (config := {decide := true, instances := true})
      [TailPath.ops, TailPath.pc, invalidOps, scratchOps, overLimitOps,
       successOps, tagsOps, Follows, Op.row, Op.effect, put, next,
       state_simp_rules, hpc, BitVec.add_assoc]

theorem tail_body_pc (path : TailPath) (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + BitVec.ofNat 64 path.pc) :
    read_pc (tailBody path base s) = base + 980#64 := by
  have hpc : r .PC s = base + BitVec.ofNat 64 path.pc := hp
  cases path <;>
    simp [tailBody, TailPath.ops, TailPath.pc, invalidOps, scratchOps,
      overLimitOps, successOps, tagsOps, block, Op.effect, put, next,
      state_simp_rules, hpc, BitVec.add_assoc]

@[simp] theorem tail_body_sp (path : TailPath) (s : ArmState) (base : BitVec 64) :
    r (.GPR 31#5) (tailBody path base s) = r (.GPR 31#5) s := by
  cases path <;> delimited_tail_expand

@[simp] theorem tail_body_out (path : TailPath) (s : ArmState) (base : BitVec 64) :
    r (.GPR 0#5) (tailBody path base s) = r (.GPR 0#5) s := by
  cases path <;> delimited_tail_expand

theorem tail_body_vectors (path : TailPath) (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) (low : 8 ≤ reg.toNat) (high : reg.toNat ≤ 15) :
    (r (.SFP reg) (tailBody path base s)).setWidth 64 =
      (r (.SFP reg) s).setWidth 64 := by
  have ne : reg ≠ 0#5 := by bv_omega
  cases path <;>
    simp [tailBody, TailPath.ops, invalidOps, scratchOps, overLimitOps,
      successOps, tagsOps, block, Op.effect, put, next, state_simp_rules, ne]

/-- Only output bytes and the actual lower sixteen-byte slot are writable.
The saved activation is deliberately absent from this exact tail frame. -/
theorem tail_body_frame (path : TailPath) (s : ArmState) (base : BitVec 64)
    (owned : TailOwned s) : MemoryFrame (tailWrites s) s (tailBody path base s) := by
  rcases owned with ⟨stack, stackHigh, output, disjoint, activation⟩
  intro a ha
  have out := ha ((r (.GPR 0#5) s).toNat, 76) (by simp [tailWrites])
  have work := ha ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [tailWrites])
  cases path <;> delimited_tail_expand <;> delimited_tail_reads <;>
    simp (disch := delimited_side) [write_mem_bytes_frame, ArmState.mem_w_eq_mem]

/-- This includes the epilogue's real STR X8,[X0], not merely its register loads. -/
theorem tailMemoryFrame (path : TailPath) (s : ArmState) (base : BitVec 64)
    (owned : TailOwned s) : MemoryFrame (tailWrites s) s (tailResult path base s) := by
  have body := tail_body_frame path s base owned
  intro a ha
  change (block base epilogueOps (tailBody path base s)).mem a = s.mem a
  rw [epilogue_memory]
  have out := ha ((r (.GPR 0#5) s).toNat, 76) (by simp [tailWrites])
  rw [write_mem_bytes_frame _ _ _ _ a (by simpa using (show
      (r (.GPR 0#5) s).toNat + 8 ≤ 2^64 by have h := owned.output; omega))
    (by simpa using (show a.toNat < (r (.GPR 0#5) s).toNat ∨
      (r (.GPR 0#5) s).toNat + 8 ≤ a.toNat by omega))]
  exact body a ha

theorem tail_body_saved (path : TailPath) (entry s : ArmState) (base : BitVec 64)
    (saved : Saved entry s) (owned : TailOwned s) : Saved entry (tailBody path base s) :=
  saved.frame (tail_body_frame path s base owned) (tail_body_sp path s base)
    owned.stackHigh owned.activation_protected (tail_body_vectors path s base)

/-- The block contract closes at the actual RET and restores the original
entry's LR, SP, X19..X30, and only the ABI-preserved SIMD low lanes. -/
theorem tail_run_returned (path : TailPath) (entry s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 path.pc)
    (saved : Saved entry s) (owned : TailOwned s) :
    run (path.steps + 8) s = tailResult path base s ∧
      Returned entry (tailResult path base s) := by
  have code : CodeAt (tailBody path base s) base := by
    simpa only [tailBody, CodeAt, block_program] using hc
  have err : read_err (tailBody path base s) = .None := by
    simpa only [tailBody, block_error] using he
  have align := block_aligned base path.ops s ha
  constructor
  · rw [run_plus, tail_body_run path s base hc he ha hp]
    exact epilogue_run _ base code err align (tail_body_pc path s base hp)
  · exact epilogue_restores entry _ base (tail_body_saved path entry s base saved owned) err

/-- The invalid tail's SIMD stores supply both zero Nat operands and the third
zero payload; X9 supplies the exact caller-selected reason 17 or 18. -/
theorem invalid_tail_image (s : ArmState) (base : BitVec 64) (owned : TailOwned s) :
    SszNative.UintCodec.errorAt (widthLoad (tailResult .invalid base s))
      (r (.GPR 0#5) s).toNat ((r (.GPR 9#5) s).setWidth 32).toNat 0 0 := by
  rcases owned with ⟨stack, stackHigh, output, disjoint, activation⟩
  refine ⟨?_, ?_, ?_, Or.inl ⟨⟨?_, ?_⟩, by decide⟩,
    Or.inl ⟨⟨?_, ?_⟩, by decide⟩, Or.inl ⟨⟨?_, ?_⟩, by decide⟩, ?_⟩
  all_goals
    unfold tailResult
    rw [epilogue_load]
    simp only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat]
    delimited_tail_expand
    delimited_tail_reads

/-- The resource path really emits 32768. Its tag stores use X10=8 and X8=16,
not the over-limit offsets 40 and 48. -/
theorem scratch_tail_image (s : ArmState) (base : BitVec 64) (owned : TailOwned s) :
    SszNative.UintCodec.scratchExhaustedAt (widthLoad (tailResult .scratch base s))
      (r (.GPR 0#5) s).toNat := by
  rcases owned with ⟨stack, stackHigh, output, disjoint, activation⟩
  change SszNative.UintCodec.errorAt _ _ 32768 0 0
  refine ⟨?_, ?_, ?_, Or.inl ⟨⟨?_, ?_⟩, by decide⟩,
    Or.inl ⟨⟨?_, ?_⟩, by decide⟩, Or.inl ⟨⟨?_, ?_⟩, by decide⟩, ?_⟩
  all_goals
    unfold tailResult
    rw [epilogue_load]
    simp only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat]
    delimited_tail_expand
    delimited_tail_reads

/-- Raw copied descriptors, independent of the represented Nat values. These
observations retain the exact source words for the shared native result ABI. -/
theorem over_limit_tail_fields (s : ArmState) (base : BitVec 64) (owned : TailOwned s) :
    widthLoad (tailResult .overLimit base s) ((r (.GPR 0#5) s).toNat + 24) 8 =
        some (r (.GPR 22#5) s).toNat ∧
      widthLoad (tailResult .overLimit base s) ((r (.GPR 0#5) s).toNat + 32) 8 =
        some (r (.GPR 21#5) s).toNat ∧
      widthLoad (tailResult .overLimit base s) ((r (.GPR 0#5) s).toNat + 40) 8 =
        some (r (.GPR 20#5) s).toNat ∧
      widthLoad (tailResult .overLimit base s) ((r (.GPR 0#5) s).toNat + 48) 8 =
        some (r (.GPR 19#5) s).toNat := by
  rcases owned with ⟨stack, stackHigh, output, disjoint, activation⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    unfold tailResult
    rw [epilogue_load]
    simp only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat]
    delimited_tail_expand
    delimited_tail_reads

/-- The original cap and actual Pair representations are retained without
canonicalization, copying borrowed limbs, or requiring readonly disjointness. -/
theorem over_limit_tail_image (s : ArmState) (base : BitVec 64) (expected actual : Nat)
    (owned : TailOwned s)
    (expectedPair : SszNative.NatMemory.Pair (widthLoad s)
      (r (.GPR 22#5) s) (r (.GPR 21#5) s) expected)
    (actualPair : SszNative.NatMemory.Pair (widthLoad s)
      (r (.GPR 20#5) s) (r (.GPR 19#5) s) actual)
    (expectedOwned : NatOwned (tailWrites s) (r (.GPR 22#5) s) (r (.GPR 21#5) s))
    (actualOwned : NatOwned (tailWrites s) (r (.GPR 20#5) s) (r (.GPR 19#5) s)) :
    SszNative.BitView.ResultAt (widthLoad (tailResult .overLimit base s))
      (r (.GPR 0#5) s).toNat (.error (.overLimit expected actual)) := by
  have frame := tailMemoryFrame .overLimit s base owned
  have ep := frame.pair _ _ _ expectedPair expectedOwned
  have ap := frame.pair _ _ _ actualPair actualOwned
  have fields := over_limit_tail_fields s base owned
  rcases owned with ⟨stack, stackHigh, output, disjoint, activation⟩
  change SszNative.UintCodec.errorAt _ _ 2 expected actual
  refine ⟨?_, ?_, ?_,
    SszNative.NatMemory.Pair.at _ _ _ _ _ ep fields.1
      (by simpa only [Nat.add_assoc] using fields.2.1),
    SszNative.NatMemory.Pair.at _ _ _ _ _ ap fields.2.2.1
      (by simpa only [Nat.add_assoc] using fields.2.2.2),
    Or.inl ⟨⟨?_, ?_⟩, by decide⟩, ?_⟩
  all_goals
    unfold tailResult
    rw [epilogue_load]
    simp only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat]
    delimited_tail_expand
    delimited_tail_reads

/-- Exact native success stores, including the epilogue's final tag. -/
theorem success_tail_memory (s : ArmState) (base : BitVec 64) (bytes count : Nat)
    (byteCount : r (.GPR 9#5) s = BitVec.ofNat 64 bytes)
    (countLow : r (.GPR 24#5) s = BitVec.ofNat 64 count)
    (countHigh : r (.GPR 23#5) s = BitVec.ofNat 64 (count / 2^64))
    (tag : r (.GPR 8#5) s = 0#64) :
    (tailResult .success base s).mem =
      (successMemory s (r (.GPR 0#5) s) (r (.GPR 2#5) s) bytes count).mem := by
  unfold tailResult
  rw [epilogue_memory]
  simp [tailBody, TailPath.ops, successOps, block, Op.effect, put, next,
    state_simp_rules, successMemory, byteCount, countLow, countHigh, tag]
  apply mem_write_mem_bytes_of_mem_eq
  simp only [ArmState.mem_w_eq_mem]
  apply mem_write_mem_bytes_of_mem_eq
  simp only [ArmState.mem_w_eq_mem]
  apply mem_write_mem_bytes_of_mem_eq
  simp only [ArmState.mem_w_eq_mem]
  apply mem_write_mem_bytes_of_mem_eq
  simp only [ArmState.mem_w_eq_mem]

/-- Success borrows the original byte pointer and writes both count limbs. -/
theorem success_tail_image (s : ArmState) (base : BitVec 64)
    (packed : Ssz.Bytes) (count : Nat) (owned : TailOwned s)
    (physical : (r (.GPR 2#5) s).toNat + packed.size ≤ 2^64)
    (bytesBound : packed.size < 2^64) (countBound : count < 2^128)
    (scope : packed.size = (count + 7) / 8)
    (byteCount : r (.GPR 9#5) s = BitVec.ofNat 64 packed.size)
    (countLow : r (.GPR 24#5) s = BitVec.ofNat 64 count)
    (countHigh : r (.GPR 23#5) s = BitVec.ofNat 64 (count / 2^64))
    (tag : r (.GPR 8#5) s = 0#64)
    (dataOwned : Protected (tailWrites s) (r (.GPR 2#5) s).toNat packed.size)
    (input : SszNative.ByteView.BytesAt (widthLoad s) (r (.GPR 2#5) s).toNat packed) :
    SszNative.BitView.ResultAt (widthLoad (tailResult .success base s))
      (r (.GPR 0#5) s).toNat (.ok (.bits (Ssz.unpackBits packed count))) := by
  have memory := success_tail_memory s base packed.size count byteCount countLow countHigh tag
  have loads : widthLoad (tailResult .success base s) =
      widthLoad (successMemory s (r (.GPR 0#5) s) (r (.GPR 2#5) s) packed.size count) := by
    funext a n
    unfold widthLoad
    rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp memory) n]
  have outputOwned : Protected [((r (.GPR 0#5) s).toNat, 76)]
      (r (.GPR 2#5) s).toNat packed.size := by
    rcases dataOwned with empty | separate
    · exact Or.inl empty
    · right
      intro span member
      exact separate span (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        simp [tailWrites, member])
  rw [loads]
  exact success_memory_result s _ _ packed count owned.output physical bytesBound countBound
    scope outputOwned input

end SszArm.Delimited
