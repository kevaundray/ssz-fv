import SszArm.BitVectorValueLoad
import SszArm.UintResultMemory

namespace SszArm.BitVector.ValueTail

open Block
open Delimited (Span MemoryFrame Protected)
open UintCodec (widthLoad)

def storeResult (s : ArmState) (base : BitVec 64) : ArmState :=
  StoreStage.restore.result
    (StoreStage.tag.result
      (StoreStage.spill.result (StoreStage.payload.result s base) base) base) base

theorem store_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 6720#64) : run 14 s = storeResult s base := by
  have first := store_executes .payload s base code error aligned pc
  have second := store_executes .spill (StoreStage.payload.result s base) base
    (by simpa only [CodeAt, store_program] using code)
    (by simpa only [store_error] using error)
    (store_aligned _ _ _ aligned)
    (by simp [StoreStage.result, StoreStage.start, state_simp_rules])
  have third := store_executes .tag
    (StoreStage.spill.result (StoreStage.payload.result s base) base) base
    (by simpa only [CodeAt, store_program] using code)
    (by simpa only [store_error] using error)
    (store_aligned _ _ _ (store_aligned _ _ _ aligned))
    (by simp [StoreStage.result, StoreStage.start, state_simp_rules])
  have last := store_executes .restore
    (StoreStage.tag.result (StoreStage.spill.result (StoreStage.payload.result s base) base) base) base
    (by simpa only [CodeAt, store_program] using code)
    (by simpa only [store_error] using error)
    (store_aligned _ _ _ (store_aligned _ _ _ (store_aligned _ _ _ aligned)))
    (by simp [StoreStage.result, StoreStage.start, state_simp_rules])
  change run 4 s = _ at first
  change run 3 _ = _ at second
  change run 3 _ = _ at third
  change run 4 _ = _ at last
  change run (4 + (3 + (3 + 4))) s = _
  rw [run_plus, first, run_plus, second, run_plus, third, last]
  rfl

@[simp] theorem stored_pc (s : ArmState) (base : BitVec 64) :
    read_pc (storeResult s base) = base + 4732#64 := by
  simp [storeResult, StoreStage.result, state_simp_rules]

@[simp] theorem stored_program (s : ArmState) (base : BitVec 64) :
    (storeResult s base).program = s.program := by simp [storeResult]

@[simp] theorem stored_error (s : ArmState) (base : BitVec 64) :
    read_err (storeResult s base) = read_err s := by simp [storeResult]

@[simp] theorem stored_sp (s : ArmState) (base : BitVec 64) :
    r (.GPR 31#5) (storeResult s base) = r (.GPR 31#5) s := by
  simp [storeResult, StoreStage.result, state_simp_rules, BitVec.sub_add_cancel]

theorem stored_register (s : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (r9 : reg ≠ 9#5) (r10 : reg ≠ 10#5) (rsp : reg ≠ 31#5) :
    r (.GPR reg) (storeResult s base) = r (.GPR reg) s := by
  simp only [storeResult, store_register _ _ _ _ r9 r10 rsp]

@[simp] theorem stored_vector (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.SFP reg) (storeResult s base) = r (.SFP reg) s := by simp [storeResult]

/-- Exactly the output fields and lowering slot that are actually written.
The outer output padding, including bytes8..15 and17..31, is framed. -/
def writes (s : ArmState) : List Span :=
  [((r (.GPR 23#5) s).toNat, 8), ((r (.GPR 23#5) s).toNat + 16, 1),
   ((r (.GPR 23#5) s).toNat + 32, 32), ((r (.GPR 31#5) s).toNat - 16, 16)]

structure Space (s : ArmState) : Prop where
  stackLow : 16 ≤ (r (.GPR 31#5) s).toNat
  stackHigh : (r (.GPR 31#5) s).toNat + 176 ≤ 2^64
  output : (r (.GPR 23#5) s).toNat + 64 ≤ 2^64
  separate : (r (.GPR 23#5) s).toNat + 64 ≤ (r (.GPR 31#5) s).toNat - 16 ∨
    (r (.GPR 31#5) s).toNat ≤ (r (.GPR 23#5) s).toNat

macro "value_store_expand" : tactic => `(tactic|
  simp (config := {decide := true, instances := true}) only
    [storeResult, StoreStage.result, state_simp_rules, ArmState.mem_w_eq_mem,
     BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add_ofNat, Nat.reduceAdd,
     BitVec.add_zero, BitVec.zero_add, BitVec.sub_add_cancel])

theorem stored_frame (s : ArmState) (base : BitVec 64) (space : Space s) :
    MemoryFrame (writes s) s (storeResult s base) := by
  obtain ⟨stackLow, stackHigh, output, separate⟩ := space
  intro address outside
  have tag := outside ((r (.GPR 23#5) s).toNat, 8) (by simp [writes])
  have kind := outside ((r (.GPR 23#5) s).toNat + 16, 1) (by simp [writes])
  have payload := outside ((r (.GPR 23#5) s).toNat + 32, 32) (by simp [writes])
  have spill := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [writes])
  value_store_expand
  simp (disch := value_side) [BoolCodec.write_mem_bytes_frame, ArmState.mem_w_eq_mem]

theorem stored_fields (s : ArmState) (base : BitVec 64) (space : Space s) :
    widthLoad (storeResult s base) (r (.GPR 23#5) s).toNat 8 = some 0 ∧
    widthLoad (storeResult s base) ((r (.GPR 23#5) s).toNat + 16) 1 = some 3 ∧
    widthLoad (storeResult s base) ((r (.GPR 23#5) s).toNat + 32) 8 = some (r (.GPR 24#5) s).toNat ∧
    widthLoad (storeResult s base) ((r (.GPR 23#5) s).toNat + 40) 8 = some (r (.GPR 20#5) s).toNat ∧
    widthLoad (storeResult s base) ((r (.GPR 23#5) s).toNat + 48) 8 = some (r (.GPR 9#5) s).toNat ∧
    widthLoad (storeResult s base) ((r (.GPR 23#5) s).toNat + 56) 8 = some (r (.GPR 8#5) s).toNat := by
  obtain ⟨stackLow, stackHigh, output, separate⟩ := space
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat]
  all_goals
    value_store_expand
    simp (config := {decide := true, instances := true}) (disch := value_side) only
      [UintCodec.Tail.write_pair_words, state_simp_rules, BitVec.add_assoc,
       BitVec.ofNat_add_ofNat, Nat.reduceAdd,
       BoolCodec.read_mem_bytes_write_mem_bytes_same,
       BoolCodec.read_mem_bytes_write_mem_bytes_disjoint]

/-- Borrowed-data preservation is derived from the actual write frame. There is
no zero-length pointer normalization. -/
theorem stored_result (s : ArmState) (base : BitVec 64) (space : Space s)
    (count : BitVec 128) (data : Ssz.Bytes)
    (low : r (.GPR 9#5) s = countLow count) (high : r (.GPR 8#5) s = countHigh count)
    (size : (r (.GPR 20#5) s).toNat = data.size)
    (scope : data.size = (count.toNat + 7) / 8)
    (dataAt : SszNative.ByteView.BytesAt (widthLoad s) (r (.GPR 24#5) s).toNat data)
    (dataBound : (r (.GPR 24#5) s).toNat + data.size ≤ 2^64)
    (dataOwned : Protected (writes s) (r (.GPR 24#5) s).toNat data.size) :
    SszNative.BitVector.ResultAt (widthLoad (storeResult s base))
      (r (.GPR 23#5) s).toNat (r (.GPR 24#5) s).toNat data (.ok count) := by
  obtain ⟨tag, kind, pointer, length, lower, upper⟩ := stored_fields s base space
  refine ⟨tag, kind, pointer, by simpa only [size] using length, ?_, ?_, ?_, scope⟩
  · simpa only [low, countLow, BitVec.toNat_setWidth] using lower
  · have bound := count.isLt
    have highNat : (countHigh count).toNat = count.toNat / 2^64 := by
      simp only [countHigh, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
        Nat.shiftRight_eq_div_pow]
      omega
    simpa only [high, highNat] using upper
  · intro index within
    rw [(stored_frame s base space).load _ 1 (by omega)
      (dataOwned.subspan index 1 (by omega))]
    exact dataAt index within

end SszArm.BitVector.ValueTail
