import SszArm.HashCombineFill
import SszArm.HashCombineBufferedFull

namespace SszArm.Hash.Combine

theorem FilledPost.shortState {origin s : ArmState} {base : BitVec 64}
    {value : StreamState} {right : ByteArray} (filled : FilledPost origin s base value right)
    (nonzero : value.buffered.val ≠ 0)
    (short : value.buffered.val + fillCount value right < 64) :
    StateAt s (r (.GPR 31#5) s) (SszNative.HashStream.update value right).state := by
  have stateEq : (SszNative.HashStream.update value right).state =
      { buffer := fillBuffer value right
        chaining := value.chaining
        buffered := ⟨value.buffered.val + fillCount value right, short⟩
        byteLen := fillLength value right } := by
    have short' : value.buffered.val + min (64 - value.buffered.val) right.size < 64 := short
    simp [SszNative.HashStream.update, nonzero, short', fillBuffer, fillCount, fillLength]
  rw [stateEq]
  exact ⟨filled.buffer, filled.chaining, filled.buffered, filled.byteLen⟩

/-- All right-slice paths, including zero bytes, incomplete buffered fill,
complete buffered fill and arbitrarily many following direct blocks. -/
theorem right_correct (origin s : ArmState) (base : BitVec 64) (left right : ByteArray)
    (value : StreamState) (code : CodeAt origin base) (data : DataAt origin base)
    (compression : CompressionCorrect base) (owned : CombineOwned origin base left right)
    (activation : Activation origin s)
    (pc : read_pc s = if value.buffered.val = 0 then base + 308#64 else base + 196#64)
    (state : StateAt s (r (.GPR 31#5) s) { value with byteLen := fillLength value right })
    (rightLength : (r (.GPR 20#5) s).toNat = right.size)
    (rightPointer : r (.GPR 21#5) s = r (.GPR 3#5) origin)
    (buffered : (r (.GPR 22#5) s).toNat = value.buffered.val)
    (bufferPointer : r (.GPR 25#5) s = r (.GPR 31#5) s) :
    ∃ fuel, let t := run fuel s
      Activation origin t ∧ read_pc t = base + 364#64 ∧
      StateAt t (r (.GPR 31#5) t) (SszNative.HashStream.update value right).state := by
  by_cases empty : value.buffered.val = 0
  · have startPC : read_pc s = base + 308#64 := by simpa only [empty, if_pos rfl] using pc
    obtain ⟨fuel, active, finishedPC, result⟩ := right_guard_drain_correct origin s base left right
      0 (Nat.zero_le _) value.buffer value.chaining (fillLength value right)
      code data compression owned activation startPC state.buffer state.chaining state.byteLen
      (by simpa only [BitVec.ofNat_zero, BitVec.add_zero] using rightPointer)
      (by simpa only [Nat.sub_zero] using rightLength)
    refine ⟨fuel, active, finishedPC, ?_⟩
    simpa only [SszNative.HashStream.update, empty, dite_true, fillLength] using result
  · have startPC : read_pc s = base + 196#64 := by simpa only [empty, if_false] using pc
    obtain ⟨fillFuel, filled⟩ := fill_correct origin s base left right value code data owned
      activation startPC state rightLength rightPointer buffered bufferPointer
    let u := run fillFuel s
    by_cases short : value.buffered.val + fillCount value right < 64
    · refine ⟨fillFuel, filled.activation, ?_, filled.shortState empty short⟩
      simpa only [if_pos short] using filled.pc
    · have fullPC : read_pc u = base + 248#64 := by simpa only [if_neg short] using filled.pc
      obtain ⟨fullFuel, active, finishedPC, result⟩ := buffered_full_correct origin u base left right
        (fillCount value right) (fillCount_inputBound value right) (fillBuffer value right)
        value.chaining (fillLength value right) code data compression owned filled.activation
        fullPC filled.buffer filled.chaining filled.byteLen filled.rightPointer filled.rightLength filled.count
      refine ⟨fillFuel + fullFuel, ?_⟩
      rw [run_plus]
      refine ⟨active, finishedPC, ?_⟩
      have full : ¬ value.buffered.val + min (64 - value.buffered.val) right.size < 64 := short
      simpa [SszNative.HashStream.update, SszNative.HashStream.compressBuffer, empty,
        full, fillBuffer, fillCount, fillLength] using result

end SszArm.Hash.Combine
