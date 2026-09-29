import SszArm.HashCombineDirect
import SszArm.HashCombineTail
import SszArm.HashGeometry

namespace SszArm.Hash.Combine

open Delimited (Span Protected MemoryFrame)

def drainWrites (s : ArmState) : List Span :=
  [stackSpan s 160, ((r (.GPR 31#5) s).toNat, 112)]

structure DrainPost (side : Side) (s t : ArmState) (base : BitVec 64) : Prop where
  pc : read_pc t = base + BitVec.ofNat 64 side.tailReturn
  error : read_err t = .None
  program : t.program = s.program
  sp : r (.GPR 31#5) t = r (.GPR 31#5) s
  registers : ∀ reg : BitVec 5, 19 ≤ reg.toNat → reg.toNat ≤ 29 →
    reg ≠ side.count → reg ≠ side.cursor → reg ≠ 25#5 →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
    (r (.SFP reg) t).setWidth 64 = (r (.SFP reg) s).setWidth 64
  frame : MemoryFrame (drainWrites s) s t
  leftBuffer : side = .left → r (.GPR 25#5) t = r (.GPR 31#5) s

/-- Arbitrary direct blocks plus the actual residual memcpy implement `drain`.
The occupancy store is the next wrapper instruction, so this contract records
buffer/chaining/length separately rather than asserting an unexecuted store. -/
theorem drain_correct (side : Side) (s : ArmState) (base address : BitVec 64)
    (input : ByteArray) (start : Nat) (startBound : start ≤ input.size)
    (buffer : Vector UInt8 64) (words : Vector UInt32 8) (byteLen : UInt64)
    (code : CodeAt s base) (data : DataAt s base) (compression : CompressionCorrect base)
    (pc : read_pc s = if (input.size - start) / 64 = 0 then
      base + BitVec.ofNat 64 side.stop else base + BitVec.ofNat 64 side.start)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (owned : DirectOwned s base address input words)
    (statePointer : r (.GPR 24#5) s = r (.GPR 31#5) s)
    (statePhysical : (r (.GPR 31#5) s).toNat + 112 ≤ 2^64)
    (inputWritable : Protected [((r (.GPR 31#5) s).toNat, 64)] address.toNat input.size)
    (initialOwned : Protected (drainWrites s) (base + initialOffset).toNat 32)
    (roundsOwned : Protected (drainWrites s) (base + roundsOffset).toNat 256)
    (bufferAt : BytesAt s (r (.GPR 31#5) s) ⟨buffer.toArray⟩)
    (lengthAt : read_mem_bytes 8 (r (.GPR 31#5) s + 104#64) s = byteLen.toBitVec)
    (cursor : r (.GPR side.cursor) s = address + BitVec.ofNat 64 start)
    (count : (r (.GPR side.count) s).toNat = input.size - start) :
    ∃ fuel, let t := run fuel s
      let value := (SszNative.HashStream.drain buffer words byteLen input start startBound).state
      DrainPost side s t base ∧ DataAt t base ∧
      (r (.GPR side.count) t).toNat = value.buffered.val ∧
      BytesAt t (r (.GPR 31#5) s) ⟨value.buffer.toArray⟩ ∧
      ChainingAt t (r (.GPR 31#5) s + 64#64) value.chaining ∧
      read_mem_bytes 8 (r (.GPR 31#5) s + 104#64) t = value.byteLen.toBitVec := by
  let q := (input.size - start) / 64
  let rest := (input.size - start) % 64
  let stop := start + 64 * q
  have short : rest < 64 := Nat.mod_lt _ (by decide)
  have split : start + 64 * q + rest = input.size := by dsimp [q, rest]; omega
  obtain ⟨loopFuel, loopPost, loopCount, loopCursor, loopPC, loopOwned, loopData⟩ :=
    direct_loop side q rest short s base address input start words code data compression pc error
      aligned owned cursor (by dsimp [q, rest]; omega) split
  let u := run loopFuel s
  have uSP : r (.GPR 31#5) u = r (.GPR 31#5) s := loopPost.sp
  have uState : r (.GPR 24#5) u = r (.GPR 31#5) s := loopPost.statePointer.trans statePointer
  have uCount : (r (.GPR side.count) u).toNat = rest := loopCount
  have directContained : ∀ span ∈ directWrites s, ∃ outer ∈ drainWrites s,
      outer.1 ≤ span.1 ∧ span.1 + span.2 ≤ outer.1 + outer.2 := by
    intro span member
    simp only [directWrites, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨stackSpan s 160, by simp [drainWrites], Nat.le_refl _, Nat.le_refl _⟩
    · refine ⟨((r (.GPR 31#5) s).toNat, 112), by simp [drainWrites], ?_, ?_⟩
      all_goals rw [statePointer]; bv_omega
  have bufferProtected : Protected (directWrites s) (r (.GPR 31#5) s).toNat 64 := by
    right
    intro span member
    simp only [directWrites, List.mem_cons, List.not_mem_nil, or_false] at member
    have low := owned.stackLow
    rcases member with rfl | rfl
    · right; simp only [stackSpan]; omega
    · left; rw [statePointer]; bv_omega
  have uBuffer : BytesAt u (r (.GPR 31#5) u) ⟨buffer.toArray⟩ := by
    rw [uSP]
    apply bytesAt_frame loopPost.frame _ _ bufferAt
    · simpa only [Hash.vectorByteArray_size] using (show (r (.GPR 31#5) s).toNat + 64 ≤ 2^64 by omega)
    · simpa only [Hash.vectorByteArray_size] using bufferProtected
  have uLength : read_mem_bytes 8 (r (.GPR 31#5) s + 104#64) u = byteLen.toBitVec := by
    rw [read_frame _ 8 loopPost.frame (by bv_omega)]
    · exact lengthAt
    · right
      intro span member
      simp only [directWrites, List.mem_cons, List.not_mem_nil, or_false] at member
      have low := owned.stackLow
      rcases member with rfl | rfl
      · right; simp only [stackSpan]; bv_omega
      · right; rw [statePointer]; bv_omega
  have separate : Memcpy.Disjoint (r (.GPR 31#5) u) (address + BitVec.ofNat 64 stop) rest := by
    rw [uSP]
    by_cases empty : rest = 0
    · simp only [empty, Memcpy.Disjoint, Nat.add_zero]
      omega
    · have sourceNat : (address + BitVec.ofNat 64 stop).toNat = address.toNat + stop := by
        have physical := owned.physical
        dsimp [stop]
        bv_omega
      rw [Memcpy.Disjoint, sourceNat]
      rcases inputWritable with nil | apart
      · omega
      · have separation := apart ((r (.GPR 31#5) s).toNat, 64) (by simp)
        dsimp [stop]
        omega
  have tailResult := tail_copy_correct side u base address input stop rest buffer
    (code.of_program_eq loopPost.program) loopPost.error (loopPost.aligned aligned) loopPC
    (by rw [uSP]; omega) owned.physical short (by dsimp [stop]; omega) loopOwned.inputAt
    uBuffer loopCursor loopCount separate
  let tailFuel := side.tailOps.length + (Memcpy.fuel rest + 1)
  let t := run tailFuel u
  have tailPost : TailPost side u t base := tailResult.1
  have tailContained : ∀ span ∈ [((r (.GPR 31#5) u).toNat, (r (.GPR side.count) u).toNat)],
      ∃ outer ∈ drainWrites s,
        outer.1 ≤ span.1 ∧ span.1 + span.2 ≤ outer.1 + outer.2 := by
    intro span member
    simp only [List.mem_singleton] at member
    subst span
    refine ⟨((r (.GPR 31#5) s).toNat, 112), by simp [drainWrites], ?_, ?_⟩
    all_goals simp only [uSP, uCount]; omega
  have frame : MemoryFrame (drainWrites s) s t :=
    (frame_mono loopPost.frame directContained).trans (frame_mono tailPost.frame tailContained)
  have resultCount : (r (.GPR side.count) t).toNat = rest := by
    rw [tailPost.registers side.count (by cases side <;> decide)
      (by cases side <;> decide) (by cases side <;> decide)]
    exact loopCount
  have resultWords : ChainingAt t (r (.GPR 31#5) s + 64#64)
      ((List.range q).foldl
        (fun current i => Ssz.Sha256.compress current input (start + 64 * i)) words) := by
    have sourceWords : ChainingAt u (r (.GPR 31#5) s + 64#64)
        ((List.range q).foldl
          (fun current i => Ssz.Sha256.compress current input (start + 64 * i)) words) := by
      rw [← uState]
      exact loopOwned.chaining
    apply sourceWords.frame tailPost.frame (by bv_omega)
    right
    intro span member
    simp only [List.mem_singleton] at member
    subst span
    right
    rw [uSP, loopCount]
    bv_omega
  have resultLength : read_mem_bytes 8 (r (.GPR 31#5) s + 104#64) t = byteLen.toBitVec := by
    rw [read_frame _ 8 tailPost.frame (by bv_omega)]
    · exact uLength
    · right
      intro span member
      simp only [List.mem_singleton] at member
      subst span
      right
      rw [uSP, loopCount]
      bv_omega
  refine ⟨loopFuel + tailFuel, ?_⟩
  rw [run_plus]
  refine ⟨⟨tailPost.pc, tailPost.error, tailPost.program.trans loopPost.program,
      tailPost.sp.trans uSP, ?_, ?_, frame, ?_⟩,
    data.frame frame initialOwned roundsOwned, resultCount, ?_, resultWords, resultLength⟩
  · intro reg lo hi notCount notCursor not25
    exact (tailPost.registers reg lo hi not25).trans
      (loopPost.registers reg lo hi notCount notCursor)
  · intro reg lo hi
    exact (tailPost.vectors reg lo hi).trans (loopPost.vectors reg lo hi)
  · intro left
    exact (tailPost.leftBuffer left).trans uSP
  · simpa only [uSP, SszNative.HashStream.drain, q, rest, stop] using tailResult.2

end SszArm.Hash.Combine
