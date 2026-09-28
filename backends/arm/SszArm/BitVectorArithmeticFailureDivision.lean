import SszArm.BitVectorArithmeticFailureCommon

namespace SszArm.BitVector.ArithmeticFailure

open UintCodec (widthLoad)
open Delimited (MemoryFrame)

private def divisionImage (t : ArmState) (out textPointer textLength firstPointer : BitVec 64)
    (code padding : BitVec 32) : ArmState :=
  write_mem_bytes 16 out (textPointer ++ 1#64)
    (write_mem_bytes 8 (out + 72#64) (padding ++ code)
      (write_mem_bytes 16 (out + 16#64) (firstPointer ++ textLength) t))

private theorem division_image_fields (t : ArmState)
    (out textPointer textLength firstPointer : BitVec 64) (code padding : BitVec 32)
    (physical : out.toNat + 80 ≤ 2^64) :
    let image := divisionImage t out textPointer textLength firstPointer code padding
    widthLoad image out.toNat 8 = some 1 ∧
    widthLoad image (out.toNat + 8) 8 = some textPointer.toNat ∧
    widthLoad image (out.toNat + 16) 8 = some textLength.toNat ∧
    widthLoad image (out.toNat + 24) 8 = some firstPointer.toNat ∧
    widthLoad image (out.toNat + 72) 4 = some code.toNat ∧
    (∀ offset bytes, offset + bytes ≤ 40 →
      widthLoad image (out.toNat + 32 + offset) bytes =
        widthLoad t (out.toNat + 32 + offset) bytes) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first | intro offset bytes within | skip
  all_goals
    simp only [widthLoad, divisionImage, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    simp (config := {decide := true}) (disch := failure_side) only
      [UintCodec.Tail.write_pair_words, write_pair32, BitVec.add_assoc,
       BitVec.ofNat_add_ofNat, Nat.reduceAdd, show (1#64).toNat = 1 by decide,
       BoolCodec.read_mem_bytes_write_mem_bytes_same,
       BoolCodec.read_mem_bytes_write_mem_bytes_disjoint]

private theorem division_fields (t : ArmState) (base : BitVec 64)
    (physical : (r (.GPR 23#5) t).toNat + 80 ≤ 2^64) :
    widthLoad (ErrorTail.Tail.division.result t base) (r (.GPR 23#5) t).toNat 8 = some 1 ∧
    widthLoad (ErrorTail.Tail.division.result t base) ((r (.GPR 23#5) t).toNat + 8) 8 =
      some (read_mem_bytes 8 (r (.GPR 31#5) t + 64#64) t).toNat ∧
    widthLoad (ErrorTail.Tail.division.result t base) ((r (.GPR 23#5) t).toNat + 16) 8 =
      some (read_mem_bytes 8 (r (.GPR 31#5) t + 72#64) t).toNat ∧
    widthLoad (ErrorTail.Tail.division.result t base) ((r (.GPR 23#5) t).toNat + 24) 8 =
      some (r (.GPR 25#5) t).toNat ∧
    widthLoad (ErrorTail.Tail.division.result t base) ((r (.GPR 23#5) t).toNat + 72) 4 =
      some ((r (.GPR 26#5) t).setWidth 32).toNat ∧
    (∀ offset bytes, offset + bytes ≤ 40 →
      widthLoad (ErrorTail.Tail.division.result t base)
          ((r (.GPR 23#5) t).toNat + 32 + offset) bytes =
        widthLoad t ((r (.GPR 23#5) t).toNat + 32 + offset) bytes) := by
  have fields := division_image_fields t (r (.GPR 23#5) t)
    (read_mem_bytes 8 (r (.GPR 31#5) t + 64#64) t)
    (read_mem_bytes 8 (r (.GPR 31#5) t + 72#64) t)
    (r (.GPR 25#5) t) ((r (.GPR 26#5) t).setWidth 32)
    (read_mem_bytes 4 (r (.GPR 31#5) t + 212#64)
      (write_mem_bytes 16 (r (.GPR 23#5) t + 16#64)
        (r (.GPR 25#5) t ++ read_mem_bytes 8 (r (.GPR 31#5) t + 72#64) t) t)) physical
  simpa (config := {decide := true}) only
    [widthLoad, divisionImage, ErrorTail.Tail.result, state_simp_rules] using fields

/-- All branch-controlling and saved private fields come from the completed
helper's object. Both Failure constructors produce the nonzero native status. -/
private theorem division_frontier {s d : ArmState} {base : BitVec 64}
    {length : SszNative.NatOperand} {data : Ssz.Bytes}
    {reason : SszNative.NatArithmetic.Failure}
    (owned : Owned s length data) (current : Working s d length)
    (post : NatDivision.Post (divisionEntry s base) d length)
    (failure : (outcome s length data).divided.result = .error reason) :
    read_pc (Block.divisionStatusResult d base) = base + 492#64 ∧
    r (.GPR 25#5) (Block.divisionStatusResult d base) = 0#64 ∧
    (r (.GPR 26#5) (Block.divisionStatusResult d base)).setWidth 32 = status reason ∧
    read_mem_bytes 8 (r (.GPR 31#5) s + 64#64) (Block.divisionStatusResult d base) = 1#64 ∧
    read_mem_bytes 8 (r (.GPR 31#5) s + 72#64) (Block.divisionStatusResult d base) = 0#64 ∧
    SszNative.NatArithmetic.errorAt (widthLoad d) (r (.GPR 31#5) s + 144#64).toNat reason := by
  have args := division_arguments s base length data owned
  have stored := post.result
  rw [division_outcome s base length data owned, failure, args.out] at stored
  change SszNative.NatArithmetic.errorAt (widthLoad d)
    (r (.GPR 31#5) s + 144#64).toNat reason at stored
  have pointer : read_mem_bytes 8 (r (.GPR 31#5) s + 144#64) d = 1#64 := by
    simpa only [Nat.add_zero, BitVec.add_zero] using
      read_of_observe_offset d (r (.GPR 31#5) s + 144#64) 0 8 1#64
        (by simpa only [Nat.add_zero, show (1#64).toNat = 1 by decide] using stored.1)
  have payload : read_mem_bytes 8 (r (.GPR 31#5) s + 152#64) d = 0#64 := by
    simpa only [BitVec.add_assoc, show 144#64 + 8#64 = 152#64 by decide] using
      read_of_observe_offset d (r (.GPR 31#5) s + 144#64) 8 8 0#64 stored.2.1
  have remainder : read_mem_bytes 8 (r (.GPR 31#5) s + 160#64) d = 0#64 := by
    simpa only [BitVec.add_assoc, show 144#64 + 16#64 = 160#64 by decide] using
      read_of_observe_offset d (r (.GPR 31#5) s + 144#64) 16 8 0#64 stored.2.2.1
  have loaded : read_mem_bytes 4 (r (.GPR 31#5) s + 208#64) d = status reason := by
    simpa only [BitVec.add_assoc, show 144#64 + 64#64 = 208#64 by decide] using error_status stored
  have high := owned.stackHigh
  refine ⟨?_, ?_, ?_, ?_, ?_, stored⟩
  · cases reason <;>
      simp (config := {decide := true}) [Block.divisionStatusResult, state_simp_rules,
        current.sp, loaded, status]
  · simp (config := {decide := true}) only [Block.divisionStatusResult, state_simp_rules,
      current.sp, remainder]
  · cases reason <;>
      simp (config := {decide := true}) [Block.divisionStatusResult, state_simp_rules,
        current.sp, loaded, status]
  · simp only [Block.divisionStatusResult, state_simp_rules, current.sp, pointer, payload]
    exact read_pair_written_low _ _ _ _ (by bv_omega)
  · simp only [Block.divisionStatusResult, state_simp_rules, current.sp, pointer, payload]
    have upper := read_pair_written_high
      (w (.GPR 25#5) (read_mem_bytes 8 (r (.GPR 31#5) s + 160#64) d)
        (w (.GPR 26#5) ((read_mem_bytes 4 (r (.GPR 31#5) s + 208#64) d).setWidth 64)
          (w (.GPR 9#5) 0#64 (w (.GPR 8#5) 1#64 d))))
      (r (.GPR 31#5) s + 64#64) 0#64 1#64 (by bv_omega)
    simpa only [BitVec.add_assoc, show 64#64 + 8#64 = 72#64 by decide] using upper

/-- Division's native error exit copies exactly forty bytes, reconstructs the
three preceding words from the actual saved pair/remainder, and copies the
private status padding in the final paired store. -/
theorem division_failure {s d : ArmState} {base : BitVec 64}
    {length : SszNative.NatOperand} {data : Ssz.Bytes}
    {reason : SszNative.NatArithmetic.Failure}
    (owned : Owned s length data) (current : Working s d length)
    (post : NatDivision.Post (divisionEntry s base) d length)
    (failure : (outcome s length data).divided.result = .error reason)
    (code : JointCodeAt (Block.divisionStatusResult d base) base)
    (aligned : CheckSPAlignment s) :
    ∃ fuel final, run fuel (Block.divisionStatusResult d base) = final ∧
      Terminal s final base data (.error (.arithmetic reason)) ∧
      MemoryFrame (localWrites s) (Block.divisionStatusResult d base) final := by
  let a := Block.divisionStatusResult d base
  obtain ⟨aPC, a25, a26, a64, a72, stored⟩ := division_frontier owned current post failure
  have aCurrent : Registers s a := registers (current.after_status base)
  have privatePointer := division_private_register post
  let b := Stages.CallPreparation.divisionError.result a base
  have prepare : run 3 a = b := Stages.prepare .divisionError a base code.body
    aCurrent.error (aCurrent.aligned aligned) aPC
  have bCurrent := aCurrent.prepare .divisionError base
  have bCode : JointCodeAt b base := by rw [← prepare]; exact code.run _
  have bPC : read_pc b = base + 504#64 := by
    simp only [b, Stages.CallPreparation.result, Stages.CallPreparation.stop, state_simp_rules]
  have b0 : r (.GPR 0#5) b = r (.GPR 0#5) s + 32#64 := by
    simp (config := {decide := true}) [b, Stages.CallPreparation.result, state_simp_rules, aCurrent.output]
  have b1 : r (.GPR 1#5) b = r (.GPR 31#5) s + 168#64 := by
    simp (config := {decide := true}) [b, Stages.CallPreparation.result, state_simp_rules,
      a, privatePointer, BitVec.add_assoc]
  have b2 : r (.GPR 2#5) b = 40#64 := by
    simp (config := {decide := true}) [b, Stages.CallPreparation.result, state_simp_rules]
  obtain ⟨destination, source, separate⟩ := output_copy_space owned 32 168 40
    (by decide) (by decide) (by decide)
  obtain ⟨fuel, t, execution, copied⟩ := memcpy_correct .divisionError b base
    (Or.inl rfl) bCode bCurrent.error bPC
    (by simpa only [b0, b2, show (40#64).toNat = 40 by decide] using destination)
    (by simpa only [b1, b2, show (40#64).toNat = 40 by decide] using source)
    (by simpa only [b0, b1, b2, show (40#64).toNat = 40 by decide] using separate)
  have tCurrent := bCurrent.copy copied
  have tCode : JointCodeAt t base := by rw [← execution]; exact bCode.run _
  have tail : run 7 t = ErrorTail.Tail.division.result t base := ErrorTail.executes .division t base
    tCode.body tCurrent.error (tCurrent.aligned aligned) copied.returned
  have finalCurrent := tCurrent.tail .division base
  have whole : run (3 + (fuel + 7)) a = ErrorTail.Tail.division.result t base := by
    rw [run_plus, prepare, run_plus, execution, tail]
  have stackHigh := owned.stackHigh
  have outputBound := owned.outputBound
  have out32 : (r (.GPR 0#5) s + 32#64).toNat = (r (.GPR 0#5) s).toNat + 32 := by bv_omega
  have sp168 : (r (.GPR 31#5) s + 168#64).toNat =
      (r (.GPR 31#5) s + 144#64).toNat + 24 := by bv_omega
  have stackOutput : (r (.GPR 0#5) s).toNat + 80 ≤ (r (.GPR 31#5) s).toNat - 80 ∨
      (r (.GPR 31#5) s).toNat + 368 ≤ (r (.GPR 0#5) s).toNat := by
    have low := owned.stackLow
    rcases owned.outputStack with empty | separate
    · omega
    · have disjoint := separate ((r (.GPR 31#5) s).toNat - 80, 448) (by simp)
      omega
  have stackKept : ∀ offset, offset + 8 ≤ 272 →
      read_mem_bytes 8 (r (.GPR 31#5) s + BitVec.ofNat 64 offset) t =
        read_mem_bytes 8 (r (.GPR 31#5) s + BitVec.ofNat 64 offset) a := by
    intro offset within
    have preserved := copied.frame.read (r (.GPR 31#5) s + BitVec.ofNat 64 offset) 8
      (by bv_omega) (Or.inr (by
        intro span member
        simp only [List.mem_singleton] at member
        subst span
        simp only [b0, b2, show (40#64).toNat = 40 by decide]
        bv_omega))
    rw [preserved]
    simp only [b, Memory.State.read_mem_bytes_eq_mem_read_bytes, preparation_memory]
  have t64 : read_mem_bytes 8 (r (.GPR 31#5) t + 64#64) t = 1#64 := by
    rw [tCurrent.sp, stackKept 64 (by decide)]
    exact a64
  have t72 : read_mem_bytes 8 (r (.GPR 31#5) t + 72#64) t = 0#64 := by
    rw [tCurrent.sp, stackKept 72 (by decide)]
    exact a72
  have t25 : r (.GPR 25#5) t = 0#64 := by
    rw [copied.registers 25#5 (by decide) (by decide)]
    simpa (config := {decide := true}) only [b, Stages.CallPreparation.result, state_simp_rules] using a25
  have t26 : (r (.GPR 26#5) t).setWidth 32 = status reason := by
    rw [copied.registers 26#5 (by decide) (by decide)]
    simpa (config := {decide := true}) only [b, Stages.CallPreparation.result, state_simp_rules] using a26
  have copyFields : ∀ offset bytes, offset + bytes ≤ 40 →
      widthLoad t ((r (.GPR 0#5) s).toNat + 32 + offset) bytes =
        widthLoad d ((r (.GPR 31#5) s + 144#64).toNat + 24 + offset) bytes := by
    intro offset bytes within
    have loaded := copied.copied offset bytes
      (by simpa only [b2, show (40#64).toNat = 40 by decide] using within)
    simp only [b0, b1, out32, sp168, b, preparation_observe] at loaded
    rw [loaded]
    simp only [widthLoad, a, Block.divisionStatusResult, state_simp_rules, current.sp]
    simp (disch := failure_side) only [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint]
    simp only [state_simp_rules]
  obtain ⟨tag, textPointer, textLength, firstPointer, finalStatus, preserved⟩ :=
    division_fields t base (by rw [tCurrent.output]; exact outputBound)
  rw [tCurrent.output] at tag textPointer textLength firstPointer finalStatus preserved
  rw [t64] at textPointer
  rw [t72] at textLength
  rw [t25] at firstPointer
  rw [t26] at finalStatus
  have field : ∀ offset bytes, offset + bytes ≤ 40 →
      widthLoad (ErrorTail.Tail.division.result t base)
          ((r (.GPR 0#5) s).toNat + 32 + offset) bytes =
        widthLoad d ((r (.GPR 31#5) s + 144#64).toNat + 24 + offset) bytes := by
    intro offset bytes within
    exact (preserved offset bytes within).trans (copyFields offset bytes within)
  have finalStored : SszNative.NatArithmetic.errorAt
      (widthLoad (ErrorTail.Tail.division.result t base)) ((r (.GPR 0#5) s).toNat + 8) reason := by
    refine ⟨textPointer, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [Nat.add_assoc] using textLength
    · simpa [Nat.add_assoc] using firstPointer
    · simpa only [Nat.add_zero, Nat.add_assoc, Nat.reduceAdd] using
        (field 0 8 (by decide)).trans (by simpa only [Nat.add_zero] using stored.2.2.2.1)
    · simpa only [Nat.add_assoc, Nat.reduceAdd] using
        (field 8 8 (by decide)).trans (by simpa only [Nat.add_assoc, Nat.reduceAdd] using stored.2.2.2.2.1)
    · simpa only [Nat.add_assoc, Nat.reduceAdd] using
        (field 16 8 (by decide)).trans (by simpa only [Nat.add_assoc, Nat.reduceAdd] using stored.2.2.2.2.2.1)
    · simpa only [Nat.add_assoc, Nat.reduceAdd] using
        (field 24 8 (by decide)).trans (by simpa only [Nat.add_assoc, Nat.reduceAdd] using stored.2.2.2.2.2.2.1)
    · simpa only [Nat.add_assoc, Nat.reduceAdd] using
        (field 32 8 (by decide)).trans (by simpa only [Nat.add_assoc, Nat.reduceAdd] using stored.2.2.2.2.2.2.2.1)
    · cases reason <;> simpa [status, Nat.add_assoc] using finalStatus
  have initial : MemoryFrame (localWrites s) a b := frame_of_memory (preparation_memory _ _ _)
  have middle : MemoryFrame (localWrites s) b t :=
    (output_copy_covered owned 32 40 (by decide) (by decide)).frame
      (by simpa only [b0, b2, show (40#64).toNat = 40 by decide] using copied.frame)
  refine ⟨_, _, whole, ⟨?_, finalCurrent.error, finalCurrent.sp,
    finalCurrent.vectors, error_result finalStored tag⟩,
    (initial.trans middle).trans (tail_frame owned tCurrent .division base)⟩
  simp only [ErrorTail.Tail.result, ErrorTail.Tail.stop, state_simp_rules]

end SszArm.BitVector.ArithmeticFailure
