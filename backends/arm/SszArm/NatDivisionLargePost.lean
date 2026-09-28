import SszArm.NatDivisionLargeArray
import SszArm.NatDivisionSuccessPost
import SszArm.NatDivisionNormalizeStore

namespace SszArm.NatDivision

open Delimited (MemoryFrame)
open UintCodec (widthLoad)
open SszNative.Limbs

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- After the checked cursor commit, execute the entire significant-word copy,
reverse runtime-backed division, normalization, serialization and original RET. -/
theorem large_reserved_post (original s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (reservation : SszNative.Arena.Reservation)
    (owned : Owned original (.large pointer words)) (saved : Saved original s)
    (out : r (.GPR 19#5) s = r (.GPR 0#5) original)
    (hc : JointCodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 452#64)
    (h1 : r (.GPR 1#5) s = pointer)
    (h2 : r (.GPR 2#5) s = BitVec.ofNat 64 words.length)
    (h8 : r (.GPR 8#5) s = BitVec.ofNat 64 (sigWords words))
    (h9 : r (.GPR 9#5) s = 0#64)
    (h20 : r (.GPR 20#5) s = r (.GPR 3#5) original)
    (h22 : r (.GPR 22#5) s = BitVec.ofNat 64 (sigWords words + 1))
    (h23 : r (.GPR 23#5) s = BitVec.ofNat 64 (8 * (sigWords words - 1)))
    (h24 : r (.GPR 24#5) s = BitVec.ofNat 64 reservation.pointer)
    (count : 2 < sigWords words)
    (reserve : SszNative.Arena.reserve (arenaOf original).base (arenaOf original).capacity
      (arenaOf original).used (sigWords words) = some reservation)
    (cursor : (read_mem_bytes 8 (r (.GPR 4#5) original + 16#64) s).toNat = reservation.used)
    (before : MemoryFrame (writesFor original (outcome original (.large pointer words))) original s) :
    ∃ fuel, Post original (run fuel s) (.large pointer words) := by
  let divisor := r (.GPR 3#5) original
  let divided := SszNative.LimbDivision.divideWords divisor (trim words)
  let destination := BitVec.ofNat 64 reservation.pointer
  let quotient := SszNative.NatOperand.fromWords destination divided.1
  let remainder := BitVec.ofNat 64 divided.2
  have source : outcome original (.large pointer words) =
      { result := .ok (quotient, remainder), used := reservation.used,
        allocation := some reservation, written := divided.1 } :=
    SszNative.NatDivision.phase_reserved (.large pointer words) divisor
      (arenaOf original).base (arenaOf original).capacity (arenaOf original).used
      owned.divisor_nonzero owned.divisor_ne_one count reservation reserve
  have allocated : (outcome original (.large pointer words)).allocation = some reservation := by rw [source]
  have writtenLength : (outcome original (.large pointer words)).written.length = sigWords words := by
    rw [source]
    simp only [divided, SszNative.LimbDivision.divideWords_length, trim_length]
  have geometry := owned.allocation_geometry reservation allocated
  have destNat : destination.toNat = reservation.pointer := Nat.mod_eq_of_lt geometry.2.1
  have inputAt := operand_at_preserved before (.large pointer words) owned.operandAt owned.operandOwned
  have inputSource := owned.large_source pointer words saved.sp
  have inputWords := large_words s pointer words inputAt
  have space := owned.loop_space reservation allocated saved.sp
  rw [writtenLength] at space
  have apart : pointer.toNat + 8 * words.length ≤ destination.toNat ∨
      destination.toNat + 8 * sigWords words ≤ pointer.toNat := by
    have nonempty : 0 < words.length := by have h := sigWords_le_length words; omega
    simpa only [destNat, writtenLength] using owned.input_allocation_separate pointer words nonempty reservation allocated
  obtain ⟨fuel, t, executed, frame, pc, status, normalizedPointer, normalizedPayload, rem, finalWords⟩ :=
    large_array_run s base pointer destination divisor words hc he ha hp h1 h2 h8 h9 h20 h22 h23 h24
      (by omega) owned.divisor inputSource inputWords ⟨space.physical, space.apart⟩ apart
  have body : MemoryFrame (bodyWrites original (.large pointer words)) s t := by
    apply payload_body_frame owned reservation allocated saved.sp
    simpa only [writtenLength] using frame.memory
  have full := before.trans (body_frame_full (.large pointer words) body)
  have outT : r (.GPR 19#5) t = r (.GPR 0#5) original := (frame.registers 19#5 (by simp)).trans out
  have savedT : Saved original t := by
    apply saved.body_preserved owned body (frame.registers 31#5 (by simp))
    · intro reg low high
      apply frame.registers
      have member : reg = 25#5 ∨ reg = 26#5 ∨ reg = 27#5 ∨ reg = 28#5 ∨ reg = 29#5 := by bv_omega
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rcases member with rfl | rfl | rfl | rfl | rfl <;> simp
    · intro reg low high
      exact congrArg (BitVec.setWidth 64) (frame.vectors reg)
  have tc : CodeAt t base := by simpa only [CodeAt, frame.program] using hc.1
  have te : read_err t = .None := frame.error.trans he
  have ta : CheckSPAlignment t := by
    simpa only [CheckSPAlignment, state_simp_rules, frame.registers 31#5 (by simp)] using ha
  have writtenT : WrittenAt (widthLoad t) (outcome original (.large pointer words)) := by
    intro res allocated'
    have same : res = reservation := by rw [allocated] at allocated'; exact (Option.some.inj allocated').symm
    subst res
    rw [source]
    change SszNative.NatMemory.wordsAt (widthLoad t) reservation.pointer divided.1
    rw [← destNat]
    exact loopWords_at t destination divided.1 (loopWords_of_words t destination divided.1 finalWords)
  have cursorT : (read_mem_bytes 8 (r (.GPR 4#5) original + 16#64) t).toNat =
      (outcome original (.large pointer words)).used := by
    have physical := owned.arenaBound
    have address : (r (.GPR 4#5) original + 16#64).toNat = (r (.GPR 4#5) original).toNat + 16 := by bv_omega
    have cursorOwned := owned.payload_cursor reservation allocated saved.sp
    rw [writtenLength] at cursorOwned
    rw [frame.memory.read _ 8 (by rw [address]; omega)]
    · rw [source]
      exact cursor
    · simpa only [address] using cursorOwned
  let u := w .PC (base + 800#64) (write_mem_bytes 8 (r (.GPR 19#5) t) quotient.pointer t)
  have storeRun : run 2 t = u := by
    rw [quotient_normalization_store t base tc te ta pc, normalizedPointer]
  have outputBound : (r (.GPR 19#5) t).toNat + 8 ≤ 2^64 := by rw [outT]; have := owned.outputBound; omega
  obtain ⟨storeFrame, storeGpr, storeVector, storeProgram, storeError, storeAligned,
    storePc, pointerStored⟩ := normalization_store_observations t base quotient.pointer outputBound
  have localMemory := output_local_frame owned savedT outT storeFrame
  have savedU : Saved original u := by
    apply savedT.output_preserved owned.stackBound (owned.return_space savedT.sp outT) storeFrame
    · exact storeGpr 31#5
    · intro reg low high
      exact storeGpr reg
    · intro reg low high
      exact congrArg (BitVec.setWidth 64) (storeVector reg)
  have outU : r (.GPR 19#5) u = r (.GPR 0#5) original := (storeGpr 19#5).trans outT
  have writtenU := written_local_preserved owned localMemory writtenT
  have cursorU := cursor_local_preserved owned localMemory cursorT
  have quotientAt : quotient.At (widthLoad u) := by
    simpa only [source] using allocated_operand_at owned reservation allocated writtenU
  have quotientOwned : OperandOwned (returnWrites u) quotient := by
    simpa only [source] using allocated_operand_owned owned reservation allocated savedU.sp outU
  have payloadU : r (.GPR 10#5) u = quotient.payload := (storeGpr 10#5).trans normalizedPayload
  have remU : r (.GPR 1#5) u = remainder := by
    have h := congrArg (BitVec.ofNat 64) rem
    have value : r (.GPR 1#5) t = remainder := by
      simpa only [remainder, divided, BitVec.ofNat_toNat, BitVec.setWidth_eq] using h
    exact (storeGpr 1#5).trans value
  have statusU : (r (.GPR 8#5) u).setWidth 32 = 0#32 := by rw [storeGpr 8#5, status]; rfl
  have uc : CodeAt u base := by
    have program : u.program = t.program := storeProgram
    simpa only [CodeAt, program] using tc
  have ue : read_err u = .None := storeError.trans te
  have ua : CheckSPAlignment u := storeAligned ta
  have up : read_pc u = base + 800#64 := storePc
  have post := normalized_result_post original u base (.large pointer words) quotient remainder owned
    savedU outU uc ue ua up (by rw [source]) pointerStored payloadU remU statusU quotientAt quotientOwned
    writtenU cursorU (full.trans (local_frame_for (outcome original (.large pointer words)) localMemory))
  refine ⟨fuel + 2 + 16, ?_⟩
  rw [run_plus, run_plus, executed, storeRun]
  exact post

end SszArm.NatDivision
