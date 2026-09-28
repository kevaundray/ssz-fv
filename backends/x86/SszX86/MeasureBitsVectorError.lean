import SszX86.MeasureBitsVectorCheck
import SszX86.MeasureBitsVectorNoAlloc
import SszX86.MeasureBitsVectorCommit
import SszX86.MeasureBitsScope
import SszX86.MeasureOutput

namespace SszX86.Measure.Bits
open SszNative SszNative.Serialize UintCodec

def vectorInput (s : MachineData) (expected : NatOperand) (bits : Packed) : MachineData :=
  vectorLoaded s expected.pointer expected.payload
    (bits.count.setWidth 64) ((bits.count >>> 64).setWidth 64)

private theorem allocated_scope_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s u : MachineData) (expected : NatOperand) (bits : Packed)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s (.bitVector expected) (.bits bits) buffer address capacity used)
    (mismatch : expected.value ≠ bits.count.toNat)
    (large : ¬ bits.count.toNat < 2^64) (r : Arena.Reservation)
    (reserved : Arena.reserve address.toNat capacity.toNat used.toNat 2 = some r)
    (memory : u.dmem = vectorCommitMem s r bits.count)
    (outputReg : u.regs.rbx = s.regs.rbx)
    (descriptorReg : u.regs.rsi = s.regs.rsi)
    (actualPointer : u.regs.rcx.toBitVec = BitVec.ofNat 64 r.pointer)
    (actualPayload : u.regs.rax.toBitVec = 2#64)
    (stackReg : u.regs.rsp = s.regs.rsp) (vectors : u.zmms = s.zmms) :
    Eventually (step e)
      (fun t => t.2 = base + 3335 ∧ BodyPost s (.bitVector expected) (.bits bits)
        buffer address capacity used t.1)
      (u, base + 2893) := by
  have descriptorWords := nat_loads (vectorCommitMem s r bits.count)
    (s.regs.rsi.toBitVec + 8#64) expected
    (vector_commit_inputs s expected bits buffer address capacity used owned r reserved).1.2
  apply scope_publish_cps e base hc u expected.pointer expected.payload
  · change Large.Mapped u.dmem u.regs.rbx.toBitVec 72
    rw [memory, outputReg]
    unfold vectorCommitMem NatFromU128.commitMem
    repeat' first | exact owned.resultMapped | apply Large.mapped_store
  · simpa only [memory, descriptorReg] using descriptorWords.1
  · simpa only [memory, descriptorReg, BitVec.add_assoc, BitVec.reduceAdd] using descriptorWords.2
  intro publishFlags
  apply Eventually.done
  refine ⟨rfl, ?_⟩
  apply vector_allocated_scope_post s _ expected bits buffer address capacity used owned mismatch large r reserved
  · simp only [scopeFinal, scopePrepared, memory, outputReg, actualPointer, actualPayload]
  · exact stackReg
  · exact vectors

/-- All actual count-construction outcomes after a failed vector comparison.
The original ownership supplies every load/store and survives committed Scope. -/
theorem vector_error_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (expected : NatOperand) (bits : Packed)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s (.bitVector expected) (.bits bits) buffer address capacity used)
    (mismatch : expected.value ≠ bits.count.toNat)
    (frame : VectorReadFrame (vectorInput s expected bits) t) :
    Eventually (step e)
      (fun u => u.2 = base + 3335 ∧ BodyPost s (.bitVector expected) (.bits bits)
        buffer address capacity used u.1)
      (t, base + 2805) := by
  have words := nat_loads s.dmem (s.regs.rsi.toBitVec + 8#64) expected owned.descriptor.2
  have memory : t.dmem = s.dmem := frame.memory
  have outputReg : t.regs.rbx = s.regs.rbx := frame.output
  have descriptorReg : t.regs.rsi = s.regs.rsi := frame.descriptor
  have arenaReg : t.regs.rcx = s.regs.rcx := frame.arena
  have stackReg : t.regs.rsp = s.regs.rsp := frame.stack
  have vectors : t.zmms = s.zmms := frame.vectors
  have lowCount : t.regs.rax.toBitVec = bits.count.setWidth 64 := by
    simpa only [vectorInput, vectorLoaded, UInt64.toBitVec_ofBitVec] using congrArg UInt64.toBitVec frame.low
  have highCount : t.regs.rdx.toBitVec = (bits.count >>> 64).setWidth 64 := by
    simpa only [vectorInput, vectorLoaded, UInt64.toBitVec_ofBitVec] using congrArg UInt64.toBitVec frame.high
  have outputMapped : OutputMapped t := by simpa only [OutputMapped, memory, outputReg] using owned.resultMapped
  have header := arena_loads s.dmem s.regs.rcx.toBitVec address capacity used owned.arena
  apply vector_mismatch_high_cps e base hc
  intro flags
  by_cases small : bits.count.toNat < 2^64
  · have zero := (NatFromU128.wide_small_iff bits.count).1 small
    simp only [highCount, zero, ↓reduceIte]
    apply vector_small_error_cps e base hc
    intro zeroFlags
    apply scope_publish_cps e base hc (pointer := expected.pointer) (payload := expected.payload)
    · exact outputMapped
    · simpa only [memory, descriptorReg] using words.1
    · simpa only [memory, descriptorReg, BitVec.add_assoc, BitVec.reduceAdd] using words.2
    intro publishFlags
    apply Eventually.done
    refine ⟨rfl, ?_⟩
    apply vector_small_scope_post s _ expected bits buffer address capacity used owned mismatch small
    · simp only [scopeFinal, scopePrepared, memory, outputReg, lowCount]
      rfl
    · exact stackReg
    · exact vectors
  · have nonzero : (bits.count >>> 64).setWidth 64 ≠ 0#64 := by
      intro zero
      exact small ((NatFromU128.wide_small_iff bits.count).2 zero)
    simp only [highCount, nonzero, ↓reduceIte]
    apply eventually_trans (step e)
      (VectorReservation.Post {t with status := flags} base address capacity used) _ _
      (VectorReservation.runs e base hc {t with status := flags} address capacity used
        ⟨by simpa only [memory, arenaReg] using header.1,
          by simpa only [memory, arenaReg] using header.2.1,
          by simpa only [memory, arenaReg] using header.2.2⟩)
    rintro ⟨u, pc⟩ ⟨reservationFrame, branch⟩
    rcases branch with ⟨failed, rfl⟩ | ⟨r, reserved, rfl, readyFlags, rfl⟩
    · have outReg : u.regs.rbx = t.regs.rbx := UInt64.eq_of_toBitVec_eq
        (reservationFrame.registers .rbx (by decide) (by decide) (by decide) (by decide))
      have spReg : u.regs.rsp = t.regs.rsp := UInt64.eq_of_toBitVec_eq
        (reservationFrame.registers .rsp (by decide) (by decide) (by decide) (by decide))
      have unchangedMemory : u.dmem = t.dmem := reservationFrame.memory
      apply scratch_cps e base hc
      · simpa only [OutputMapped, unchangedMemory, outReg] using outputMapped
      apply Eventually.done
      refine ⟨rfl, ?_⟩
      apply vector_scratch_post s _ expected bits buffer address capacity used owned mismatch small failed
      · simp only [unchangedMemory, memory, outReg, outputReg]
      · exact spReg.trans stackReg
      · exact reservationFrame.vectors.trans vectors
    · obtain ⟨checks, shape⟩ := (Arena.reserve_eq_some_iff_checks _ _ _ 2 (by decide) r).1 reserved
      have pointerWord : address + BitVec.ofNat 64 (Arena.start address.toNat used.toNat) =
          BitVec.ofNat 64 r.pointer := by
        rw [shape]
        simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      have cursorWord : BitVec.ofNat 64 (Arena.start address.toNat used.toNat + 16) =
          BitVec.ofNat 64 r.used := by
        rw [shape]
        rfl
      let ready := VectorReservation.Ready {t with status := flags} address used readyFlags
      have committedMemory : (VectorReservation.committed ready).dmem = vectorCommitMem s r bits.count := by
        simp only [VectorReservation.committed, ready, VectorReservation.Ready,
          vectorCommitMem, memory, arenaReg, lowCount, highCount,
          UInt64.toBitVec_ofBitVec, UInt64.toBitVec_ofNat', pointerWord, cursorWord]
      have committedOut : (VectorReservation.committed ready).regs.rbx = s.regs.rbx := outputReg
      have committedDescriptor : (VectorReservation.committed ready).regs.rsi = s.regs.rsi := descriptorReg
      have committedPointer : (VectorReservation.committed ready).regs.rcx.toBitVec = BitVec.ofNat 64 r.pointer := by
        simpa only [VectorReservation.committed, ready, VectorReservation.Ready,
          UInt64.toBitVec_ofBitVec, UInt64.toBitVec_ofNat'] using pointerWord
      have committedPayload : (VectorReservation.committed ready).regs.rax.toBitVec = 2#64 := rfl
      apply VectorReservation.commit_cps e base hc
      · exact ⟨_, by simpa only [VectorReservation.Ready, memory, arenaReg] using header.2.2⟩
      · simpa only [VectorReservation.Ready, UInt64.toBitVec_ofBitVec,
          UInt64.toBitVec_ofNat', pointerWord, memory] using
          reserve_mapped s _ _ buffer address capacity used owned r reserved
      exact allocated_scope_cps e base hc s (VectorReservation.committed ready) expected bits
        buffer address capacity used owned mismatch small r reserved committedMemory committedOut
        committedDescriptor committedPointer committedPayload stackReg vectors

end SszX86.Measure.Bits
