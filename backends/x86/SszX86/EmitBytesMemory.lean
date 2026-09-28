import SszX86.EmitBytesStart
import SszX86.EmitBitsFinishMemory

namespace SszX86.Emit.Bytes
open BoolCodec UintCodec

structure Owned (s : MachineData) (bytes : Ssz.Bytes) (src : BitVec 64) : Prop where
  tag : s.regs.rax.toBitVec = 2#64 ∨ s.regs.rax.toBitVec = 3#64
  capacity : bytes.size ≤ s.regs.r9.toNat
  length : Mem.loadInt s.dmem (s.regs.r12.toBitVec + 16) 8 = some (bytes.size : Int)
  pointer : Mem.loadInt s.dmem (s.regs.r12.toBitVec + 8) 8 = some (src.toNat : Int)
  source : BytesAt s.dmem src bytes
  output : Large.Mapped s.dmem s.regs.r14.toBitVec bytes.size
  result : Large.Mapped s.dmem s.regs.rbx.toBitVec 8
  stack : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 8) 8
  outputResult : Large.Disjoint s.regs.r14.toBitVec s.regs.rbx.toBitVec bytes.size 8
  outputStack : Large.Disjoint s.regs.r14.toBitVec (s.regs.rsp.toBitVec - 8) bytes.size 8
  resultStack : Large.Disjoint s.regs.rbx.toBitVec (s.regs.rsp.toBitVec - 8) 8 8
  sourceOutput : Large.Disjoint src s.regs.r14.toBitVec bytes.size bytes.size
  sourceStack : Large.Disjoint src (s.regs.rsp.toBitVec - 8) bytes.size 8

def ready (s : MachineData) (bytes : Ssz.Bytes) (src : BitVec 64) : MachineData :=
  copyReady (compared (lengthLoaded (tagged s) bytes.size)) src

theorem Owned.bound {s : MachineData} {bytes : Ssz.Bytes} {src : BitVec 64}
    (owned : Owned s bytes src) : bytes.size < 2 ^ 64 :=
  Nat.lt_of_le_of_lt owned.capacity s.regs.r9.toBitVec.isLt

theorem copied_anchors (s : MachineData) (bytes : Ssz.Bytes) (src ra : BitVec 64)
    (t : MachineState) (post : CopyPost (ready s bytes src) ra bytes.toList t) :
    t.1.regs.rsp = s.regs.rsp ∧ t.1.regs.rbx = s.regs.rbx ∧
    t.1.regs.r13 = UInt64.ofNat bytes.size ∧ t.1.zmms = s.zmms := by
  have regs := post.returned.2.2.2.2
  refine ⟨?_, ?_, ?_, post.returned.2.2.2.1⟩
  · apply UInt64.toBitVec_inj.1
    have stack := post.returned.2.2.1
    change t.1.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 8 + 8#64 at stack
    bv_omega
  · apply UInt64.toBitVec_inj.1
    have kept := regs .rbx (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
    simpa only [Reg64s.get64, callState, ready, copyReady, compared, lengthLoaded, tagged] using kept
  · apply UInt64.toBitVec_inj.1
    have kept := regs .r13 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
    simpa only [Reg64s.get64, callState, ready, copyReady, compared, lengthLoaded, tagged] using kept

theorem copied_frame (s : MachineData) (bytes : Ssz.Bytes) (src ra : BitVec 64)
    (t : MachineState) (post : CopyPost (ready s bytes src) ra bytes.toList t) :
    MemoryFrame s.dmem t.1.dmem (BodyWritable s bytes.size) := by
  intro a outside
  apply post.frame a
  rintro (output | slot)
  · apply outside
    left
    simpa only [ready, copyReady, compared, lengthLoaded, tagged, Array.length_toList] using output
  · obtain ⟨i, hi, equal⟩ := slot
    exact outside (Or.inr (Or.inr ⟨i, by omega, equal⟩))

theorem copied_result_mapped (s : MachineData) (bytes : Ssz.Bytes) (src ra : BitVec 64)
    (owned : Owned s bytes src) (t : MachineState)
    (post : CopyPost (ready s bytes src) ra bytes.toList t) :
    Large.Mapped t.1.dmem t.1.regs.rbx.toBitVec 8 := by
  rw [(copied_anchors s bytes src ra t post).2.1]
  intro i hi
  rw [post.frame]
  · exact owned.result i hi
  · rintro (output | slot)
    · obtain ⟨j, hj, equal⟩ := output
      apply owned.outputResult j (by simpa only [Array.length_toList] using hj) i hi
      exact equal.symm
    · obtain ⟨j, hj, equal⟩ := slot
      exact owned.resultStack i hi j hj equal

theorem copied_post (s : MachineData) (bytes : Ssz.Bytes) (src ra : BitVec 64)
    (owned : Owned s bytes src) (t : MachineState)
    (post : CopyPost (ready s bytes src) ra bytes.toList t) :
    BodyPost s bytes (written t.1) := by
  obtain ⟨stack, result, count, vector⟩ := copied_anchors s bytes src ra t post
  have output : BytesAt t.1.dmem s.regs.r14.toBitVec bytes := by
    intro i hi
    have copied := post.output i (by simpa only [Array.length_toList] using hi)
    rw [Array.getElem?_toList, Array.getElem?_eq_getElem hi] at copied
    simpa only [ready, copyReady, compared, lengthLoaded, tagged] using copied
  have final := Bits.length_post s t.1 bytes owned.bound stack result vector output
    (copied_frame s bytes src ra t post) owned.outputResult
  simpa only [Bits.lengthStored, written, count, UInt64.toBitVec_ofNat'] using final

end SszX86.Emit.Bytes
