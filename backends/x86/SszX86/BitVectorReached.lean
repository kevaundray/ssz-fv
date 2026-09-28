import SszX86.BitVectorDivisionWorldPhase
import SszX86.BitVectorHelperStack

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

/-- Only stable body registers and physically retained cache loads are recorded.
The original borrowed source remains explicit even when its length is zero. -/
structure Anchors (s u : MachineData) (length : NatOperand) : Prop where
  stack : u.regs.rsp = s.regs.rsp
  arena : u.regs.rbx = s.regs.rbx
  count : u.regs.r14 = s.regs.r14
  pointer : u.regs.r15.toBitVec = length.pointer
  payload : u.regs.r12.toBitVec = length.payload
  outputCache : Mem.loadInt u.dmem (s.regs.rsp.toBitVec + 8#64) 8 = some (s.regs.rdi.toNat : Int)
  sourceCache : Mem.loadInt u.dmem (s.regs.rsp.toBitVec + 104#64) 8 = some (s.regs.rdx.toNat : Int)

theorem Anchors.fixed {s u v : MachineData} {length : NatOperand}
    (h : Anchors s u length) (fixed : Fixed u v)
    (outputCache : Mem.loadInt v.dmem (s.regs.rsp.toBitVec + 8#64) 8 = some (s.regs.rdi.toNat : Int))
    (sourceCache : Mem.loadInt v.dmem (s.regs.rsp.toBitVec + 104#64) 8 = some (s.regs.rdx.toNat : Int)) :
    Anchors s v length := by
  refine ⟨fixed.stack.trans h.stack, fixed.arena.trans h.arena,
    fixed.length.trans h.count, ?_, ?_, outputCache, sourceCache⟩
  · rw [fixed.pointer]
    exact h.pointer
  · rw [fixed.payload]
    exact h.payload

theorem Owned.body_mapped {s : MachineData} {saved : Saved} {length : NatOperand}
    {data : Ssz.Bytes} {address capacity used : BitVec 64}
    (owned : Owned s saved length data address capacity used) :
    Large.Mapped s.dmem s.regs.rsp.toBitVec 224 := by
  have part := mapped_subrange s.dmem (s.regs.rsp.toBitVec - 72#64) workSize 72 224
    owned.work_mapped (by decide)
  have location : s.regs.rsp.toBitVec - 72#64 + BitVec.ofNat 64 72 = s.regs.rsp.toBitVec := by bv_omega
  rw [location] at part
  exact part

structure DivisionReached (base : Int64) (s : MachineData) (saved : Saved)
    (length : NatOperand) (data : Ssz.Bytes) (address capacity used : BitVec 64)
    (t : MachineState) : Prop where
  post : NatDivision.Post (divisionReady s length (base + 157).toBitVec) length 8
    address capacity used (base + 157).toBitVec t
  world : World s saved length data address capacity used
    (outcomeCursor (SszNative.NatDivision.run length 8 address.toNat capacity.toNat used.toNat))
    (SszNative.BitVector.allocationWrites
      (SszNative.NatDivision.run length 8 address.toNat capacity.toNat used.toNat)) t.1.dmem
  anchors : Anchors s t.1 length

theorem division_reached (e : Executable) (base : Int64) (hc : JointCodeAt e base)
    (s : MachineData) (saved : Saved) (length : NatOperand) (data : Ssz.Bytes)
    (address capacity used : BitVec 64) (owned : Owned s saved length data address capacity used) :
    Eventually (step e) (DivisionReached base s saved length data address capacity used)
      (s, base + 115) := by
  apply eventually_trans (step e) _ _ _
    (division_world_phase e base hc s saved length data address capacity used owned)
  intro t result
  apply Eventually.done
  rcases result with ⟨post, world, fixed⟩
  have initial := entry_world s saved length data address capacity used (base + 157).toBitVec owned
  have helper := division_owned s saved length data address capacity used (base + 157).toBitVec owned
  have positions := division_ready_positions s saved length data address capacity used (base + 157).toBitVec owned
  have caches := entry_cache s saved length data address capacity used (base + 157).toBitVec owned
  have outputProtected := division_stack_protected s (divisionReady s length (base + 157).toBitVec)
    saved length data address capacity used initial.physical positions.1 positions.2 rfl 8 8
    (by decide) (Or.inl (by decide))
  have sourceProtected := division_stack_protected s (divisionReady s length (base + 157).toBitVec)
    saved length data address capacity used initial.physical positions.1 positions.2 rfl 104 8
    (by decide) (Or.inr (by decide))
  have outputKept := division_stack_load s (divisionReady s length (base + 157).toBitVec)
    length 8 address capacity used (base + 157).toBitVec helper t.1.dmem post.frame 8 8 outputProtected
  have sourceKept := division_stack_load s (divisionReady s length (base + 157).toBitVec)
    length 8 address capacity used (base + 157).toBitVec helper t.1.dmem post.frame 104 8 sourceProtected
  refine ⟨post, world, fixed.stack, fixed.arena, fixed.length, ?_, ?_,
    outputKept.trans caches.1, sourceKept.trans caches.2⟩
  · rw [fixed.pointer]
    exact UInt64.toBitVec_ofBitVec _
  · rw [fixed.payload]
    exact UInt64.toBitVec_ofBitVec _

end SszX86.BitVector
