import SszArm.HashCombineControl
import SszArm.HashCombineMemory

namespace SszArm.Hash.Combine

open Delimited (MemoryFrame)

def Side.tailOps : Side → List Op
  | .left => [.p160, .p164, .p168, .p172]
  | .right => [.p344, .p348, .p352]

def Side.tailSite : Side → CopySite
  | .left => .leftTail
  | .right => .rightTail

def Side.tailReturn : Side → Nat
  | .left => 180
  | .right => 360

@[irreducible] def tailSetup (side : Side) (s : ArmState) : ArmState := block side.tailOps s

theorem tailSetup_run (side : Side) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 side.stop) :
    run side.tailOps.length s = tailSetup side s := by
  have follows : Follows base side.tailOps s := by
    change r .PC s = _ at pc
    cases side <;> simp [Follows, Side.tailOps, Side.stop, Op.row, Op.effect, put, next,
      state_simp_rules, aligned, pc, BitVec.add_assoc]
  rw [tailSetup]
  exact runs side.tailOps s base code error follows

@[simp] theorem tailSetup_program (side : Side) (s : ArmState) :
    (tailSetup side s).program = s.program := by simp only [tailSetup, block_program]

@[simp] theorem tailSetup_error (side : Side) (s : ArmState) :
    read_err (tailSetup side s) = read_err s := by simp only [tailSetup, block_error]

@[simp] theorem tailSetup_memory (side : Side) (s : ArmState) :
    (tailSetup side s).mem = s.mem := by
  cases side <;> simp [tailSetup, Side.tailOps, block, Op.effect, put, next, state_simp_rules]

@[simp] theorem tailSetup_register (side : Side) (s : ArmState) (reg : BitVec 5)
    (different : reg ∉ [0#5, 1#5, 2#5, 25#5]) :
    r (.GPR reg) (tailSetup side s) = r (.GPR reg) s := by
  have h0 : reg ≠ 0#5 := by simp_all
  have h1 : reg ≠ 1#5 := by simp_all
  have h2 : reg ≠ 2#5 := by simp_all
  have h25 : reg ≠ 25#5 := by simp_all
  cases side <;> simp [tailSetup, Side.tailOps, block, Op.effect, put, next,
    state_simp_rules, h0, h1, h2, h25]

@[simp] theorem tailSetup_vector (side : Side) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (tailSetup side s) = r (.SFP reg) s := by
  cases side <;> simp [tailSetup, Side.tailOps, block, Op.effect, put, next, state_simp_rules]

theorem tailSetup_arguments (side : Side) (s : ArmState) :
    r (.GPR 0#5) (tailSetup side s) = r (.GPR 31#5) s ∧
    r (.GPR 1#5) (tailSetup side s) = r (.GPR side.cursor) s ∧
    r (.GPR 2#5) (tailSetup side s) = r (.GPR side.count) s := by
  cases side <;> simp [tailSetup, Side.tailOps, Side.cursor, Side.count, block,
    Op.effect, put, next, state_simp_rules]

structure TailPost (side : Side) (s t : ArmState) (base : BitVec 64) : Prop where
  pc : read_pc t = base + BitVec.ofNat 64 side.tailReturn
  error : read_err t = .None
  program : t.program = s.program
  sp : r (.GPR 31#5) t = r (.GPR 31#5) s
  registers : ∀ reg : BitVec 5, 19 ≤ reg.toNat → reg.toNat ≤ 29 → reg ≠ 25#5 →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
    (r (.SFP reg) t).setWidth 64 = (r (.SFP reg) s).setWidth 64
  frame : MemoryFrame [((r (.GPR 31#5) s).toNat, (r (.GPR side.count) s).toNat)] s t
  leftBuffer : side = .left → r (.GPR 25#5) t = r (.GPR 31#5) s

/-- Zero-length tails use the same real helper, including its RET. Nonzero tails
retain the stale buffer suffix and keep both raw input allocations read-only. -/
theorem tail_copy_correct (side : Side) (s : ArmState) (base address : BitVec 64)
    (input : ByteArray) (start count : Nat) (buffer : Vector UInt8 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 side.stop)
    (bufferPhysical : (r (.GPR 31#5) s).toNat + 64 ≤ 2^64)
    (inputPhysical : address.toNat + input.size ≤ 2^64)
    (short : count < 64) (bound : start + count ≤ input.size)
    (source : BytesAt s address input)
    (old : BytesAt s (r (.GPR 31#5) s) ⟨buffer.toArray⟩)
    (cursor : r (.GPR side.cursor) s = address + BitVec.ofNat 64 start)
    (length : (r (.GPR side.count) s).toNat = count)
    (separate : Memcpy.Disjoint (r (.GPR 31#5) s) (address + BitVec.ofNat 64 start) count) :
    let fuel := side.tailOps.length + (Memcpy.fuel count + 1)
    TailPost side s (run fuel s) base ∧
      BytesAt (run fuel s) (r (.GPR 31#5) s)
        ⟨(SszNative.HashStream.copy buffer 0 input start count (by omega) bound).toArray⟩ := by
  let a := tailSetup side s
  have arguments : r (.GPR 0#5) a = r (.GPR 31#5) s ∧
      r (.GPR 1#5) a = r (.GPR side.cursor) s ∧
      r (.GPR 2#5) a = r (.GPR side.count) s := tailSetup_arguments side s
  have aLength : (r (.GPR 2#5) a).toNat = count := arguments.2.2 ▸ length
  have aPC : read_pc a = base + BitVec.ofNat 64 side.tailSite.op.row.1 := by
    change r .PC s = _ at pc
    cases side <;> simp [a, tailSetup, Side.tailOps, Side.tailSite, Side.stop,
      CopySite.op, Op.row, block, Op.effect, put, next, state_simp_rules, pc, BitVec.add_assoc]
  have aAligned : CheckSPAlignment a := by
    cases side <;> simpa [a, tailSetup, Side.tailOps, block, Op.effect, put, next,
      state_simp_rules] using aligned
  have aSource : BytesAt a address input := by
    simpa only [a, BytesAt, tailSetup_memory] using source
  have aOld : BytesAt a (r (.GPR 31#5) s) ⟨buffer.toArray⟩ := by
    simpa only [a, BytesAt, tailSetup_memory] using old
  have destination : (r (.GPR 0#5) a).toNat + count ≤ 2^64 := by
    rw [arguments.1]
    omega
  have physical : (r (.GPR 1#5) a).toNat + count ≤ 2^64 := by
    rw [arguments.2.1, cursor]
    bv_omega
  have sep : Memcpy.Disjoint (r (.GPR 0#5) a) (r (.GPR 1#5) a) count := by
    simpa only [arguments.1, arguments.2.1, cursor] using separate
  have copied := copy_correct side.tailSite a base (code.of_program_eq (tailSetup_program side s))
    aPC ((tailSetup_error side s).trans error) aAligned
    (by simpa only [aLength] using destination) (by simpa only [aLength] using physical)
    (by simpa only [aLength] using sep)
  simp only [aLength] at copied
  have bufferResult := copied.buffer (r (.GPR 31#5) s) address buffer input 0 start count
    (by omega) bound bufferPhysical inputPhysical aOld aSource
    (by simpa only [show BitVec.ofNat 64 0 = 0#64 by rfl, BitVec.add_zero] using arguments.1)
    (arguments.2.1.trans cursor) aLength
  dsimp only
  rw [run_plus, tailSetup_run side s base code error aligned pc]
  refine ⟨⟨?_, copied.error, copied.program.trans (tailSetup_program side s), ?_, ?_, ?_, ?_, ?_⟩,
    bufferResult⟩
  · rw [copied.pc, aPC]
    cases side <;> simp [Side.tailSite, Side.tailReturn, CopySite.op, Op.row, BitVec.add_assoc]
  · exact (copied.registers 31#5 (by decide)).trans (tailSetup_register side s 31#5 (by decide))
  · intro reg lo hi different
    exact (copied.registers reg (by simp only [List.mem_cons, List.not_mem_nil, or_false]; bv_omega)).trans
      (tailSetup_register side s reg (by simp only [List.mem_cons, List.not_mem_nil, or_false]; bv_omega))
  · intro reg lo hi
    rw [copied.vectors reg (by bv_omega), tailSetup_vector]
  · intro address outside
    have same := copied.frame address (by simpa only [arguments.1, aLength, length] using outside)
    exact same.trans (congrFun (tailSetup_memory side s) address)
  · intro left
    subst side
    rw [copied.registers 25#5 (by decide)]
    simp [a, tailSetup, Side.tailOps, block, Op.effect, put, next, state_simp_rules]

end SszArm.Hash.Combine
