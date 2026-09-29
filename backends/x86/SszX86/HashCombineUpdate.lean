import SszX86.HashCombineRight
import SszX86.HashCombineFullBuffer

namespace SszX86.Hash.Combine
open SszNative.HashStream

structure UpdatePost (root : Int64) (s : MachineData) (state : Model)
    (input : ByteArray) (t : MachineState) : Prop where
  pc : t.2 = root + 399
  state : StateAt t.1.dmem (s.regs.rsp.toBitVec + 8) (update state input).state
  frame : MemoryFrame s.dmem t.1.dmem (DrainWritable s.regs.rsp.toBitVec)
  mapping : MappedPreserved s.dmem t.1.dmem
  rsp : t.1.regs.rsp.toBitVec = s.regs.rsp.toBitVec
  rbx : t.1.regs.rbx = s.regs.rbx
  r12 : t.1.regs.r12 = s.regs.r12

theorem right_post_update (root : Int64) (s t : MachineData)
    (original state : Model) (source : BitVec 64) (input : ByteArray)
    (start : Nat) (bound : start ≤ input.size) (result : MachineState)
    (finish : RightPost root t state source input start bound result)
    (sp : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec)
    (rbx : t.regs.rbx = s.regs.rbx) (r12 : t.regs.r12 = s.regs.r12)
    (frame : MemoryFrame s.dmem t.dmem (DrainWritable s.regs.rsp.toBitVec))
    (mapping : MappedPreserved s.dmem t.dmem)
    (model : (update original input).state =
      (drain state.buffer state.chaining state.byteLen input start bound).state) :
    UpdatePost root s original input result := by
  refine ⟨finish.pc, ?_, ?_, ?_, finish.rsp.trans sp,
    finish.rbx.trans rbx, finish.r12.trans r12⟩
  · rw [model]
    simpa only [sp] using finish.state
  · intro a outside
    exact (finish.frame a (by simpa only [sp] using outside)).trans (frame a outside)
  · intro p n hm
    exact finish.mapping p n (mapping p n hm)

/-- The two encoded alignment NOPs are traversed only on the full-block branch. -/
theorem right_drain_entry_runs (e : Executable) (root : Int64) (hc : LinkedCode e root)
    (compress : CompressionCorrect e root) (s : MachineData) (state : Model)
    (source : BitVec 64) (input : ByteArray) (start : Nat) (bound : start ≤ input.size)
    (memory : DrainMemory root s.dmem s.regs.rsp.toBitVec source input)
    (stored : StateAt s.dmem (s.regs.rsp.toBitVec + 8) state)
    (chainReg : s.regs.r12.toBitVec = s.regs.rsp.toBitVec + 72)
    (sourceReg : s.regs.r15.toBitVec = source + BitVec.ofNat 64 start)
    (countReg : s.regs.r14.toNat = input.size - start) :
    Eventually (step e) (RightPost root s state source input start bound) (s, root + 331) := by
  apply right_entry_test_runs e root hc.combine s
  intro flags
  let t : MachineData := {s with status := flags}
  have run := right_drain_runs e root hc compress t state source input start bound
    memory stored chainReg sourceReg countReg
  have casts : (if s.regs.r14.toNat < 64 then root + 377 else root + 352) =
      (if 64 ≤ input.size - start then root + 352 else root + 377) := by
    rw [countReg]
    split <;> split <;> try rfl <;> omega
  rw [casts]
  exact run

/-- The already-added counter is retained when the buffer is empty. -/
theorem empty_right_runs (e : Executable) (root : Int64) (hc : LinkedCode e root)
    (compress : CompressionCorrect e root) (s : MachineData) (state : Model)
    (source : BitVec 64) (input : ByteArray)
    (memory : DrainMemory root s.dmem s.regs.rsp.toBitVec source input)
    (stored : StateAt s.dmem (s.regs.rsp.toBitVec + 8)
      {state with byteLen := state.byteLen + UInt64.ofNat input.size})
    (empty : state.buffered.val = 0)
    (chainReg : s.regs.r12.toBitVec = s.regs.rsp.toBitVec + 72)
    (sourceReg : s.regs.r15.toBitVec = source)
    (countReg : s.regs.r14.toNat = input.size) :
    Eventually (step e) (UpdatePost root s state input) (s, root + 331) := by
  let counted : Model := {state with byteLen := state.byteLen + UInt64.ofNat input.size}
  have run := right_drain_entry_runs e root hc compress s counted source input 0 (by omega)
    memory stored chainReg (by simpa only [BitVec.add_zero] using sourceReg)
    (by simpa only [Nat.sub_zero] using countReg)
  apply eventually_weaken (step e) _ _ _ _ run
  intro result finish
  exact right_post_update root s s state counted source input 0 (by omega) result finish
    rfl rfl rfl (fun _ _ => rfl) (fun _ _ h => h)
    (update_empty_buffer state input empty)

end SszX86.Hash.Combine
