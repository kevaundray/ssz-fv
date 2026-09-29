import SszX86.HashCombineDrainMemory
import SszX86.HashCombineBuffer

namespace SszX86.Hash.Combine
open SszNative.HashStream

private theorem compression_slot (s : MachineData) (chaining : Vector UInt32 8)
    (block : Vector UInt8 64) (root : Int64)
    (pre : CompressionCallPre root s chaining block) :
    Mapped s.dmem (s.regs.rsp.toBitVec - 8) 8 := by
  have sub := mapped_subrange _ _ 168 160 8 pre.stack.2 (by decide)
  have address : s.regs.rsp.toBitVec - 168 + BitVec.ofNat 64 160 =
      s.regs.rsp.toBitVec - 8 := by bv_omega
  simpa only [address] using sub

/-- Real MOV/MOV/CALL198, using only the current physical direct-block borrow. -/
theorem left_compress_runs (e : Executable) (root : Int64) (hc : LinkedCode e root)
    (compress : CompressionCorrect e root) (s : MachineData) (state : Model)
    (source : BitVec 64) (input : ByteArray) (start : Nat)
    (memory : DrainMemory root s.dmem s.regs.rsp.toBitVec source input)
    (stored : StateAt s.dmem (s.regs.rsp.toBitVec + 8) state)
    (chainReg : s.regs.r12.toBitVec = s.regs.rsp.toBitVec + 72)
    (sourceReg : s.regs.rbp.toBitVec = source + BitVec.ofNat 64 start)
    (full : start + 64 ≤ input.size) :
    Eventually (step e)
      (CompressionCallPost (leftCompressionArgs s) state.chaining
        (inputBlock input start full) (root + 203).toBitVec)
      (s, root + 192) := by
  have pre := direct_compression_pre root (leftCompressionArgs s) state source input start
    memory stored chainReg sourceReg full
  apply left_compression_args_runs e root hc.combine s
  apply combine_call198_cps e root hc.combine _ _ (compression_slot _ _ _ _ pre)
  simpa only [Int64.sub_eq_add_neg] using
    compression_helper_runs e root hc.compress compress (leftCompressionArgs s)
      (root + 203).toBitVec state.chaining (inputBlock input start full) pre

/-- Real MOV/MOV/CALL358 for direct blocks of the right allocation. -/
theorem right_compress_runs (e : Executable) (root : Int64) (hc : LinkedCode e root)
    (compress : CompressionCorrect e root) (s : MachineData) (state : Model)
    (source : BitVec 64) (input : ByteArray) (start : Nat)
    (memory : DrainMemory root s.dmem s.regs.rsp.toBitVec source input)
    (stored : StateAt s.dmem (s.regs.rsp.toBitVec + 8) state)
    (chainReg : s.regs.r12.toBitVec = s.regs.rsp.toBitVec + 72)
    (sourceReg : s.regs.r15.toBitVec = source + BitVec.ofNat 64 start)
    (full : start + 64 ≤ input.size) :
    Eventually (step e)
      (CompressionCallPost (rightCompressionArgs s) state.chaining
        (inputBlock input start full) (root + 363).toBitVec)
      (s, root + 352) := by
  have pre := direct_compression_pre root (rightCompressionArgs s) state source input start
    memory stored chainReg sourceReg full
  apply right_compression_args_runs e root hc.combine s
  apply combine_call358_cps e root hc.combine _ _ (compression_slot _ _ _ _ pre)
  simpa only [Int64.sub_eq_add_neg] using
    compression_helper_runs e root hc.compress compress (rightCompressionArgs s)
      (root + 363).toBitVec state.chaining (inputBlock input start full) pre

/-- The complete left loop body includes the helper's actual return, decrement,
source advance, comparison and original branch. -/
theorem left_body_runs (e : Executable) (root : Int64) (hc : LinkedCode e root)
    (compress : CompressionCorrect e root) (s : MachineData) (state : Model)
    (source : BitVec 64) (input : ByteArray) (start : Nat)
    (memory : DrainMemory root s.dmem s.regs.rsp.toBitVec source input)
    (stored : StateAt s.dmem (s.regs.rsp.toBitVec + 8) state)
    (chainReg : s.regs.r12.toBitVec = s.regs.rsp.toBitVec + 72)
    (sourceReg : s.regs.rbp.toBitVec = source + BitVec.ofNat 64 start)
    (full : start + 64 ≤ input.size) (P : MachineState → Prop)
    (next : ∀ t, CompressionCallPost (leftCompressionArgs s) state.chaining
        (inputBlock input start full) (root + 203).toBitVec t →
      ∀ flags flags', Eventually (step e) P
        ({leftAdvanced t.1 flags with status := flags'},
          if 64 ≤ (leftAdvanced t.1 flags).regs.r13.toNat then root + 192 else root + 217)) :
    Eventually (step e) P (s, root + 192) := by
  apply eventually_trans (step e) _ P _
    (left_compress_runs e root hc compress s state source input start memory stored
      chainReg sourceReg full)
  rintro ⟨t, pc⟩ post
  have returned : pc = root + 203 := by
    simpa only [Int64.ofBitVec_toBitVec] using post.returned.1
  subst pc
  apply left_advance_runs e root hc.combine t P
  intro flags
  apply left_loop_test_runs e root hc.combine (leftAdvanced t flags) P
  intro flags'
  exact next (t, root + 203) post flags flags'

/-- The right body has the same physical proof, but keeps its own original
allocation and cursor registers; no concatenated source is manufactured. -/
theorem right_body_runs (e : Executable) (root : Int64) (hc : LinkedCode e root)
    (compress : CompressionCorrect e root) (s : MachineData) (state : Model)
    (source : BitVec 64) (input : ByteArray) (start : Nat)
    (memory : DrainMemory root s.dmem s.regs.rsp.toBitVec source input)
    (stored : StateAt s.dmem (s.regs.rsp.toBitVec + 8) state)
    (chainReg : s.regs.r12.toBitVec = s.regs.rsp.toBitVec + 72)
    (sourceReg : s.regs.r15.toBitVec = source + BitVec.ofNat 64 start)
    (full : start + 64 ≤ input.size) (P : MachineState → Prop)
    (next : ∀ t, CompressionCallPost (rightCompressionArgs s) state.chaining
        (inputBlock input start full) (root + 363).toBitVec t →
      ∀ flags flags', Eventually (step e) P
        ({rightAdvanced t.1 flags with status := flags'},
          if 64 ≤ (rightAdvanced t.1 flags).regs.r14.toNat then root + 352 else root + 377)) :
    Eventually (step e) P (s, root + 352) := by
  apply eventually_trans (step e) _ P _
    (right_compress_runs e root hc compress s state source input start memory stored
      chainReg sourceReg full)
  rintro ⟨t, pc⟩ post
  have returned : pc = root + 363 := by
    simpa only [Int64.ofBitVec_toBitVec] using post.returned.1
  subst pc
  apply right_advance_runs e root hc.combine t P
  intro flags
  apply right_loop_test_runs e root hc.combine (rightAdvanced t flags) P
  intro flags'
  exact next (t, root + 363) post flags flags'

end SszX86.Hash.Combine
