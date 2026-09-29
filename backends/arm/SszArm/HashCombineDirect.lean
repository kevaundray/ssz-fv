import SszArm.HashCombineControl
import SszArm.HashCombineMemory

namespace SszArm.Hash.Combine

open Delimited (Span Protected MemoryFrame)

def directWrites (s : ArmState) : List Span :=
  [stackSpan s 160, ((r (.GPR 24#5) s + 64#64).toNat, 32)]

structure DirectOwned (s : ArmState) (base address : BitVec 64)
    (input : ByteArray) (words : Vector UInt32 8) : Prop where
  physical : address.toNat + input.size ≤ 2^64
  stateBound : (r (.GPR 24#5) s + 64#64).toNat + 32 ≤ 2^64
  stackLow : 160 ≤ (r (.GPR 31#5) s).toNat
  stateStack : Protected [stackSpan s 160] (r (.GPR 24#5) s + 64#64).toNat 32
  inputOwned : Protected (directWrites s) address.toNat input.size
  initialOwned : Protected (directWrites s) (base + initialOffset).toNat 32
  roundsOwned : Protected (directWrites s) (base + roundsOffset).toNat 256
  inputAt : BytesAt s address input
  chaining : ChainingAt s (r (.GPR 24#5) s + 64#64) words

structure DirectPost (side : Side) (s t : ArmState) : Prop where
  error : read_err t = .None
  program : t.program = s.program
  sp : r (.GPR 31#5) t = r (.GPR 31#5) s
  registers : ∀ reg : BitVec 5, 19 ≤ reg.toNat → reg.toNat ≤ 29 →
    reg ≠ side.count → reg ≠ side.cursor → r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
    (r (.SFP reg) t).setWidth 64 = (r (.SFP reg) s).setWidth 64
  frame : MemoryFrame (directWrites s) s t

theorem DirectPost.statePointer {side : Side} {s t : ArmState} (post : DirectPost side s t) :
    r (.GPR 24#5) t = r (.GPR 24#5) s :=
  post.registers 24#5 (by decide) (by decide) (by cases side <;> decide) (by cases side <;> decide)

theorem DirectPost.writes {side : Side} {s t : ArmState} (post : DirectPost side s t) :
    directWrites t = directWrites s := by
  simp only [directWrites, stackSpan, post.sp, post.statePointer]

theorem DirectPost.aligned {side : Side} {s t : ArmState} (post : DirectPost side s t)
    (aligned : CheckSPAlignment s) : CheckSPAlignment t := by
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq, post.sp] using aligned

theorem DirectPost.trans {side : Side} {s t u : ArmState}
    (first : DirectPost side s t) (second : DirectPost side t u) : DirectPost side s u := by
  refine ⟨second.error, second.program.trans first.program, second.sp.trans first.sp,
    ?_, ?_, ?_⟩
  · intro reg lo hi notCount notCursor
    exact (second.registers reg lo hi notCount notCursor).trans
      (first.registers reg lo hi notCount notCursor)
  · intro reg lo hi
    exact (second.vectors reg lo hi).trans (first.vectors reg lo hi)
  · exact first.frame.trans (by simpa only [first.writes] using second.frame)

theorem DirectOwned.after {side : Side} {s t : ArmState} {base address : BitVec 64}
    {input : ByteArray} {words nextWords : Vector UInt32 8}
    (owned : DirectOwned s base address input words) (post : DirectPost side s t)
    (chaining : ChainingAt t (r (.GPR 24#5) s + 64#64) nextWords) :
    DirectOwned t base address input nextWords := by
  refine ⟨owned.physical, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [post.statePointer] using owned.stateBound
  · simpa only [post.sp] using owned.stackLow
  · simpa only [stackSpan, post.sp, post.statePointer] using owned.stateStack
  · simpa only [post.writes] using owned.inputOwned
  · simpa only [post.writes] using owned.initialOwned
  · simpa only [post.writes] using owned.roundsOwned
  · exact bytesAt_frame post.frame owned.physical owned.inputOwned owned.inputAt
  · simpa only [post.statePointer] using chaining

/-- One actual direct-block iteration: argument setup, real BL/compression/RET,
then subtraction, cursor advance and the original unsigned back edge. -/
theorem direct_step (side : Side) (s : ArmState) (base address : BitVec 64)
    (input : ByteArray) (start : Nat) (words : Vector UInt32 8)
    (code : CodeAt s base) (data : DataAt s base) (compression : CompressionCorrect base)
    (pc : read_pc s = base + BitVec.ofNat 64 side.start)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (owned : DirectOwned s base address input words)
    (cursor : r (.GPR side.cursor) s = address + BitVec.ofNat 64 start)
    (bound : start + 64 ≤ input.size) :
    ∃ fuel, let t := run fuel s
      DirectPost side s t ∧
      r (.GPR side.count) t = r (.GPR side.count) s - 64#64 ∧
      r (.GPR side.cursor) t = r (.GPR side.cursor) s + 64#64 ∧
      read_pc t = (if 64 ≤ (r (.GPR side.count) s - 64#64).toNat then
        base + BitVec.ofNat 64 side.start else base + BitVec.ofNat 64 side.stop) ∧
      DirectOwned t base address input (Ssz.Sha256.compress words input start) ∧
      DataAt t base := by
  let a := setup side s
  have aCode : CodeAt a base := code.of_program_eq (setup_program side s)
  have aData : DataAt a base := by
    refine ⟨?_, ?_, data.initialBound, data.roundsBound⟩
    · simpa only [TableAt, BytesAt, a, setup_memory] using data.initial
    · simpa only [TableAt, BytesAt, a, setup_memory] using data.rounds
  have aPC := setup_call_pc side s base pc
  have aError : read_err a = .None := (setup_error side s).trans error
  have aAligned : CheckSPAlignment a := setup_aligned side s aligned
  have aWrites : compressionWrites a = directWrites s := by
    simp only [compressionWrites, directWrites, stackSpan, a, setup_state,
      setup_register side s 31#5 (by decide) (by decide)]
  have aInput : r (.GPR 1#5) a = address + BitVec.ofNat 64 start := by
    rw [setup_input, cursor]
  have aState : r (.GPR 0#5) a = r (.GPR 24#5) s + 64#64 := setup_state side s
  have aSP : r (.GPR 31#5) a = r (.GPR 31#5) s :=
    setup_register side s 31#5 (by decide) (by decide)
  have cursorNat : (address + BitVec.ofNat 64 start).toNat = address.toNat + start := by
    have physical := owned.physical
    bv_omega
  have compressionOwned : CompressionOwned a base words (sliceBytes input start 64) := by
    refine ⟨sliceBytes_size input start 64 bound, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [aState]
      intro i
      rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp (setup_memory side s)) 4]
      exact owned.chaining i
    · rw [aInput]
      simpa only [BytesAt, a, setup_memory] using bytesAt_slice owned.inputAt start 64 bound
    · simpa only [aState] using owned.stateBound
    · rw [aInput, cursorNat]
      have physical := owned.physical
      omega
    · simpa only [aSP] using owned.stackLow
    · simpa only [stackSpan, aSP, aState] using owned.stateStack
    · rw [aWrites, aInput, cursorNat]
      exact protected_subspan owned.inputOwned (by omega) (by omega)
    · simpa only [aWrites] using owned.roundsOwned
  obtain ⟨fuel, returned, chaining, memory⟩ := compression_call_correct side.site a base words
    (sliceBytes input start 64) aCode aData compression aPC aError aAligned compressionOwned
  let middle := run (fuel + 1) a
  have middleSP : r (.GPR 31#5) middle = r (.GPR 31#5) s := by
    exact returned.sp.trans ((compressEntry_register side.site a 31#5 (by decide)).trans aSP)
  have middleReg (reg : BitVec 5) (lo : 19 ≤ reg.toNat) (hi : reg.toNat ≤ 29) :
      r (.GPR reg) middle = r (.GPR reg) s := by
    exact (returned.registers reg lo (by omega)).trans
      ((compressEntry_register side.site a reg (by bv_omega)).trans
        (setup_register side s reg (by bv_omega) (by bv_omega)))
  have middlePC : read_pc middle = base + BitVec.ofNat 64 (side.start + 12) := by
    rw [returned.pc, compressEntry_link, setup_pc, pc]
    cases side <;> simp [Side.start, BitVec.add_assoc]
  have middleProgram : middle.program = s.program :=
    returned.program.trans ((compressEntry_program side.site a).trans (setup_program side s))
  have middleCode : CodeAt middle base := code.of_program_eq middleProgram
  have middleAligned : CheckSPAlignment middle := by
    simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq, middleSP] using aligned
  have middleMemory : MemoryFrame (directWrites s) s middle := by
    intro address outside
    have same := memory address (by simpa only [aWrites] using outside)
    exact same.trans (congrFun (setup_memory side s) address)
  let t := advance side middle
  have execution : run (2 + (fuel + 1) + 4) s = t := by
    rw [run_plus, run_plus, setup_run side s base code error aligned pc]
    exact advance_run side middle base middleCode returned.error middleAligned middlePC
  have post : DirectPost side s t := by
    refine ⟨(advance_error side middle).trans returned.error,
      (advance_program side middle).trans middleProgram, ?_, ?_, ?_, ?_⟩
    · exact (advance_register side middle 31#5 (by cases side <;> decide)
        (by cases side <;> decide)).trans middleSP
    · intro reg lo hi notCount notCursor
      exact (advance_register side middle reg notCount notCursor).trans (middleReg reg lo hi)
    · intro reg lo hi
      rw [advance_vector]
      have entryVector : r (.SFP reg) (compressEntry side.site a) = r (.SFP reg) a := by
        cases side <;>
          simp [Side.site, compressEntry, CompressSite.op, Op.effect, call, state_simp_rules]
      exact (returned.vectors reg lo hi).trans
        (congrArg (fun value : BitVec 128 => value.setWidth 64)
          (entryVector.trans (setup_vector side s reg)))
    · intro address outside
      exact (congrFun (advance_memory side middle) address).trans (middleMemory address outside)
  have countReg : r (.GPR side.count) middle = r (.GPR side.count) s :=
    middleReg side.count (by cases side <;> decide) (by cases side <;> decide)
  have cursorReg : r (.GPR side.cursor) middle = r (.GPR side.cursor) s :=
    middleReg side.cursor (by cases side <;> decide) (by cases side <;> decide)
  have resultChaining : ChainingAt t (r (.GPR 24#5) s + 64#64)
      (Ssz.Sha256.compress words input start) := by
    intro i
    rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp (advance_memory side middle)) 4]
    simpa only [aState, compress_slice words input start bound] using chaining i
  refine ⟨2 + (fuel + 1) + 4, ?_⟩
  rw [execution]
  refine ⟨post, ?_, ?_, ?_, owned.after post resultChaining,
    data.frame post.frame owned.initialOwned owned.roundsOwned⟩
  · exact (advance_count side middle).trans (congrArg (fun x => x - 64#64) countReg)
  · exact (advance_cursor side middle).trans (congrArg (fun x => x + 64#64) cursorReg)
  · simpa only [countReg] using advance_pc side middle base middlePC

/-- Both direct loops terminate for every physical slice length. The induction
counts whole blocks only; the residual count is retained for the real memcpy. -/
theorem direct_loop (side : Side) (q rest : Nat) (short : rest < 64)
    (s : ArmState) (base address : BitVec 64) (input : ByteArray)
    (start : Nat) (words : Vector UInt32 8)
    (code : CodeAt s base) (data : DataAt s base) (compression : CompressionCorrect base)
    (pc : read_pc s = if q = 0 then base + BitVec.ofNat 64 side.stop
      else base + BitVec.ofNat 64 side.start)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (owned : DirectOwned s base address input words)
    (cursor : r (.GPR side.cursor) s = address + BitVec.ofNat 64 start)
    (count : (r (.GPR side.count) s).toNat = 64 * q + rest)
    (split : start + 64 * q + rest = input.size) :
    ∃ fuel, let t := run fuel s
      DirectPost side s t ∧
      (r (.GPR side.count) t).toNat = rest ∧
      r (.GPR side.cursor) t = address + BitVec.ofNat 64 (start + 64 * q) ∧
      read_pc t = base + BitVec.ofNat 64 side.stop ∧
      DirectOwned t base address input
        ((List.range q).foldl
          (fun current i => Ssz.Sha256.compress current input (start + 64 * i)) words) ∧
      DataAt t base := by
  induction q generalizing s start words with
  | zero =>
    refine ⟨0, ?_⟩
    simp only [run_opener_zero, Nat.mul_zero, Nat.add_zero, List.range_zero, List.foldl_nil]
    refine ⟨⟨error, rfl, rfl, ?_, ?_, MemoryFrame.refl _ _⟩,
      ?_, cursor, ?_, owned, data⟩
    · intro reg lo hi notCount notCursor
      rfl
    · intro reg lo hi
      rfl
    · simpa using count
    · simpa using pc
  | succ q ih =>
    have startPC : read_pc s = base + BitVec.ofNat 64 side.start := by simpa using pc
    obtain ⟨firstFuel, first, countStep, cursorStep, nextPC, nextOwned, nextData⟩ :=
      direct_step side s base address input start words code data compression startPC error
        aligned owned cursor (by omega)
    let middle := run firstFuel s
    have middleCount : (r (.GPR side.count) middle).toNat = 64 * q + rest := by
      rw [countStep]
      bv_omega
    have middleCursor : r (.GPR side.cursor) middle =
        address + BitVec.ofNat 64 (start + 64) := by
      rw [cursorStep, cursor]
      bv_omega
    have middlePC : read_pc middle = if q = 0 then base + BitVec.ofNat 64 side.stop
        else base + BitVec.ofNat 64 side.start := by
      have remaining : (r (.GPR side.count) s - 64#64).toNat = 64 * q + rest := by
        bv_omega
      rw [nextPC, remaining]
      by_cases zero : q = 0
      · simp only [zero, Nat.mul_zero, Nat.zero_add, if_true,
          if_neg (by omega : ¬64 ≤ rest)]
      · simp only [zero, if_false, if_pos (by omega : 64 ≤ 64 * q + rest)]
    obtain ⟨lastFuel, last, finalCount, finalCursor, finalPC, finalOwned, finalData⟩ :=
      ih middle (start + 64) (Ssz.Sha256.compress words input start)
        (code.of_program_eq first.program) nextData middlePC first.error
        (first.aligned aligned) nextOwned middleCursor middleCount (by omega)
    refine ⟨firstFuel + lastFuel, ?_⟩
    rw [run_plus]
    refine ⟨first.trans last, finalCount, ?_, finalPC, ?_, finalData⟩
    · have offset : start + 64 + 64 * q = start + 64 * (q + 1) := by omega
      simpa only [middle, offset] using finalCursor
    · have offsets :
          (fun current i => Ssz.Sha256.compress current input (start + 64 + 64 * i)) =
          (fun current i => Ssz.Sha256.compress current input (start + 64 * Nat.succ i)) := by
        funext current i
        congr 1
        omega
      simpa only [middle, List.range_succ_eq_map, List.foldl_cons, List.foldl_map,
        Nat.mul_zero, Nat.add_zero, offsets] using finalOwned

end SszArm.Hash.Combine
