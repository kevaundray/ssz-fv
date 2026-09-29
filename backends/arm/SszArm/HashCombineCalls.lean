import SszArm.HashCombineOps
import SszArm.HashMemory

namespace SszArm.Hash.Combine

open Delimited (MemoryFrame)

inductive CopySite where
  | initial | leftTail | rightFill | rightTail | state
  deriving DecidableEq

def CopySite.op : CopySite → Op
  | .initial => .p76
  | .leftTail => .p176
  | .rightFill => .p224
  | .rightTail => .p356
  | .state => .p376

def copyEntry (site : CopySite) (s : ArmState) : ArmState :=
  site.op.effect s

@[simp] theorem copyEntry_program (site : CopySite) (s : ArmState) :
    (copyEntry site s).program = s.program := by
  simpa only [copyEntry] using Op.program site.op s

@[simp] theorem copyEntry_error (site : CopySite) (s : ArmState) :
    read_err (copyEntry site s) = read_err s := by
  simpa only [copyEntry] using Op.error site.op s

@[simp] theorem copyEntry_register (site : CopySite) (s : ArmState)
    (reg : BitVec 5) (different : reg ≠ 30#5) :
    r (.GPR reg) (copyEntry site s) = r (.GPR reg) s := by
  cases site <;> simp [copyEntry, CopySite.op, Op.effect, call, state_simp_rules, different]

@[simp] theorem copyEntry_vector (site : CopySite) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (copyEntry site s) = r (.SFP reg) s := by
  cases site <;> simp [copyEntry, CopySite.op, Op.effect, call, state_simp_rules]

@[simp] theorem copyEntry_memory (site : CopySite) (s : ArmState) :
    (copyEntry site s).mem = s.mem := by
  cases site <;> simp [copyEntry, CopySite.op, Op.effect, call, state_simp_rules]

theorem copyEntry_pc (site : CopySite) (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + BitVec.ofNat 64 site.op.row.1) :
    read_pc (copyEntry site s) = base + memcpyOffset := by
  change r .PC s = _ at pc
  cases site <;> simp [copyEntry, CopySite.op, Op.row, Op.effect, call,
    state_simp_rules, memcpyOffset, BitVec.add_assoc] at pc ⊢ <;> bv_omega

@[simp] theorem copyEntry_link (site : CopySite) (s : ArmState) :
    r (.GPR 30#5) (copyEntry site s) = read_pc s + 4#64 := by
  cases site <;> simp [copyEntry, CopySite.op, Op.effect, call, state_simp_rules]

theorem copy_run (site : CopySite) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (pc : read_pc s = base + BitVec.ofNat 64 site.op.row.1)
    (error : read_err s = .None) (aligned : CheckSPAlignment s) :
    run (Memcpy.fuel (r (.GPR 2#5) s).toNat + 1) s = Memcpy.result (copyEntry site s) := by
  arm_word_nf at *
  rw [run, step site.op s base code error aligned pc]
  change run (Memcpy.fuel (r (.GPR 2#5) s).toNat) (copyEntry site s) = _
  have length := copyEntry_register site s 2#5 (by decide)
  rw [← length]
  exact Memcpy.program_run _ _
    (code.of_program_eq (copyEntry_program site s)).memcpy
    (copyEntry_pc site s base pc) ((copyEntry_error site s).trans error)

structure CopyPost (site : CopySite) (s t : ArmState) : Prop where
  pc : read_pc t = read_pc s + 4#64
  error : read_err t = .None
  program : t.program = s.program
  registers : ∀ reg : BitVec 5, reg ∉ [1#5, 2#5, 3#5, 4#5, 30#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, reg ≠ 0#5 → r (.SFP reg) t = r (.SFP reg) s
  memory : ∀ a, t.mem a = Memcpy.image s.mem (r (.GPR 0#5) s) (r (.GPR 1#5) s)
    (r (.GPR 2#5) s).toNat a
  frame : MemoryFrame [((r (.GPR 0#5) s).toNat, (r (.GPR 2#5) s).toNat)] s t

theorem copy_correct (site : CopySite) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (pc : read_pc s = base + BitVec.ofNat 64 site.op.row.1)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (destination : (r (.GPR 0#5) s).toNat + (r (.GPR 2#5) s).toNat ≤ 2^64)
    (source : (r (.GPR 1#5) s).toNat + (r (.GPR 2#5) s).toNat ≤ 2^64)
    (separate : Memcpy.Disjoint (r (.GPR 0#5) s) (r (.GPR 1#5) s)
      (r (.GPR 2#5) s).toNat) :
    CopyPost site s (run (Memcpy.fuel (r (.GPR 2#5) s).toNat + 1) s) := by
  arm_word_nf at *
  rw [copy_run site s base code pc error aligned]
  let c := copyEntry site s
  have r0 : r (.GPR 0#5) c = r (.GPR 0#5) s := copyEntry_register _ _ _ (by decide)
  have r1 : r (.GPR 1#5) c = r (.GPR 1#5) s := copyEntry_register _ _ _ (by decide)
  have r2 : r (.GPR 2#5) c = r (.GPR 2#5) s := copyEntry_register _ _ _ (by decide)
  have dst : (r (.GPR 0#5) c).toNat + (r (.GPR 2#5) c).toNat ≤ 2^64 := by
    rwa [r0, r2]
  have src : (r (.GPR 1#5) c).toNat + (r (.GPR 2#5) c).toNat ≤ 2^64 := by
    rwa [r1, r2]
  have sep : Memcpy.Disjoint (r (.GPR 0#5) c) (r (.GPR 1#5) c)
      (r (.GPR 2#5) c).toNat := by rwa [r0, r1, r2]
  have memory : ∀ a, (Memcpy.result c).mem a =
      Memcpy.image s.mem (r (.GPR 0#5) s) (r (.GPR 1#5) s) (r (.GPR 2#5) s).toNat a := by
    intro a
    have observed := Memcpy.result_memory c dst src sep a
    arm_word_nf at observed r0 r1 r2 ⊢
    simpa only [r0, r1, r2, c, copyEntry_memory] using observed
  refine ⟨?_, ?_, ?_, ?_, ?_, memory, ?_⟩
  · exact (Memcpy.result_return c).trans (copyEntry_link site s)
  · exact (Memcpy.result_frame c .ERR trivial).trans ((copyEntry_error site s).trans error)
  · exact (Memcpy.result_program c).trans (copyEntry_program site s)
  · intro reg untouched
    have h1 : reg ≠ 1#5 := by simp_all
    have h2 : reg ≠ 2#5 := by simp_all
    have h3 : reg ≠ 3#5 := by simp_all
    have h4 : reg ≠ 4#5 := by simp_all
    have h30 : reg ≠ 30#5 := by simp_all
    exact (Memcpy.result_frame c (.GPR reg) ⟨h1, h2, h3, h4⟩).trans
      (copyEntry_register site s reg h30)
  · intro reg nonzero
    exact (Memcpy.result_frame c (.SFP reg) nonzero).trans (copyEntry_vector site s reg)
  · intro address outside
    rw [memory, Memcpy.image, if_neg (by
      have apart := outside ((r (.GPR 0#5) s).toNat, (r (.GPR 2#5) s).toNat) (by simp)
      omega)]

theorem CopyPost.state {site : CopySite} {s t : ArmState} {value : StreamState}
    (post : CopyPost site s t) (length : (r (.GPR 2#5) s).toNat = 112)
    (source : StateAt s (r (.GPR 1#5) s) value)
    (destination : (r (.GPR 0#5) s).toNat + 112 ≤ 2^64)
    (physical : (r (.GPR 1#5) s).toNat + 112 ≤ 2^64) :
    StateAt t (r (.GPR 0#5) s) value :=
  source.of_copy (by simpa only [length] using post.memory) destination physical

inductive CompressSite where
  | left | buffered | right
  deriving DecidableEq

def CompressSite.op : CompressSite → Op
  | .left => .p140
  | .buffered => .p264
  | .right => .p324

def compressEntry (site : CompressSite) (s : ArmState) : ArmState :=
  site.op.effect s

@[simp] theorem compressEntry_program (site : CompressSite) (s : ArmState) :
    (compressEntry site s).program = s.program := by
  simpa only [compressEntry] using Op.program site.op s

@[simp] theorem compressEntry_error (site : CompressSite) (s : ArmState) :
    read_err (compressEntry site s) = read_err s := by
  simpa only [compressEntry] using Op.error site.op s

@[simp] theorem compressEntry_register (site : CompressSite) (s : ArmState)
    (reg : BitVec 5) (different : reg ≠ 30#5) :
    r (.GPR reg) (compressEntry site s) = r (.GPR reg) s := by
  cases site <;> simp [compressEntry, CompressSite.op, Op.effect, call, state_simp_rules, different]

@[simp] theorem compressEntry_memory (site : CompressSite) (s : ArmState) :
    (compressEntry site s).mem = s.mem := by
  cases site <;> simp [compressEntry, CompressSite.op, Op.effect, call, state_simp_rules]

theorem compressEntry_pc (site : CompressSite) (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + BitVec.ofNat 64 site.op.row.1) :
    read_pc (compressEntry site s) = base + compressOffset := by
  change r .PC s = _ at pc
  cases site <;> simp [compressEntry, CompressSite.op, Op.row, Op.effect, call,
    state_simp_rules, compressOffset, BitVec.add_assoc] at pc ⊢ <;> bv_omega

@[simp] theorem compressEntry_link (site : CompressSite) (s : ArmState) :
    r (.GPR 30#5) (compressEntry site s) = read_pc s + 4#64 := by
  cases site <;> simp [compressEntry, CompressSite.op, Op.effect, call, state_simp_rules]

theorem compression_call_correct (site : CompressSite) (s : ArmState) (base : BitVec 64)
    (words : Vector UInt32 8) (bytes : ByteArray)
    (code : CodeAt s base) (data : DataAt s base) (compression : CompressionCorrect base)
    (pc : read_pc s = base + BitVec.ofNat 64 site.op.row.1)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (owned : CompressionOwned s base words bytes) :
    ∃ fuel, Returned (compressEntry site s) (run (fuel + 1) s) ∧
      ChainingAt (run (fuel + 1) s) (r (.GPR 0#5) s) (Ssz.Sha256.compress words bytes 0) ∧
      MemoryFrame (compressionWrites s) s (run (fuel + 1) s) := by
  let c := compressEntry site s
  have entryCode := code.of_program_eq (compressEntry_program site s)
  have entryOwned : CompressionOwned c base words bytes := by
    have r0 := compressEntry_register site s 0#5 (by decide)
    have r1 := compressEntry_register site s 1#5 (by decide)
    have sp := compressEntry_register site s 31#5 (by decide)
    have reads := Memory.mem_eq_iff_read_mem_bytes_eq.mp (compressEntry_memory site s)
    refine ⟨owned.blockSize, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [c, ChainingAt, r0, reads] using owned.state
    · simpa only [c, BytesAt, r1, compressEntry_memory] using owned.input
    · simpa only [c, r0] using owned.stateBound
    · simpa only [c, r1] using owned.inputBound
    · simpa only [c, sp] using owned.stackLow
    · simpa only [c, stackSpan, sp, r0] using owned.stateStack
    · simpa only [c, compressionWrites, stackSpan, sp, r0, r1] using owned.inputOwned
    · simpa only [c, compressionWrites, stackSpan, sp, r0] using owned.roundsOwned
  have entryTable : TableAt c (base + roundsOffset) roundsTable := by
    simpa only [c, TableAt, BytesAt, roundsByteArray_size, compressEntry_memory] using data.rounds
  have entryAligned : CheckSPAlignment c := by
    cases site <;>
      simpa [c, compressEntry, CompressSite.op, Op.effect, call, state_simp_rules] using aligned
  obtain ⟨fuel, returned, chaining, frame⟩ := compression c words bytes entryCode.compress
    entryTable data.roundsBound (compressEntry_pc site s base pc)
    ((compressEntry_error site s).trans error) entryAligned entryOwned
  have execution : run (fuel + 1) s = run fuel c := by
    rw [run, step site.op s base code error aligned pc]
    rfl
  refine ⟨fuel, ?_, ?_, ?_⟩
  all_goals rw [execution]
  · exact returned
  · simpa only [c, compressEntry_register site s 0#5 (by decide)] using chaining
  · simpa only [c, compressionWrites, stackSpan,
      compressEntry_register site s 0#5 (by decide),
      compressEntry_register site s 31#5 (by decide), Delimited.MemoryFrame,
      compressEntry_memory] using frame

end SszArm.Hash.Combine
