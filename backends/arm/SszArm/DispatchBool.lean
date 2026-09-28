import SszArm.DispatchEntry
import SszArm.BoolProofs

namespace SszArm.Dispatch.Boolean

/-- Physical original-entry ownership. Read-only data and descriptor may alias;
only actual output and stack writes are separated from them. -/
structure Owned (s : ArmState) (data : Ssz.Bytes) : Prop where
  entry : EntryOwned s .bool
  stackLow : 400 ≤ (r (.GPR 31#5) s).toNat
  outputBound : (r (.GPR 0#5) s).toNat + 80 ≤ 2^64
  outputStack : (r (.GPR 0#5) s).toNat + 80 ≤ (r (.GPR 31#5) s).toNat - 400 ∨
    (r (.GPR 31#5) s).toNat ≤ (r (.GPR 0#5) s).toNat
  length : (r (.GPR 3#5) s).toNat = data.size
  inputBound : (r (.GPR 2#5) s).toNat + data.size ≤ 2^64
  input : ∀ i < data.size, read_mem_bytes 1 (r (.GPR 2#5) s + BitVec.ofNat 64 i) s = data[i]!.toBitVec
  inputOutput : data.size = 0 ∨ (r (.GPR 2#5) s).toNat + data.size ≤ (r (.GPR 0#5) s).toNat ∨
    (r (.GPR 0#5) s).toNat + 76 ≤ (r (.GPR 2#5) s).toNat
  inputStack : data.size = 0 ∨ (r (.GPR 2#5) s).toNat + data.size ≤ (r (.GPR 31#5) s).toNat - 400 ∨
    (r (.GPR 31#5) s).toNat ≤ (r (.GPR 2#5) s).toNat
  descriptorOutput : (r (.GPR 1#5) s).toNat + 8 ≤ (r (.GPR 0#5) s).toNat ∨
    (r (.GPR 0#5) s).toNat + 76 ≤ (r (.GPR 1#5) s).toNat
  descriptorStack : (r (.GPR 1#5) s).toNat + 8 ≤ (r (.GPR 31#5) s).toNat - 400 ∨
    (r (.GPR 31#5) s).toNat ≤ (r (.GPR 1#5) s).toNat

theorem Owned.body {s : ArmState} {data : Ssz.Bytes} (owned : Owned s data) :
    BoolCodec.ScratchSeparated (entered s .bool) := by
  have low := owned.stackLow
  have bound := owned.outputBound
  have separate := owned.outputStack
  simp only [BoolCodec.ScratchSeparated, entered_sp, entered_reg _ _ 0#5 (by decide) (by decide) (by decide), bodySP]
  bv_omega

theorem Owned.activation {s : ArmState} {data : Ssz.Bytes} (owned : Owned s data) :
    (r (.GPR 0#5) (entered s .bool)).toNat + 80 ≤
      (r (.GPR 31#5) (entered s .bool)).toNat + 272 ∨
    (r (.GPR 31#5) (entered s .bool)).toNat + 368 ≤
      (r (.GPR 0#5) (entered s .bool)).toNat := by
  have low := owned.stackLow
  have separate := owned.outputStack
  simp only [entered_sp, entered_reg _ _ 0#5 (by decide) (by decide) (by decide), bodySP]
  bv_omega

theorem Owned.byte {s : ArmState} {data : Ssz.Bytes} (owned : Owned s data)
    (one : data.size = 1) : BoolCodec.inputByte (entered s .bool) = data[0]!.toBitVec := by
  change read_mem_bytes 1 (r (.GPR 2#5) (entered s .bool)) (entered s .bool) = _
  rw [entered_reg s .bool 2#5 (by decide) (by decide) (by decide)]
  rw [entered_read s .bool owned.entry.stackLow _ 1]
  · simpa using owned.input 0 (by omega)
  · have bound := owned.inputBound
    omega
  · have separate := owned.inputStack
    omega

/-- Original caller ABI and exact output/frame observation, not postdispatch
saved-slot assumptions. The source pointer is never normalized for empty input. -/
structure Post (s t : ArmState) (data : Ssz.Bytes) : Prop where
  result : SszNative.BoolCodec.ResultAt
    (fun offset width => some (read_mem_bytes width (r (.GPR 0#5) s + BitVec.ofNat 64 offset) t).toNat)
    (Ssz.deserialize .bool data)
  pc : read_pc t = r (.GPR 30#5) s
  sp : r (.GPR 31#5) t = r (.GPR 31#5) s
  registers : ∀ reg offset, (reg, offset) ∈ BoolCodec.savedRegisters → r (.GPR reg) t = r (.GPR reg) s
  frame : ∀ a : BitVec 64,
    (a.toNat < (r (.GPR 0#5) s).toNat ∨ (r (.GPR 0#5) s).toNat + 76 ≤ a.toNat) →
    (a.toNat < (r (.GPR 31#5) s).toNat - 400 ∨ (r (.GPR 31#5) s).toNat - 368 ≤ a.toNat) →
    (a.toNat < (r (.GPR 31#5) s).toNat - 96 ∨ (r (.GPR 31#5) s).toNat ≤ a.toNat) →
    t.mem a = s.mem a
  input : ∀ a : BitVec 64, (r (.GPR 2#5) s).toNat ≤ a.toNat →
    a.toNat < (r (.GPR 2#5) s).toNat + data.size → t.mem a = s.mem a
  descriptor : ∀ a : BitVec 64, (r (.GPR 1#5) s).toNat ≤ a.toNat →
    a.toNat < (r (.GPR 1#5) s).toNat + 8 → t.mem a = s.mem a

/-- The complete actual private function entry reaches real RET and refines the
pinned Boolean decoder for every scope and byte-error branch. -/
theorem program_correct (s : ArmState) (base : BitVec 64) (data : Ssz.Bytes)
    (owned : Owned s data) (dispatch : CodeAt s base) (body : BoolCodec.CodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s) (pc : read_pc s = base) :
    ∃ fuel, Post s (run fuel s) data := by
  let b := entered s .bool
  have bodyCode : BoolCodec.CodeAt b base := by
    simpa only [b, BoolCodec.CodeAt, entered_program] using body
  have bodyError : read_err b = .None := by simpa only [b, entered_error] using error
  have bodyPC : read_pc b = base + 604#64 := entered_pc s base .bool owned.entry pc
  obtain ⟨result, returnPC, returnSP, registers, frame⟩ :=
    BoolCodec.body_refines b base data bodyCode bodyPC bodyError
      (entered_aligned s .bool aligned) owned.body owned.activation
      (by simpa [b] using owned.length)
      owned.byte
  refine ⟨Kind.bool.steps + BoolCodec.bodySteps b, ?_⟩
  rw [run_plus, entry_run s base .bool owned.entry dispatch error aligned pc]
  have wholeFrame : ∀ a : BitVec 64,
      (a.toNat < (r (.GPR 0#5) s).toNat ∨ (r (.GPR 0#5) s).toNat + 76 ≤ a.toNat) →
      (a.toNat < (r (.GPR 31#5) s).toNat - 400 ∨ (r (.GPR 31#5) s).toNat - 368 ≤ a.toNat) →
      (a.toNat < (r (.GPR 31#5) s).toNat - 96 ∨ (r (.GPR 31#5) s).toNat ≤ a.toNat) →
      (run (BoolCodec.bodySteps b) b).mem a = s.mem a := by
    intro a out scratch activation
    apply (frame a (by simpa only [b, entered_reg _ _ 0#5 (by decide) (by decide) (by decide)] using out) ?_).trans
      (entered_frame s .bool owned.entry.stackLow a activation)
    have low := owned.stackLow
    simp only [b, entered_sp, bodySP]
    bv_omega
  refine ⟨?_, ?_, ?_, ?_, wholeFrame, ?_, ?_⟩
  · simpa only [b, entered_reg _ _ 0#5 (by decide) (by decide) (by decide)] using result
  · exact returnPC.trans (by
      simpa only [b, entered_sp] using entered_saved s .bool owned.entry.stackLow 30#5 280 (by decide))
  · simpa only [b, entered_sp, bodySP, BitVec.sub_add_cancel] using returnSP
  · intro reg offset member
    exact (registers reg offset member).trans (by
      simpa only [b, entered_sp] using entered_saved s .bool owned.entry.stackLow reg offset member)
  · intro a low high
    have out := owned.inputOutput
    have stack := owned.inputStack
    apply wholeFrame a <;> omega
  · intro a low high
    have out := owned.descriptorOutput
    have stack := owned.descriptorStack
    apply wholeFrame a <;> omega

end SszArm.Dispatch.Boolean
