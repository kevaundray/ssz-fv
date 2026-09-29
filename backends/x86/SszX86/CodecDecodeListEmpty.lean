import SszX86.CodecDecodeListReturn

set_option autoImplicit false

namespace SszX86.CodecDecodeList
open SszNative UintCodec

/-- Exact returned machine state of the zero-byte shortcut. Only the six PUSH
words and the four active result stores differ in memory. -/
def emptyState (s : MachineData) (ra : BitVec 64) : MachineData :=
  returned
    {stackState (Dispatch.savedState s) with
      dmem := CodecDeserialize.sequenceMem (Dispatch.savedMem s) s.regs.rdi.toBitVec 16 0}
    (Dispatch.saved s ra)

/-- Original entry through RET for the native empty-list shortcut. No descriptor,
limit, arena contents, successful fixed-size computation, or child execution is
assumed. The return address is loaded from the original caller stack. -/
theorem empty_runs (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (ra : BitVec 64) (empty : s.regs.r8.toBitVec = 0#64)
    (stack : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 48) 48)
    (output : BoolCodec.Mapped s.dmem s.regs.rdi.toBitVec)
    (ret : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra)))
    (separate : ∀ i < 56, ∀ j < 80,
      s.regs.rsp.toBitVec - 48 + BitVec.ofNat 64 i ≠ s.regs.rdi.toBitVec + BitVec.ofNat 64 j) :
    Eventually (step e) (fun t => t = (emptyState s ra, Int64.ofBitVec ra)) (s, base) := by
  have sp : (stackState (Dispatch.savedState s)).regs.rsp.toBitVec =
      s.regs.rsp.toBitVec - 152 := by
    simp only [stackState, Dispatch.savedState, UInt64.toBitVec_ofBitVec]
    bv_omega
  have mapped : BoolCodec.Mapped (Dispatch.savedMem s) s.regs.rdi.toBitVec :=
    Dispatch.saved_mapped s _ _ output
  have saved := saved_at s ra ret
  have kept := sequence_saved (Dispatch.savedMem s) s.regs.rdi.toBitVec 16 0
    (s.regs.rsp.toBitVec - 152) (Dispatch.saved s ra) saved (by
      intro i hi j hj
      have address : s.regs.rsp.toBitVec - 152 + BitVec.ofNat 64 (104 + i) =
          s.regs.rsp.toBitVec - 48 + BitVec.ofNat 64 i := by
        rw [BitVec.ofNat_add]
        bv_omega
      rw [address]
      exact separate i hi j hj)
  apply pushes_runs e base code s _ stack
  apply stack_runs e base code
  apply empty_branch e base code _ empty
  intro flags
  apply empty_stores e base code _ mapped
  apply epilogue e base code _ (Dispatch.saved s ra)
  · simpa only [sp] using kept
  · rfl

/-- ABI restoration is read directly from the exact returned machine state. -/
theorem empty_abi (s : MachineData) (ra : BitVec 64) :
    (emptyState s ra).regs.rsp.toBitVec = s.regs.rsp.toBitVec + 8 ∧
    (emptyState s ra).regs.rbx = s.regs.rbx ∧
    (emptyState s ra).regs.r12 = s.regs.r12 ∧
    (emptyState s ra).regs.r13 = s.regs.r13 ∧
    (emptyState s ra).regs.r14 = s.regs.r14 ∧
    (emptyState s ra).regs.r15 = s.regs.r15 ∧
    (emptyState s ra).regs.rbp = s.regs.rbp := by
  simp only [emptyState, returned, stackState, Dispatch.savedState, Dispatch.saved,
    UInt64.ofBitVec_toBitVec, UInt64.toBitVec_ofBitVec]
  bv_omega

/-- Exact active result fields. No claim initializes inactive/padding bytes
of the empty Value or the unused bytes of the outer Result. -/
theorem empty_result (s : MachineData) (ra : BitVec 64)
    (bound : s.regs.rdi.toNat + 80 ≤ 2 ^ 64) :
    Mem.loadInt (emptyState s ra).dmem s.regs.rdi.toBitVec 8 = some 0 ∧
    Mem.loadInt (emptyState s ra).dmem (s.regs.rdi.toBitVec + 16) 1 = some 4 ∧
    Mem.loadInt (emptyState s ra).dmem (s.regs.rdi.toBitVec + 24) 8 = some 16 ∧
    Mem.loadInt (emptyState s ra).dmem (s.regs.rdi.toBitVec + 32) 8 = some 0 :=
  CodecDeserialize.sequence_loads (Dispatch.savedMem s) s.regs.rdi.toBitVec 16 0 bound

/-- The shared operational model takes this same shortcut without effects,
regardless of the raw child schema and arbitrarily represented logical limit. -/
theorem empty_model (element : SszNative.Codec.Desc) (limit : Option NatOperand)
    (visit : CodecDecode.Input → Delimited.ArenaState → CodecDecode.Outcome CodecDecode.Node)
    (input : CodecDecode.Input) (arena : Delimited.ArenaState) (empty : input.bytes.size = 0) :
    CodecDecode.list element limit visit input arena =
      CodecDecode.unchanged arena.used (.ok (.seq none [])) := by
  simp [CodecDecode.list, CodecDecode.compositeSize, CodecDecode.bind,
    CodecDecode.unchanged, empty]

end SszX86.CodecDecodeList
