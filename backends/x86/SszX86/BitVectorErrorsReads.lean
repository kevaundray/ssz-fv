import SszX86.BitVectorErrors
import SszX86.BitVectorErrorsReadMemory

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

macro "errors_private_read " off:num " from " observed:term : tactic => `(tactic|
  exact errors_raw_read _ _ $off _ _ (by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using $observed))

/-- The add branch obtains its padding from mapped memory and its status from
its real loaded register, rather than requiring an assumed future error image. -/
theorem add_reads_of_private (u : MachineData) (reason : NatArithmetic.Failure)
    (observed : NatArithmetic.AddResultAt (widthLoad u.dmem)
      (u.regs.rsp.toNat + 16) (.error reason))
    (privateMapped : Large.Mapped u.dmem (u.regs.rsp.toBitVec + 16#64) 72)
    (statusLoaded : Mem.loadInt u.dmem (u.regs.rsp.toBitVec + 80#64) 4 =
      some ((u.regs.rax.toBitVec.setWidth 32).toNat : Int)) :
    ∃ padding : BitVec 32, AddErrorReads u reason padding := by
  rcases observed with ⟨h0, h1, h2, h3, h4, h5, h6, h7, reasonAt⟩
  obtain ⟨padding, paddingAt⟩ := mapped_word u.dmem
    ((u.regs.rsp.toBitVec + 16#64) + BitVec.ofNat 64 68) 4
    (Large.mapped_load _ _ 72 68 4 privateMapped (by decide))
  have reasonLoaded : Mem.loadInt u.dmem (u.regs.rsp.toBitVec + 80#64) 4 =
      some ((arithmeticErrorImage reason padding).reason.toNat : Int) := by
    apply errors_raw_read _ _ 80 4
    cases reason <;>
      simpa only [Nat.add_assoc, Nat.reduceAdd, arithmeticErrorImage,
        show (32768#32).toNat = 32768 by decide,
        show (32770#32).toNat = 32770 by decide] using reasonAt
  refine ⟨padding, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · errors_private_read 16 from h0
  · errors_private_read 24 from h1
  · errors_private_read 32 from h2
  · errors_private_read 40 from h3
  · errors_private_read 48 from h4
  · errors_private_read 56 from h5
  · errors_private_read 64 from h6
  · errors_private_read 72 from h7
  · exact errors_word_unique _ _ 4 _ _ statusLoaded reasonLoaded
  · simpa only [BitVec.add_assoc, BitVec.reduceAdd] using paddingAt

/-- Division's two actual staged words and R13 are related to the private
observation; the copied final padding is still recovered from physical memory. -/
theorem division_reads_of_private (u : MachineData) (reason : NatArithmetic.Failure)
    (observed : NatArithmetic.DivisionResultAt (widthLoad u.dmem)
      (u.regs.rsp.toNat + 16) (.error reason))
    (privateMapped : Large.Mapped u.dmem (u.regs.rsp.toBitVec + 16#64) 72)
    (statusLoaded : Mem.loadInt u.dmem (u.regs.rsp.toBitVec + 80#64) 4 =
      some ((u.regs.rax.toBitVec.setWidth 32).toNat : Int))
    (textCache : Mem.loadInt u.dmem (u.regs.rsp.toBitVec + 120#64) 8 =
      Mem.loadInt u.dmem (u.regs.rsp.toBitVec + 16#64) 8)
    (lengthCache : Mem.loadInt u.dmem (u.regs.rsp.toBitVec + 128#64) 8 =
      Mem.loadInt u.dmem (u.regs.rsp.toBitVec + 24#64) 8)
    (firstLoaded : Mem.loadInt u.dmem (u.regs.rsp.toBitVec + 32#64) 8 =
      some (u.regs.r13.toBitVec.toNat : Int)) :
    ∃ padding : BitVec 32, DivisionErrorReads u reason padding := by
  obtain ⟨padding, fields⟩ := add_reads_of_private u reason observed privateMapped statusLoaded
  refine ⟨padding, ⟨textCache.trans fields.text, lengthCache.trans fields.textLength,
    ?_, fields.firstPayload, fields.secondPointer, fields.secondPayload,
    fields.thirdPointer, fields.thirdPayload, fields.status, fields.paddingWord⟩⟩
  apply errors_word_unique _ _ 8 _ (0#64) firstLoaded
  exact fields.firstPointer

/-- The real private ExactResultAt determines every semantic field. The ninth
native copy word comes from mapped memory, and its low 32 bits are proved to be
three by coherence with the actual four-byte status load. -/
theorem exact_reads_of_private (u : MachineData) (expected : NatOperand) (actual : BitVec 64)
    (observed : NatNarrow.ExactResultAt (widthLoad u.dmem)
      (u.regs.rsp.toNat + 16) expected actual)
    (failed : NatNarrow.runExact expected actual = false)
    (privateMapped : Large.Mapped u.dmem (u.regs.rsp.toBitVec + 16#64) 72) :
    ∃ statusPadding : BitVec 64, ExactErrorReads u expected actual statusPadding := by
  simp only [NatNarrow.ExactResultAt, failed, Bool.false_eq_true, ↓reduceIte] at observed
  rcases observed with ⟨h0, h1, pair, h4, h5, h6, h7, reasonAt⟩
  obtain ⟨whole, wholeAt⟩ := mapped_word u.dmem
    ((u.regs.rsp.toBitVec + 16#64) + BitVec.ofNat 64 64) 8
    (Large.mapped_load _ _ 72 64 8 privateMapped (by decide))
  have wholeLoaded : Mem.loadInt u.dmem (u.regs.rsp.toBitVec + 80#64) 8 =
      some (whole.toNat : Int) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using wholeAt
  have reasonLoaded : Mem.loadInt u.dmem (u.regs.rsp.toBitVec + 80#64) 4 =
      some ((3#32).toNat : Int) := by
    apply errors_raw_read _ _ 80 4
    simpa only [Nat.add_assoc, Nat.reduceAdd, show (3#32).toNat = 3 by decide] using reasonAt
  refine ⟨whole, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, wholeLoaded,
    errors_load_low32 _ _ whole (3#32) wholeLoaded reasonLoaded, pair.2.2⟩⟩
  · errors_private_read 16 from h0
  · errors_private_read 24 from h1
  · errors_private_read 32 from pair.1
  · errors_private_read 40 from pair.2.1
  · errors_private_read 48 from h4
  · errors_private_read 56 from h5
  · errors_private_read 64 from h6
  · errors_private_read 72 from h7

end SszX86.BitVector
