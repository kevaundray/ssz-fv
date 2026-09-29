import SszX86.NatMulReserveSpills

namespace SszX86.NatMul.Reservation
open UintCodec

/-- Later local spills do not undo the successful arena cursor commit. -/
theorem prepared_cursor (s : MachineData)
    (apart : Large.Disjoint s.regs.rsp.toBitVec (s.regs.r9.toBitVec + 16#64) 40 8) :
    Mem.loadInt (preparedMem s) (s.regs.r9.toBitVec + 16#64) 8 =
      some (s.regs.r11.toNat : Int) := by
  have separated (off : Nat) (inside : off + 8 ≤ 40) :
      Large.Disjoint (s.regs.r9.toBitVec + 16#64)
        (s.regs.rsp.toBitVec + BitVec.ofNat 64 off) 8 8 := by
    intro i hi j hj equal
    have ne := apart (off + j) (by omega) i hi
    apply ne
    simpa only [memmove_addr_add] using equal.symm
  unfold preparedMem cursorMem
  rw [BoolCodec.load_store_disjoint _ _ _ _ _ _
      (by word_simpa [Large.Disjoint] using separated 0 (by decide)),
    BoolCodec.load_store_disjoint _ _ _ _ _ _ (separated 32 (by decide)),
    BoolCodec.load_store_disjoint _ _ _ _ _ _ (separated 16 (by decide))]
  exact Measure.Bits.stored_word_load _ _ _

/-- A physically protected header word is unchanged by both memset and its
actual pushed return address. No future header value is assumed. -/
theorem helper_cursor_load (s : MachineData) (ra : BitVec 64) (n : Nat)
    (t : MachineState) (post : MemsetCall.Post s ra n t) (cursor : BitVec 64)
    (buffer : Large.Disjoint cursor s.regs.rdi.toBitVec 8 n)
    (stack : Large.Disjoint cursor (s.regs.rsp.toBitVec - 8#64) 8 8) :
    Mem.loadInt t.1.dmem cursor 8 = Mem.loadInt s.dmem cursor 8 := by
  apply memmove_loadInt_congr
  intro i hi
  apply post.frame
  rintro (⟨j, hj, equal⟩ | ⟨j, hj, equal⟩)
  · exact buffer i hi j hj equal
  · exact stack i hi j hj equal

end SszX86.NatMul.Reservation
