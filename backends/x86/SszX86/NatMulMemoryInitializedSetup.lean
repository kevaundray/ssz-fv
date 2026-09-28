import SszX86.NatMulMemoryInitialized
import SszX86.NatMulLoopFetch

namespace SszX86.NatMul
open SszNative
open UintCodec

/-- PC501's real destination-pointer spill preserves the initialized buffer,
original inputs, arena cursor, and the four earlier local spills. -/
theorem Initialized.setup {original current : MachineData} {left right : NatOperand}
    {address capacity used ra : BitVec 64} {r : Arena.Reservation} {t : MachineState}
    (owned : Owned original left right address capacity used ra)
    (stack : current.regs.rsp.toBitVec = original.regs.rsp.toBitVec-88)
    (counts : Reservation.total current = left.wordCount+right.wordCount)
    (model : SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat =
      NatArithmetic.committed r (SszNative.NatMul.writtenWords left right))
    (initialized : Initialized original current left right address capacity used r t)
    (rightPointer : BitVec 64) (next : Int64) :
    Initialized original current left right address capacity used r (Product.setupState t.1 rightPointer, next) ∧
      Mem.loadInt (Product.setupState t.1 rightPointer).dmem (current.regs.rsp.toBitVec+8#64) 8 =
        some (r.pointer : Int) := by
  have allocated : (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).allocation = some r := by
    rw [model]
    rfl
  have length : (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).written.length =
      Reservation.total current := by
    rw [model]
    change (SszNative.NatMul.writtenWords left right).length = Reservation.total current
    rw [SszNative.NatMul.writtenWords_length, counts]
  have separation := initialization_separation original current left right address capacity used ra owned stack r allocated
    (8*Reservation.total current) (by rw [length])
  have pointerNat := allocated_pointer_nat original left right address capacity used ra owned r allocated
  have storeAddress : t.1.regs.rsp.toBitVec+8#64 =
      (original.regs.rsp.toBitVec-96)+BitVec.ofNat 64 16 := by
    rw [initialized.stack, stack]
    bv_omega
  have work : WorkFrame original (Product.setupState t.1 rightPointer).dmem
      (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat) := by
    change WorkFrame original (Mem.storeInt t.1.dmem (t.1.regs.rsp.toBitVec+8#64) 8
      t.1.regs.rbx.toBitVec.toInt) _
    rw [storeAddress]
    exact initialized.work.store_local owned.stack_low 16 8 (by decide) _
  have frame := work.to_frame owned.stack_low
  have localLoad (off : Nat) (inside : off+8 ≤ 40) (apart : off+8 ≤ 8 ∨ 16 ≤ off) :
      Mem.loadInt (Product.setupState t.1 rightPointer).dmem (current.regs.rsp.toBitVec+BitVec.ofNat 64 off) 8 =
        Mem.loadInt t.1.dmem (current.regs.rsp.toBitVec+BitVec.ofNat 64 off) 8 := by
    change Mem.loadInt (Mem.storeInt t.1.dmem (t.1.regs.rsp.toBitVec+8#64) 8 t.1.regs.rbx.toBitVec.toInt)
      (current.regs.rsp.toBitVec+BitVec.ofNat 64 off) 8 = _
    rw [initialized.stack]
    apply BoolCodec.load_store_disjoint
    intro i hi j hj
    bv_omega
  have cursorLoad : widthLoad (Product.setupState t.1 rightPointer).dmem (original.regs.r9.toNat+16) 8 =
      widthLoad t.1.dmem (original.regs.r9.toNat+16) 8 := by
    unfold widthLoad
    congr 1
    change Mem.loadInt (Mem.storeInt t.1.dmem (t.1.regs.rsp.toBitVec+8#64) 8 t.1.regs.rbx.toBitVec.toInt)
      (BitVec.ofNat 64 (original.regs.r9.toBitVec.toNat+16)) 8 = _
    rw [width_address, initialized.stack]
    apply BoolCodec.load_store_disjoint
    intro i hi j hj equal
    apply separation.stack_cursor (8+j) (by omega) i hi
    simpa only [memmove_addr_add] using equal.symm
  have zeroLoad (index : Nat) (inside : index < Reservation.total current) :
      widthLoad (Product.setupState t.1 rightPointer).dmem (r.pointer+8*index) 8 =
        widthLoad t.1.dmem (r.pointer+8*index) 8 := by
    unfold widthLoad
    congr 1
    change Mem.loadInt (Mem.storeInt t.1.dmem (t.1.regs.rsp.toBitVec+8#64) 8 t.1.regs.rbx.toBitVec.toInt)
      (BitVec.ofNat 64 (r.pointer+8*index)) 8 = _
    rw [BitVec.ofNat_add, initialized.stack]
    apply BoolCodec.load_store_disjoint
    intro i hi j hj equal
    apply separation.stack_buffer (8+j) (by omega) (8*index+i) (by omega)
    simpa only [memmove_addr_add] using equal.symm
  constructor
  · refine ⟨initialized.stack, initialized.destination, work,
      operand_preserved original left right left address capacity used ra owned _ frame owned.left_at owned.left_owned,
      operand_preserved original left right right address capacity used ra owned _ frame owned.right_at owned.right_owned,
      ?_, cursorLoad.trans initialized.cursor, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact Large.mapped_store _ _ _ _ _ _ initialized.output_mapped
    · intro i
      rw [zeroLoad i.val (by simpa only [List.length_replicate] using i.isLt)]
      exact initialized.zero_words i
    · exact Large.mapped_store _ _ _ _ _ _ initialized.destination_mapped
    · exact Large.mapped_store _ _ _ _ _ _ initialized.locals_mapped
    · have first := localLoad 0 (by decide) (by decide)
      simp only [BitVec.add_zero] at first
      exact first.trans initialized.slot0
    · exact (localLoad 16 (by decide) (by decide)).trans initialized.slot16
    · exact (localLoad 24 (by decide) (by decide)).trans initialized.slot24
    · exact (localLoad 32 (by decide) (by decide)).trans initialized.slot32
  · have stored := Measure.Bits.stored_word_load t.1.dmem (t.1.regs.rsp.toBitVec+8#64) t.1.regs.rbx.toBitVec
    simpa only [Product.setupState, initialized.stack, initialized.destination, pointerNat] using stored

end SszX86.NatMul
