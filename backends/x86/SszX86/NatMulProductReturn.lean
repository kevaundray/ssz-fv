import SszX86.NatMulProduct
import SszX86.NatMulResultReturn

namespace SszX86.NatMul
open SszNative
open UintCodec

theorem product_finish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (lp rp : BitVec 64) (lw rw : List (BitVec 64))
    (address capacity used ra : BitVec 64)
    (owned : Owned s (.large lp lw) (.large rp rw) address capacity used ra)
    (r : Arena.Reservation)
    (outcome : SszNative.NatMul.run (.large lp lw) (.large rp rw) address.toNat capacity.toNat used.toNat =
      NatArithmetic.committed r (SszNative.NatMul.writtenWords (.large lp lw) (.large rp rw)))
    (work : WorkFrame s t.dmem
      (SszNative.NatMul.run (.large lp lw) (.large rp rw) address.toNat capacity.toNat used.toNat))
    (hl : 0 < Limbs.sigWords lw) (hr : 0 < Limbs.sigWords rw)
    (cursor : widthLoad t.dmem (s.regs.r9.toNat+16) 8 = some r.used)
    (outputMapped : Large.Mapped t.dmem s.regs.rdi.toBitVec 72)
    (output : Mem.loadInt t.dmem (t.regs.rsp.toBitVec + 24#64) 8 = some (s.regs.rdi.toNat : Int))
    (stack : t.regs.rsp = s.regs.rsp - 88) (simd : t.zmms = s.zmms)
    (rsi : t.regs.rsi.toBitVec = rp) (r10 : t.regs.r10.toBitVec = BitVec.ofNat 64 r.pointer)
    (r12 : t.regs.r12.toBitVec = BitVec.ofNat 64 (Limbs.sigWords lw))
    (r13 : t.regs.r13.toBitVec = BitVec.ofNat 64 (Limbs.sigWords rw))
    (r14 : t.regs.r14.toBitVec = BitVec.ofNat 64 (Limbs.sigWords lw+Limbs.sigWords rw))
    (r15 : t.regs.r15.toBitVec = 0#64)
    (rbp : t.regs.rbp.toBitVec = BitVec.ofNat 64 (Limbs.sigWords lw+Limbs.sigWords rw) - 1)
    (locals : Product.Locals t.dmem t.regs.rsp.toBitVec lp (BitVec.ofNat 64 lw.length) (BitVec.ofNat 64 r.pointer))
    (zero : NatMemory.wordsAt (widthLoad t.dmem) r.pointer
      (List.replicate (Limbs.sigWords lw+Limbs.sigWords rw) 0))
    (bufferMapped : Large.Mapped t.dmem (BitVec.ofNat 64 r.pointer)
      (8*(Limbs.sigWords lw+Limbs.sigWords rw))) :
    Eventually (step e) (Post s (.large lp lw) (.large rp rw) address capacity used ra) (t, base+512) := by
  have allocated : (SszNative.NatMul.run (.large lp lw) (.large rp rw)
      address.toNat capacity.toNat used.toNat).allocation = some r := by rw [outcome]; rfl
  have writes : (SszNative.NatMul.run (.large lp lw) (.large rp rw)
      address.toNat capacity.toNat used.toNat).written =
      SszNative.NatMul.writtenWords (.large lp lw) (.large rp rw) := by rw [outcome]; rfl
  have length : (SszNative.NatMul.run (.large lp lw) (.large rp rw)
      address.toNat capacity.toNat used.toNat).written.length = Limbs.sigWords lw+Limbs.sigWords rw := by
    rw [writes, SszNative.NatMul.writtenWords_length]
    rfl
  have bounds := allocation_bounds s (.large lp lw) (.large rp rw) address capacity used ra owned r allocated
  have pointerNat := allocated_pointer_nat s (.large lp lw) (.large rp rw) address capacity used ra owned r allocated
  have frame := work.to_frame owned.stack_low
  have leftAt := operand_preserved s (.large lp lw) (.large rp rw) (.large lp lw)
    address capacity used ra owned t.dmem frame owned.left_at owned.left_owned
  have rightAt := operand_preserved s (.large lp lw) (.large rp rw) (.large rp rw)
    address capacity used ra owned t.dmem frame owned.right_at owned.right_owned
  have stackNat : t.regs.rsp.toBitVec.toNat = s.regs.rsp.toNat - 88 := by
    have low := owned.stack_low
    change 96 ≤ s.regs.rsp.toBitVec.toNat at low
    rw [stack]
    change (s.regs.rsp.toBitVec-88#64).toNat = s.regs.rsp.toBitVec.toNat-88
    bv_omega
  have stackApart : Body.Apart t.regs.rsp.toBitVec.toNat 24 r.pointer
      (8*(Limbs.sigWords lw+Limbs.sigWords rw)) := by
    rw [stackNat]
    have apart := owned.arena_stack
    have low := owned.stack_low
    have usedBound := owned.used_bound
    rw [length] at bounds
    unfold Body.Apart at *
    omega
  apply Product.product_cps e base hc t lp rp (BitVec.ofNat 64 r.pointer) lw rw leftAt rightAt hl hr
  · simpa only [pointerNat, length] using bounds.2.2.2.2.2
  · simpa only [NatAdd.Carry.Apart, length] using allocated_operand_apart s (.large lp lw) (.large rp rw) (.large lp lw)
      address capacity used ra owned owned.left_at owned.left_owned r allocated
  · simpa only [NatAdd.Carry.Apart, length] using allocated_operand_apart s (.large lp lw) (.large rp rw) (.large rp rw)
      address capacity used ra owned owned.right_at owned.right_owned r allocated
  · rw [stackNat]
    have bound := owned.return_bound
    omega
  · simpa only [pointerNat] using stackApart
  · exact rsi
  · exact r10
  · exact r12
  · exact r13
  · exact r14
  · exact r15
  · exact locals
  · simpa only [pointerNat] using zero
  · exact bufferMapped
  intro u stable index count written buffer finalMapped
  have buffer' : BufferFrame t.dmem u.dmem r.pointer
      (8*(SszNative.NatMul.run (.large lp lw) (.large rp rw)
        address.toNat capacity.toNat used.toNat).written.length) := by
    simpa only [pointerNat, length] using buffer
  have finalWork := work.buffer r allocated buffer'
  have savedLoad (off : Nat) (inside : off+8 ≤ 40) :
      Mem.loadInt u.dmem (t.regs.rsp.toBitVec+BitVec.ofNat 64 off) 8 =
        Mem.loadInt t.dmem (t.regs.rsp.toBitVec+BitVec.ofNat 64 off) 8 := by
    have addressEq : t.regs.rsp.toBitVec+BitVec.ofNat 64 off =
        (s.regs.rsp.toBitVec-96)+BitVec.ofNat 64 (off+8) := by
      rw [stack]
      change (s.regs.rsp.toBitVec-88#64)+BitVec.ofNat 64 off =
        (s.regs.rsp.toBitVec-96)+BitVec.ofNat 64 (off+8)
      bv_omega
    rw [addressEq]
    exact buffer'.stack_load owned r allocated (off+8) 8 (by omega)
  apply result_finish_cps e base hc s u (.large lp lw) (.large rp rw)
    address capacity used ra owned r allocated finalWork
  · simpa only [pointerNat, writes] using written
  · have cursorEq : Mem.loadInt u.dmem (s.regs.r9.toBitVec+16#64) 8 =
        Mem.loadInt t.dmem (s.regs.r9.toBitVec+16#64) 8 := by
      apply buffer'.load
      · have bound := owned.header_bound
        change s.regs.r9.toBitVec.toNat+24 ≤ 2^64 at bound
        bv_omega
      · have apart := owned.arena_header
        have usedBound := owned.used_bound
        have bound := owned.header_bound
        change s.regs.r9.toBitVec.toNat+24 ≤ 2^64 at bound
        have natural : (s.regs.r9.toBitVec+16#64).toNat = s.regs.r9.toNat+16 := by
          change (s.regs.r9.toBitVec+16#64).toNat = s.regs.r9.toBitVec.toNat+16
          bv_omega
        rw [natural]
        unfold Body.Apart at *
        omega
    rw [allocation_cursor _ _ _ _ _ r allocated]
    change widthLoad u.dmem (s.regs.r9.toBitVec.toNat+16) 8 = some r.used
    change widthLoad t.dmem (s.regs.r9.toBitVec.toNat+16) 8 = some r.used at cursor
    simp only [widthLoad, width_address] at cursor ⊢
    rw [cursorEq]
    exact cursor
  · apply buffer'.mapped s.regs.rdi.toBitVec 72 outputMapped owned.output_bound
    have apart := owned.arena_output
    have usedBound := owned.used_bound
    change Body.Apart s.regs.rdi.toNat 72 r.pointer _
    unfold Body.Apart at *
    omega
  · simpa only [length, stable.rbp] using rbp
  · simpa only [stable.rsp, savedLoad 24 (by decide)] using output
  · have slot := locals.destination
    simpa only [stable.rsp, savedLoad 8 (by decide), pointerNat] using slot
  · exact stable.rsp.trans stack
  · exact stable.zmms.trans simd

end SszX86.NatMul
