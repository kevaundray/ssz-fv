import SszX86.BitListProgressiveOwned
import SszX86.BitListStaging

namespace SszX86.BitList
open SszNative UintCodec BoolCodec

theorem list_spNat (s : MachineData) (pointer payload ra : BitVec 64)
    (low : 112 ≤ s.regs.rsp.toNat) :
    (listState s pointer payload ra).regs.rsp.toNat = s.regs.rsp.toNat - 8 := by
  simp only [listState, UInt64.toNat_ofBitVec]
  simp only [← UInt64.toNat_toBitVec] at low ⊢
  bv_omega

theorem list_optionNat (s : MachineData) (pointer payload ra : BitVec 64)
    (high : s.regs.rsp.toNat + 368 ≤ 2^64) :
    (listState s pointer payload ra).regs.rsi.toNat = s.regs.rsp.toNat + 16 := by
  simp only [listState, UInt64.toNat_ofBitVec]
  simp only [← UInt64.toNat_toBitVec] at high ⊢
  bv_omega

theorem list_mapped (s : MachineData) (pointer payload ra p : BitVec 64) (n : Nat)
    (h : Large.Mapped s.dmem p n) : Large.Mapped (listState s pointer payload ra).dmem p n := by
  rw [list_memory]
  exact staged_mapped _ _ _ _ _ _ _ h

theorem list_frame (s : MachineData) (pointer payload ra : BitVec 64)
    (low : 112 ≤ s.regs.rsp.toNat) (high : s.regs.rsp.toNat + 368 ≤ 2^64)
    (a : BitVec 64) (outside : Body.Outside a.toNat (workStart s false) (workBytes false)) :
    (listState s pointer payload ra).dmem.get? a = s.dmem.get? a := by
  rw [list_memory]
  apply staged_frame
  intro i hi
  change Body.Outside a.toNat (s.regs.rsp.toNat - 112) 152 at outside
  simp only [← UInt64.toNat_toBitVec] at low high outside
  unfold Body.Outside at outside
  bv_omega

theorem list_load (s : MachineData) (pointer payload ra : BitVec 64)
    (low : 112 ≤ s.regs.rsp.toNat) (high : s.regs.rsp.toNat + 368 ≤ 2^64)
    (p n : Nat) (bound : p + n ≤ 2^64)
    (apart : Body.Apart p n (workStart s false) (workBytes false)) :
    Mem.loadInt (listState s pointer payload ra).dmem (BitVec.ofNat 64 p) n =
      Mem.loadInt s.dmem (BitVec.ofNat 64 p) n := by
  apply memmove_loadInt_congr
  intro i hi
  apply list_frame s pointer payload ra low high
  have within : p + i < 2^64 := by omega
  rw [← BitVec.ofNat_add]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt within]
  unfold Body.Outside Body.Apart at *
  omega

theorem list_width (s : MachineData) (pointer payload ra : BitVec 64)
    (low : 112 ≤ s.regs.rsp.toNat) (high : s.regs.rsp.toNat + 368 ≤ 2^64)
    (p n : Nat) (bound : p + n ≤ 2^64)
    (apart : Body.Apart p n (workStart s false) (workBytes false)) :
    widthLoad (listState s pointer payload ra).dmem p n = widthLoad s.dmem p n := by
  unfold widthLoad
  rw [list_load s pointer payload ra low high p n bound apart]

theorem list_fields (s : MachineData) (pointer payload ra : BitVec 64) :
    Mem.loadInt (listState s pointer payload ra).dmem (s.regs.rsp.toBitVec - 8) 8 =
      some (Int.ofBytes (wordBytes ra)) ∧
    widthLoad (listState s pointer payload ra).dmem (s.regs.rsp.toNat + 16) 4 = some 1 ∧
    widthLoad (listState s pointer payload ra).dmem (s.regs.rsp.toNat + 24) 8 = some pointer.toNat ∧
    widthLoad (listState s pointer payload ra).dmem (s.regs.rsp.toNat + 32) 8 = some payload.toNat := by
  have fields := staged_fields s.dmem (s.regs.rsp.toBitVec - 8) pointer payload ra
  have off (n : Nat) : BitVec.ofNat 64 (s.regs.rsp.toNat + n) =
      s.regs.rsp.toBitVec + BitVec.ofNat 64 n := by
    simp only [← UInt64.toNat_toBitVec, width_address]
  have a : s.regs.rsp.toBitVec - 8 + 24#64 = s.regs.rsp.toBitVec + 16#64 := by bv_omega
  have b : s.regs.rsp.toBitVec - 8 + 32#64 = s.regs.rsp.toBitVec + 24#64 := by bv_omega
  have c : s.regs.rsp.toBitVec - 8 + 40#64 = s.regs.rsp.toBitVec + 32#64 := by bv_omega
  rw [a, b, c] at fields
  refine ⟨?_, ?_, ?_, ?_⟩
  · have encoded : Int.ofBytes (wordBytes ra) = (ra.toNat : Int) := by
      rw [wordBytes, ← registerBytes_eq_uintBytes, ofBytes_toBytes]
      exact stage_signed ra
    rw [list_memory, encoded]
    exact fields.1
  · change (Mem.loadInt _ (BitVec.ofNat 64 (s.regs.rsp.toNat + 16)) 4).map Int.toNat = some 1
    rw [list_memory, off, fields.2.1]
    rfl
  · change (Mem.loadInt _ (BitVec.ofNat 64 (s.regs.rsp.toNat + 24)) 8).map Int.toNat = some pointer.toNat
    rw [list_memory, off, fields.2.2.1]
    rfl
  · change (Mem.loadInt _ (BitVec.ofNat 64 (s.regs.rsp.toNat + 32)) 8).map Int.toNat = some payload.toNat
    rw [list_memory, off, fields.2.2.2]
    rfl

end SszX86.BitList
