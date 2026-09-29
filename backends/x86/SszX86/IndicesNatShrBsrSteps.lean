import SszX86.IndicesNatShrBsrLoop
import SszX86.DelimitedWorkMemory

set_option autoImplicit false

namespace SszX86.IndicesNatShr
open UintCodec

def bsrMem (s : MachineData) : DataMem :=
  let m := Mem.storeInt s.dmem (s.regs.rsp.toBitVec - 16#64) 8 s.regs.r10.toBitVec.toInt
  Mem.storeInt m (s.regs.rsp.toBitVec - 16#64 + 8#64) 8 s.regs.r9.toBitVec.toInt

def bsrPushed (s : MachineData) : MachineData :=
  {s with dmem := bsrMem s,
    regs := {s.regs with rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec - 16#64)}}

def bsrPublished (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with r11 := s.regs.r9}, status := flags}

def bsrRestored (s : MachineData) (r9 r10 : BitVec 64) : MachineData :=
  {s with regs := {s.regs with rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec + 16#64),
    r9 := UInt64.ofBitVec r9, r10 := UInt64.ofBitVec r10}}

private theorem wrapped_address (value : Int) :
    BitVec.ofInt 64 (value.bmod 18446744073709551616) = BitVec.ofInt 64 value := by
  simpa only [BitVec.toInt_ofInt, Nat.reducePow] using
    (BitVec.ofInt_toInt (x := BitVec.ofInt 64 value))

private theorem lower_address (pointer : BitVec 64) :
    BitVec.ofInt 64 ((pointer.toInt + (-16)).bmod 18446744073709551616) =
      pointer - 16#64 := by
  have minus : BitVec.ofInt 64 (-16) = -(16#64) := by decide
  simp only [wrapped_address, BitVec.ofInt_add, BitVec.ofInt_toInt,
    minus, ← BitVec.sub_eq_add_neg]

private def bsrReserved (s : MachineData) : MachineData :=
  {s with regs := {s.regs with rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec - 16#64)}}

private def bsrFirstStore (s : MachineData) : MachineData :=
  {s with dmem := Mem.storeInt s.dmem s.regs.rsp.toBitVec 8 s.regs.r10.toBitVec.toInt}

private def bsrSecondStore (s : MachineData) : MachineData :=
  {s with dmem := Mem.storeInt s.dmem (s.regs.rsp.toBitVec + 8#64) 8 s.regs.r9.toBitVec.toInt}

private theorem bsr_reserve_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (post : MachineState → Prop)
    (next : Eventually (step e) post (bsrReserved s, base + 85)) :
    Eventually (step e) post (s, base + 80) := by
  indices_shr_step 21 using code
  simpa [bsrReserved, lower_address, BitVec.sub_eq_add_neg] using next

private theorem bsr_first_store_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (mapped : Large.Mapped s.dmem s.regs.rsp.toBitVec 16)
    (post : MachineState → Prop)
    (next : Eventually (step e) post (bsrFirstStore s, base + 89)) :
    Eventually (step e) post (s, base + 85) := by
  indices_shr_step 22 using code
  apply Delimited.store_cps
  · exact Delimited.mapped_load_zero _ _ 16 8 mapped (by decide)
  simpa only [Effects.All, bsrFirstStore] using next

private theorem bsr_second_store_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (mapped : Large.Mapped s.dmem s.regs.rsp.toBitVec 16)
    (post : MachineState → Prop)
    (next : Eventually (step e) post (bsrSecondStore s, base + 94)) :
    Eventually (step e) post (s, base + 89) := by
  indices_shr_step 23 using code
  apply Delimited.store_cps
  · exact Large.mapped_load _ _ 16 8 8 mapped (by decide)
  simpa only [Effects.All, bsrSecondStore] using next

/-- The literal original lowering writes only its two private stack words. -/
theorem bsr_push_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (mapped : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 16#64) 16)
    (post : MachineState → Prop)
    (next : Eventually (step e) post (bsrPushed s, base + 94)) :
    Eventually (step e) post (s, base + 80) := by
  apply bsr_reserve_cps e base code
  apply bsr_first_store_cps e base code
  · exact mapped
  apply bsr_second_store_cps e base code
  · exact Large.mapped_store _ _ _ _ _ _ mapped
  simpa only [bsrReserved, bsrFirstStore, bsrSecondStore, bsrPushed, bsrMem] using next

theorem bsr_start_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (nonzero : s.regs.r11.toBitVec ≠ 0#64)
    (post : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) post
      (bsrState s (-1#64) s.regs.r11.toBitVec flags, base + 109)) :
    Eventually (step e) post (s, base + 94) := by
  indices_shr_step 24 using code
  indices_shr_step 25 using code
  constructor <;> indices_shr_step 26 using code
  all_goals
    simp [nonzero, StatusFlags.from_result, Effects.All]
    indices_shr_step 27 using code
    simpa [bsrState] using next _

/-- The original comparison's flags are exposed rather than silently retained. -/
theorem bsr_publish_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (post : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) post (bsrPublished s flags, base + 126)) :
    Eventually (step e) post (s, base + 117) := by
  indices_shr_step 31 using code
  indices_shr_step 32 using code
  indices_shr_step 33 using code
  simpa [bsrPublished] using next _

theorem bsr_restore_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (r9 r10 : BitVec 64)
    (lo : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (r10.toNat : Int))
    (hi : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 8#64) 8 = some (r9.toNat : Int))
    (post : MachineState → Prop)
    (next : Eventually (step e) post (bsrRestored s r9 r10, base + 140)) :
    Eventually (step e) post (s, base + 126) := by
  indices_shr_step 34 using code
  indices_shr_load lo
  indices_shr_step 35 using code
  indices_shr_load hi
  indices_shr_step 36 using code
  simpa [bsrRestored] using next

/-- The restore observations follow from these original stores, not from a
continuation or a supplied future-memory assertion. -/
theorem bsr_saved_reads (s : MachineData) (stackLow : 16 ≤ s.regs.rsp.toNat) :
    Mem.loadInt (bsrMem s) (s.regs.rsp.toBitVec - 16#64) 8 =
      some (s.regs.r10.toNat : Int) ∧
    Mem.loadInt (bsrMem s) (s.regs.rsp.toBitVec - 16#64 + 8#64) 8 =
      some (s.regs.r9.toNat : Int) := by
  have lower : (s.regs.rsp.toBitVec - 16#64).toNat = s.regs.rsp.toNat - 16 :=
    BitVec.toNat_sub_of_le (by change 16 ≤ s.regs.rsp.toNat; exact stackLow)
  have bound : (s.regs.rsp.toBitVec - 16#64).toNat + 16 ≤ 2 ^ 64 := by
    rw [lower]
    have top := s.regs.rsp.toBitVec.isLt
    change s.regs.rsp.toNat < 2 ^ 64 at top
    omega
  constructor
  · unfold bsrMem
    rw [BoolCodec.load_store_disjoint _ _ _ _ _ _ (by
      intro i hi j hj same
      have collision := memmove_addr_injective (s.regs.rsp.toBitVec - 16#64) 16
        i (8 + j) bound (by omega) (by omega)
        (by simpa only [memmove_addr_add] using same)
      omega)]
    exact Delimited.stored_word_load _ _ _
  · exact Delimited.stored_word_load _ _ _

end SszX86.IndicesNatShr
