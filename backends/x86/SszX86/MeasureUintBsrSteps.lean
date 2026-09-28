import SszX86.MeasureUintScan
import SszX86.DelimitedBitStack
import SszX86.DelimitedWorkMemory

namespace SszX86.Measure.Uint
open UintCodec

/-- Identical stack representation, but all execution below is at measure PCs. -/
abbrev bsrMem := Delimited.bitSaveMem

def bsrPushed (s : MachineData) : MachineData :=
  {s with
    dmem := bsrMem s
    regs := {s.regs with rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec - 16#64)}}

def bsrState (s : MachineData) (counter bits : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      r10 := UInt64.ofBitVec counter
      r11 := UInt64.ofBitVec bits}
    status := flags}

def bsrPublished (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with rdi := s.regs.r10}, status := flags}

def bsrRestored (s : MachineData) (r10 r11 : BitVec 64) : MachineData :=
  {s with regs := {s.regs with
    rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec + 16#64),
    r10 := UInt64.ofBitVec r10, r11 := UInt64.ofBitVec r11}}

private theorem bsr_wrapped_address (value : Int) :
    BitVec.ofInt 64 (value.bmod 18446744073709551616) = BitVec.ofInt 64 value := by
  simpa only [BitVec.toInt_ofInt, Nat.reducePow] using
    (BitVec.ofInt_toInt (x := BitVec.ofInt 64 value))

private theorem bsr_lower_address (pointer : BitVec 64) :
    BitVec.ofInt 64 ((pointer.toInt + (-16)).bmod 18446744073709551616) =
      pointer - 16#64 := by
  have minus : BitVec.ofInt 64 (-16) = -(16#64) := by decide
  simp only [bsr_wrapped_address, BitVec.ofInt_add, BitVec.ofInt_toInt,
    minus, ← BitVec.sub_eq_add_neg]

private def bsrReserved (s : MachineData) : MachineData :=
  {s with regs := {s.regs with rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec - 16#64)}}

private def bsrFirstStore (s : MachineData) : MachineData :=
  {s with dmem := Mem.storeInt s.dmem s.regs.rsp.toBitVec 8 s.regs.r11.toBitVec.toInt}

private def bsrSecondStore (s : MachineData) : MachineData :=
  {s with dmem := Mem.storeInt s.dmem (s.regs.rsp.toBitVec + 8#64) 8 s.regs.r10.toBitVec.toInt}

private theorem bsr_reserve_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (bsrReserved s, base + 1741)) :
    Eventually (step e) P (s, base + 1736) := by
  measure_step 235 using hc
  simpa [bsrReserved, bsr_lower_address, BitVec.sub_eq_add_neg] using next

private theorem bsr_first_store_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (memoryMapped : Large.Mapped s.dmem s.regs.rsp.toBitVec 16)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (bsrFirstStore s, base + 1745)) :
    Eventually (step e) P (s, base + 1741) := by
  measure_step 236 using hc
  apply Delimited.store_cps
  · exact Delimited.mapped_load_zero _ _ 16 8 memoryMapped (by decide)
  simpa only [Effects.All, bsrFirstStore] using next

private theorem bsr_second_store_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (memoryMapped : Large.Mapped s.dmem s.regs.rsp.toBitVec 16)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (bsrSecondStore s, base + 1750)) :
    Eventually (step e) P (s, base + 1745) := by
  measure_step 237 using hc
  apply Delimited.store_cps
  · exact Large.mapped_load _ _ 16 8 8 memoryMapped (by decide)
  simpa only [Effects.All, bsrSecondStore] using next

/-- The lowered BSR explicitly reserves and writes exactly two stack words. -/
theorem bsr_push_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData)
    (memoryMapped : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 16#64) 16)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (bsrPushed s, base + 1750)) :
    Eventually (step e) P (s, base + 1736) := by
  apply bsr_reserve_cps e base hc
  apply bsr_first_store_cps e base hc
  · exact memoryMapped
  apply bsr_second_store_cps e base hc
  · exact Large.mapped_store _ _ _ _ _ _ memoryMapped
  simpa only [bsrReserved, bsrFirstStore, bsrSecondStore,
    bsrPushed, bsrMem, Delimited.bitSaveMem] using next

/-- The zero-input edge is excluded by the actual selected limb, not by a BSR axiom. -/
theorem bsr_start_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (nonzero : s.regs.rcx.toBitVec ≠ 0#64)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (bsrState s (-1#64) s.regs.rcx.toBitVec flags, base + 1765)) :
    Eventually (step e) P (s, base + 1750) := by
  measure_step 238 using hc
  measure_step 239 using hc
  constructor <;> measure_step 240 using hc
  all_goals
    simp [nonzero, StatusFlags.from_result, Effects.All]
    measure_step 241 using hc
    simpa [bsrState] using next _

/-- Literal INC64/SHR64/JNE. Undefined flags are cut at this bounded boundary. -/
theorem bsr_iteration_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (counter bits : BitVec 64) (flags : StatusFlags)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (bsrState s (counter + 1) (bits >>> 1) flags,
        if bits >>> 1 = 0#64 then base + 1773 else base + 1765)) :
    Eventually (step e) P (bsrState s counter bits flags, base + 1765) := by
  have target := hc.targets ("measure_u1765", 1765) (by decide)
  simp only [bsrState]
  measure_step 242 using hc
  measure_step 243 using hc
  simp (config := {instances := true})
    [ShiftCountExpr.interpMasked, ShiftCountExpr.interp, ConstExpr.interp,
      BitVec.take, Effects.All]
  constructor <;> measure_step 244 using hc
  all_goals
    by_cases zero : bits >>> 1 = 0#64
    · have registerZero : UInt64.ofBitVec bits >>> 1 = UInt64.ofBitVec (0#64) := by
        change UInt64.ofBitVec bits >>> UInt64.ofNat 1 = UInt64.ofBitVec (0#64)
        rw [← UInt64.ofBitVec_shiftRight bits 1 (by decide), zero]
      simpa [registerZero, zero, bsrState, StatusFlags.from_result, Effects.All] using next _
    · simpa [zero, target, bsrState, StatusFlags.from_result, Effects.All] using next _

/-- The zero-displacement JMP is an actual instruction in the shipped lowering. -/
theorem bsr_publish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (bsrPublished s flags, base + 1782)) :
    Eventually (step e) P (s, base + 1773) := by
  measure_step 245 using hc
  measure_step 246 using hc
  measure_step 247 using hc
  simpa [bsrPublished] using next _

/-- Both scratch registers and the sixteen-byte reservation are restored. -/
theorem bsr_restore_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (r10 r11 : BitVec 64)
    (lo : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (r11.toNat : Int))
    (hi : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 8#64) 8 = some (r10.toNat : Int))
    (P : MachineState → Prop)
    (next : Eventually (step e) P (bsrRestored s r10 r11, base + 1796)) :
    Eventually (step e) P (s, base + 1782) := by
  measure_step 248 using hc
  measure_uint_load lo
  measure_step 249 using hc
  measure_uint_load hi
  measure_step 250 using hc
  simpa [bsrRestored] using next

/-- These reads are consequences of the original two writes, never future-memory premises. -/
theorem bsr_saved_reads (s : MachineData) :
    Mem.loadInt (bsrMem s) (s.regs.rsp.toBitVec - 16#64) 8 =
      some (s.regs.r11.toNat : Int) ∧
    Mem.loadInt (bsrMem s) (s.regs.rsp.toBitVec - 16#64 + 8#64) 8 =
      some (s.regs.r10.toNat : Int) := by
  constructor
  · unfold bsrMem Delimited.bitSaveMem
    rw [BoolCodec.load_store_disjoint _ _ _ _ _ _ (by
      intro i hi j hj
      bv_omega)]
    exact Delimited.stored_word_load _ _ _
  · exact Delimited.stored_word_load _ _ _

/-- The lowering's entire write footprint is exactly within its two private words. -/
theorem bsr_memory_frame (s : MachineData) :
    MemoryFrame s.dmem (bsrMem s) (fun a => InSpan a (s.regs.rsp.toBitVec - 16#64) 16) := by
  intro a outside
  have upper (m : DataMem) :
      (Mem.storeInt m (s.regs.rsp.toBitVec - 16#64 + 8#64) 8
        s.regs.r10.toBitVec.toInt).get? a = m.get? a := by
    apply memmove_store_lookup_outside
    intro i inside equal
    have within : i < 8 := by simpa only [Int.toBytes_length] using inside
    apply outside
    refine ⟨8 + i, by omega, ?_⟩
    rw [equal, BitVec.ofNat_add]
    bv_omega
  unfold bsrMem Delimited.bitSaveMem
  rw [upper]
  apply memmove_store_lookup_outside
  intro i inside equal
  have within : i < 8 := by simpa only [Int.toBytes_length] using inside
  exact outside ⟨i, by omega, equal⟩

end SszX86.Measure.Uint
