import SszX86.NatMulReserveArena
import SszX86.NatMulMemset

namespace SszX86.NatMul.Reservation
open UintCodec
open SszX86.Delimited
open Emit (MemoryFrame InSpan)

def cursorMem (s : MachineData) : DataMem :=
  let m := Mem.storeInt s.dmem (s.regs.rsp.toBitVec + 24#64) 8 s.regs.rdi.toBitVec.toInt
  Mem.storeInt m (s.regs.r9.toBitVec + 16#64) 8 s.regs.r11.toBitVec.toInt

def cursorState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    dmem := cursorMem s
    regs := {s.regs with
      rbp := UInt64.ofBitVec (s.regs.r12.toBitVec - s.regs.r10.toBitVec)}
    status := flags}

def preparedMem (s : MachineData) : DataMem :=
  let m := Mem.storeInt (cursorMem s) (s.regs.rsp.toBitVec + 16#64) 8 s.regs.rsi.toBitVec.toInt
  let m := Mem.storeInt m (s.regs.rsp.toBitVec + 32#64) 8 s.regs.rcx.toBitVec.toInt
  Mem.storeInt m s.regs.rsp.toBitVec 8 s.regs.rax.toBitVec.toInt

def preparedState (s : MachineData) (flags : StatusFlags) : MachineData :=
  let pointer := UInt64.ofBitVec (s.regs.r15.toBitVec + s.regs.r8.toBitVec)
  {s with
    dmem := preparedMem s
    regs := {s.regs with
      rbp := UInt64.ofBitVec (s.regs.r12.toBitVec - s.regs.r10.toBitVec)
      rbx := pointer
      rdi := pointer
      r15 := 0
      rsi := 0}
    status := flags}

theorem cursor_mapped (s : MachineData) (p : BitVec 64) (n : Nat)
    (hm : Large.Mapped s.dmem p n) : Large.Mapped (cursorMem s) p n := by
  unfold cursorMem
  repeat' first | exact hm | apply Large.mapped_store

theorem prepared_mapped (s : MachineData) (p : BitVec 64) (n : Nat)
    (hm : Large.Mapped s.dmem p n) : Large.Mapped (preparedMem s) p n := by
  unfold preparedMem cursorMem
  repeat' first | exact hm | apply Large.mapped_store

/-- The result spill precedes the exact arena cursor store. -/
theorem cursor_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (stack : Large.Mapped s.dmem s.regs.rsp.toBitVec 40)
    (arena : Large.Mapped s.dmem (s.regs.r9.toBitVec + 16#64) 8)
    (next : ∀ flags, Eventually (step e) P (cursorState s flags, base + 459)) :
    Eventually (step e) P (s, base + 444) := by
  have spill := Large.mapped_load s.dmem s.regs.rsp.toBitVec 40 24 8 stack (by decide)
  natmul_step 4 row 0 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
  apply store_cps
  · exact spill
  simp only [Effects.All]
  natmul_step 4 row 1 using hc
  natmul_step 4 row 2 using hc
  natmul_step 4 row 3 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
  apply store_cps
  · have hm : Large.Mapped
        (Mem.storeInt s.dmem (s.regs.rsp.toBitVec + 24#64) 8 s.regs.rdi.toBitVec.toInt)
        (s.regs.r9.toBitVec + 16#64) 8 := Large.mapped_store _ _ _ _ _ _ arena
    simpa (config := {instances := true}) [Width.bytes] using
      Large.mapped_load _ _ 8 0 8 hm (by decide)
  simp only [Effects.All]
  simpa [cursorState, cursorMem] using next _

/-- All four stack words are written before the real helper invocation. -/
theorem prepare_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (stack : Large.Mapped s.dmem s.regs.rsp.toBitVec 40)
    (arena : Large.Mapped s.dmem (s.regs.r9.toBitVec + 16#64) 8)
    (next : ∀ flags, Eventually (step e) P (preparedState s flags, base + 487)) :
    Eventually (step e) P (s, base + 444) := by
  apply cursor_cps e base hc s P stack arena
  intro f0
  have hm := cursor_mapped s s.regs.rsp.toBitVec 40 stack
  natmul_step 4 row 4 using hc
  natmul_step 4 row 5 using hc
  natmul_step 4 row 6 using hc
  constructor
  all_goals
    natmul_step 4 row 7 using hc
    natmul_step 4 row 8 using hc
    simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
    apply store_cps
    · exact Large.mapped_load _ _ 40 16 8 hm (by decide)
    simp only [Effects.All]
    natmul_step 4 row 9 using hc
    constructor
  all_goals
    natmul_step 4 row 10 using hc
    simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
    apply store_cps
    · apply Large.mapped_load _ _ 40 32 8 _ (by decide)
      exact Large.mapped_store _ _ _ _ _ _ hm
    simp only [Effects.All]
    natmul_step 4 row 11 using hc
    apply store_cps
    · have hm' := Large.mapped_store (cursorMem s) s.regs.rsp.toBitVec
        (s.regs.rsp.toBitVec + 16#64) 40 8 s.regs.rsi.toBitVec.toInt hm
      have hm'' := Large.mapped_store _ s.regs.rsp.toBitVec
        (s.regs.rsp.toBitVec + 32#64) 40 8 s.regs.rcx.toBitVec.toInt hm'
      simpa (config := {instances := true}) [Width.bytes, cursorState] using
        Large.mapped_load _ _ 40 0 8 hm'' (by decide)
    simp only [Effects.All]
    simpa [preparedState, preparedMem, cursorState, UInt64.add_comm] using next _

def Written (s : MachineData) (a : BitVec 64) : Prop :=
  InSpan a (s.regs.rsp.toBitVec + 24#64) 8 ∨
  InSpan a (s.regs.r9.toBitVec + 16#64) 8 ∨
  InSpan a (s.regs.rsp.toBitVec + 16#64) 8 ∨
  InSpan a (s.regs.rsp.toBitVec + 32#64) 8 ∨
  InSpan a s.regs.rsp.toBitVec 8

/-- No allocation payload bytes are introduced by the commitment lemma. -/
theorem prepared_frame (s : MachineData) :
    MemoryFrame s.dmem (preparedMem s) (Written s) := by
  intro a outside
  have outside24 : ∀ i < 8, a ≠ (s.regs.rsp.toBitVec + 24#64) + BitVec.ofNat 64 i := by
    intro i hi equal
    exact outside (Or.inl ⟨i, hi, equal⟩)
  have outsideCursor : ∀ i < 8, a ≠ (s.regs.r9.toBitVec + 16#64) + BitVec.ofNat 64 i := by
    intro i hi equal
    exact outside (Or.inr (Or.inl ⟨i, hi, equal⟩))
  have outside16 : ∀ i < 8, a ≠ (s.regs.rsp.toBitVec + 16#64) + BitVec.ofNat 64 i := by
    intro i hi equal
    exact outside (Or.inr (Or.inr (Or.inl ⟨i, hi, equal⟩)))
  have outside32 : ∀ i < 8, a ≠ (s.regs.rsp.toBitVec + 32#64) + BitVec.ofNat 64 i := by
    intro i hi equal
    exact outside (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, hi, equal⟩))))
  have outside0 : ∀ i < 8, a ≠ s.regs.rsp.toBitVec + BitVec.ofNat 64 i := by
    intro i hi equal
    exact outside (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, hi, equal⟩))))
  simp only [preparedMem, cursorMem, Mem.storeInt]
  rw [memmove_store_lookup_outside _ _ _ _ (by simpa only [Int.toBytes_length] using outside0),
    memmove_store_lookup_outside _ _ _ _ (by simpa only [Int.toBytes_length] using outside32),
    memmove_store_lookup_outside _ _ _ _ (by simpa only [Int.toBytes_length] using outside16),
    memmove_store_lookup_outside _ _ _ _ (by simpa only [Int.toBytes_length] using outsideCursor),
    memmove_store_lookup_outside _ _ _ _ (by simpa only [Int.toBytes_length] using outside24)]

end SszX86.NatMul.Reservation
