import SszX86.NatMulWordMath
import SszX86.DelimitedReservation

namespace SszX86.NatMulWord
open UintCodec

theorem commit_cursor_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData)
    (hm : ∃ old, Mem.loadInt s.dmem (s.regs.r8.toBitVec + 16#64) 8 = some old)
    (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with dmem := Mem.storeInt s.dmem (s.regs.r8.toBitVec + 16#64) 8 s.regs.rax.toBitVec.toInt},
        base + 314)) :
    Eventually (step e) P (s, base + 310) := by
  natmulword_step 2:14 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
  apply Delimited.store_cps
  · exact hm
  simp only [Effects.All]
  exact next

def initialProductState (s : MachineData) (limb : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec (s.regs.rcx.toBitVec * limb)
      rdx := UInt64.ofBitVec (productHigh s.regs.rcx.toBitVec limb)
      r10 := UInt64.ofBitVec (productHigh s.regs.rcx.toBitVec limb)}
    status := flags}

/-- Word zero is multiplied from the original source before it is spilled and
stored; the destination's former contents are never read by this algorithm. -/
theorem initial_product_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (limb : BitVec 64)
    (loaded : Mem.loadInt s.dmem s.regs.rsi.toBitVec 8 = some (limb.toNat : Int))
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (initialProductState s limb flags, base + 323)) :
    Eventually (step e) P (s, base + 314) := by
  have widthDifferent : (Width.W64 == Width.W8) = false := by decide
  natmulword_step 2:15 using hc
  natmulword_step 2:16 using hc
  natmulword_load loaded
  simp only [widthDifferent, Bool.false_eq_true, ↓reduceIte]
  constructor <;> constructor <;> constructor <;> constructor
  all_goals natmulword_step 2:17 using hc
  all_goals simpa [initialProductState, productHigh] using next _

def initialStores (s : MachineData) : DataMem :=
  let m := Mem.storeInt s.dmem s.regs.rsp.toBitVec 8 s.regs.rax.toBitVec.toInt
  let m := Mem.storeInt m (s.regs.rsp.toBitVec + 8#64) 8 s.regs.r13.toBitVec.toInt
  Mem.storeInt m (s.regs.r14.toBitVec + s.regs.r13.toBitVec) 8 s.regs.rax.toBitVec.toInt

theorem initial_stores_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (locals : Large.Mapped s.dmem s.regs.rsp.toBitVec 16)
    (payload : Large.Mapped s.dmem (s.regs.r14.toBitVec + s.regs.r13.toBitVec) 8)
    (P : MachineState → Prop)
    (next : Eventually (step e) P ({s with dmem := initialStores s}, base + 336)) :
    Eventually (step e) P (s, base + 323) := by
  natmulword_step 2:18 using hc
  apply Delimited.store_cps
  · exact Delimited.mapped_load_zero s.dmem s.regs.rsp.toBitVec 16 8 locals (by decide)
  simp only [Effects.All]
  natmulword_step 2:19 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
  apply Delimited.store_cps
  · apply Large.mapped_load (capacity := 16) (offset := 8) («width» := 8)
    · exact Large.mapped_store _ _ _ _ _ _ locals
    · decide
  simp only [Effects.All]
  natmulword_step 2:20 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
  apply Delimited.store_cps
  · apply Delimited.mapped_load_zero (capacity := 8) (byteCount := 8)
    · exact Large.mapped_store _ _ _ _ _ _ (Large.mapped_store _ _ _ _ _ _ payload)
    · decide
  simp only [Effects.All]
  simpa only [initialStores] using next

def loopStartState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rax := 1
      r8 := 1
      r11 := UInt64.ofBitVec (s.regs.r11.toBitVec + 1)
      r12 := UInt64.ofBitVec (s.regs.r12.toBitVec &&& s.regs.r15.toBitVec)
      rbp := UInt64.ofBitVec (s.regs.rbp.toBitVec + 8)}
    status := flags}

theorem start_loop_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (many : s.regs.r11.toBitVec + 1#64 ≠ s.regs.r9.toBitVec)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (loopStartState s flags, base + 466)) :
    Eventually (step e) P (s, base + 336) := by
  natmulword_step 2:21 using hc
  natmulword_step 2:22 using hc
  natmulword_step 2:23 using hc
  natmulword_step 2:24 using hc
  have different : s.regs.r9.toBitVec ≠ s.regs.r11.toBitVec + 1#64 := Ne.symm many
  simp [StatusFlags.from_result, different, Effects.All]
  natmulword_step 2:25 using hc
  constructor <;> natmulword_step 2:26 using hc
  all_goals natmulword_step 2:27 using hc
  all_goals natmulword_step 2:28 using hc
  all_goals simpa [loopStartState, UInt64.add_comm, Delimited.uint64_literal, -UInt64.ofNat_one] using next _

end SszX86.NatMulWord
