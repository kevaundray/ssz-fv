import SszX86.EmitUintSmallPair

namespace SszX86.Emit.Uint
open Kraken.X64.Parser
open BoolCodec UintCodec
open Instructions
open UintCodec.Large (get put putF compare subFlags shift)

def largePair (s : MachineData) (limb : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec (get s .rax + 2)
      r9 := UInt64.ofBitVec (get s .r9 + 16)
      r10 := UInt64.ofBitVec (limb >>> ((low8 (oddCL (get s .r9))).toNat &&& 63))
      r11 := UInt64.ofBitVec (limb >>> ((low8 (evenCL (get s .r9))).toNat &&& 63))
      rcx := UInt64.ofBitVec (oddCL (get s .r9))}
    dmem := pairMemory s limb
    status := flags}

private def firstMemory (s : MachineData) (limb : BitVec 64) : DataMem :=
  Mem.storeInt s.dmem (get s .r14 + get s .rax) 1
    (firstPairByte limb (get s .r9)).toInt

private def loadedPair (s : MachineData) (limb : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      r10 := UInt64.ofBitVec (get s .rax >>> (3 : Nat))
      r11 := UInt64.ofBitVec limb}
    status := flags}

private def firstStored (s : MachineData) (limb : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      r10 := UInt64.ofBitVec (get s .rax >>> (3 : Nat))
      r11 := UInt64.ofBitVec (limb >>> ((low8 (evenCL (get s .r9))).toNat &&& 63))
      rcx := UInt64.ofBitVec (evenCL (get s .r9))}
    dmem := firstMemory s limb
    status := flags}

private def reloadedPair (s : MachineData) (limb : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      r10 := UInt64.ofBitVec limb
      r11 := UInt64.ofBitVec (limb >>> ((low8 (evenCL (get s .r9))).toNat &&& 63))
      rcx := UInt64.ofBitVec (evenCL (get s .r9))}
    dmem := firstMemory s limb
    status := flags}

private def storedPair (s : MachineData) (limb : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      r10 := UInt64.ofBitVec (limb >>> ((low8 (oddCL (get s .r9))).toNat &&& 63))
      r11 := UInt64.ofBitVec (limb >>> ((low8 (evenCL (get s .r9))).toNat &&& 63))
      rcx := UInt64.ofBitVec (oddCL (get s .r9))}
    dmem := pairMemory s limb
    status := flags}

private theorem shiftedIndex (s : MachineData) :
    (s.regs.rax.toBitVec >>> (3 : Nat)).toNat = s.regs.rax.toNat / 8 := by
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, UInt64.toNat_toBitVec]

private theorem load_pair (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (limb : BitVec 64) (P : MachineState → Prop)
    (limbRead : (get s .rax).toNat / 8 < (get s .rdx).toNat →
      Mem.loadInt s.dmem (get s .rdi + (get s .rax >>> (3 : Nat)) * 8) 8 =
        some (limb.toNat : Int))
    (zero : (get s .rdx).toNat ≤ (get s .rax).toNat / 8 → limb = 0#64)
    (next : ∀ flags, Eventually (step e) P (loadedPair s limb flags, base + 979)) :
    Eventually (step e) P (s, base + 946) := by
  by_cases inside : (get s .rax).toNat / 8 < (get s .rdx).toNat
  · have comparison : s.regs.rax.toNat / 8 < s.regs.rdx.toNat := by
      simpa only [UintCodec.Large.get, Reg64s.get64, UInt64.toNat_toBitVec] using inside
    uint_exec at946 using hc
    uint_exec at949 using hc
    uint_exec at953 using hc
    uint_exec at956 using hc
    simp only [shiftedIndex, UInt64.toNat_toBitVec, comparison, decide_true, ↓reduceIte]
    refine at958 e base hc _ limb ?_ (by simp [Writable]) P ?_
    · simpa [Read, readAddress, UintCodec.Large.get, Reg64s.get64] using limbRead inside
    intro loadFlags
    simp only [instruction, Instructions.next, UintCodec.Large.put, Reg64s.set64]
    uint_exec at962 using hc
    simpa [loadedPair, UintCodec.Large.get, Reg64s.get64] using next _
  · have comparison : ¬ s.regs.rax.toNat / 8 < s.regs.rdx.toNat := by
      simpa only [UintCodec.Large.get, Reg64s.get64, UInt64.toNat_toBitVec] using inside
    have empty := zero (by omega)
    subst limb
    uint_exec at946 using hc
    uint_exec at949 using hc
    uint_exec at953 using hc
    uint_exec at956 using hc
    simp only [shiftedIndex, UInt64.toNat_toBitVec, comparison, decide_false,
      Bool.false_eq_true, ↓reduceIte]
    uint_exec at976 using hc
    simpa [loadedPair, UintCodec.Large.get, Reg64s.get64] using next _

private theorem store_first (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (limb : BitVec 64) (initialFlags : StatusFlags) (P : MachineState → Prop)
    (hmap : ∃ old, Mem.loadInt s.dmem (get s .r14 + get s .rax) 1 = some old)
    (next : ∀ flags, Eventually (step e) P (firstStored s limb flags, base + 992)) :
    Eventually (step e) P (loadedPair s limb initialFlags, base + 979) := by
  simp only [loadedPair]
  uint_exec at979 using hc
  uint_exec at982 using hc
  uint_exec at985 using hc
  uint_write at988 using hc mapped hmap
  simpa [firstStored, firstMemory, firstPairByte, evenCL, UintCodec.Large.get,
    UintCodec.Large.shift, low8, low32, Reg64s.get64] using next _

private theorem reload_pair (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (limb : BitVec 64) (initialFlags : StatusFlags) (P : MachineState → Prop)
    (limbRead : (get s .rax).toNat / 8 < (get s .rdx).toNat →
      Mem.loadInt (firstMemory s limb) (get s .rdi + (get s .rax >>> (3 : Nat)) * 8) 8 =
        some (limb.toNat : Int))
    (zero : (get s .rdx).toNat ≤ (get s .rax).toNat / 8 → limb = 0#64)
    (next : ∀ flags, Eventually (step e) P (reloadedPair s limb flags, base + 916)) :
    Eventually (step e) P (firstStored s limb initialFlags, base + 992) := by
  by_cases inside : (get s .rax).toNat / 8 < (get s .rdx).toNat
  · have comparison : s.regs.rax.toNat / 8 < s.regs.rdx.toNat := by
      simpa only [UintCodec.Large.get, Reg64s.get64, UInt64.toNat_toBitVec] using inside
    simp only [firstStored]
    uint_exec at992 using hc
    uint_exec at995 using hc
    simp only [shiftedIndex, UInt64.toNat_toBitVec, comparison, decide_true, ↓reduceIte]
    refine at912 e base hc _ limb ?_ (by simp [Writable]) P ?_
    · simpa [Read, readAddress, UintCodec.Large.get, Reg64s.get64] using limbRead inside
    intro reloadFlags
    simp only [instruction, Instructions.next, UintCodec.Large.put, Reg64s.set64]
    simpa [reloadedPair, UintCodec.Large.get, Reg64s.get64] using next _
  · have comparison : ¬ s.regs.rax.toNat / 8 < s.regs.rdx.toNat := by
      simpa only [UintCodec.Large.get, Reg64s.get64, UInt64.toNat_toBitVec] using inside
    have empty := zero (by omega)
    subst limb
    simp only [firstStored]
    uint_exec at992 using hc
    uint_exec at995 using hc
    simp only [shiftedIndex, UInt64.toNat_toBitVec, comparison, decide_false,
      Bool.false_eq_true, ↓reduceIte]
    uint_exec at997 using hc
    uint_exec at1000 using hc
    simpa [reloadedPair, UintCodec.Large.get, Reg64s.get64] using next _

private theorem store_second (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (limb : BitVec 64) (initialFlags : StatusFlags) (P : MachineState → Prop)
    (hmap : ∃ old, Mem.loadInt (firstMemory s limb) (get s .r14 + get s .rax + 1) 1 = some old)
    (next : ∀ flags, Eventually (step e) P (storedPair s limb flags, base + 933)) :
    Eventually (step e) P (reloadedPair s limb initialFlags, base + 916) := by
  simp only [reloadedPair]
  uint_exec at916 using hc
  uint_exec at919 using hc
  uint_exec at922 using hc
  uint_exec at925 using hc
  uint_write at928 using hc mapped hmap
  simpa [storedPair, pairMemory, firstMemory, secondPairByte, evenCL, oddCL,
    UintCodec.Large.get, UintCodec.Large.shift, low8, low32, Reg64s.get64] using next _

private theorem finish_pair (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (limb : BitVec 64) (initialFlags : StatusFlags) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (largePair s limb flags,
        if get s .r8 = get s .rax + 2 then base + 1002 else base + 946)) :
    Eventually (step e) P (storedPair s limb initialFlags, base + 933) := by
  simp only [storedPair]
  uint_exec at933 using hc
  uint_exec at937 using hc
  uint_exec at941 using hc
  uint_exec at944 using hc
  have selected := next
    (UintCodec.Large.subFlags s.regs.r8.toBitVec (s.regs.rax.toBitVec + 2))
  have pc (condition : Prop) [Decidable condition] :
      base + Int64.ofNat (if condition then 1002 else 946) =
        if condition then base + 1002 else base + 946 := by
    by_cases chosen : condition <;> simp [chosen]
  simp [largePair, UintCodec.Large.get, Reg64s.get64, pc] at selected ⊢
  with_unfolding_all exact selected

/-- The pair loop reads a limb only when its unsigned physical index is in
range. The second native load is justified by static separation from the first
output byte; it is not assumed to be an unchanged future observation. -/
theorem large_pair_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (limb : BitVec 64) (capacity : Nat) (P : MachineState → Prop)
    (hmap : Large.Mapped s.dmem s.regs.r14.toBitVec capacity)
    (within : s.regs.rax.toNat + 2 ≤ capacity)
    (limbRead : (get s .rax).toNat / 8 < (get s .rdx).toNat →
      Mem.loadInt s.dmem (get s .rdi + BitVec.ofNat 64 (8 * ((get s .rax).toNat / 8))) 8 =
        some (limb.toNat : Int))
    (zero : (get s .rdx).toNat ≤ (get s .rax).toNat / 8 → limb = 0#64)
    (separate : (get s .rax).toNat / 8 < (get s .rdx).toNat → ∀ a, a < 8 →
      get s .rdi + BitVec.ofNat 64 (8 * ((get s .rax).toNat / 8)) + BitVec.ofNat 64 a ≠
        get s .r14 + get s .rax)
    (next : ∀ flags, Eventually (step e) P
      (largePair s limb flags,
        if get s .r8 = get s .rax + 2 then base + 1002 else base + 946)) :
    Eventually (step e) P (s, base + 946) := by
  have indexNat : ((get s .rax) >>> (3 : Nat)).toNat = (get s .rax).toNat / 8 := by
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have indexBits : (get s .rax) >>> (3 : Nat) =
      BitVec.ofNat 64 ((get s .rax).toNat / 8) := by
    apply BitVec.eq_of_toNat_eq
    rw [indexNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (get s .rax).isLt; omega)]
  have address : get s .rdi + ((get s .rax) >>> (3 : Nat)) * 8 =
      get s .rdi + BitVec.ofNat 64 (8 * ((get s .rax).toNat / 8)) := by
    simp only [BitVec.ofNat_eq_ofNat]
    rw [indexBits, ← BitVec.ofNat_mul, Nat.mul_comm]
  have originalIndex : BitVec.ofNat 64 s.regs.rax.toNat = s.regs.rax.toBitVec := by
    change BitVec.ofNat 64 s.regs.rax.toBitVec.toNat = s.regs.rax.toBitVec
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have firstMapped : ∃ old, Mem.loadInt s.dmem (get s .r14 + get s .rax) 1 = some old := by
    simpa only [UintCodec.Large.get, Reg64s.get64, originalIndex] using
      Large.mapped_load s.dmem s.regs.r14.toBitVec capacity s.regs.rax.toNat 1 hmap (by omega)
  have secondMapped : ∃ old, Mem.loadInt (firstMemory s limb)
      (get s .r14 + get s .rax + 1) 1 = some old := by
    have stillMapped := Large.mapped_store s.dmem s.regs.r14.toBitVec
      (get s .r14 + get s .rax) capacity 1 (firstPairByte limb (get s .r9)).toInt hmap
    simpa only [firstMemory, UintCodec.Large.get, Reg64s.get64, BitVec.ofNat_add,
      originalIndex, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using
      Large.mapped_load _ s.regs.r14.toBitVec capacity (s.regs.rax.toNat + 1) 1 stillMapped (by omega)
  have reloaded (inside : (get s .rax).toNat / 8 < (get s .rdx).toNat) :
      Mem.loadInt (firstMemory s limb)
        (get s .rdi + ((get s .rax) >>> (3 : Nat)) * 8) 8 = some (limb.toNat : Int) := by
    rw [firstMemory, address, load_store_disjoint]
    · exact limbRead inside
    · intro a ha b hb
      have bzero : b = 0 := by omega
      subst b
      simpa only [BitVec.add_zero] using separate inside a ha
  apply load_pair e base hc s limb P
  · intro inside
    rw [address]
    exact limbRead inside
  · exact zero
  · intro loadFlags
    apply store_first e base hc s limb loadFlags P firstMapped
    intro firstFlags
    apply reload_pair e base hc s limb firstFlags P reloaded zero
    intro reloadFlags
    apply store_second e base hc s limb reloadFlags P secondMapped
    intro storeFlags
    exact finish_pair e base hc s limb storeFlags P next

end SszX86.Emit.Uint
