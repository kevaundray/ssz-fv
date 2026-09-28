import SszX86.EmitUintScalar

namespace SszX86.Emit.Uint
open Kraken.X64.Parser
open BoolCodec UintCodec
open Instructions
open UintCodec.Large (get put putF compare subFlags shift)

def evenCL (counter : BitVec 64) : BitVec 64 :=
  (low32 counter).replaceLow (low8 (low32 counter) &&& 48#8)

def oddCL (counter : BitVec 64) : BitVec 64 :=
  (evenCL counter).replaceLow (low8 (evenCL counter) ||| 8#8)

def firstPairByte (limb counter : BitVec 64) : BitVec 8 :=
  (limb >>> ((low8 (evenCL counter)).toNat &&& 63)).setWidth 8

def secondPairByte (limb counter : BitVec 64) : BitVec 8 :=
  (limb >>> ((low8 (oddCL counter)).toNat &&& 63)).setWidth 8

def pairMemory (s : MachineData) (limb : BitVec 64) : DataMem :=
  let first := Mem.storeInt s.dmem (get s .r14 + get s .rax) 1
    (firstPairByte limb (get s .r9)).toInt
  Mem.storeInt first (get s .r14 + get s .rax + 1) 1
    (secondPairByte limb (get s .r9)).toInt

def smallPair (s : MachineData) (flags : StatusFlags) : MachineData :=
  let limb := if (get s .rax).toNat < 8 then get s .rdx else 0
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec (get s .rax + 2)
      r8 := s.regs.rax
      r9 := UInt64.ofBitVec (get s .r9 + 16)
      r10 := UInt64.ofBitVec (limb >>> ((low8 (oddCL (get s .r9))).toNat &&& 63))
      rcx := UInt64.ofBitVec (oddCL (get s .r9))}
    dmem := pairMemory s limb
    status := flags}

private def smallReady (s : MachineData) (flags : StatusFlags) : MachineData :=
  let limb := if (get s .rax).toNat < 8 then get s .rdx else 0
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec (limb >>> ((low8 (evenCL (get s .r9))).toNat &&& 63))
      r8 := s.regs.rax
      r10 := UInt64.ofBitVec limb
      rcx := UInt64.ofBitVec (evenCL (get s .r9))}
    status := flags}

private def smallStored (s : MachineData) (flags : StatusFlags) : MachineData :=
  let limb := if (get s .rax).toNat < 8 then get s .rdx else 0
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec (get s .rax + 2)
      r8 := s.regs.rax
      r10 := UInt64.ofBitVec (limb >>> ((low8 (oddCL (get s .r9))).toNat &&& 63))
      rcx := UInt64.ofBitVec (oddCL (get s .r9))}
    dmem := pairMemory s limb
    status := flags}

private theorem small_pair_ready (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (smallReady s flags, base + 1085)) :
    Eventually (step e) P (s, base + 1056) := by
  uint_exec at1056 using hc
  uint_exec at1059 using hc
  uint_exec at1063 using hc
  uint_exec at1069 using hc
  uint_exec at1073 using hc
  uint_exec at1076 using hc
  uint_exec at1079 using hc
  uint_exec at1082 using hc
  simpa [smallReady, evenCL, UintCodec.Large.get, UintCodec.Large.shift,
    low8, low32, Reg64s.get64] using next _

private theorem small_pair_store (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (initialFlags : StatusFlags) (capacity : Nat) (P : MachineState → Prop)
    (hmap : Large.Mapped s.dmem s.regs.r14.toBitVec capacity)
    (within : s.regs.rax.toNat + 2 ≤ capacity)
    (next : ∀ flags, Eventually (step e) P (smallStored s flags, base + 1104)) :
    Eventually (step e) P (smallReady s initialFlags, base + 1085) := by
  have indexBits : BitVec.ofNat 64 s.regs.rax.toNat = s.regs.rax.toBitVec := by
    change BitVec.ofNat 64 s.regs.rax.toBitVec.toNat = s.regs.rax.toBitVec
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have firstMapped : ∃ old, Mem.loadInt s.dmem
      (s.regs.r14.toBitVec + s.regs.rax.toBitVec) 1 = some old := by
    simpa only [indexBits] using
      Large.mapped_load s.dmem s.regs.r14.toBitVec capacity s.regs.rax.toNat 1 hmap (by omega)
  have secondMapped (limb : BitVec 64) : ∃ old, Mem.loadInt
      (Mem.storeInt s.dmem (s.regs.r14.toBitVec + s.regs.rax.toBitVec) 1
        (firstPairByte limb s.regs.r9.toBitVec).toInt)
      (s.regs.r14.toBitVec + s.regs.rax.toBitVec + 1) 1 = some old := by
    have stillMapped := Large.mapped_store s.dmem s.regs.r14.toBitVec
      (s.regs.r14.toBitVec + s.regs.rax.toBitVec) capacity 1
      (firstPairByte limb s.regs.r9.toBitVec).toInt hmap
    simpa only [BitVec.ofNat_add, indexBits, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using
      Large.mapped_load _ s.regs.r14.toBitVec capacity (s.regs.rax.toNat + 1) 1 stillMapped (by omega)
  simp only [smallReady]
  uint_write at1085 using hc mapped firstMapped
  uint_exec at1089 using hc
  uint_exec at1092 using hc
  uint_exec at1095 using hc
  have secondCell := secondMapped (if (get s .rax).toNat < 8 then get s .rdx else 0)
  simp only [firstPairByte, UintCodec.Large.get, Reg64s.get64] at secondCell
  uint_write at1099 using hc mapped secondCell
  simpa [smallStored, pairMemory, firstPairByte, secondPairByte, evenCL, oddCL,
    UintCodec.Large.get, UintCodec.Large.shift, low8, low32, Reg64s.get64] using next _

private theorem small_pair_finish (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (initialFlags : StatusFlags) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (smallPair s flags,
        if get s .rdi = get s .rax + 2 then base + 1113 else base + 1056)) :
    Eventually (step e) P (smallStored s initialFlags, base + 1104) := by
  simp only [smallStored]
  uint_exec at1104 using hc
  uint_exec at1108 using hc
  uint_exec at1111 using hc
  have selected := next
    (UintCodec.Large.subFlags s.regs.rdi.toBitVec (s.regs.rax.toBitVec + 2))
  have pc (condition : Prop) [Decidable condition] :
      base + Int64.ofNat (if condition then 1113 else 1056) =
        if condition then base + 1113 else base + 1056 := by
    by_cases chosen : condition <;> simp [chosen]
  simp [smallPair, UintCodec.Large.get, Reg64s.get64, pc] at selected ⊢
  with_unfolding_all exact selected

/-- Two actual Small bytes, including the unsigned CMP/CMOV zero extension,
partial CL writes, both stores, and the actual backward JNE. -/
theorem small_pair_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (capacity : Nat) (P : MachineState → Prop)
    (hmap : Large.Mapped s.dmem s.regs.r14.toBitVec capacity)
    (within : s.regs.rax.toNat + 2 ≤ capacity)
    (next : ∀ flags, Eventually (step e) P
      (smallPair s flags,
        if get s .rdi = get s .rax + 2 then base + 1113 else base + 1056)) :
    Eventually (step e) P (s, base + 1056) := by
  apply small_pair_ready e base hc s P
  intro readyFlags
  apply small_pair_store e base hc s readyFlags capacity P hmap within
  intro storedFlags
  exact small_pair_finish e base hc s storedFlags P next

/-- Convert the two literal stores to consecutive model bytes. The residue
proof is independent of width, and the two bytes share one physical limb. -/
theorem small_pair_bytes (s : MachineData) (limb : BitVec 64) (index : Nat)
    (indexEq : get s .rax = BitVec.ofNat 64 index)
    (counter : get s .r9 = BitVec.ofNat 64 (8 * index))
    (payload : get s .rdx = limb) (even : index % 2 = 0)
    (physical : index < 2 ^ 64) :
    let value := if (get s .rax).toNat < 8 then get s .rdx else 0
    firstPairByte value (get s .r9) = (SszNative.Limbs.byteAt [limb] index).toBitVec ∧
    secondPairByte value (get s .r9) = (SszNative.Limbs.byteAt [limb] (index + 1)).toBitVec := by
  have low : (get s .rax).toNat = index := by rw [indexEq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt physical]
  have selected : (if (get s .rax).toNat < 8 then get s .rdx else 0) =
      ([limb][index / 8]?.getD 0) := by
    rw [low, payload]
    exact (small_limb limb index).symm
  have firstShift : (low8 (evenCL (get s .r9))).toNat &&& 63 = 8 * (index % 8) := by
    rw [counter]
    exact pair_shift index even
  have secondShift : (low8 (oddCL (get s .r9))).toNat &&& 63 = 8 * ((index + 1) % 8) := by
    rw [counter]
    exact odd_shift index even
  dsimp only
  rw [firstPairByte, secondPairByte, selected, firstShift, secondShift]
  constructor
  · exact congrArg UInt8.toBitVec (shifted_limb_byte [limb] index)
  · rw [← pair_same_limb index even]
    exact congrArg UInt8.toBitVec (shifted_limb_byte [limb] (index + 1))

end SszX86.Emit.Uint
