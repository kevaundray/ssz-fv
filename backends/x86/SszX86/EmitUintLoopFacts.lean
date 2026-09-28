import SszX86.EmitUintLargePair

namespace SszX86.Emit.Uint
open SszNative
open BoolCodec UintCodec
open Instructions (low8 low32)
open UintCodec.Large (get)

/-- Static physical data used by the loop, derived from the original Owned
record. No execution, later guard, or future memory is an input. -/
structure LoopOwned (original : MachineData) (number : NatOperand) (count : Nat) : Prop where
  bounded : count < 2 ^ 64
  outputBound : original.regs.r14.toNat + count ≤ 2 ^ 64
  outputMapped : Large.Mapped original.dmem original.regs.r14.toBitVec count
  operand : number.At (widthLoad original.dmem)
  readGuard : ∀ address,
    (match number with
      | .small _ => False
      | .large pointer limbs => InSpan address pointer (8 * limbs.length)) →
    ¬ InSpan address original.regs.r14.toBitVec count

/-- Machine invariant at the real unrolled-pair loop header. Every completed
prefix byte has its logical value, and all other original bytes are intact. -/
structure LoopInv (original current : MachineData) (number : NatOperand)
    (count index : Nat) : Prop where
  stack : current.regs.rsp = original.regs.rsp
  result : current.regs.rbx = original.regs.rbx
  output : current.regs.r14 = original.regs.r14
  vector : current.zmms = original.zmms
  length : get current .rsi = BitVec.ofNat 64 count
  indexReg : get current .rax = BitVec.ofNat 64 index
  counter : get current .r9 = BitVec.ofNat 64 (8 * index)
  payload : get current .rdx = number.payload
  source : get current .rdi = match number with
    | .small _ => BitVec.ofNat 64 (2 * (count / 2))
    | .large pointer _ => pointer
  limit : (match number with
    | .small _ => True
    | .large _ _ => get current .r8 = BitVec.ofNat 64 (2 * (count / 2)))
  lastSmallIndex : (match number with
    | .small _ => 0 < index → get current .r8 = BitVec.ofNat 64 (index - 2)
    | .large _ _ => True)
  hprefix : Prefix original.dmem current.dmem original.regs.r14.toBitVec
    (Limbs.bytes number.words count) index

theorem pair_bytes (s : MachineData) (limbs : List (BitVec 64)) (index : Nat)
    (counter : get s .r9 = BitVec.ofNat 64 (8 * index)) (even : index % 2 = 0) :
    firstPairByte (limbs[index / 8]?.getD 0) (get s .r9) = (Limbs.byteAt limbs index).toBitVec ∧
    secondPairByte (limbs[index / 8]?.getD 0) (get s .r9) = (Limbs.byteAt limbs (index + 1)).toBitVec := by
  have firstShift : (low8 (evenCL (get s .r9))).toNat &&& 63 = 8 * (index % 8) := by
    rw [counter]
    exact pair_shift index even
  have secondShift : (low8 (oddCL (get s .r9))).toNat &&& 63 = 8 * ((index + 1) % 8) := by
    rw [counter]
    exact odd_shift index even
  rw [firstPairByte, secondPairByte, firstShift, secondShift]
  constructor
  · simpa only [UInt8.toBitVec_ofBitVec] using congrArg UInt8.toBitVec (shifted_limb_byte limbs index)
  · rw [← pair_same_limb index even]
    simpa only [UInt8.toBitVec_ofBitVec] using congrArg UInt8.toBitVec (shifted_limb_byte limbs (index + 1))

theorem pair_prefix (original current : MachineData) (number : NatOperand)
    (count index : Nat) (owned : LoopOwned original number count)
    (inv : LoopInv original current number count index) (even : index % 2 = 0)
    (within : index + 2 ≤ count) :
    Prefix original.dmem (pairMemory current (number.words[index / 8]?.getD 0))
      original.regs.r14.toBitVec (Limbs.bytes number.words count) (index + 2) := by
  have first := prefix_store inv.hprefix (by simpa only [Limbs.bytes, Array.size_ofFn, UInt64.toNat_toBitVec] using owned.outputBound)
    (by simpa only [Limbs.bytes, Array.size_ofFn] using (by omega : index < count))
  have second := prefix_store first (by simpa only [Limbs.bytes, Array.size_ofFn, UInt64.toNat_toBitVec] using owned.outputBound)
    (by simpa only [Limbs.bytes, Array.size_ofFn] using (by omega : index + 1 < count))
  have bytes := pair_bytes current number.words index inv.counter even
  have indexEq : current.regs.rax.toBitVec = BitVec.ofNat 64 index := inv.indexReg
  rw [pairMemory, bytes.1, bytes.2]
  simpa only [UintCodec.Large.get, Reg64s.get64, inv.output, indexEq,
    Limbs.bytes, Array.getElem_ofFn, Nat.add_assoc, BitVec.ofNat_add,
    BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using second

theorem LoopOwned.of_owned (s : MachineData) (logicalWidth number : NatOperand) (count : Nat)
    (owned : Owned s logicalWidth number count) : LoopOwned s number count := by
  refine ⟨?_, owned.output_bound, owned.output, owned.numberAt.2.2, ?_⟩
  · have bound := s.regs.r9.toBitVec.isLt
    have fits := owned.capacity
    simp only [UInt64.toNat_toBitVec] at bound
    omega
  · intro a inside output
    exact owned.readonly a (Or.inr (Or.inr inside)) (Or.inl output)

/-- A borrowed limb read is transported through the exact completed-prefix
frame. The complete physical allocation, including high zero padding, survives. -/
theorem loop_limb (original current : MachineData) (pointer : BitVec 64)
    (limbs : List (BitVec 64)) (count index limbIndex : Nat)
    (owned : LoopOwned original (.large pointer limbs) count)
    (inv : LoopInv original current (.large pointer limbs) count index)
    (within : limbIndex < limbs.length) :
    Mem.loadInt current.dmem (pointer + BitVec.ofNat 64 (8 * limbIndex)) 8 =
      some ((limbs[limbIndex]?.getD 0).toNat : Int) := by
  have stored := widthLoad_eq original.dmem _ 8 _ (owned.operand.2.2.2 ⟨limbIndex, within⟩)
  rw [prefix_protected inv.hprefix]
  · simpa only [width_address, Fin.getElem_fin, List.getElem?_eq_getElem within, Option.getD_some] using stored
  · intro a inside output
    have source := Bits.span_subspan pointer (8 * limbIndex) 8 (8 * limbs.length) (by omega) inside
    exact owned.readGuard a source (by simpa only [Limbs.bytes, Array.size_ofFn] using output)

end SszX86.Emit.Uint
