import SszArm.EmitUintLoopSmallPrepare
import SszArm.EmitUintLoopAdvance

namespace SszArm.Emit.Uint

open SszNative (NatOperand)
open UintCodec (widthLoad)

/-- Only the already-emitted prefix is observed. At index zero this places no
condition on any original output byte. -/
def Prefix (s : ArmState) (args : Args) (number : NatOperand) (count : Nat) : Prop :=
  ∀ index, index < count → widthLoad s (args.output.toNat + index) 1 =
    some (SszNative.Limbs.byteAt number.words index).toNat

structure SmallRegisters (s : ArmState) (word : BitVec 64) (index size : Nat) : Prop where
  word : r (.GPR 8#5) s = word
  bits : r (.GPR 9#5) s = BitVec.ofNat 64 (8 * index)
  index : r (.GPR 10#5) s = BitVec.ofNat 64 index
  length : r (.GPR 1#5) s = BitVec.ofNat 64 size

@[irreducible] def smallRound (s : ArmState) (base : BitVec 64) : ArmState :=
  advanced (byteStored (smallPrepared s base) base .small) base .small

theorem small_round {s : ArmState} {args : Args} {width : NatOperand} {word : BitVec 64}
    {size index : Nat} (base : BitVec 64)
    (owned : Owned s args (.uint width) (.uint (.small word)) size)
    (registers : BodyRegisters s args) (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 936#64)
    (loop : SmallRegisters s word index size) (inside : index < size)
    (writtenPrefix : Prefix s args (.small word) index) :
    run 16 s = smallRound s base ∧ Frame s (smallRound s base) args size ∧
    SmallRegisters (smallRound s base) word (index + 1) size ∧
    read_pc (smallRound s base) = (if index + 1 = size then base + 1000#64 else base + 936#64) ∧
    Prefix (smallRound s base) args (.small word) (index + 1) := by
  let prepared := smallPrepared s base
  let stored := byteStored prepared base .small
  have prepFrame : Frame s prepared args size := smallPrepared_frame s base args size
  have prepOwned := prepFrame.owned owned
  have prepRegisters := prepFrame.bodyRegisters registers
  have data := smallPrepared_data s base word index size owned.representable inside
    loop.word loop.bits loop.index loop.length
  have indexBound : index < 2^64 := by have bound := owned.representable; omega
  have current : (r (.GPR ByteStoreKind.small.index) prepared).toNat = index := by
    rw [show ByteStoreKind.small.index = 10#5 by rfl,
      smallPrepared_register s base 10#5 (by decide), loop.index,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt indexBound]
  have storeRun : run 7 prepared = stored := byte_store_run base .small prepOwned prepRegisters
    (prepFrame.code code) (prepFrame.error.trans error) (prepFrame.aligned aligned)
    (smallPrepared_pc s base) current inside
  have storeFrame : Frame prepared stored args size := byteStored_frame base .small prepOwned prepRegisters current inside
  have storePC : read_pc stored = base + BitVec.ofNat 64 ByteStoreKind.small.advanceStart := by
    simp only [stored, byteStored_pc, ByteStoreKind.start, ByteStoreKind.advanceStart]
  have advanceRun := advance_run stored base .small (storeFrame.code (prepFrame.code code))
    (storeFrame.error.trans (prepFrame.error.trans error))
    (storeFrame.aligned (prepFrame.aligned aligned)) storePC
  have advanceFrame := advanced_frame stored base .small args size
  have zero : r (.FLAG .Z) stored = 1#1 ↔ index + 1 = size := by
    simpa only [stored, byteStored_flag] using data.2.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change run (7 + (7 + 2)) s = _
    rw [run_plus, small_prepare_run s base code error aligned pc, run_plus, storeRun, advanceRun]
    rw [smallRound]
  · simpa only [smallRound] using prepFrame.trans (storeFrame.trans advanceFrame)
  · constructor
    · rw [smallRound, advanced_register _ _ _ _ (by decide), byteStored_register,
        smallPrepared_register _ _ _ (by decide)]
      exact loop.word
    · rw [smallRound, advanced_register _ _ _ _ (by decide), byteStored_register]
      exact data.1
    · rw [smallRound]
      change r (.GPR ByteStoreKind.small.index) (advanced stored base .small) = _
      rw [advanced_index, byteStored_register]
      exact data.2.1
    · rw [smallRound, advanced_register _ _ _ _ (by decide), byteStored_register,
        smallPrepared_register _ _ _ (by decide)]
      exact loop.length
  · simpa only [smallRound, ByteStoreKind.loopStart] using advanced_pc stored base .small index size zero
  · intro prior before
    rw [smallRound, load_eq_of_mem_eq (by exact advanced_memory stored base .small)]
    have earlier : prior < index ∨ prior = index := by omega
    rcases earlier with earlier | rfl
    · rw [byteStored_prior base .small prepOwned prepRegisters current inside prior earlier,
        load_eq_of_mem_eq (smallPrepared_memory s base)]
      exact writtenPrefix prior earlier
    · rw [byteStored_byte base .small prepOwned prepRegisters current inside, data.2.2.1,
        emitted_byte]

end SszArm.Emit.Uint
