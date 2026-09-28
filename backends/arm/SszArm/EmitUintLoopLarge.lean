import SszArm.EmitUintLoopLargeChoice

namespace SszArm.Emit.Uint

open SszNative (NatOperand)
open UintCodec (widthLoad)

theorem large_round {s : ArmState} {args : Args} {width : NatOperand}
    {pointer : BitVec 64} {words : List (BitVec 64)} {size index : Nat}
    (base : BitVec 64) (owned : Owned s args (.uint width) (.uint (.large pointer words)) size)
    (registers : BodyRegisters s args) (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 1132#64)
    (loop : LargeRegisters s pointer words index size) (inside : index < size)
    (writtenPrefix : Prefix s args (.large pointer words) index) :
    ∃ steps t, run steps s = t ∧ Frame s t args size ∧
      LargeRegisters t pointer words (index + 1) size ∧
      read_pc t = (if index + 1 = size then base + 1000#64 else base + 1132#64) ∧
      Prefix t args (.large pointer words) (index + 1) := by
  obtain ⟨chosenSteps, chosen, chooseRun, chooseFrame, chosenPC, chosenWord, chosenLoop, chosenPrefix⟩ :=
    large_choose base owned registers code error aligned pc loop inside writtenPrefix
  let prepared := largePrepared chosen base
  let stored := byteStored prepared base .large
  let final := advanced stored base .large
  have prepFrame : Frame chosen prepared args size := largePrepared_frame chosen base args size
  have chosenOwned := chooseFrame.owned owned
  have prepOwned := prepFrame.owned chosenOwned
  have prepRegisters := prepFrame.bodyRegisters (chooseFrame.bodyRegisters registers)
  have data := largePrepared_data chosen base (emittedWord (.large pointer words) index) index size
    owned.representable inside chosenWord chosenLoop.bits chosenLoop.index chosenLoop.length
  have indexBound : index < 2^64 := by have bound := owned.representable; omega
  have current : (r (.GPR ByteStoreKind.large.index) prepared).toNat = index := by
    rw [show ByteStoreKind.large.index = 11#5 by rfl,
      largePrepared_register chosen base 11#5 (by decide), chosenLoop.index,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt indexBound]
  have storeRun : run 7 prepared = stored := byte_store_run base .large prepOwned prepRegisters
    (prepFrame.code (chooseFrame.code code))
    (prepFrame.error.trans (chooseFrame.error.trans error))
    (prepFrame.aligned (chooseFrame.aligned aligned)) (largePrepared_pc chosen base) current inside
  have storeFrame : Frame prepared stored args size := byteStored_frame base .large prepOwned prepRegisters current inside
  have storePC : read_pc stored = base + BitVec.ofNat 64 ByteStoreKind.large.advanceStart := by
    simp only [stored, byteStored_pc, ByteStoreKind.start, ByteStoreKind.advanceStart]
  have advanceRun := advance_run stored base .large (storeFrame.code (prepFrame.code (chooseFrame.code code)))
    (storeFrame.error.trans (prepFrame.error.trans (chooseFrame.error.trans error)))
    (storeFrame.aligned (prepFrame.aligned (chooseFrame.aligned aligned))) storePC
  have advanceFrame := advanced_frame stored base .large args size
  have zero : r (.FLAG .Z) stored = 1#1 ↔ index + 1 = size := by
    simpa only [stored, byteStored_flag] using data.2.2.2
  refine ⟨chosenSteps + (5 + (7 + 2)), final, ?_,
    chooseFrame.trans (prepFrame.trans (storeFrame.trans advanceFrame)), ?_, ?_, ?_⟩
  · rw [run_plus, chooseRun, run_plus,
      large_prepare_run chosen base (chooseFrame.code code) (chooseFrame.error.trans error)
        (chooseFrame.aligned aligned) chosenPC,
      run_plus, storeRun, advanceRun]
  · constructor
    · rw [advanced_register _ _ _ _ (by decide), byteStored_register,
        largePrepared_register _ _ _ (by decide)]
      exact chosenLoop.count
    · rw [advanced_register _ _ _ _ (by decide), byteStored_register,
        largePrepared_register _ _ _ (by decide)]
      exact chosenLoop.pointer
    · rw [advanced_register _ _ _ _ (by decide), byteStored_register]
      exact data.1
    · change r (.GPR ByteStoreKind.large.index) (advanced stored base .large) = _
      rw [advanced_index, byteStored_register]
      exact data.2.1
    · rw [advanced_register _ _ _ _ (by decide), byteStored_register,
        largePrepared_register _ _ _ (by decide)]
      exact chosenLoop.length
  · exact advanced_pc stored base .large index size zero
  · intro prior before
    change widthLoad (advanced stored base .large) (args.output.toNat + prior) 1 = _
    rw [load_eq_of_mem_eq (advanced_memory stored base .large)]
    have earlier : prior < index ∨ prior = index := by omega
    rcases earlier with earlier | rfl
    · rw [byteStored_prior base .large prepOwned prepRegisters current inside prior earlier,
        load_eq_of_mem_eq (largePrepared_memory chosen base)]
      exact chosenPrefix prior earlier
    · rw [byteStored_byte base .large prepOwned prepRegisters current inside, data.2.2.1,
        emitted_byte]

end SszArm.Emit.Uint
