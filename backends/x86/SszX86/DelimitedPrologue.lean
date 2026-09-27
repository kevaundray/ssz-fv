import SszX86.DelimitedBitStack
import SszX86.DelimitedStackMemory
import SszX86.DelimitedRetain

namespace SszX86.Delimited

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

private theorem bit_save_reads (s : MachineData) :
    Mem.loadInt (bitSaveMem s) (s.regs.rsp.toBitVec - 16#64) 8 =
      some (s.regs.r11.toBitVec.toInt.take 64) ∧
    Mem.loadInt (bitSaveMem s) (s.regs.rsp.toBitVec - 16#64 + 8#64) 8 =
      some (s.regs.r10.toBitVec.toInt.take 64) := by
  constructor
  · unfold bitSaveMem
    rw [BoolCodec.load_store_disjoint _ _ _ _ _ _ (by
      intro i hi j hj
      bv_omega)]
    exact BoolCodec.load_store_same _ _ 8 _ (by decide)
  · exact BoolCodec.load_store_same _ _ 8 _ (by decide)

def scannedState (s : MachineData) (highest : Nat) (flags : StatusFlags) : MachineData :=
  {s with
    dmem := bitSaveMem s
    regs := {s.regs with rbx := UInt64.ofNat highest}
    status := flags}

private def publishedState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rbx := UInt64.ofBitVec ((s.regs.r10.toBitVec.setWidth 32).setWidth 64)}
    status := flags}

private theorem bit_saved_scan (s : MachineData) (byte : UInt8) (flags : StatusFlags)
    (input : s.regs.rax.toBitVec.setWidth 32 = byte.toBitVec.setWidth 32) :
    bitSaved s flags = bitScanState (bitPushed s) (-1#64) (byte.toBitVec.setWidth 32) flags := by
  simp only [bitSaved, bitScanState, bitPushed, input]

private theorem bit_restore_image (s : MachineData) (highest : Nat)
    (small : highest < 8) (firstFlags lastFlags : StatusFlags) :
    bitRestored
      (publishedState (bitScanState (bitPushed s) (BitVec.ofNat 64 highest) 0#32 firstFlags)
        lastFlags)
      s.regs.r10.toBitVec s.regs.r11.toBitVec = scannedState s highest lastFlags := by
  have published : UInt64.ofBitVec
      (((BitVec.ofNat 64 highest).setWidth 32).setWidth 64) = UInt64.ofNat highest := by
    apply UInt64.toBitVec_inj.1
    simp only [UInt64.toBitVec_ofNat']
    bv_omega
  simp only [bitRestored, publishedState, bitScanState, bitPushed, scannedState,
    UInt64.toBitVec_ofBitVec, BitVec.sub_add_cancel, UInt64.ofBitVec_toBitVec, published]

/-- The complete linked BSR lowering, including both temporary saves and both
restoring loads. Only the original destination register and flags are clobbered. -/
theorem scan_bits_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (byte : UInt8) (nonzero : byte ≠ 0)
    (input : s.regs.rax.toBitVec = byte.toBitVec.setWidth 64)
    (hm : UintCodec.Large.Mapped s.dmem (s.regs.rsp.toBitVec - 16#64) 16)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (scannedState s (Ssz.highestBit byte) flags, base + 103)) :
    Eventually (step e) P (s, base + 43) := by
  have input32 : s.regs.rax.toBitVec.setWidth 32 = byte.toBitVec.setWidth 32 := by
    rw [input]
    bv_omega
  have byteNonzero : byte.toBitVec ≠ 0#8 := by
    intro zero
    exact nonzero (UInt8.toBitVec_inj.1 zero)
  have nonzero32 : s.regs.rax.toBitVec.setWidth 32 ≠ 0#32 := by
    rw [input32]
    bv_omega
  have finished : ∀ flags, Eventually (step e) P
      (bitScanState (bitPushed s) (BitVec.ofNat 64 (Ssz.highestBit byte)) 0#32 flags,
        base + 80) := by
    intro firstFlags
    apply bit_scan_publish e base hc
    intro lastFlags
    change Eventually (step e) P
      (publishedState
        (bitScanState (bitPushed s) (BitVec.ofNat 64 (Ssz.highestBit byte)) 0#32 firstFlags)
        lastFlags, base + 89)
    apply bit_restore_cps e base hc _ s.regs.r10.toBitVec s.regs.r11.toBitVec
    · exact (bit_save_reads s).1
    · exact (bit_save_reads s).2
    rw [bit_restore_image s _ (SszNative.BitView.highestBit_lt byte)]
    exact hp lastFlags
  apply bit_save_cps e base hc s hm nonzero32
  intro flags
  rw [bit_saved_scan s byte flags input32]
  simpa using bit_scan_loop e base hc (bitPushed s) byte nonzero P finished
    (Ssz.highestBit byte) 0 (by omega) flags

def prologueMem (s : MachineData) : DataMem :=
  let m := Mem.storeInt (pushedMem s) (s.regs.rsp.toBitVec - 104#64) 8 s.regs.r11.toBitVec.toInt
  Mem.storeInt m (s.regs.rsp.toBitVec - 96#64) 8 s.regs.r10.toBitVec.toInt

def prologueState (s : MachineData) (highest : Nat) (flags : StatusFlags) : MachineData :=
  {s with
    dmem := prologueMem s
    regs := {s.regs with
      rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec - 88)
      r13 := UInt64.ofBitVec (s.regs.rcx.toBitVec - 1#64)
      rax := UInt64.ofBitVec ((s.regs.rax.toBitVec.setWidth 8).setWidth 64)
      rbx := UInt64.ofNat highest}
    status := flags}

private theorem prologue_image (s : MachineData) (highest : Nat)
    (firstFlags lastFlags : StatusFlags) :
    scannedState (localState (pushedState s) firstFlags) highest lastFlags =
      prologueState s highest lastFlags := by
  have main : (s.regs.rsp.toBitVec - 48) - 40#64 = s.regs.rsp.toBitVec - 88 := by bv_omega
  have lower : (s.regs.rsp.toBitVec - 88) - 16#64 = s.regs.rsp.toBitVec - 104#64 := by bv_omega
  have upper : s.regs.rsp.toBitVec - 104#64 + 8#64 = s.regs.rsp.toBitVec - 96#64 := by bv_omega
  simp only [scannedState, localState, pushedState, bitSaveMem, prologueState, prologueMem,
    UInt64.toBitVec_ofBitVec, main, lower, upper]

theorem prologue_mapped (s : MachineData)
    (hm : UintCodec.Large.Mapped s.dmem (s.regs.rsp.toBitVec - 104) 104) :
    UintCodec.Large.Mapped (prologueMem s) (s.regs.rsp.toBitVec - 104) 104 := by
  unfold prologueMem pushedMem
  repeat' first | exact hm | apply UintCodec.Large.mapped_store

theorem prologue_saved (s : MachineData) :
    SavedAt (prologueMem s) (s.regs.rsp.toBitVec - 88) s := by
  have preserved (distance : Nat) (lo : 40 ≤ distance) (hi : distance + 8 ≤ 88) :
      Mem.loadInt (prologueMem s) (s.regs.rsp.toBitVec - 88 + BitVec.ofNat 64 distance) 8 =
        Mem.loadInt (pushedMem s) (s.regs.rsp.toBitVec - 88 + BitVec.ofNat 64 distance) 8 := by
    have address : s.regs.rsp.toBitVec - 88 + BitVec.ofNat 64 distance =
        s.regs.rsp.toBitVec - BitVec.ofNat 64 (88-distance) := by bv_omega
    rw [address]
    unfold prologueMem
    rw [stack_load_apart _ s.regs.rsp.toBitVec (88-distance) 96 _
      (by omega) (by decide) (Or.inl (by omega))]
    exact stack_load_apart _ s.regs.rsp.toBitVec (88-distance) 104 _
      (by omega) (by decide) (Or.inl (by omega))
  have saved := pushed_saved s
  exact ⟨(preserved 40 (by decide) (by decide)).trans saved.rbx,
    (preserved 48 (by decide) (by decide)).trans saved.r12,
    (preserved 56 (by decide) (by decide)).trans saved.r13,
    (preserved 64 (by decide) (by decide)).trans saved.r14,
    (preserved 72 (by decide) (by decide)).trans saved.r15,
    (preserved 80 (by decide) (by decide)).trans saved.rbp⟩

theorem prologue_frame (s : MachineData) (a : BitVec 64)
    (outside : ∀ i < 104, a ≠ (s.regs.rsp.toBitVec - 104) + BitVec.ofNat 64 i) :
    (prologueMem s).get? a = s.dmem.get? a := by
  unfold prologueMem
  rw [stack_store_frame _ s.regs.rsp.toBitVec a 96 8 _ (by decide) (by decide) outside]
  rw [stack_store_frame _ s.regs.rsp.toBitVec a 104 8 _ (by decide) (by decide) outside]
  exact pushed_frame s a outside

/-- Entry to the allocating path reaches count formation after the actual six
PUSHes, local reservation, bit-scan loop, and temporary-register restoration. -/
theorem prologue_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (byte : UInt8) (nonzero : byte ≠ 0)
    (input : s.regs.rax.toBitVec.setWidth 8 = byte.toBitVec)
    (hm : UintCodec.Large.Mapped s.dmem (s.regs.rsp.toBitVec - 104) 104)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (prologueState s (Ssz.highestBit byte) flags, base + 103)) :
    Eventually (step e) P (s, base + 22) := by
  apply pushes_cps e base hc s hm
  apply locals_cps e base hc
  intro firstFlags
  apply scan_bits_cps e base hc (localState (pushedState s) firstFlags) byte nonzero
  · simp only [localState, pushedState, UInt64.toBitVec_ofBitVec, input]
  · have address : (localState (pushedState s) firstFlags).regs.rsp.toBitVec - 16#64 =
        s.regs.rsp.toBitVec - 104 := by
      simp only [localState, pushedState, UInt64.toBitVec_ofBitVec]
      bv_omega
    rw [address]
    have mappedPushes : UintCodec.Large.Mapped (pushedMem s) (s.regs.rsp.toBitVec - 104) 104 := by
      unfold pushedMem
      repeat' first | exact hm | apply UintCodec.Large.mapped_store
    intro i hi
    exact mappedPushes i (by omega)
  intro lastFlags
  rw [prologue_image]
  exact hp lastFlags

end SszX86.Delimited
