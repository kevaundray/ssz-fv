import SszX86.BitVectorExactErrorCopy

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

def exactErrorInit (s : MachineData) (out : BitVec 64) : MachineData :=
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec out
      rdi := UInt64.ofBitVec (out + 8#64)
      rsi := UInt64.ofBitVec (s.regs.rsp.toBitVec + 16#64)
      rcx := 9
      rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec - 8#64)}
    dmem := Mem.storeInt s.dmem (s.regs.rsp.toBitVec - 8#64) 8 s.regs.r11.toBitVec.toInt}

def exactErrorCopied (s : MachineData) (out : BitVec 64) (v : ExactErrorImage) : MachineData :=
  exactCopyThree (exactCopyThree (exactCopyThree (exactErrorInit s out)
    v.w0 v.w1 v.w2) v.w3 v.w4 v.w5) v.w6 v.w7 v.w8

def exactErrorMem (m : DataMem) (out : BitVec 64) (v : ExactErrorImage) : DataMem :=
  let m := exactCopyThreeMem m (out + 8#64) v.w0 v.w1 v.w2
  let m := exactCopyThreeMem m (out + 32#64) v.w3 v.w4 v.w5
  let m := exactCopyThreeMem m (out + 56#64) v.w6 v.w7 v.w8
  Mem.storeInt m (out + BitVec.ofNat 64 0) 8 1

def exactErrorState (s : MachineData) (out : BitVec 64) (v : ExactErrorImage) : MachineData :=
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec out
      rdi := UInt64.ofBitVec (out + 80#64)
      rsi := UInt64.ofBitVec (s.regs.rsp.toBitVec + 88#64)
      rcx := 0}
    dmem := exactErrorMem
      (Mem.storeInt s.dmem (s.regs.rsp.toBitVec - 8#64) 8 s.regs.r11.toBitVec.toInt) out v}

theorem exact_error_init_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (out : BitVec 64)
    (houtput : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 8#64) 8 = some (out.toNat : Int))
    (slot : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec - 8#64) 8 = some old)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (exactErrorInit s out, base + 4678)) :
    Eventually (step e) P (s, base + 4650) := by
  bitvector_remaining_step 96 using hc
  bitvector_load houtput
  bitvector_remaining_step 97 using hc
  bitvector_remaining_step 98 using hc
  bitvector_remaining_step 99 using hc
  bitvector_remaining_step 100 using hc
  bitvector_remaining_step 101 using hc
  simp only [error_wrapped_address, BitVec.ofInt_add, BitVec.ofInt_toInt,
    show BitVec.ofInt 64 (-8) = -(8#64) by decide]
  apply Delimited.store_cps
  · simpa only [BitVec.sub_eq_add_neg] using slot
  simp only [Effects.All]
  simpa only [exactErrorInit, error_wrapped_address, BitVec.ofInt_add, BitVec.ofInt_toInt,
    show BitVec.ofInt 64 (-8) = -(8#64) by decide,
    BitVec.sub_eq_add_neg, UInt64.toBitVec_ofBitVec, BitVec.ofInt_ofNat,
    UInt64.ofBitVec_ofNat, Width.bytes] using next

theorem exact_save_read (m : DataMem) (sp : BitVec 64) (a n : Nat) (value : Int)
    (low : 72 ≤ sp.toNat) (bound : sp.toNat + 224 ≤ 2^64) (within : a + n ≤ 224) :
    Mem.loadInt (Mem.storeInt m (sp - 8#64) 8 value) (sp + BitVec.ofNat 64 a) n =
      Mem.loadInt m (sp + BitVec.ofNat 64 a) n := by
  apply load_store_disjoint
  intro i hi j hj
  bv_omega

theorem exact_output_read (m : DataMem) (sp out : BitVec 64)
    (a n b k : Nat) (value : Int)
    (low : 72 ≤ sp.toNat) (bound : sp.toNat + 224 ≤ 2^64)
    (outBound : out.toNat + 80 ≤ 2^64)
    (apart : Body.Apart out.toNat 80 (sp.toNat - 72) 296)
    (readWithin : a + n ≤ 224) (writeWithin : b + k ≤ 80) :
    Mem.loadInt (Mem.storeInt m (out + BitVec.ofNat 64 b) k value)
      (sp + BitVec.ofNat 64 a) n = Mem.loadInt m (sp + BitVec.ofNat 64 a) n := by
  apply load_store_disjoint
  intro i hi j hj
  unfold Body.Apart at apart
  bv_omega

theorem exact_slot_read (m : DataMem) (sp out : BitVec 64) (b k : Nat) (value : Int)
    (low : 72 ≤ sp.toNat) (bound : sp.toNat + 224 ≤ 2^64)
    (outBound : out.toNat + 80 ≤ 2^64)
    (apart : Body.Apart out.toNat 80 (sp.toNat - 72) 296)
    (writeWithin : b + k ≤ 80) :
    Mem.loadInt (Mem.storeInt m (out + BitVec.ofNat 64 b) k value) (sp - 8#64) 8 =
      Mem.loadInt m (sp - 8#64) 8 := by
  apply load_store_disjoint
  intro i hi j hj
  unfold Body.Apart at apart
  bv_omega

theorem exact_output_mapped (m : DataMem) (out : BitVec 64) (off : Nat)
    (hm : Large.Mapped m out 80) (within : off + 24 ≤ 80) :
    Large.Mapped m (out + BitVec.ofNat 64 off) 24 := by
  intro i hi
  simpa only [memmove_addr_add] using hm (off + i) (by omega)

theorem exact_copy_apart (sp out : BitVec 64) (srcOff dstOff : Nat)
    (low : 72 ≤ sp.toNat) (bound : sp.toNat + 224 ≤ 2^64)
    (outBound : out.toNat + 80 ≤ 2^64)
    (apart : Body.Apart out.toNat 80 (sp.toNat - 72) 296)
    (srcWithin : srcOff + 24 ≤ 224) (dstWithin : dstOff + 24 ≤ 80) :
    Large.Disjoint (sp + BitVec.ofNat 64 srcOff) (out + BitVec.ofNat 64 dstOff) 24 24 := by
  intro i hi j hj
  unfold Body.Apart at apart
  bv_omega

macro "exact_error_physical " : tactic => `(tactic|
  simp (disch := first | assumption | omega | decide) only
    [exactCopyThree, exactCopyThreeMem, exactErrorInit, UInt64.toBitVec_ofBitVec,
      BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, exact_output_read, exact_save_read])

theorem exact_error_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (out : BitVec 64) (v : ExactErrorImage)
    (outputMapped : Large.Mapped s.dmem out 80)
    (slot : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec - 8#64) 8 = some old)
    (low : 72 ≤ s.regs.rsp.toBitVec.toNat)
    (bound : s.regs.rsp.toBitVec.toNat + 224 ≤ 2^64)
    (outBound : out.toNat + 80 ≤ 2^64)
    (apart : Body.Apart out.toNat 80 (s.regs.rsp.toBitVec.toNat - 72) 296)
    (houtput : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 8#64) 8 = some (out.toNat : Int))
    (h0 : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 16#64) 8 = some (v.w0.toNat : Int))
    (h1 : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 24#64) 8 = some (v.w1.toNat : Int))
    (h2 : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 32#64) 8 = some (v.w2.toNat : Int))
    (h3 : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 40#64) 8 = some (v.w3.toNat : Int))
    (h4 : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 48#64) 8 = some (v.w4.toNat : Int))
    (h5 : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 56#64) 8 = some (v.w5.toNat : Int))
    (h6 : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 64#64) 8 = some (v.w6.toNat : Int))
    (h7 : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 72#64) 8 = some (v.w7.toNat : Int))
    (h8 : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 80#64) 8 = some (v.w8.toNat : Int))
    (P : MachineState → Prop)
    (next : Eventually (step e) P (exactErrorState s out v, base + 7720)) :
    Eventually (step e) P (s, base + 4650) := by
  apply exact_error_init_cps e base hc s out houtput slot P
  apply exact_error_copy0_cps e base hc (exactErrorInit s out) v.w0 v.w1 v.w2
  · apply exact_output_mapped _ out 8
    · exact Large.mapped_store _ _ _ _ _ _ outputMapped
    · decide
  · exact exact_copy_apart _ _ 16 8 low bound outBound apart (by decide) (by decide)
  · exact_error_physical
    exact h0
  · exact_error_physical
    exact h1
  · exact_error_physical
    exact h2
  apply exact_error_copy1_cps e base hc
    (exactCopyThree (exactErrorInit s out) v.w0 v.w1 v.w2) v.w3 v.w4 v.w5
  · simp only [exactCopyThree, exactErrorInit, UInt64.toBitVec_ofBitVec,
      BitVec.add_assoc, BitVec.reduceAdd]
    apply exact_output_mapped _ out 32
    · dsimp [exactCopyThreeMem]
      repeat' first | exact outputMapped | apply Large.mapped_store
    · decide
  · simpa only [exactCopyThree, exactErrorInit, UInt64.toBitVec_ofBitVec,
      BitVec.add_assoc, BitVec.reduceAdd] using
      exact_copy_apart s.regs.rsp.toBitVec out 40 32 low bound outBound apart (by decide) (by decide)
  · exact_error_physical
    exact h3
  · exact_error_physical
    exact h4
  · exact_error_physical
    exact h5
  apply exact_error_copy2_cps e base hc
    (exactCopyThree (exactCopyThree (exactErrorInit s out) v.w0 v.w1 v.w2) v.w3 v.w4 v.w5)
    v.w6 v.w7 v.w8
  · simp only [exactCopyThree, exactErrorInit, UInt64.toBitVec_ofBitVec,
      BitVec.add_assoc, BitVec.reduceAdd]
    apply exact_output_mapped _ out 56
    · dsimp [exactCopyThreeMem]
      repeat' first | exact outputMapped | apply Large.mapped_store
    · decide
  · simpa only [exactCopyThree, exactErrorInit, UInt64.toBitVec_ofBitVec,
      BitVec.add_assoc, BitVec.reduceAdd] using
      exact_copy_apart s.regs.rsp.toBitVec out 64 56 low bound outBound apart (by decide) (by decide)
  · exact_error_physical
    exact h6
  · exact_error_physical
    exact h7
  · exact_error_physical
    exact h8
  have saved : Mem.loadInt (exactErrorCopied s out v).dmem (s.regs.rsp.toBitVec - 8#64) 8 =
      some (s.regs.r11.toBitVec.toInt.take 64) := by
    simp (disch := first | assumption | omega | decide) only
      [exactErrorCopied, exactCopyThree, exactCopyThreeMem, exactErrorInit,
        UInt64.toBitVec_ofBitVec, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero,
        exact_slot_read, load_store_same, Nat.reduceMul]
  have hm : Large.Mapped (exactErrorCopied s out v).dmem out 80 := by
    dsimp [exactErrorCopied, exactCopyThree, exactCopyThreeMem, exactErrorInit]
    repeat' first | exact outputMapped | apply Large.mapped_store
  change Eventually (step e) P (exactErrorCopied s out v, base + 4804)
  have copiedStack : (exactErrorCopied s out v).regs.rsp.toBitVec =
      s.regs.rsp.toBitVec - 8#64 := rfl
  bitvector_remaining_step 138 using hc
  bitvector_remaining_step 139 using hc
  simp only [copiedStack]
  bitvector_load saved
  simp only [Delimited.take_cast]
  bitvector_remaining_step 140 using hc
  bitvector_remaining_output 141 at 0 width 8 using hc mapped hm
  bitvector_remaining_step 142 using hc
  have restoreStack : UInt64.ofBitVec (s.regs.rsp.toBitVec - 8#64) + (8 : UInt64) =
      s.regs.rsp := by
    apply UInt64.eq_of_toBitVec_eq
    simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat, BitVec.sub_add_cancel]
  simpa only [exactErrorState, exactErrorMem, exactErrorCopied, exactCopyThree,
    exactCopyThreeMem, exactErrorInit, UInt64.toBitVec_ofBitVec, UInt64.ofBitVec_toBitVec,
    error_wrapped_address, BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_ofNat,
    BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.sub_add_cancel, restoreStack] using next

theorem exact_error_output_frame (m : DataMem) (out a : BitVec 64) (v : ExactErrorImage)
    (outside : ∀ i < 80, a ≠ out + BitVec.ofNat 64 i) :
    (exactErrorMem m out v).get? a = m.get? a := by
  simp (disch := first | assumption | omega | decide) only
    [exactErrorMem, exactCopyThreeMem, BitVec.add_assoc, BitVec.reduceAdd,
      store_frame (limit := 80)]

/-- Only the nine destination words, tag, and real R11 save slot can change. -/
theorem exact_error_frame (s : MachineData) (out a : BitVec 64) (v : ExactErrorImage)
    (outsideOutput : ∀ i < 80, a ≠ out + BitVec.ofNat 64 i)
    (outsideSlot : ∀ i < 8, a ≠ (s.regs.rsp.toBitVec - 8#64) + BitVec.ofNat 64 i) :
    (exactErrorState s out v).dmem.get? a = s.dmem.get? a := by
  simp only [exactErrorState, exact_error_output_frame _ out a v outsideOutput]
  apply memmove_store_lookup_outside
  simpa only [Int.toBytes_length] using outsideSlot

theorem exact_error_regions_frame (s : MachineData) (out : BitVec 64) (v : ExactErrorImage)
    (outBound : out.toNat + 80 ≤ 2^64)
    (slotBound : (s.regs.rsp.toBitVec - 8#64).toNat + 8 ≤ 2^64) :
    RegionsFrame s.dmem (exactErrorState s out v).dmem
      [(out.toNat, 80), ((s.regs.rsp.toBitVec - 8#64).toNat, 8)] := by
  intro a outside
  apply exact_error_frame
  · intro i hi
    exact Body.outside_byte out a 80 i outBound (outside (out.toNat, 80) (by simp)) hi
  · intro i hi
    exact Body.outside_byte (s.regs.rsp.toBitVec - 8#64) a 8 i slotBound
      (outside ((s.regs.rsp.toBitVec - 8#64).toNat, 8) (by simp)) hi

private theorem exact_signed_nat {n : Nat} (v : BitVec n) :
    (v.toInt.take n).toNat = v.toNat := by
  have h := congrArg BitVec.toNat (BitVec.ofInt_toInt (x := v))
  simp only [BitVec.toNat_ofInt] at h
  simpa [Int.take] using h

/-- All nine complete copy words are observed, including the entire final word. -/
theorem exact_error_observed (m : DataMem) (out : BitVec 64) (v : ExactErrorImage)
    (bound : out.toNat + 80 ≤ 2^64) :
    observe (exactErrorMem m out v) out 0 8 = some 1 ∧
    observe (exactErrorMem m out v) out 8 8 = some v.w0.toNat ∧
    observe (exactErrorMem m out v) out 16 8 = some v.w1.toNat ∧
    observe (exactErrorMem m out v) out 24 8 = some v.w2.toNat ∧
    observe (exactErrorMem m out v) out 32 8 = some v.w3.toNat ∧
    observe (exactErrorMem m out v) out 40 8 = some v.w4.toNat ∧
    observe (exactErrorMem m out v) out 48 8 = some v.w5.toNat ∧
    observe (exactErrorMem m out v) out 56 8 = some v.w6.toNat ∧
    observe (exactErrorMem m out v) out 64 8 = some v.w7.toNat ∧
    observe (exactErrorMem m out v) out 72 8 = some v.w8.toNat := by
  simp (disch := first | assumption | omega | decide) only
    [observe, exactErrorMem, exactCopyThreeMem, BitVec.add_assoc, BitVec.reduceAdd,
      load_store_offset_disjoint, load_store_same, Nat.reduceMul]
  simp only [Option.map_some, exact_signed_nat]
  decide

theorem exact_store_slice (m : DataMem) (dst : BitVec 64) (v : BitVec 64)
    (off count : Nat) (within : off + count ≤ 8) :
    Mem.loadInt (Mem.storeInt m dst 8 v.toInt) (dst + BitVec.ofNat 64 off) count =
      some (Int.ofBytes (((Int.toBytes 8 v.toInt).drop off).take count)) := by
  have len : (((Int.toBytes 8 v.toInt).drop off).take count).length = count := by
    simp only [List.length_take, List.length_drop, Int.toBytes_length]
    omega
  conv => lhs; rw [← len]
  apply memmove_loadInt_of_lookup
  intro i hi
  have inside : i < count := by simpa only [len] using hi
  rw [memmove_addr_add, memmove_chunk_lookup _ _ _ _ inside]
  exact memmove_store_lookup_inside m dst (Int.toBytes 8 v.toInt) (off + i)
    (by simp only [Int.toBytes_length]; omega) (by simp only [Int.toBytes_length]; decide)

/-- Separate status and unspecified padding observations of the actual final MOV. -/
theorem exact_error_status_padding (m : DataMem) (out : BitVec 64) (v : ExactErrorImage)
    (bound : out.toNat + 80 ≤ 2^64) :
    observe (exactErrorMem m out v) out 72 4 =
      some (Int.ofBytes (((Int.toBytes 8 v.w8.toInt).drop 0).take 4)).toNat ∧
    observe (exactErrorMem m out v) out 76 4 =
      some (Int.ofBytes (((Int.toBytes 8 v.w8.toInt).drop 4).take 4)).toNat := by
  constructor
  · simp (disch := first | assumption | omega | decide) only
      [observe, exactErrorMem, exactCopyThreeMem, BitVec.add_assoc, BitVec.reduceAdd,
        load_store_offset_disjoint]
    simpa only [BitVec.add_zero, Option.map_some] using congrArg (Option.map Int.toNat)
      (exact_store_slice _ (out + 72#64) v.w8 0 4 (by decide))
  · simp (disch := first | assumption | omega | decide) only
      [observe, exactErrorMem, exactCopyThreeMem, BitVec.add_assoc, BitVec.reduceAdd,
        load_store_offset_disjoint]
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, Option.map_some] using
      congrArg (Option.map Int.toNat) (exact_store_slice _ (out + 72#64) v.w8 4 4 (by decide))

end SszX86.BitVector
