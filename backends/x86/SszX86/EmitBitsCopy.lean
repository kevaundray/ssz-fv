import SszX86.EmitBitsPrepared

namespace SszX86.Emit.Bits
open SszNative.Serialize (Desc Packed)
open UintCodec BoolCodec
open BitVector (constructLow constructQuotient)

/-- Proven post-CALL facts; this is an intermediate conclusion, never an entry
premise of the public bit-emitter body theorem. -/
structure Copied (s t : MachineData) (bits : Packed) (src : BitVec 64)
    (size : Nat) (list : Bool) : Prop where
  stack : t.regs.rsp = s.regs.rsp
  result : t.regs.rbx = s.regs.rbx
  output : t.regs.r14 = s.regs.r14
  source : t.regs.r12.toBitVec = src
  full : t.regs.r13.toBitVec = BitVec.ofNat 64 (bits.count.toNat / 8)
  saved : t.regs.rbp.toBitVec = BitVec.ofNat 64
    (if list then bits.count.toNat % 8 else bits.bytes.size)
  capacity : t.regs.r15 = s.regs.r9
  vector : t.zmms = s.zmms
  «prefix» : BytesAt t.dmem s.regs.r14.toBitVec (Bits.prefix bits)
  frame : MemoryFrame s.dmem t.dmem (BodyWritable s size)
  mapping : BitVector.Mapping.Extends s.dmem t.dmem
  low : Mem.loadInt t.dmem (s.regs.rsp.toBitVec + if list then 16 else 8) 8 =
    some ((constructLow bits.count).toNat : Int)
  length : list = true → Mem.loadInt t.dmem (s.regs.rsp.toBitVec + 8) 8 =
    some (bits.bytes.size : Int)

theorem quotient_word (bits : Packed) (physical : bits.bytes.size < 2^64) :
    constructQuotient bits.count = BitVec.ofNat 64 (bits.count.toNat / 8) := by
  have value := quotient_nat bits physical
  have bound := (constructQuotient bits.count).isLt
  apply BitVec.eq_of_toNat_eq
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show bits.count.toNat / 8 < 2^64 by omega)]
    using value

private theorem copied_spill (s : MachineData) (desc : Desc) (bits : Packed)
    (src : BitVec 64) (size : Nat) (owned : Owned s desc bits src size)
    (list : Bool) (flags : StatusFlags) (ra : BitVec 64) (t : MachineState)
    (post : CopyPost (prepared s bits src list flags) ra («prefix» bits).toList t)
    (byteOffset : Nat) (lower : 8 ≤ byteOffset) (upper : byteOffset + 8 ≤ 104) :
    Mem.loadInt t.1.dmem (s.regs.rsp.toBitVec + BitVec.ofNat 64 byteOffset) 8 =
      Mem.loadInt (spillMemory s bits list) (s.regs.rsp.toBitVec + BitVec.ofNat 64 byteOffset) 8 := by
  apply protected_load post.frame
  intro a inside written
  obtain ⟨i, hi, rfl⟩ := inside
  rcases written with output | stack
  · obtain ⟨j, hj, equal⟩ := output
    have fullBound := full_le_size owned.kind owned.valid.success
    have hj' : j < size := by
      simp only [Array.length_toList, prefix_size] at hj
      omega
    have address : s.regs.rsp.toBitVec + BitVec.ofNat 64 byteOffset + BitVec.ofNat 64 i =
        (s.regs.rsp.toBitVec - 8) + BitVec.ofNat 64 (8 + byteOffset + i) := by bv_omega
    exact owned.outputStack j hj' (8 + byteOffset + i) (by omega)
      (by simpa only [prepared, address] using equal.symm)
  · obtain ⟨j, hj, equal⟩ := stack
    simp only [prepared] at equal
    bv_omega

/-- Actual linked memcpy, including CALL's return-slot write and the callee's
real RET, transports original packed ownership to the two native tail PCs. -/
theorem copy_prepared (e : Executable) (base : Int64) (hc : CodeAt e base)
    (helper : MemcpyCodeAt e (base + 110736))
    (s : MachineData) (desc : Desc) (bits : Packed) (src : BitVec 64) (size : Nat)
    (owned : Owned s desc bits src size) (list : Bool) (flags : StatusFlags)
    (P : MachineState → Prop)
    (next : ∀ t, Copied s t bits src size list →
      Eventually (step e) P (t, base + if list then 504 else 738)) :
    Eventually (step e) P (prepared s bits src list flags, base + if list then 498 else 732) := by
  let site : CopySite := if list then .bitList else .bitVector
  have sizeBound := full_le_size owned.kind owned.valid.success
  have backingBound := (backing_guards bits).1
  have prefixBound : bits.count.toNat / 8 < 2^64 := by have := owned.physical; omega
  have mapping := spill_mapped s bits list
  have spillFrame := spill_frame s bits list size
  have separate := owned.copy_apart
  have call := copy_call_runs e base hc helper site (prepared s bits src list flags)
    («prefix» bits).toList
    (by simp [prepared, Array.length_toList, prefix_size, quotient_word bits owned.physical])
    (by simpa only [Array.length_toList, prefix_size] using prefixBound)
    (by simpa only [prepared, UInt64.toBitVec_ofBitVec] using
      prefix_bytes bits _ src (owned.source_at spillFrame))
    (by
      intro i hi
      have hi' : i < size := by
        simp only [Array.length_toList, prefix_size] at hi
        omega
      exact mapping _ _ owned.outputMapped i hi')
    (by
      intro i hi
      exact mapping _ _ owned.stackMapped i (by omega))
    (by simpa only [prepared, UInt64.toBitVec_ofBitVec, Array.length_toList, prefix_size] using separate.1)
    (by simpa only [prepared, UInt64.toBitVec_ofBitVec, Array.length_toList, prefix_size] using separate.2.1)
    (by simpa only [prepared, Array.length_toList, prefix_size] using separate.2.2)
  have execution := BitVector.Mapping.retains_mapping e _ _ call
  have startPc : Int64.ofNat site.pc = if list then (498 : Int64) else 732 := by
    cases list <;> rfl
  rw [startPc] at execution
  apply eventually_trans (step e) _ _ _ execution
  rintro ⟨t, pc⟩ ⟨post, mappingAfter⟩
  have returnedPc : pc = base + if list then 504 else 738 := by
    have same := post.returned.1
    cases list <;> simpa [site, CopySite.next] using same
  subst pc
  apply next t
  have reg (r : Reg64) (h1 : r ≠ .rax) (h2 : r ≠ .rsp)
      (h3 : r ≠ .rcx) (h4 : r ≠ .rdx) (h5 : r ≠ .rsi) (h6 : r ≠ .rdi) (h7 : r ≠ .r8) :=
    post.returned.2.2.2.2 r h1 h2 h3 h4 h5 h6 h7
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply UInt64.toBitVec_inj.mp
    simpa [callState, prepared, BitVec.sub_add_cancel] using post.returned.2.2.1
  · apply UInt64.toBitVec_inj.mp
    simpa [callState, prepared, Reg64s.get64] using reg .rbx (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
  · apply UInt64.toBitVec_inj.mp
    simpa [callState, prepared, Reg64s.get64] using reg .r14 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
  · simpa [callState, prepared, Reg64s.get64] using reg .r12 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
  · simpa [callState, prepared, Reg64s.get64, quotient_word bits owned.physical] using
      reg .r13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have saved := reg .rbp (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
    cases list <;> simpa [callState, prepared, Reg64s.get64] using saved
  · apply UInt64.toBitVec_inj.mp
    simpa [callState, prepared, Reg64s.get64] using reg .r15 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact post.returned.2.2.2.1
  · exact list_prefix_output bits _ _ post.output
  · apply frame_trans spillFrame
    apply frame_mono post.frame
    intro a written
    rcases written with output | stack
    · obtain ⟨i, hi, equal⟩ := output
      exact Or.inl ⟨i, by simpa only [Array.length_toList, prefix_size] using
        Nat.lt_of_lt_of_le hi (by simpa only [Array.length_toList, prefix_size] using sizeBound), equal⟩
    · obtain ⟨i, hi, equal⟩ := stack
      exact Or.inr (Or.inr ⟨i, by omega, equal⟩)
  · exact mapping.trans mappingAfter
  · cases list
    · exact (copied_spill s desc bits src size owned false flags _ _ post 8 (by decide)
        (by decide)).trans (spill_low s bits false)
    · exact (copied_spill s desc bits src size owned true flags _ _ post 16 (by decide)
        (by decide)).trans (spill_low s bits true)
  · intro isList
    subst list
    exact (copied_spill s desc bits src size owned true flags _ _ post 8 (by decide)
      (by decide)).trans (spill_length s bits owned.physical)

end SszX86.Emit.Bits
