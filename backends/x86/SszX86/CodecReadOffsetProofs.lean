import SszX86.CodecReadOffsetExec

namespace SszX86.CodecReadOffset
open SszX86.UintCodec

/-- The returned value and exact writable footprint. The input and return
address are borrowed, and may overlap each other, but not the PUSH slot. -/
def Returned (s : MachineData) (ra result : BitVec 64) (t : MachineState) : Prop :=
  t.2 = Int64.ofBitVec ra ∧ t.1.regs.rax.toBitVec = result ∧
  t.1.dmem = pushedMem s ∧ t.1.zmms = s.zmms ∧
  t.1.regs.rsp.toBitVec = s.regs.rsp.toBitVec + 8 ∧
  ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .rsp →
    t.1.regs.get64 r = s.regs.get64 r

theorem pushed_frame (s : MachineData) (a : BitVec 64)
    (outside : ∀ i < 8, a ≠ s.regs.rsp.toBitVec - 8 + BitVec.ofNat 64 i) :
    (pushedMem s).get? a = s.dmem.get? a := by
  apply memmove_store_lookup_outside
  intro i hi
  exact outside i (by simpa only [Int.toBytes_length] using hi)

private theorem pushed_input (s : MachineData) (b0 b1 b2 b3 : BitVec 8)
    (input : BytesAt s.dmem s.regs.rdi.toBitVec b0 b1 b2 b3)
    (apart : ∀ i < 4, ∀ j < 8,
      s.regs.rdi.toBitVec + BitVec.ofNat 64 i ≠
        s.regs.rsp.toBitVec - 8 + BitVec.ofNat 64 j) :
    BytesAt (pushedMem s) s.regs.rdi.toBitVec b0 b1 b2 b3 := by
  have keep (i : Nat) (hi : i < 4) :
      Mem.loadInt (pushedMem s) (s.regs.rdi.toBitVec + BitVec.ofNat 64 i) 1 =
        Mem.loadInt s.dmem (s.regs.rdi.toBitVec + BitVec.ofNat 64 i) 1 := by
    apply BoolCodec.load_store_disjoint
    intro k hk j hj
    have hk0 : k = 0 := by omega
    subst k
    simpa using apart i hi j hj
  unfold BytesAt at *
  simpa only [keep 0 (by decide), keep 1 (by decide), keep 2 (by decide),
    keep 3 (by decide), BitVec.ofNat_zero, BitVec.add_zero] using input

theorem return_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (saved ra : BitVec 64)
    (hpop : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 =
      some (Int.ofBytes (wordBytes saved)))
    (hret : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 8) 8 =
      some (Int.ofBytes (wordBytes ra)))
    (P : MachineState → Prop)
    (next : P ({s with regs := {s.regs with rcx := UInt64.ofBitVec saved,
      rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec + 16)}}, Int64.ofBitVec ra)) :
    Eventually (step e) P (s, base + 57) := by
  codec_offset_step 19 using hc
  simp only [MachineData.load, Effects.All, hpop, ofBytes_wordBytes]
  codec_offset_step 20 using hc
  simp only [MachineData.load, Effects.All, hret, ofBytes_wordBytes]
  simpa [BitVec.add_assoc, UInt64.add_assoc] using Eventually.done _ next

/-- Entry-to-RET correctness for every native caller-safe slice. The four panic
edges are excluded by the original slice length, rather than by assumed future
branch outcomes. The return area is not written and no padding is initialized. -/
theorem program_correct (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (ra : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    (length : 4 ≤ s.regs.rsi.toNat)
    (stack : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 8) 8)
    (input : BytesAt s.dmem s.regs.rdi.toBitVec b0 b1 b2 b3)
    (apart : ∀ i < 4, ∀ j < 8,
      s.regs.rdi.toBitVec + BitVec.ofNat 64 i ≠
        s.regs.rsp.toBitVec - 8 + BitVec.ofNat 64 j)
    (ret : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 =
      some (Int.ofBytes (wordBytes ra))) :
    Eventually (step e) (Returned s ra (value b0 b1 b2 b3)) (s, base) := by
  have input' := pushed_input s b0 b1 b2 b3 input apart
  have pop : Mem.loadInt (pushedMem s) (s.regs.rsp.toBitVec - 8) 8 =
      some (Int.ofBytes (wordBytes s.regs.rax.toBitVec)) := by
    rw [wordBytes, ← registerBytes_eq_uintBytes, ofBytes_toBytes]
    exact BoolCodec.load_store_same _ _ 8 _ (by decide)
  have ret' : Mem.loadInt (pushedMem s) s.regs.rsp.toBitVec 8 =
      some (Int.ofBytes (wordBytes ra)) := by
    rw [pushedMem, BoolCodec.load_store_disjoint]
    · exact ret
    · intro i hi j hj
      bv_omega
  have afterPush : Eventually (step e) (Returned s ra (value b0 b1 b2 b3))
      (pushedState s, base + 1) := by
    apply bounds_cps e base hc _ length
    intro f0
    apply body_cps e base hc _ b0 b1 b2 b3 input'
    intro f1
    apply return_cps e base hc _ s.regs.rax.toBitVec ra
    · exact pop
    · simpa [state, pushedState] using ret'
    · refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
      · simp [state, pushedState]
        bv_omega
      · intro r h1 h2 h3 h4 h5
        cases r <;> simp_all [state, pushedState, Reg64s.get64]
  rw [← Int64.add_zero base]
  codec_offset_step 0 using hc
  apply Delimited.store_cps
  · simpa using Large.mapped_load s.dmem (s.regs.rsp.toBitVec - 8) 8 0 8 stack (by decide)
  · simpa [pushedState, pushedMem, Effects.All] using afterPush

end SszX86.CodecReadOffset
