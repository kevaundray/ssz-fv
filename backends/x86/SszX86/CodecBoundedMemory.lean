import SszX86.CodecBoundedResult

namespace SszX86.CodecBounded
open SszX86.UintCodec
open SszNative

abbrev InSpan := Emit.InSpan
abbrev MemoryFrame := Emit.MemoryFrame

def calledMem (s : MachineData) (base : Int64) : DataMem :=
  Mem.storeInt (savedMem s) (s.regs.rsp.toBitVec - 48) 8 (base + 47).toBitVec.toInt

def prefixMem (s : MachineData) (base : Int64) : Option NatOperand → DataMem
  | none => savedMem s
  | some _ => calledMem s base

theorem saved_frame (s : MachineData) :
    MemoryFrame s.dmem (savedMem s) (fun a => InSpan a (s.regs.rsp.toBitVec - 48) 48) := by
  intro a outside
  have keep (m : DataMem) (off : Nat) (v : Int) (lo : 8 ≤ off) (hi : off ≤ 40) :
      (Mem.storeInt m (s.regs.rsp.toBitVec - BitVec.ofNat 64 off) 8 v).get? a = m.get? a := by
    apply memmove_store_lookup_outside
    intro i hi'
    have i8 : i < 8 := by simpa only [Int.toBytes_length] using hi'
    intro eq
    apply outside
    refine ⟨48-off+i, by omega, ?_⟩
    rw [eq]
    bv_omega
  simp only [savedMem]
  rw [keep _ 40 _ (by decide) (by decide), keep _ 32 _ (by decide) (by decide),
    keep _ 24 _ (by decide) (by decide), keep _ 16 _ (by decide) (by decide),
    keep _ 8 _ (by decide) (by decide)]

theorem called_frame (s : MachineData) (base : Int64) :
    MemoryFrame s.dmem (calledMem s base) (fun a => InSpan a (s.regs.rsp.toBitVec - 48) 48) := by
  intro a outside
  unfold calledMem
  rw [memmove_store_lookup_outside]
  · exact saved_frame s a outside
  · intro i hi eq
    apply outside
    exact ⟨i, by simpa only [Int.toBytes_length] using (show i < 48 by
      have h : i < 8 := by simpa only [Int.toBytes_length] using hi
      omega), eq⟩

theorem prefix_frame (s : MachineData) (base : Int64) (cap : Option NatOperand) :
    MemoryFrame s.dmem (prefixMem s base cap)
      (fun a => InSpan a (s.regs.rsp.toBitVec - 48) 48) := by
  cases cap with
  | none => exact saved_frame s
  | some cap => exact called_frame s base

private theorem stack_keep (m : DataMem) (sp : BitVec 64) (a b : Nat) (v : Int)
    (ha : a ≤ 48) (hb : b ≤ 48) (apart : a + 8 ≤ b ∨ b + 8 ≤ a) :
    Mem.loadInt (Mem.storeInt m (sp - BitVec.ofNat 64 b) 8 v)
      (sp - BitVec.ofNat 64 a) 8 = Mem.loadInt m (sp - BitVec.ofNat 64 a) 8 := by
  apply BoolCodec.load_store_disjoint
  intro i hi j hj
  bv_omega

theorem saved_at (s : MachineData) (ra : BitVec 64)
    (ret : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))) :
    SavedAt (savedMem s) (s.regs.rsp.toBitVec - 40) s ra := by
  have addr (off : BitVec 64) : s.regs.rsp.toBitVec - 40 + off =
      s.regs.rsp.toBitVec - (40 - off) := by bv_omega
  constructor
  · exact Delimited.stored_return_load _ _ _
  · simp only [addr, BitVec.reduceSub, savedMem]
    rw [stack_keep _ _ 32 40 _ (by decide) (by decide) (by decide)]
    exact Delimited.stored_return_load _ _ _
  · simp only [addr, BitVec.reduceSub, savedMem]
    rw [stack_keep _ _ 24 40 _ (by decide) (by decide) (by decide),
      stack_keep _ _ 24 32 _ (by decide) (by decide) (by decide)]
    exact Delimited.stored_return_load _ _ _
  · simp only [addr, BitVec.reduceSub, savedMem]
    rw [stack_keep _ _ 16 40 _ (by decide) (by decide) (by decide),
      stack_keep _ _ 16 32 _ (by decide) (by decide) (by decide),
      stack_keep _ _ 16 24 _ (by decide) (by decide) (by decide)]
    exact Delimited.stored_return_load _ _ _
  · simp only [addr, BitVec.reduceSub, savedMem]
    rw [stack_keep _ _ 8 40 _ (by decide) (by decide) (by decide),
      stack_keep _ _ 8 32 _ (by decide) (by decide) (by decide),
      stack_keep _ _ 8 24 _ (by decide) (by decide) (by decide),
      stack_keep _ _ 8 16 _ (by decide) (by decide) (by decide)]
    exact Delimited.stored_return_load _ _ _
  · simp only [addr, BitVec.sub_self, BitVec.sub_zero]
    rw [Measure.frame_load _ _ _ (saved_frame s)]
    · exact ret
    · intro i hi inside
      rcases inside with ⟨j, hj, eq⟩
      bv_omega

theorem SavedAt.frame {m n : DataMem} {sp : BitVec 64} {s : MachineData} {ra : BitVec 64}
    (saved : SavedAt m sp s ra) (w : BitVec 64 → Prop) (frame : MemoryFrame m n w)
    (safe : ∀ a, InSpan a sp 48 → ¬w a) : SavedAt n sp s ra := by
  have keep (off : Nat) (bound : off + 8 ≤ 48) :
      Mem.loadInt n (sp + BitVec.ofNat 64 off) 8 =
        Mem.loadInt m (sp + BitVec.ofNat 64 off) 8 :=
    Measure.frame_load_window _ _ w frame sp off 8 48 bound safe
  constructor
  · simpa using (keep 0 (by decide)).trans saved.rbx
  · exact (keep 8 (by decide)).trans saved.r12
  · exact (keep 16 (by decide)).trans saved.r14
  · exact (keep 24 (by decide)).trans saved.r15
  · exact (keep 32 (by decide)).trans saved.rbp
  · exact (keep 40 (by decide)).trans saved.ret

theorem called_saved (s : MachineData) (base : Int64) (ra : BitVec 64)
    (ret : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))) :
    SavedAt (calledMem s base) (s.regs.rsp.toBitVec - 40) s ra := by
  apply (saved_at s ra ret).frame (fun a => InSpan a (s.regs.rsp.toBitVec - 48) 8)
  · intro a outside
    apply memmove_store_lookup_outside
    intro i hi eq
    exact outside ⟨i, by simpa only [Int.toBytes_length] using hi, eq⟩
  · intro a inside conflict
    rcases inside with ⟨i, hi, rfl⟩
    rcases conflict with ⟨j, hj, eq⟩
    bv_omega

def InputsAt (m : DataMem) (option actualAt : BitVec 64) (actual : NatOperand) : Option NatOperand → Prop
  | none => Mem.loadInt m option 4 = some 0
  | some cap => Mem.loadInt m option 4 = some 1 ∧
      Emit.NatAt m (option + 8) cap ∧ Emit.NatAt m actualAt actual

def Borrowed (option actualAt : BitVec 64) (actual : NatOperand) (cap : Option NatOperand)
    (a : BitVec 64) : Prop :=
  InSpan a option 4 ∨ match cap with
    | none => False
    | some cap => InSpan a (option + 8) 16 ∨ InSpan a actualAt 16 ∨
        Emit.NatBorrowed cap a ∨ Emit.NatBorrowed actual a

theorem inputs_frame (m n : DataMem) (option actualAt : BitVec 64)
    (actual : NatOperand) (cap : Option NatOperand) (w : BitVec 64 → Prop)
    (frame : MemoryFrame m n w)
    (safe : ∀ a, Borrowed option actualAt actual cap a → ¬w a)
    (input : InputsAt m option actualAt actual cap) : InputsAt n option actualAt actual cap := by
  have tag : Mem.loadInt n option 4 = Mem.loadInt m option 4 := by
    apply Measure.frame_load _ _ _ frame
    intro i hi
    exact safe _ (Or.inl ⟨i, hi, rfl⟩)
  cases cap with
  | none => exact tag.trans input
  | some cap =>
    refine ⟨tag.trans input.1, ?_, ?_⟩
    · exact Emit.natAt_frame m n w frame (option + 8) cap
        (fun a ha => safe a (Or.inr (Or.inl ha)))
        (fun a ha => safe a (Or.inr (Or.inr (Or.inr (Or.inl ha))))) input.2.1
    · exact Emit.natAt_frame m n w frame actualAt actual
        (fun a ha => safe a (Or.inr (Or.inr (Or.inl ha))))
        (fun a ha => safe a (Or.inr (Or.inr (Or.inr (Or.inr ha))))) input.2.2

theorem error_payload_frame (m : DataMem) (out cp cv ap av : BitVec 64) :
    MemoryFrame m (errorPayload m out cp cv ap av) (fun a => InSpan a out 68) := by
  intro a outside
  have keep (m : DataMem) (off width : Nat) (v : Int) (bound : off + width ≤ 68) :
      (Mem.storeInt m (out + BitVec.ofNat 64 off) width v).get? a = m.get? a := by
    apply BoolCodec.store_frame (limit := 68) m out a off width v bound
    intro i hi eq
    exact outside ⟨i, hi, eq⟩
  have keep0 (m : DataMem) (v : Int) : (Mem.storeInt m out 8 v).get? a = m.get? a := by
    simpa using keep m 0 8 v (by decide)
  simp (disch := decide) only [errorPayload, keep, keep0]

theorem status_frame (m : DataMem) (out : BitVec 64) (status : Int) :
    MemoryFrame m (Mem.storeInt m (out + 64#64) 4 status) (fun a => InSpan a out 68) := by
  intro a outside
  apply BoolCodec.store_frame (limit := 68) m out a 64 4 status (by decide)
  intro i hi eq
  exact outside ⟨i, hi, eq⟩

end SszX86.CodecBounded
