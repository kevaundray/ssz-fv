import SszX86.CodecIsFixedFields

namespace SszX86.CodecIsFixed
open SszNative UintCodec BoolCodec

structure Working (s : MachineData) (base : Int64) (r : Codec.Footprint)
    (desc : SszNative.Codec.Desc) (bytes : Nat) : Prop where
  descriptor : Codec.DescAt s.dmem r s.regs.rdi.toBitVec desc
  table : TableAt s.dmem base
  table_readonly : ∀ i < tableBytes.length, r (tableAddress base + BitVec.ofNat 64 i)
  stack : Codec.StackAt s.dmem s.regs.rsp.toBitVec bytes
  enough : stackBytes desc ≤ 24 + bytes
  above : s.regs.rsp.toNat + 32 ≤ 2 ^ 64
  readonly : ∀ a, r a → ¬ Codec.StackWrites s.regs.rsp.toBitVec bytes a

structure FieldsOwned (s : MachineData) (base : Int64) (r : Codec.Footprint)
    (fields : List (String × SszNative.Codec.Desc)) (bytes : Nat) : Prop where
  stored : Codec.FieldsAt s.dmem r s.regs.rbx.toBitVec fields
  counter : s.regs.r14.toBitVec = BitVec.ofNat 64 (24 * fields.length)
  byteBound : 24 * fields.length < 2 ^ 64
  table : TableAt s.dmem base
  table_readonly : ∀ i < tableBytes.length, r (tableAddress base + BitVec.ofNat 64 i)
  stack : Codec.StackAt s.dmem s.regs.rsp.toBitVec bytes
  enough : fieldsStackBytes fields ≤ bytes
  above : s.regs.rsp.toNat + 32 ≤ 2 ^ 64
  readonly : ∀ a, r a → ¬ Codec.StackWrites s.regs.rsp.toBitVec bytes a

theorem stack_above (sp : BitVec 64) (bytes offset count : Nat)
    (low : bytes ≤ sp.toNat) (bound : sp.toNat + offset + count ≤ 2 ^ 64) :
    ∀ i < count, ¬ Codec.StackWrites sp bytes (sp + BitVec.ofNat 64 offset + BitVec.ofNat 64 i) := by
  intro i hi inside
  obtain ⟨j, hj, same⟩ := inside
  bv_omega

theorem frame_load_above {m n : DataMem} (sp : BitVec 64) (bytes offset count : Nat)
    (low : bytes ≤ sp.toNat) (bound : sp.toNat + offset + count ≤ 2 ^ 64)
    (frame : Codec.MemoryFrame m n (Codec.StackWrites sp bytes)) :
    Mem.loadInt n (sp + BitVec.ofNat 64 offset) count =
      Mem.loadInt m (sp + BitVec.ofNat 64 offset) count := by
  apply memmove_loadInt_congr
  intro i hi
  exact frame _ (stack_above sp bytes offset count low bound i hi)

/-- The call's return-slot store is part of the parent's finite owned stack,
not an assumed recursive execution. -/
theorem call_frame (s : MachineData) (ra : BitVec 64) (bytes : Nat) (enough : 8 ≤ bytes) :
    Codec.MemoryFrame s.dmem (callState s ra).dmem
      (Codec.StackWrites s.regs.rsp.toBitVec bytes) := by
  intro a outside
  apply memmove_store_lookup_outside
  intro i hi equal
  have bound : i < 8 := by simpa only [Int.toBytes_length] using hi
  apply outside
  apply Codec.stack_subspan s.regs.rsp.toBitVec 0 8 bytes (by omega) a
  exact ⟨i, bound, equal⟩

theorem call_return_load (s : MachineData) (ra : BitVec 64) :
    Mem.loadInt (callState s ra).dmem (callState s ra).regs.rsp.toBitVec 8 =
      some (Int.ofBytes (wordBytes ra)) := by
  change Mem.loadInt (Mem.storeInt s.dmem (s.regs.rsp.toBitVec - 8) 8 ra.toInt)
    (s.regs.rsp.toBitVec - 8) 8 = _
  rw [wordBytes, ← registerBytes_eq_uintBytes, ofBytes_toBytes]
  exact load_store_same _ _ 8 ra.toInt (by decide)

theorem call_mapped (s : MachineData) (ra p : BitVec 64) (n : Nat)
    (hm : Large.Mapped s.dmem p n) : Large.Mapped (callState s ra).dmem p n :=
  Large.mapped_store _ _ _ _ _ _ hm

/-- A recursive call's initial-state ownership follows from the current
physical child storage and the parent's stack envelope. -/
theorem child_owned (s : MachineData) (base : Int64) (r : Codec.Footprint)
    (desc : SszNative.Codec.Desc) (bytes : Nat)
    (stored : Codec.DescAt s.dmem r s.regs.rdi.toBitVec desc)
    (table : TableAt s.dmem base)
    (table_readonly : ∀ i < tableBytes.length, r (tableAddress base + BitVec.ofNat 64 i))
    (stack : Codec.StackAt s.dmem s.regs.rsp.toBitVec bytes)
    (enough : 8 + stackBytes desc ≤ bytes)
    (above : s.regs.rsp.toNat + 32 ≤ 2 ^ 64)
    (readonly : ∀ a, r a → ¬ Codec.StackWrites s.regs.rsp.toBitVec bytes a) :
    Owned (callState s (base + 114).toBitVec) base r desc (base + 114).toBitVec (bytes - 8) := by
  have eight : 8 ≤ bytes := by omega
  have frame := call_frame s (base + 114).toBitVec bytes eight
  have substack := stack.substack 8 (bytes - 8) (by omega)
  refine ⟨stored.frame frame readonly, table_frame table table_readonly frame readonly,
    table_readonly, ?_, by omega, ?_, call_return_load _ _, ?_⟩
  · refine ⟨substack.lowEnough, ?_⟩
    exact call_mapped _ _ _ _ substack.mapped
  · change (s.regs.rsp.toBitVec - 8).toNat + 8 ≤ 2 ^ 64
    have low := stack.lowEnough
    have word := s.regs.rsp.toBitVec.isLt
    simp only [UInt64.toNat_toBitVec] at *
    bv_omega
  · intro a input inside
    apply readonly a input
    exact Codec.stack_subspan s.regs.rsp.toBitVec 8 (bytes - 8) bytes (by omega) a inside

/-- Composition hides the CALL representation, but retains both its write and
all writes made by the well-founded recursive callee. -/
theorem child_frame (s : MachineData) (base : Int64) (desc : SszNative.Codec.Desc)
    (bytes : Nat) (enough : 8 ≤ bytes) (t : MachineState)
    (post : Post (callState s (base + 114).toBitVec) desc (base + 114).toBitVec (bytes - 8) t) :
    Codec.MemoryFrame s.dmem t.1.dmem (Codec.StackWrites s.regs.rsp.toBitVec bytes) := by
  intro a outside
  have suboutside : ¬ Codec.StackWrites (callState s (base + 114).toBitVec).regs.rsp.toBitVec
      (bytes - 8) a := by
    intro inside
    apply outside
    exact Codec.stack_subspan s.regs.rsp.toBitVec 8 (bytes - 8) bytes (by omega) a inside
  exact (post.frame a suboutside).trans (call_frame s _ bytes enough a outside)

theorem child_stack (s : MachineData) (base : Int64) (desc : SszNative.Codec.Desc)
    (bytes : Nat) (t : MachineState)
    (post : Post (callState s (base + 114).toBitVec) desc (base + 114).toBitVec (bytes - 8) t) :
    t.1.regs.rsp = s.regs.rsp := by
  apply UInt64.toBitVec_inj.1
  have returned := post.returned.sp
  simpa only [callState, UInt64.toBitVec_ofBitVec, BitVec.sub_add_cancel] using returned

/-- Invariant carried between instruction blocks within one activation. -/
structure Prefix (s t : MachineData) (bytes : Nat) : Prop where
  stack : t.regs.rsp = s.regs.rsp
  rbp : t.regs.rbp = s.regs.rbp
  r12 : t.regs.r12 = s.regs.r12
  r13 : t.regs.r13 = s.regs.r13
  r15 : t.regs.r15 = s.regs.r15
  vectors : t.zmms = s.zmms
  frame : Codec.MemoryFrame s.dmem t.dmem (Codec.StackWrites s.regs.rsp.toBitVec bytes)
  «mapped» : ∀ p n, Large.Mapped s.dmem p n → Large.Mapped t.dmem p n

theorem Prefix.refl (s : MachineData) (bytes : Nat) : Prefix s s bytes :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ h => h⟩

theorem Prefix.trans {s t u : MachineData} {bytes : Nat}
    (first : Prefix s t bytes) (second : Prefix t u bytes) : Prefix s u bytes := by
  refine ⟨second.stack.trans first.stack, second.rbp.trans first.rbp,
    second.r12.trans first.r12, second.r13.trans first.r13, second.r15.trans first.r15,
    second.vectors.trans first.vectors, ?_, ?_⟩
  · intro a outside
    exact (second.frame a (by simpa only [first.stack] using outside)).trans
      (first.frame a outside)
  · intro p n hm
    exact second.mapped p n (first.mapped p n hm)

theorem BodyPost.preceded {s current : MachineData} {bytes : Nat} {value : Bool}
    {base : Int64} {t : MachineState} (prefix : Prefix s current bytes)
    (post : BodyPost current bytes value base t) : BodyPost s bytes value base t := by
  refine ⟨post.pc, post.result, post.stack.trans prefix.stack,
    post.rbp.trans prefix.rbp, post.r12.trans prefix.r12, post.r13.trans prefix.r13,
    post.r15.trans prefix.r15, post.vectors.trans prefix.vectors, ?_, ?_⟩
  · intro a outside
    exact (post.frame a (by simpa only [prefix.stack] using outside)).trans
      (prefix.frame a outside)
  · intro p n hm
    exact post.mapped p n (prefix.mapped p n hm)

theorem child_prefix (s : MachineData) (base : Int64) (desc : SszNative.Codec.Desc)
    (bytes : Nat) (enough : 8 ≤ bytes) (t : MachineState)
    (post : Post (callState s (base + 114).toBitVec) desc (base + 114).toBitVec (bytes - 8) t) :
    Prefix s t.1 bytes := by
  refine ⟨child_stack s base desc bytes t post, post.returned.rbp,
    post.returned.r12, post.returned.r13, post.returned.r15, post.returned.simd,
    child_frame s base desc bytes enough t post, ?_⟩
  intro p n hm
  exact post.mapped p n (call_mapped _ _ p n hm)

end SszX86.CodecIsFixed
