import SszX86.EmitFinishMemory

namespace SszX86.Emit
open SszNative.Serialize UintCodec

/-- Only untouched bytes of the eighty-byte native success record are framed;
the usize and the four-byte discriminant have their exact values separately. -/
def ResultPadding (index : Nat) : Prop := (8 ≤ index ∧ index < 64) ∨ 68 ≤ index

theorem Owned.result_padding_protected {s : MachineData} {base : Int64}
    {desc : Desc} {value : Value} {buffer ra : BitVec 64} {written : Nat}
    (owned : Owned s base desc value buffer ra written)
    (i : Nat) (inside : i < 80) (padding : ResultPadding i) :
    ¬ Writable s written (s.regs.rdi.toBitVec + BitVec.ofNat 64 i) := by
  intro writes
  rcases writes with output | length | status | scratch
  · obtain ⟨j, hj, equal⟩ := output
    exact owned.outputResult j hj i inside equal.symm
  · obtain ⟨j, hj, equal⟩ := length
    have index := memmove_addr_injective s.regs.rdi.toBitVec 80 i j
      owned.resultBound inside (by omega) equal
    unfold ResultPadding at padding
    omega
  · obtain ⟨j, hj, equal⟩ := status
    have combined : s.regs.rdi.toBitVec + BitVec.ofNat 64 i =
        s.regs.rdi.toBitVec + BitVec.ofNat 64 (64 + j) := by
      rw [BitVec.ofNat_add]
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using equal
    have index := memmove_addr_injective s.regs.rdi.toBitVec 80 i (64 + j)
      owned.resultBound inside (by omega) combined
    unfold ResultPadding at padding
    omega
  · obtain ⟨j, hj, equal⟩ := scratch
    exact owned.resultStack i inside j (by omega) equal

theorem SuccessMemory.result_frame {s : MachineData} {base : Int64}
    {desc : Desc} {value : Value} {buffer ra : BitVec 64} {written : Nat} {m : DataMem}
    (post : SuccessMemory s desc value written m)
    (owned : Owned s base desc value buffer ra written) :
    ∀ i < 80, ResultPadding i →
      m.get? (s.regs.rdi.toBitVec + BitVec.ofNat 64 i) =
        s.dmem.get? (s.regs.rdi.toBitVec + BitVec.ofNat 64 i) := by
  intro i inside padding
  exact post.frame _ (owned.result_padding_protected i inside padding)

/-- Complete observable contract at the original caller return address. No RAX
value is asserted: the private sret entry has path-dependent scratch contents. -/
structure Post (s : MachineData) (desc : Desc) (value : Value)
    (buffer ra : BitVec 64) (written : Nat) (t : MachineState) : Prop where
  pc : t.2 = Int64.ofBitVec ra
  stack : t.1.regs.rsp.toBitVec = s.regs.rsp.toBitVec + 8
  rbx : t.1.regs.rbx.toBitVec = s.regs.rbx.toBitVec
  rbp : t.1.regs.rbp.toBitVec = s.regs.rbp.toBitVec
  r12 : t.1.regs.r12.toBitVec = s.regs.r12.toBitVec
  r13 : t.1.regs.r13.toBitVec = s.regs.r13.toBitVec
  r14 : t.1.regs.r14.toBitVec = s.regs.r14.toBitVec
  r15 : t.1.regs.r15.toBitVec = s.regs.r15.toBitVec
  vector : t.1.zmms = s.zmms
  memory : SuccessMemory s desc value written t.1.dmem
  outputFrame : ∀ i < s.regs.r9.toNat,
    t.1.dmem.get? (s.regs.r8.toBitVec + BitVec.ofNat 64 i) =
      applyWrites (fun j => s.dmem.get? (s.regs.r8.toBitVec + BitVec.ofNat 64 j))
        (emit desc value) i
  resultFrame : ∀ i < 80, ResultPadding i →
    t.1.dmem.get? (s.regs.rdi.toBitVec + BitVec.ofNat 64 i) =
      s.dmem.get? (s.regs.rdi.toBitVec + BitVec.ofNat 64 i)
  borrowedFrame : ∀ a, Borrowed s desc value buffer a →
    t.1.dmem.get? a = s.dmem.get? a

/-- Logical initialization refines physical bytes only at observed `some`
cells. The caller may supply `none` throughout the capacity, and no original
prefix observation is required. Physical tail bytes still obey `outputFrame`. -/
theorem Post.output_initialization {s : MachineData} {desc : Desc} {value : Value}
    {buffer ra : BitVec 64} {written : Nat} {t : MachineState}
    (post : Post s desc value buffer ra written t)
    (valid : ValidCall desc value s.regs.r9.toNat written)
    (before : Nat → Option UInt8)
    (tail : ∀ i byte, written ≤ i → i < s.regs.r9.toNat → before i = some byte →
      s.dmem.get? (s.regs.r8.toBitVec + BitVec.ofNat 64 i) = some byte) :
    ∀ i byte, i < s.regs.r9.toNat → applyWrites before (emit desc value) i = some byte →
      t.1.dmem.get? (s.regs.r8.toBitVec + BitVec.ofNat 64 i) = some byte := by
  intro i byte inside initialized
  rw [post.outputFrame i inside]
  by_cases live : i < (emit desc value).size
  · rw [applyWrites_prefix _ _ _ live]
    rw [applyWrites_prefix before _ _ live] at initialized
    exact initialized
  · have afterPrefix : written ≤ i := by
      have size := valid.emitted_size
      omega
    rw [applyWrites_tail _ _ _ (Nat.le_of_not_gt live)]
    apply tail i byte afterPrefix inside
    rw [applyWrites_tail before _ _ (Nat.le_of_not_gt live)] at initialized
    exact initialized

end SszX86.Emit
