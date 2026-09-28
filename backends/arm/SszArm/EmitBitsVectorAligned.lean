import SszArm.EmitBitsCompose

namespace SszArm.Emit.Bits

open SszNative.Serialize (Packed)
open SszNative (NatOperand)
open UintCodec (widthLoad)

theorem vector_aligned_suffix (s : ArmState) (base : BitVec 64) (args : Args)
    (length : NatOperand) (bits : Packed) (size : Nat)
    (owned : Owned s args (.bitVector length) (.bits bits) size)
    (work : WorkRegisters s args .vector bits) (byteAligned : bits.count.toNat % 8 = 0)
    (copiedPrefix : ∀ index, index < bits.count.toNat / 8 →
      widthLoad s (args.output.toNat + index) 1 = some (bits.bytes[index]?.getD 0).toNat)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 1256#64) :
    ∃ t, run 4 s = t ∧ Produced s t args (.bitVector length) (.bits bits) size base := by
  let a := tailGuarded .vectorBacking s
  have countEq := (backing_guards bits).2.1 byteAligned
  have same : r (.GPR 24#5) s = r (.GPR 23#5) s := by
    apply BitVec.eq_of_toNat_eq
    rw [work.backing, work.full, countEq]
  have runA := tail_guard_run .vectorBacking s base code error aligned pc
  have pcA : read_pc a = base + 1580#64 := by
    rw [vector_aligned_pc s same, pc]
    simp [BitVec.add_assoc]
  have codeA : CodeAt a base := by simpa only [a, CodeAt, tailGuarded_program] using code
  have errorA : read_err a = .None := (tailGuarded_error .vectorBacking s).trans error
  have alignedA := aligned_of_stack aligned (tailGuarded_register .vectorBacking s 31#5)
  have input : Owned a args (.bitVector length) (.bits bits) size := owned.of_mem_eq (tailGuarded_memory _ _)
  have resultA : r (.GPR 19#5) a = args.result := (tailGuarded_register _ _ _).trans work.result
  have stackA : r (.GPR 31#5) a = args.bodySP := (tailGuarded_register _ _ _).trans work.stack
  have sizeEq := vector_size owned.expected
  have count : r (.GPR 24#5) a = BitVec.ofNat 64 size := by
    apply BitVec.eq_of_toNat_eq
    rw [tailGuarded_register, work.backing, BitVec.toNat_ofNat, Nat.mod_eq_of_lt owned.representable, sizeEq]
  have runFinish := finish_run .vectorFull a base args size codeA errorA alignedA pcA resultA count
  have output : SszNative.ByteView.BytesAt (widthLoad a) args.output.toNat
      (SszNative.Serialize.emit (.bitVector length) (.bits bits)) := by
    apply canonical_at
    · intro index before
      rw [load_eq_of_mem_eq (tailGuarded_memory .vectorBacking s)]
      exact copiedPrefix index before
    · intro impossible
      exact False.elim (impossible byteAligned)
  have post := finished_post .vectorFull a base args (.bitVector length) bits size input
    errorA resultA stackA output
  refine ⟨finished .vectorFull a base args size, ?_, ?_⟩
  · change run (2 + 2) s = _
    rw [run_plus, runA]
    exact runFinish
  · apply produced_prepend post (tailGuarded_program .vectorBacking s)
    · intro address outside
      exact congrFun (tailGuarded_memory .vectorBacking s) address
    · intro reg member
      exact tailGuarded_register .vectorBacking s reg
    · intro reg low high
      rw [tailGuarded_vector]

theorem vector_aligned_body (s : ArmState) (base : BitVec 64) (args : Args)
    (length : NatOperand) (bits : Packed) (size : Nat)
    (owned : Owned s args (.bitVector length) (.bits bits) size)
    (registers : BodyRegisters s args) (byteAligned : bits.count.toNat % 8 = 0)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 568#64) (tag : r (.GPR 8#5) s = 4#64) :
    ∃ steps t, run steps s = t ∧ Produced s t args (.bitVector length) (.bits bits) size base := by
  obtain ⟨prepareRun, preparePC⟩ := prepare_run s base args (.bitVector length) bits size trivial
    owned registers code error aligned pc tag
  simp only [pathOf] at prepareRun preparePC
  have copyPost := copy_prepared_correct .vector (desc := .bitVector length) base trivial
    owned registers code error preparePC
  have input := copied_owned .vector (desc := .bitVector length) trivial owned registers copyPost
  have work := copied_work .vector (desc := .bitVector length) trivial owned registers copyPost
  have prefixBytes := copied_prefix .vector owned registers copyPost
  have copyCode : CodeAt (copied .vector s bits) base := by
    simpa only [CodeAt, copyPost.program, prepared_program] using code
  have copyAligned := aligned_of_stack aligned (work.stack.trans registers.stack.symm)
  have copyPC : read_pc (copied .vector s bits) = base + 1256#64 := copyPost.pc
  obtain ⟨t, suffixRun, post⟩ := vector_aligned_suffix (copied .vector s bits) base args length bits size
    input work byteAligned prefixBytes copyCode copyPost.error copyAligned copyPC
  refine ⟨Path.vector.prepareFuel + ((Memcpy.fuel (bits.count.toNat / 8) + 1) + 4), t, ?_, ?_⟩
  · rw [run_plus, prepareRun, run_plus]
    exact suffixRun
  · exact prepend_copy .vector (desc := .bitVector length) trivial owned registers copyPost post

end SszArm.Emit.Bits
