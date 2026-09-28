import SszArm.EmitBitsBeforeCopy

namespace SszArm.Emit.Bits

open SszNative.Serialize (Desc Packed)
open BitVector.ValueTail (countLow)

structure WorkRegisters (s : ArmState) (args : Args) (path : Path) (bits : Packed) : Prop where
  result : r (.GPR 19#5) s = args.result
  output : r (.GPR 20#5) s = args.output
  capacity : r (.GPR 21#5) s = args.capacity
  stack : r (.GPR 31#5) s = args.bodySP
  source : r (.GPR 22#5) s = read_mem_bytes 8 (args.value + 16#64) s
  full : (r (.GPR 23#5) s).toNat = bits.count.toNat / 8
  backing : (r (.GPR 24#5) s).toNat = bits.bytes.size
  low : r (.GPR path.low) s = countLow bits.count
  remainder : path = .list → (r (.GPR 25#5) s).toNat = bits.count.toNat % 8

theorem low32_remainder (count : BitVec 128) :
    ((((countLow count).setWidth 32) &&& 7#32).setWidth 64).toNat = count.toNat % 8 := by
  have narrow : (((countLow count).setWidth 32) &&& 7#32).toNat =
      ((countLow count).setWidth 32).toNat % 8 := by
    change ((countLow count).setWidth 32).toNat &&& (2^3 - 1) =
      ((countLow count).setWidth 32).toNat % 2^3
    exact Nat.and_two_pow_sub_one_eq_mod _ _
  simp only [BitVec.toNat_setWidth, narrow, countLow]
  have bound := count.isLt
  omega

theorem prepared_work (path : Path) {s : ArmState} {args : Args} {desc : Desc}
    {bits : Packed} {size : Nat} (owned : Owned s args desc (.bits bits) size)
    (registers : BodyRegisters s args) : WorkRegisters (prepared path s) args path bits := by
  have preserved (reg : BitVec 5)
      (untouched : reg ∉ [0#5, 1#5, 2#5, 8#5, 9#5, 22#5, 23#5, 24#5, 25#5, 26#5]) :=
    prepared_register path s reg untouched
  have qInput := quotientLoaded_owned path owned registers
  have qValue : r (.GPR 22#5) (quotientLoaded path s) = args.value :=
    (quotientLoaded_register path s 22#5 (by cases path <;> decide)).trans registers.value
  have low : r (.GPR path.low) (quotientLoaded path s) = countLow bits.count := by
    have value := (routed_register path s 22#5 (by decide)).trans registers.value
    have reads := Memory.mem_eq_iff_read_mem_bytes_eq.mp (routed_memory path s)
    rw [quotientLoaded, shifted_register path _ path.low (by cases path <;> decide), counted_low,
      value, reads]
    exact owned.value_at.2.2.2.2.1
  have checkedLow : r (.GPR path.low) (checked path s) = countLow bits.count := by
    simp only [checked, guarded_register, backing_register _ path.low (by cases path <;> decide)]
    exact low
  refine ⟨(preserved _ (by decide)).trans registers.result,
    (preserved _ (by decide)).trans registers.output,
    (preserved _ (by decide)).trans registers.capacity,
    (preserved _ (by decide)).trans registers.stack, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨_, pointer, _⟩ := prepared_arguments path owned registers
    have equal : r (.GPR 22#5) (prepared path s) = r (.GPR 1#5) (prepared path s) := by
      cases path <;> simp [prepared, ready, block, Path.setupOps, Op.effect,
        Activation.put, Activation.next, state_simp_rules]
    exact equal.trans pointer
  · rw [prepared, ready_register path _ 23#5 (by decide), checked_full]
    exact quotientLoaded_value path owned registers
  · rw [prepared, ready_register path _ 24#5 (by decide), checked, guarded_register, backing_length,
      guarded_register, qValue]
    have reads := Memory.mem_eq_iff_read_mem_bytes_eq.mp (guarded_memory path.capacityGuard (quotientLoaded path s))
    rw [reads]
    exact qInput.value_at.2.1
  · have same : r (.GPR path.low) (prepared path s) = r (.GPR path.low) (checked path s) := by
      cases path <;> simp [prepared, ready, block, Path.setupOps, Path.low, Op.effect,
        Activation.put, Activation.next, state_simp_rules]
    exact same.trans checkedLow
  · intro list
    subst path
    have value : r (.GPR 26#5) (checked Path.list s) = countLow bits.count := checkedLow
    have result : r (.GPR 25#5) (prepared .list s) =
        (((countLow bits.count).setWidth 32 &&& 7#32).setWidth 64) := by
      simp [prepared, ready, block, Path.setupOps, Op.effect, Activation.put, Activation.next,
        state_simp_rules, value]
    rw [result]
    exact low32_remainder bits.count

theorem copied_work (path : Path) {s : ArmState} {args : Args} {desc : Desc}
    {bits : Packed} {size : Nat} {base : BitVec 64} (kind : IsBits desc)
    (owned : Owned s args desc (.bits bits) size) (registers : BodyRegisters s args)
    (post : CopyPost path.copySite (prepared path s) (copied path s bits) base) :
    WorkRegisters (copied path s bits) args path bits := by
  have work := prepared_work path owned registers
  have input := prepared_owned path owned registers
  obtain ⟨r0, _, r2⟩ := prepared_arguments path owned registers
  have memory := post.frame
  rw [r0, r2] at memory
  have bodyFrame := copy_prefix_frame kind input memory
  have frame : Delimited.MemoryFrame (writesFor args size) (prepared path s) (copied path s bits) := by
    intro address outside
    exact bodyFrame address (fun span member => outside span (bodyWrites_subset args size span member))
  have header := frame_read_offset frame args.value 48 16 8 input.valueBound input.valueOwned (by decide)
  refine ⟨(post.registers _ (by decide)).trans work.result,
    (post.registers _ (by decide)).trans work.output,
    (post.registers _ (by decide)).trans work.capacity,
    (post.registers _ (by decide)).trans work.stack, ?_, ?_, ?_, ?_, ?_⟩
  · rw [post.registers _ (by decide), work.source, header]
  · rw [post.registers _ (by decide)]; exact work.full
  · rw [post.registers _ (by decide)]; exact work.backing
  · rw [post.registers _ (by cases path <;> decide)]; exact work.low
  · intro list; rw [post.registers _ (by decide)]; exact work.remainder list

end SszArm.Emit.Bits
