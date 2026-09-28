import SszArm.EmitBitsCallState

namespace SszArm.Emit.Bits

open SszNative.Serialize (Desc Packed)
open UintCodec (widthLoad)
open Delimited (MemoryFrame)

def copied (path : Path) (s : ArmState) (bits : Packed) : ArmState :=
  run (Memcpy.fuel (bits.count.toNat / 8) + 1) (prepared path s)

theorem copy_prepared_correct (path : Path) {s : ArmState} {args : Args} {desc : Desc}
    {bits : Packed} {size : Nat} (base : BitVec 64) (kind : IsBits desc)
    (owned : Owned s args desc (.bits bits) size) (registers : BodyRegisters s args)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc (prepared path s) = base + BitVec.ofNat 64 path.copySite.offset) :
    CopyPost path.copySite (prepared path s) (copied path s bits) base := by
  have input := prepared_owned path owned registers
  obtain ⟨r0, r1, r2⟩ := prepared_arguments path owned registers
  obtain ⟨destination, source, separate⟩ := copy_bounds kind input
  have preparedCode : CodeAt (prepared path s) base := by
    simpa only [CodeAt, prepared_program] using code
  have preparedError := (prepared_error path s).trans error
  have post := copy_correct path.copySite (prepared path s) base preparedCode preparedError pc
    (by rwa [r0, r2]) (by rwa [r1, r2]) (by rwa [r0, r1, r2])
  simpa only [copied, r2] using post

theorem copy_prefix_frame {s t : ArmState} {args : Args} {desc : Desc} {bits : Packed} {size : Nat}
    (kind : IsBits desc) (owned : Owned s args desc (.bits bits) size)
    (frame : MemoryFrame [(args.output.toNat, bits.count.toNat / 8)] s t) :
    MemoryFrame (bodyWrites args size) s t := by
  have full := full_le_size kind owned.expected
  intro address outside
  apply frame address
  intro span member
  simp only [List.mem_singleton] at member
  subst span
  by_cases empty : size = 0
  · simp only [Prod.fst, Prod.snd]
    omega
  · have position := outside (args.output.toNat, size) (by simp [bodyWrites, empty])
    simp only [Prod.fst, Prod.snd] at position ⊢
    omega

theorem copied_owned (path : Path) {s : ArmState} {args : Args} {desc : Desc}
    {bits : Packed} {size : Nat} {base : BitVec 64} (kind : IsBits desc)
    (owned : Owned s args desc (.bits bits) size) (registers : BodyRegisters s args)
    (post : CopyPost path.copySite (prepared path s) (copied path s bits) base) :
    Owned (copied path s bits) args desc (.bits bits) size := by
  have input := prepared_owned path owned registers
  obtain ⟨r0, _, r2⟩ := prepared_arguments path owned registers
  have frame := post.frame
  rw [r0, r2] at frame
  have bodyFrame := copy_prefix_frame kind input frame
  apply input.of_frame
  intro address outside
  exact bodyFrame address (fun span member => outside span (bodyWrites_subset args size span member))

theorem copied_prefix (path : Path) {s : ArmState} {args : Args} {desc : Desc}
    {bits : Packed} {size : Nat} {base : BitVec 64}
    (owned : Owned s args desc (.bits bits) size) (registers : BodyRegisters s args)
    (post : CopyPost path.copySite (prepared path s) (copied path s bits) base) :
    ∀ index, index < bits.count.toNat / 8 →
      widthLoad (copied path s bits) (args.output.toNat + index) 1 =
        some (bits.bytes[index]?.getD 0).toNat := by
  have input := prepared_owned path owned registers
  obtain ⟨r0, r1, r2⟩ := prepared_arguments path owned registers
  intro index inside
  have observation := post.copied index 1 (by rw [r2]; omega)
  rw [r0, r1] at observation
  have full := (backing_guards bits).1
  exact observation.trans (input.value_at.2.2.2.1 index (by omega))

theorem copied_frame (path : Path) {s : ArmState} {args : Args} {desc : Desc}
    {bits : Packed} {size : Nat} {base : BitVec 64} (kind : IsBits desc)
    (owned : Owned s args desc (.bits bits) size) (registers : BodyRegisters s args)
    (post : CopyPost path.copySite (prepared path s) (copied path s bits) base) :
    MemoryFrame (bodyWrites args size) s (copied path s bits) := by
  obtain ⟨r0, _, r2⟩ := prepared_arguments path owned registers
  have frame := post.frame
  rw [r0, r2] at frame
  exact (prepared_frame path owned registers).trans
    (copy_prefix_frame kind (prepared_owned path owned registers) frame)

end SszArm.Emit.Bits
