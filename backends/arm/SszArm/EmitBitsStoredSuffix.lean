import SszArm.EmitBitsTailState
import SszArm.EmitBitsCompose

namespace SszArm.Emit.Bits

open SszNative.Serialize (Desc Packed)
open UintCodec (widthLoad)

def tailByte (path : Path) (bits : Packed) : UInt8 :=
  let masked := bits.bytes[bits.count.toNat / 8]! &&& UInt8.ofNat (2 ^ (bits.count.toNat % 8) - 1)
  match path with
  | .vector => masked
  | .list => if bits.count.toNat % 8 = 0 then 1 else masked ||| (1 <<< UInt8.ofNat (bits.count.toNat % 8))

def Path.finish : Path → Finish
  | .list => .list | .vector => .vectorTail

theorem emit_tail_at (load : Nat → Nat → Option Nat) (address : Nat)
    (desc : Desc) (bits : Packed) (kind : IsBits desc)
    (copiedPrefix : ∀ index, index < bits.count.toNat / 8 →
      load (address + index) 1 = some (bits.bytes[index]?.getD 0).toNat)
    (tail : load (address + bits.count.toNat / 8) 1 = some (tailByte (pathOf desc) bits).toNat) :
    SszNative.ByteView.BytesAt load address (SszNative.Serialize.emit desc (.bits bits)) := by
  cases desc with
  | bitVector length =>
    apply canonical_at load address bits copiedPrefix
    intro hasTail
    exact tail
  | bitList limit => exact delimited_at load address bits copiedPrefix tail
  | progressiveBitList limit => exact delimited_at load address bits copiedPrefix tail
  | _ => cases kind

theorem stored_suffix (s : ArmState) (base : BitVec 64) (args : Args)
    (desc : Desc) (bits : Packed) (size : Nat) (kind : IsBits desc)
    (owned : Owned s args desc (.bits bits) size) (work : WorkRegisters s args (pathOf desc) bits)
    (live : bits.count.toNat / 8 < size)
    (byte : (r (.GPR 8#5) s).setWidth 8 = (tailByte (pathOf desc) bits).toBitVec)
    (copiedPrefix : ∀ index, index < bits.count.toNat / 8 →
      widthLoad s (args.output.toNat + index) 1 = some (bits.bytes[index]?.getD 0).toNat)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (pathOf desc).storeStart) :
    ∃ t, run (7 + (pathOf desc).finish.ops.length) s = t ∧ Produced s t args desc (.bits bits) size base := by
  let path := pathOf desc
  let a := byteStored s
  have inside : (r (.GPR 23#5) s).toNat < size := by rwa [work.full]
  have aRun := store_run path base owned work.output work.stack inside code error aligned pc
  have frame := byteStored_frame owned work.output work.stack inside
  have input := owned.of_body_frame frame
  have aWork := work.of_body_frame owned frame (fun reg _ => byteStored_register s reg)
  have aCode : CodeAt a base := by simpa only [a, CodeAt, byteStored_program] using code
  have aError : read_err a = .None := (byteStored_error s).trans error
  have aAligned := aligned_of_stack aligned (byteStored_register s 31#5)
  have aPC : read_pc a = base + BitVec.ofNat 64 path.finish.start := by
    have advance (chosen : Path) :
        base + BitVec.ofNat 64 chosen.storeStart + 28#64 =
          base + BitVec.ofNat 64 chosen.finish.start := by
      cases chosen <;> simp [Path.storeStart, Path.finish, Finish.start, BitVec.add_assoc]
    rw [byteStored_pc, pc]
    exact advance (pathOf desc)
  have output : SszNative.ByteView.BytesAt (widthLoad a) args.output.toNat
      (SszNative.Serialize.emit desc (.bits bits)) := by
    apply emit_tail_at _ _ desc bits kind
    · intro index before
      rw [byteStored_prefix owned work.output work.stack inside index (by rwa [work.full])]
      exact copiedPrefix index before
    · have tail := byteStored_tail owned work.output inside
      rw [work.full, byte] at tail
      simpa only [UInt8.toNat_toBitVec] using tail
  have actualFull : (r (.GPR 23#5) a).toNat = bits.count.toNat / 8 := aWork.full
  have count : match path.finish with
      | .list => r (.GPR 23#5) a + 1#64 = BitVec.ofNat 64 size
      | _ => r (.GPR 24#5) a = BitVec.ofNat 64 size := by
    cases desc with
    | bitVector length =>
      change r (.GPR 24#5) a = BitVec.ofNat 64 size
      apply BitVec.eq_of_toNat_eq
      rw [aWork.backing, BitVec.toNat_ofNat, Nat.mod_eq_of_lt owned.representable,
        vector_size owned.expected]
    | bitList limit =>
      change r (.GPR 23#5) a + 1#64 = BitVec.ofNat 64 size
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, actualFull,
        Nat.mod_eq_of_lt (show 1 < 2^64 by decide)]
      rw [list_size (desc := .bitList limit) trivial owned.expected]
    | progressiveBitList limit =>
      change r (.GPR 23#5) a + 1#64 = BitVec.ofNat 64 size
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, actualFull,
        Nat.mod_eq_of_lt (show 1 < 2^64 by decide)]
      rw [list_size (desc := .progressiveBitList limit) trivial owned.expected]
    | _ => cases kind
  have finishRun := finish_run path.finish a base args size aCode aError aAligned aPC aWork.result count
  have post := finished_post path.finish a base args desc bits size input aError aWork.result aWork.stack output
  refine ⟨finished path.finish a base args size, ?_, ?_⟩
  · rw [run_plus, aRun]
    exact finishRun
  · apply produced_prepend post (byteStored_program s) frame
    · intro reg member; exact byteStored_register s reg
    · intro reg low high; rw [byteStored_vector]

end SszArm.Emit.Bits
