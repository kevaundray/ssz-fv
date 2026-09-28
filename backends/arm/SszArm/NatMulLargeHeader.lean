import SszArm.NatMulLargeReserve

namespace SszArm.NatMul

open Delimited (Protected MemoryFrame)
open SszNative (NatOperand NatArithmetic)

theorem LargeReservation.header {s : ArmState} {left right : NatOperand}
    {reservation : SszNative.Arena.Reservation} (allocated : LargeReservation s left right reservation)
    (owned : Owned s left right) :
    Protected (writesFor s (outcome s left right)) (r (.GPR 5#5) s).toNat 16 := by
  have localHeader := owned.arenaLocal.subspan 0 16 (by decide)
  have positive := allocated.positive
  have writes : writesFor s (outcome s left right) = localWrites s (outcome s left right) ++
      [((r (.GPR 5#5) s).toNat + 16, 8), (reservation.pointer, 8 * (left.wordCount + right.wordCount))] := by
    simp only [writesFor, allocated.model, NatArithmetic.committed, SszNative.NatMul.writtenWords_length]
  right
  intro span member
  rw [writes] at member
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with localMember | rfl | rfl
  · rcases localHeader with empty | separate
    · omega
    · simpa only [Nat.add_zero] using separate span localMember
  · simp only [Prod.fst, Prod.snd]; omega
  · rcases allocated.fresh with empty | separate
    · omega
    · have apart := separate ((r (.GPR 5#5) s).toNat, 24) (by simp)
      simp only [Prod.fst, Prod.snd] at apart ⊢
      omega

theorem large_header16_read {s t : ArmState} {left right : NatOperand}
    (owned : Owned s left right) (frame : MemoryFrame (writesFor s (outcome s left right)) s t)
    (header : Protected (writesFor s (outcome s left right)) (r (.GPR 5#5) s).toNat 16)
    (offset : Nat) (bound : offset + 8 ≤ 16) :
    read_mem_bytes 8 (r (.GPR 5#5) s + BitVec.ofNat 64 offset) t =
      read_mem_bytes 8 (r (.GPR 5#5) s + BitVec.ofNat 64 offset) s := by
  have physical := owned.arenaBound
  have address : (r (.GPR 5#5) s + BitVec.ofNat 64 offset).toNat =
      (r (.GPR 5#5) s).toNat + offset := by bv_omega
  apply frame.read
  · rw [address]; omega
  · rw [address]; exact header.subspan offset 8 bound

end SszArm.NatMul
