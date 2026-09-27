import SszArm.NatAddSmallLoopEntry

namespace SszArm.NatAdd.SmallLoop

open SszNative

/-- The complete physical output proved by entry_run is exactly the frozen
shared native write list, including its max-significant-count plus one extent. -/
theorem native_words (small pointer : BitVec 64) (right : List (BitVec 64)) :
    SszNative.NatAdd.writtenWords (.small small) (.large pointer right) =
      (LimbAdd.loop (SszNative.NatAdd.count (.small small) (.large pointer right) + 1)
        [small] right 0).1 := by
  simpa only [NatOperand.words] using
    SszNative.NatAdd.writtenWords_native_loop (.small small) (.large pointer right)

/-- Even when the physical right list has arbitrary redundant high zeros, the
extra allocated word consumes every remaining carry. No physical-length versus
significant-length equality is needed. -/
theorem native_suffix_carry_zero (small pointer : BitVec 64) (right : List (BitVec 64)) :
    (LimbAdd.loop (SszNative.NatAdd.count (.small small) (.large pointer right))
      [] (right.drop 1) (LimbAdd.step small (right.head?.getD 0#64) 0).2).2 = 0 := by
  have native := SszNative.NatAdd.writtenWords_final_carry
    (.small small) (.large pointer right)
  have same := SszNative.NatAdd.loop_trim_eq_native
    (SszNative.NatAdd.count (.small small) (.large pointer right) + 1)
    0 [small] right 0
  simp only [NatOperand.words] at native
  rw [show LimbAdd.loop
      (SszNative.NatAdd.count (.small small) (.large pointer right) + 1)
      (Limbs.trim [small]) (Limbs.trim right) 0 =
      LimbAdd.loop (SszNative.NatAdd.count (.small small) (.large pointer right) + 1)
        [small] right 0 by simpa only [List.drop_zero] using same] at native
  simpa only [LimbAdd.loop, List.head?_cons, Option.getD_some, List.tail_cons,
    List.drop_one] using native

end SszArm.NatAdd.SmallLoop
