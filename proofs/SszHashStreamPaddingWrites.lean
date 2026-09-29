import SszHashStreamPadding

namespace SszNative.HashStream

/-- A checked write preserves every buffer cell outside its destination interval. -/
def overwrite (buf : Vector UInt8 64) (dst : Nat) (payload : List UInt8)
    (bound : dst + payload.length ≤ 64) : Vector UInt8 64 :=
  ⟨(buf.toList.take dst ++ payload ++ buf.toList.drop (dst + payload.length)).toArray,
    by
      simp only [List.size_toArray, List.length_append, List.length_take,
        List.length_drop, Vector.length_toList]
      omega⟩

theorem overwrite_toList (buf : Vector UInt8 64) (dst : Nat) (payload : List UInt8)
    (bound : dst + payload.length ≤ 64) :
    (overwrite buf dst payload bound).toList =
      buf.toList.take dst ++ payload ++ buf.toList.drop (dst + payload.length) := rfl

/-- The initialized buffer prefix after a write ends with exactly its payload. -/
theorem overwrite_take_end (buf : Vector UInt8 64) (dst : Nat) (payload : List UInt8)
    (bound : dst + payload.length ≤ 64) :
    (overwrite buf dst payload bound).toList.take (dst + payload.length) =
      buf.toList.take dst ++ payload := by
  rw [overwrite_toList]
  have hlen : (buf.toList.take dst ++ payload).length = dst + payload.length := by
    simp only [List.length_append, List.length_take, Vector.length_toList]
    omega
  rw [← hlen]
  exact List.take_append_length

/-- A write reaching the buffer's end leaves no stale suffix. -/
theorem overwrite_toList_end (buf : Vector UInt8 64) (dst : Nat) (payload : List UInt8)
    (bound : dst + payload.length ≤ 64) (hend : dst + payload.length = 64) :
    (overwrite buf dst payload bound).toList = buf.toList.take dst ++ payload := by
  rw [overwrite_toList]
  have hempty : buf.toList.drop (dst + payload.length) = [] :=
    List.drop_eq_nil_of_le (by simp only [Vector.length_toList]; omega)
  rw [hempty, List.append_nil]

/-- Bytes before the destination remain unchanged, including earlier partial writes. -/
theorem overwrite_take_before (buf : Vector UInt8 64) (dst : Nat)
    (payload : List UInt8) (bound : dst + payload.length ≤ 64)
    (n : Nat) (hn : n ≤ dst) :
    (overwrite buf dst payload bound).toList.take n = buf.toList.take n := by
  have h := congrArg (fun ys : List UInt8 => ys.take n)
    (overwrite_take_end buf dst payload bound)
  have hfirst : n ≤ (buf.toList.take dst).length := by
    simp only [List.length_take, Vector.length_toList]
    omega
  rw [List.take_take, Nat.min_eq_left (by omega : n ≤ dst + payload.length),
    List.take_append_of_le_length hfirst, List.take_take, Nat.min_eq_left hn] at h
  exact h

end SszNative.HashStream
