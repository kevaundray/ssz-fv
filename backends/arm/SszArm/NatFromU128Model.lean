import SszArm.NatFromU128Resources

namespace SszArm.NatFromU128

open UintCodec (widthLoad)

/-- The existing source-model ownership theorem applies directly to the full
physical word-write evidence exported by the actual entry-to-RET proof. -/
theorem Post.result_owned {s t : ArmState} (post : Post s t)
    (result : SszNative.NatOperand) (success : (outcome s).result = .ok result) :
    result.At (widthLoad t) :=
  SszNative.NatArithmetic.fromWide_result_at (widthLoad t)
    (addressWord s).toNat (capacityWord s).toNat (usedWord s).toNat (wide s)
    result success post.written

/-- Both established source-model memory and value refinements hold at a
returned real machine state reached from the original caller-owned entry. -/
theorem correct_model (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base) (owned : Owned s) :
    ∃ fuel t, run fuel s = t ∧ Post s t ∧
      ∀ result, (outcome s).result = .ok result →
        result.At (widthLoad t) ∧ result.value = (wide s).toNat := by
  obtain ⟨fuel, t, runs, post⟩ := correct s base hc he ha hp owned
  exact ⟨fuel, t, runs, post,
    fun result success => ⟨post.result_owned result success, post.value result success⟩⟩

end SszArm.NatFromU128
