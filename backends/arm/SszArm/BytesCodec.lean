import SszArm.MemcpyProofs
import SszArm.SszBridge
import SszBytes

namespace SszArm

/-- Equal addressed bytes give equal SSZ byte observations, without assuming
that the two buffers share an address or that addresses do not wrap. -/
theorem memoryBytes_congr (n : Nat) (a b : BitVec 64) (left right : Memory)
    (same : ∀ i < n, left (a + BitVec.ofNat 64 i) = right (b + BitVec.ofNat 64 i)) :
    memoryBytes n a left = memoryBytes n b right := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
    have first : left a = right b := by simpa using same 0 (by omega)
    simp only [memoryBytes, first]
    congr 1
    apply ih
    intro i hi
    have advance (p : BitVec 64) :
        p + 1#64 + BitVec.ofNat 64 i = p + BitVec.ofNat 64 (i + 1) := by bv_omega
    rw [advance a, advance b]
    exact same (i + 1) (by omega)

namespace Memcpy

/-- The full ISA execution copies the observed source bytes to the destination.
The existing non-wrapping and separation preconditions are unchanged. -/
theorem program_bytes (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base program) (hp : read_pc s = base) (he : read_err s = .None)
    (hdst : (r (.GPR 0) s).toNat + (r (.GPR 2) s).toNat ≤ 2 ^ 64)
    (hsrc : (r (.GPR 1) s).toNat + (r (.GPR 2) s).toNat ≤ 2 ^ 64)
    (hsep : Disjoint (r (.GPR 0) s) (r (.GPR 1) s) (r (.GPR 2) s).toNat) :
    memoryBytes (r (.GPR 2) s).toNat (r (.GPR 0) s)
      (run (fuel (r (.GPR 2) s).toNat) s).mem =
    memoryBytes (r (.GPR 2) s).toNat (r (.GPR 1) s) s.mem := by
  have hm := (program_correct s base hc hp he hdst hsrc hsep).2.2.2.2.2
  apply memoryBytes_congr
  intro i hi
  have address : (r (.GPR 0) s + BitVec.ofNat 64 i).toNat =
      (r (.GPR 0) s).toNat + i := by bv_omega
  rw [hm]
  simp only [image, address]
  rw [if_pos (by omega)]
  simp only [Nat.add_sub_cancel_left]

/-- A validated byte-vector/list payload is copied into caller-owned memory as
its upstream SSZ encoding, and that encoding decodes to the original value.
This theorem retains actual return, code, register and exact memory frames. It
covers the payload kernel, not native validation, dispatch, or decoder execution. -/
theorem program_ssz (s : ArmState) (base : BitVec 64) (desc : Ssz.Desc)
    (hc : CodeAt s base program) (hp : read_pc s = base) (he : read_err s = .None)
    (hdst : (r (.GPR 0) s).toNat + (r (.GPR 2) s).toNat ≤ 2 ^ 64)
    (hsrc : (r (.GPR 1) s).toNat + (r (.GPR 2) s).toNat ≤ 2 ^ 64)
    (hsep : Disjoint (r (.GPR 0) s) (r (.GPR 1) s) (r (.GPR 2) s).toNat)
    (hfits : Ssz.Value.fits desc
      (.bytes (memoryBytes (r (.GPR 2) s).toNat (r (.GPR 1) s) s.mem)) = true) :
    let n := (r (.GPR 2) s).toNat
    let final := run (fuel n) s
    read_err final = .None ∧ read_pc final = r (.GPR 30) s ∧
    r (.GPR 0) final = r (.GPR 0) s ∧ final.program = s.program ∧
    (∀ f, Preserved f → r f final = r f s) ∧
    (∀ a, final.mem a = image s.mem (r (.GPR 0) s) (r (.GPR 1) s) n a) ∧
    Ssz.serialize desc (.bytes (memoryBytes n (r (.GPR 1) s) s.mem)) =
      .ok (memoryBytes n (r (.GPR 0) s) final.mem) ∧
    Ssz.deserialize desc (memoryBytes n (r (.GPR 0) s) final.mem) =
      .ok (.bytes (memoryBytes n (r (.GPR 1) s) s.mem)) := by
  dsimp only
  obtain ⟨herr, hpc, hret, hprog, hframe, hmem⟩ :=
    program_correct s base hc hp he hdst hsrc hsep
  refine ⟨herr, hpc, hret, hprog, hframe, hmem, ?_⟩
  rw [program_bytes s base hc hp he hdst hsrc hsep]
  exact SszNative.bytes_codec desc _ hfits

end Memcpy
end SszArm
