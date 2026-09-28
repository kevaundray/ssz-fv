import SszArm.MeasureScalarScan
import SszArm.MeasureResultProduced

namespace SszArm.Measure.Scalar.Bytes

open SszNative (NatOperand)
open SszNative.Serialize (Desc Value)

def Kind.desc (kind : Kind) (cap : NatOperand) : Desc :=
  match kind with
  | .vector => .byteVector cap
  | .list => .byteList cap

def Kind.entry : Kind → Nat
  | .vector => 1156 | .list => 776

def Kind.reject : Kind → Nat
  | .vector => 3752 | .list => 2392

def Kind.accepts (kind : Kind) (cap : NatOperand) (size : Nat) : Prop :=
  match kind with
  | .vector => cap.value = size
  | .list => size ≤ cap.value

instance (kind : Kind) (cap : NatOperand) (size : Nat) : Decidable (kind.accepts cap size) := by
  cases kind <;> unfold Kind.accepts <;> infer_instance

def Kind.failure (kind : Kind) (cap : NatOperand) (size : Nat) : SszNative.Serialize.Error :=
  match kind with
  | .vector => .scope cap (SszNative.Serialize.count size)
  | .list => .limit cap (SszNative.Serialize.count size)

theorem measure_bytes (kind : Kind) (cap : NatOperand) (bytes : Ssz.Bytes)
    (arena : SszNative.Delimited.ArenaState) (physical : bytes.size < 2^64) :
    SszNative.Serialize.measure (kind.desc cap) (.bytes bytes) arena =
      SszNative.Serialize.unchanged arena.used
        (if kind.accepts cap bytes.size then .ok (SszNative.Serialize.count bytes.size)
         else .error (kind.failure cap bytes.size)) := by
  have countValue : (SszNative.Serialize.count bytes.size).value = bytes.size := by
    simp [SszNative.Serialize.count, NatOperand.value, NatOperand.words, SszNative.Limbs.value,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt physical]
  by_cases accepts : kind.accepts cap bytes.size
  all_goals
    cases kind <;> simp only [Kind.accepts] at accepts <;>
      simp [Kind.desc, Kind.accepts, Kind.failure, SszNative.Serialize.measure,
        SszNative.Serialize.bounded, SszNative.Serialize.bind, SszNative.Serialize.unchanged,
        countValue, accepts]

theorem byte_calls (kind : Kind) (s : ArmState) (args : Args) (cap : NatOperand)
    (bytes : Ssz.Bytes) (physical : bytes.size < 2^64) :
    (outcome s args (kind.desc cap) (.bytes bytes)).calls = [] := by
  rw [outcome, measure_bytes kind cap bytes _ physical]
  rfl

theorem byte_used (kind : Kind) (s : ArmState) (args : Args) (cap : NatOperand)
    (bytes : Ssz.Bytes) (physical : bytes.size < 2^64) :
    (outcome s args (kind.desc cap) (.bytes bytes)).used = (arenaOf s args).used := by
  rw [outcome, measure_bytes kind cap bytes _ physical]
  rfl

/-- The inlined scan has classified the cap without replacing its representation. -/
def Ready (kind : Kind) (s : ArmState) (base : BitVec 64) (cap : NatOperand) (size : Nat) : Prop :=
  r (.GPR 20#5) s = BitVec.ofNat 64 size ∧
  if kind.accepts cap size then
    read_pc s = base + 4144#64 ∧ r (.GPR 21#5) s = 0#64
  else
    read_pc s = base + BitVec.ofNat 64 kind.reject ∧
      r (.GPR 8#5) s = cap.pointer ∧ r (.GPR 9#5) s = cap.payload

end SszArm.Measure.Scalar.Bytes
