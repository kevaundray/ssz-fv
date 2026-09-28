import SszArm.MeasureHelpersNative

namespace SszArm.Measure.Helpers

@[simp] theorem constructor_called_outcome (s : ArmState) (base : BitVec 64) :
    NatFromU128.outcome (called .constructWidth s base) = NatFromU128.outcome s := by
  simp [NatFromU128.outcome, NatFromU128.wide, NatFromU128.addressWord,
    NatFromU128.capacityWord, NatFromU128.usedWord, called, state_simp_rules]

@[simp] theorem constructor_called_writes (s : ArmState) (base : BitVec 64) :
    NatFromU128.writesFor (called .constructWidth s base) = NatFromU128.writesFor s := by
  simp only [NatFromU128.writesFor, constructor_called_outcome]
  simp [NatFromU128.successWrites, NatFromU128.localWrites, called, state_simp_rules]

end SszArm.Measure.Helpers
