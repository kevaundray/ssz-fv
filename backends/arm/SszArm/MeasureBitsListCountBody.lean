import SszArm.MeasureBitsListAfterCount
import SszArm.MeasureBitsListCountSmall
import SszArm.MeasureBitsListCountFailure

namespace SszArm.Measure.Bits.List

open SszNative.Serialize (Packed)

theorem count_executes (schema : Schema) (s : ArmState) (args : Args) (bits : Packed)
    (base : BitVec 64) (owned : Owned s args schema.descriptor (.bits bits))
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (work : Work s args schema bits)
    (pc : read_pc s = base + BitVec.ofNat 64
      (if (bits.count >>> (64 : Nat)).setWidth 64 = 0#64
       then schema.kind.smallEntry else schema.kind.allocateEntry)) :
    ∃ fuel t, run fuel s = t ∧ Produced s t args schema.descriptor (.bits bits) base := by
  by_cases high : (bits.count >>> (64 : Nat)).setWidth 64 = 0#64
  · have entryPC : read_pc s = base + BitVec.ofNat 64 schema.kind.smallEntry := by
      simpa only [high, ↓reduceIte] using pc
    obtain ⟨u, firstRun, counted⟩ := count_small_executes schema s args bits base code error entryPC work high
    have uSP : r (.GPR 31#5) u = r (.GPR 31#5) s := counted.work.stack.trans work.stack.symm
    have uAligned : CheckSPAlignment u := by
      simpa only [CheckSPAlignment, state_simp_rules, uSP] using aligned
    obtain ⟨fuel, t, restRun, post⟩ := after_count_executes schema s u args bits (.small (bits.count.setWidth 64))
      base owned counted code error uAligned
    exact ⟨(ListEntry.smallOps schema.kind).length + fuel, t, by rw [run_plus, firstRun, restRun], post⟩
  · have entryPC : read_pc s = base + BitVec.ofNat 64 schema.kind.allocateEntry := by
      simpa only [high, ↓reduceIte] using pc
    cases first : (countCall s args bits).result with
    | error reason =>
      have scratch := Helpers.fromWide_failure_scratch (arenaOf s args) bits.count reason first
      subst reason
      exact count_failure_executes schema s args bits base owned code error aligned entryPC work high first
    | ok actual =>
      obtain ⟨firstFuel, u, firstRun, allocated⟩ := count_large_executes schema s args bits base owned
        code error aligned entryPC work high
      have counted := count_large_post work high allocated actual first
      have uSP : r (.GPR 31#5) u = r (.GPR 31#5) s := counted.work.stack.trans work.stack.symm
      have uAligned : CheckSPAlignment u := by
        simpa only [CheckSPAlignment, state_simp_rules, uSP] using aligned
      obtain ⟨fuel, t, restRun, post⟩ := after_count_executes schema s u args bits actual base owned counted
        code error uAligned
      exact ⟨firstFuel + fuel, t, by rw [run_plus, firstRun, restRun], post⟩

end SszArm.Measure.Bits.List
