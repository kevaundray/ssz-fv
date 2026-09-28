import SszArm.NatFromU128Reserve
import SszArm.NatFromU128BodyRun

namespace SszArm.NatFromU128

abbrev addressWord (s : ArmState) : BitVec 64 := read_mem_bytes 8 (r (.GPR 4#5) s) s
abbrev capacityWord (s : ArmState) : BitVec 64 := read_mem_bytes 8 (r (.GPR 4#5) s + 8#64) s
abbrev usedWord (s : ArmState) : BitVec 64 := read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) s

theorem GuardFrame.space {s t : ArmState} (frame : GuardFrame s t) (space : Space s) : Space t := by
  have out := frame.registers 0#5 (by decide)
  exact ⟨by simpa only [frame.sp] using space.stack,
    by simpa only [out] using space.output,
    by simpa only [out, frame.sp] using space.separate⟩

theorem Checkpoint.trans {s t u : ArmState} (st : Checkpoint s t)
    (tu : Checkpoint t u) : Checkpoint s u := by
  obtain ⟨n, hn⟩ := st.runs
  obtain ⟨m, hm⟩ := tu.runs
  refine ⟨⟨n + m, ?_⟩, st.frame.trans tu.frame, tu.memory.trans st.memory⟩
  rw [run_plus, hn, hm]

def Selected (s u : ArmState) : Body → Prop
  | .small => r (.GPR 3#5) s = 0#64
  | .failure => r (.GPR 3#5) s ≠ 0#64 ∧
      SszNative.Arena.reserve (addressWord s).toNat (capacityWord s).toNat (usedWord s).toNat 2 = none
  | .wide => r (.GPR 3#5) s ≠ 0#64 ∧
      SszNative.Arena.Checks (addressWord s).toNat (capacityWord s).toNat (usedWord s).toNat 2 ∧
      r (.GPR 9#5) u = addressWord s ∧
      (r (.GPR 10#5) u).toNat = SszNative.Arena.start (addressWord s).toNat (usedWord s).toNat ∧
      (r (.GPR 11#5) u).toNat = SszNative.Arena.finish (addressWord s).toNat (usedWord s).toNat 2

/-- Complete actual entry0 to a real RET. The selected body and every guard
condition are conclusions, not supplied by the caller. -/
theorem entry_runs (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base) (space : Space s) :
    ∃ fuel u body, run fuel s = body.final u ∧ Checkpoint s u ∧ Selected s u body := by
  let entered := Op.p0.effect base s
  have start : Checkpoint s entered := by
    refine ⟨⟨1, ?_⟩, ?_, ?_⟩
    · simpa only [run, Nat.reduceAdd] using step s base .p0 hc
        (by simpa [Op.row] using hp) he ha
    · constructor
      · exact Op.program _ _ _
      · exact Op.error _ _ _
      · intro reg keep; simp [entered, Op.effect, state_simp_rules]
      · intro reg; simp [entered, Op.effect, state_simp_rules]
    · simp [entered, Op.effect, ArmState.mem_w_eq_mem]
  have finish (u : ArmState) (body : Body) (reached : Checkpoint s u)
      (pc : read_pc u = base + BitVec.ofNat 64 body.entry)
      (selected : Selected s u body) :
      ∃ fuel u body, run fuel s = body.final u ∧ Checkpoint s u ∧ Selected s u body := by
    obtain ⟨fuel, runs⟩ := reached.runs
    refine ⟨fuel + body.ops.length, u, body, ?_, reached, selected⟩
    rw [run_plus, runs]
    exact body_run body u base (reached.frame.code base hc)
      (reached.frame.error.trans he) (reached.frame.aligned ha) pc (reached.frame.space space)
  by_cases small : r (.GPR 3#5) s = 0#64
  · apply finish entered .small start
    · simp [entered, Op.effect, state_simp_rules, small, Body.entry]
    · exact small
  · have pc : read_pc entered = base + 88#64 := by
      simp [entered, Op.effect, state_simp_rules, small]
    obtain ⟨_, u, _, checked, result⟩ := checks_runs entered base
      (addressWord s) (capacityWord s) (usedWord s)
      (start.frame.code base hc) (start.frame.error.trans he) (start.frame.aligned ha) pc
      (by simpa only [BitVec.add_zero] using start.header 0#64)
      (start.header 8#64) (start.header 16#64)
    have reached := start.trans checked
    rcases result with ⟨failed, exit⟩ | ⟨checks, exit, address, first, last⟩
    · exact finish u .failure reached exit ⟨small, failed⟩
    · exact finish u .wide reached exit ⟨small, checks, address, first, last⟩

end SszArm.NatFromU128
