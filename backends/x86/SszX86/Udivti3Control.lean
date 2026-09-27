import SszX86.Udivti3Loops

namespace SszX86.Udivti3

set_option maxRecDepth 32768
set_option maxHeartbeats 64000000

def numerator (s : MachineData) : Nat := value s.regs.rdi.toBitVec s.regs.rsi.toBitVec

def denominator (s : MachineData) : Nat := value s.regs.rdx.toBitVec s.regs.rcx.toBitVec

def wordStart (s : MachineData) (high : Bool) (status : StatusFlags) : MachineData :=
  { s with regs := { s.regs with
      rax := 0, r8 := 0, r11 := 64
      r9 := if high then 0 else s.regs.rsi
      rsi := if high then s.regs.rsi else s.regs.rdi
      r10 := if high then 1 else 0 }, status }

def wideStart (s : MachineData) (status : StatusFlags) : MachineData :=
  { s with regs := { s.regs with
      r9 := s.regs.rsi, r10 := 0, rax := 0, r11 := 64 }, status }

def secondStart (s : MachineData) (status : StatusFlags) : MachineData :=
  { s with regs := { s.regs with
      r8 := s.regs.rax, rsi := s.regs.rdi, rax := 0, r11 := 64, r10 := 0 }, status }

def zeroState (s : MachineData) (status : StatusFlags) : MachineData :=
  { s with regs := { s.regs with rax := 0, rdx := 0 }, status }

def oneState (s : MachineData) : MachineData :=
  { s with regs := { s.regs with rax := s.regs.rdi, rdx := s.regs.rsi } }

def wordExit (s : MachineData) (status : StatusFlags) : MachineData :=
  { s with regs := { s.regs with rdx := s.regs.r8 }, status }

def wideExit (s : MachineData) (status : StatusFlags) : MachineData :=
  { s with regs := { s.regs with rdx := 0 }, status }

/-- Bounded symbolic execution of acyclic control blocks. Undefined flags are
introduced universally (or split into both Boolean cases), never selected. -/
macro "udiv_control" : tactic => do
  let mut proof ← `(tactic| skip)
  for _ in [:24] do
    proof ← `(tactic| (
      $proof:tactic
      all_goals first
      | solve |
          (try simp only [wordStart, wideStart, secondStart, zeroState, oneState,
            wordExit, wideExit, numerator, denominator, value_lt_iff] at *) <;>
            udiv_finish
      | apply And.intro
      | intro af
      | split
      | udiv_step))
  return proof

theorem status_frame (s : MachineData) (status : StatusFlags) :
    Frame s { s with status } := by
  exact ⟨rfl, rfl, rfl, fun _ _ _ _ _ _ _ _ _ _ => rfl⟩

macro "udiv_frame" : tactic => `(tactic|
  (refine ⟨rfl, rfl, rfl, ?_⟩
   intro r h1 h2 h3 h4 h5 h6 h7 h8 h9
   cases r <;> simp_all [wordStart, wideStart, secondStart, zeroState,
     oneState, wordExit, wideExit, Reg64s.get64]))

theorem wordStart_frame (s : MachineData) (high : Bool) (status : StatusFlags) :
    Frame s (wordStart s high status) := by udiv_frame

theorem wideStart_frame (s : MachineData) (status : StatusFlags) :
    Frame s (wideStart s status) := by udiv_frame

theorem secondStart_frame (s : MachineData) (status : StatusFlags) :
    Frame s (secondStart s status) := by udiv_frame

theorem zeroState_frame (s : MachineData) (status : StatusFlags) :
    Frame s (zeroState s status) := by udiv_frame

theorem oneState_frame (s : MachineData) : Frame s (oneState s) := by udiv_frame

theorem wordExit_frame (s : MachineData) (status : StatusFlags) :
    Frame s (wordExit s status) := by udiv_frame

theorem wideExit_frame (s : MachineData) (status : StatusFlags) :
    Frame s (wideExit s status) := by udiv_frame

/-- The complete lexicographic numerator/divisor guard. -/
theorem entry_runs (base : Int64) (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ status, Eventually (step base) P
      ({ s with status }, if numerator s < denominator s then base + 192 else base + 20)) :
    Eventually (step base) P (s, base) := by
  by_cases hhi : s.regs.rsi.toBitVec.toNat < s.regs.rcx.toBitVec.toNat
  · udiv_control
  · by_cases heq : s.regs.rsi.toBitVec = s.regs.rcx.toBitVec
    · by_cases hlo : s.regs.rdi.toBitVec.toNat < s.regs.rdx.toBitVec.toNat <;> udiv_control
    · have hgt : s.regs.rcx.toBitVec.toNat < s.regs.rsi.toBitVec.toNat := by
        have hne : s.regs.rsi.toBitVec.toNat ≠ s.regs.rcx.toBitVec.toNat := by
          intro h
          exact heq (BitVec.eq_of_toNat_eq h)
        omega
      udiv_control

/-- TEST selects wide division; CMP selects the divisor-one fast path. -/
theorem dispatch_runs (base : Int64) (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ status, Eventually (step base) P ({ s with status },
      if s.regs.rcx.toBitVec ≠ 0 then base + 128
      else if s.regs.rdx.toBitVec = 1 then base + 185 else base + 35)) :
    Eventually (step base) P (s, base + 20) := by
  by_cases hw : s.regs.rcx.toBitVec = 0
  · by_cases ho : s.regs.rdx.toBitVec = 1 <;> udiv_control
  · udiv_control

theorem word_setup_runs (base : Int64) (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ status, Eventually (step base) P
      (wordStart s (decide (s.regs.rdx.toBitVec.toNat ≤ s.regs.rsi.toBitVec.toNat)) status,
        base + 71)) :
    Eventually (step base) P (s, base + 35) := by
  by_cases hh : s.regs.rdx.toBitVec.toNat ≤ s.regs.rsi.toBitVec.toNat
  · have hn : ¬ s.regs.rsi.toBitVec.toNat < s.regs.rdx.toBitVec.toNat := by omega
    udiv_control
  · have hl : s.regs.rsi.toBitVec.toNat < s.regs.rdx.toBitVec.toNat := by omega
    udiv_control

theorem wide_setup_runs (base : Int64) (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ status, Eventually (step base) P (wideStart s status, base + 142)) :
    Eventually (step base) P (s, base + 128) := by
  udiv_control

theorem second_runs (base : Int64) (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ status, Eventually (step base) P (secondStart s status, base + 71)) :
    Eventually (step base) P (s, base + 109) := by
  udiv_control

theorem word_exit_runs (base : Int64) (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ status, if s.regs.r10.toBitVec = 0 then
      Eventually (step base) P (wordExit s status, base + 108)
      else Eventually (step base) P ({ s with status }, base + 109)) :
    Eventually (step base) P (s, base + 100) := by
  by_cases hz : s.regs.r10.toBitVec = 0 <;> udiv_control

theorem wide_exit_runs (base : Int64) (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ status, Eventually (step base) P (wideExit s status, base + 184)) :
    Eventually (step base) P (s, base + 182) := by
  udiv_control

theorem zero_runs (base : Int64) (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ status, Eventually (step base) P (zeroState s status, base + 196)) :
    Eventually (step base) P (s, base + 192) := by
  udiv_control

theorem one_runs (base : Int64) (s : MachineData) (P : MachineState → Prop)
    (hp : Eventually (step base) P (oneState s, base + 191)) :
    Eventually (step base) P (s, base + 185) := by
  udiv_control

end SszX86.Udivti3
