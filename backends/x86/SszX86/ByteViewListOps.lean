import SszX86.ByteViewVector

namespace SszX86.ByteView.ListCompare
open Kraken.X64.Parser UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def listState (s : MachineData) (a c si x y : BitVec 64) (fl : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec a
      rcx := UInt64.ofBitVec c
      rsi := UInt64.ofBitVec si
      r8 := UInt64.ofBitVec x
      r9 := UInt64.ofBitVec y}
    status := fl}

def Frame (s t : MachineData) : Prop :=
  t.dmem = s.dmem ∧ t.zmms = s.zmms ∧
    ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 →
      t.regs.get64 r = s.regs.get64 r

theorem state_frame (s : MachineData) (a c si x y : BitVec 64) (fl : StatusFlags) :
    Frame s (listState s a c si x y fl) := by
  refine ⟨rfl, rfl, ?_⟩
  intro r h1 h2 h3 h4 h5
  cases r <;> simp_all [listState, Reg64s.get64]

@[simp] theorem register_zero : ({toBitVec := 0#64} : UInt64) = 0 := by
  apply UInt64.toBitVec_inj.1
  rfl

@[simp] theorem register_one : ({toBitVec := 1#64} : UInt64) = 1 := by
  apply UInt64.toBitVec_inj.1
  rfl

@[simp] theorem beq_zero_of_ne {w : Nat} (a : BitVec w) (h : a ≠ 0#w) :
    (a == 0#w) = false :=
  beq_eq_false_iff_ne.mpr h

@[simp] theorem low_byte_append (hi : BitVec 56) (lo : BitVec 8) :
    BitVec.setWidth 8 (hi ++ lo) = lo :=
  BitVec.setWidth_append_eq_right

@[simp] theorem cmp_beq (a b : BitVec 64) : (a - b == 0#64) = (a == b) := by
  have hz : a - b = 0#64 ↔ a = b := by
    constructor
    · intro h
      have he := congrArg (fun x : BitVec 64 => x + b) h
      simpa only [BitVec.sub_add_cancel, BitVec.zero_add] using he
    · rintro rfl
      exact BitVec.sub_self _
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, hz]

macro "view_list_step " k:num " using " hc:term : tactic => `(tactic|
  (apply step_cps
   have fetched := SszX86.ByteView.step_at _ _ $hc
     (SszX86.ByteView.program[$k]'(by decide)) (List.getElem_mem (by decide))
   simp only [SszX86.ByteView.program, List.getElem_cons_zero,
     List.getElem_cons_succ] at fetched
   apply (fetched _ _).mpr
   simp (config := {instances := true})
     [SszX86.ByteView.program, SszX86.ByteView.directives, SszX86.ByteView.labels,
      Directives.interp, Directive.interp, Instr.interp, Operation.interp,
      Operand.interp, RegOrMem.interp, Reg.interp, AddrExpr.interp, ConstExpr.interp,
      RelRegOrMem.interp, BitVec.toAddressSize, MachineData.set, MachineData.setReg,
      Reg64s.set, Reg64s.set64, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
      BitVec.drop, BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
      BitVec.extractLsb'_append_eq_right, BitVec.setWidth_append_eq_right,
      Effects.All, CondCode.interp,
      Int64.add_assoc, Width.bytes, Width.bits, listState]))

theorem scalar (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a c si x y : BitVec 64) (fl : StatusFlags)
    (P : MachineState → Prop)
    (hp : ∀ fl, Eventually (step e) P (listState s a c si x y fl,
      if s.regs.r14.toNat ≤ si.toNat then base + 2759 else base + 2591)) :
    Eventually (step e) P (listState s a c si x y fl, base + 2582) := by
  have target := hc.targets ("u2759", 2759) (by decide)
  view_list_step 116 using hc
  view_list_step 117 using hc
  rcases Nat.lt_trichotomy s.regs.r14.toNat si.toNat with h | h | h
  · have hn : s.regs.r14.toBitVec ≠ si := by
      intro he
      have hh : s.regs.r14.toNat = si.toNat := congrArg BitVec.toNat he
      omega
    simpa [target, StatusFlags.from_result, h, hn, Nat.le_of_lt h, listState, Effects.All]
      using hp _
  · have he : s.regs.r14.toBitVec = si := BitVec.eq_of_toNat_eq h
    simpa [target, StatusFlags.from_result, he, h, listState, Effects.All] using hp _
  · have hn : s.regs.r14.toBitVec ≠ si := by
      intro he
      have hh : s.regs.r14.toNat = si.toNat := congrArg BitVec.toNat he
      omega
    simpa [StatusFlags.from_result, Nat.not_lt_of_ge (Nat.le_of_lt h), Nat.not_le_of_gt h,
      hn, listState, Effects.All] using hp _

theorem small_finish (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a c si x y : BitVec 64) (fl : StatusFlags)
    (P : MachineState → Prop)
    (hp : ∀ si x y fl, Eventually (step e) P (listState s a c si x y fl,
      if s.regs.r14.toNat ≤ c.toNat then base + 2759 else base + 2591)) :
    Eventually (step e) P (listState s a c si x y fl, base + 2556) := by
  have target := hc.targets ("u2759", 2759) (by decide)
  view_list_step 109 using hc
  constructor <;> view_list_step 110 using hc
  all_goals view_list_step 111 using hc
  all_goals view_list_step 112 using hc
  all_goals view_list_step 113 using hc
  all_goals view_list_step 114 using hc
  all_goals constructor <;> view_list_step 115 using hc
  all_goals
    by_cases hz : s.regs.r14.toBitVec = 0#64
    · have hzero : s.regs.r14.toNat = 0 := by simpa using congrArg BitVec.toNat hz
      simpa [target, StatusFlags.from_result, hz, hzero, listState, Effects.All] using hp _ _ _ _
    · by_cases he : s.regs.r14.toBitVec = c
      · have heq : s.regs.r14.toNat = c.toNat := congrArg BitVec.toNat he
        simpa [target, StatusFlags.from_result, hz, he, heq, listState, Effects.All] using hp _ _ _ _
      · simp [StatusFlags.from_result, hz, he, Effects.All]
        apply scalar e base hc
        intro fl'
        simpa [listState] using hp c _ _ fl'

theorem small (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a c x y : BitVec 64) (fl : StatusFlags)
    (P : MachineState → Prop)
    (hp : ∀ si x y fl, Eventually (step e) P (listState s a c si x y fl,
      if s.regs.r14.toNat ≤ c.toNat then base + 2759 else base + 2591)) :
    Eventually (step e) P (listState s a c 0#64 x y fl, base + 2422) := by
  have target := hc.targets ("u2556", 2556) (by decide)
  have reject := hc.targets ("u2591", 2591) (by decide)
  view_list_step 74 using hc
  constructor <;> view_list_step 75 using hc
  all_goals view_list_step 76 using hc
  all_goals constructor <;> view_list_step 77 using hc
  all_goals view_list_step 78 using hc
  all_goals view_list_step 79 using hc
  all_goals constructor <;> view_list_step 80 using hc
  all_goals
    by_cases hz : s.regs.r14.toBitVec = 0#64
    · by_cases hc0 : c = 0#64
      · simp [target, StatusFlags.from_result, hz, hc0, Effects.All]
        apply small_finish e base hc s a 0#64
        simpa only [hc0] using hp
      · simp [StatusFlags.from_result, hz, hc0, Effects.All]
        view_list_step 81 using hc
        constructor <;> view_list_step 82 using hc
        all_goals constructor <;> view_list_step 83 using hc
        all_goals simp [StatusFlags.from_result, Effects.All]
        all_goals view_list_step 84 using hc
        all_goals
          have hzero : s.regs.r14.toNat = 0 := by simpa using congrArg BitVec.toNat hz
          simpa [listState, hzero] using hp 0#64 _ _ _
    · by_cases hc0 : c = 0#64
      · simp [StatusFlags.from_result, hz, hc0, Effects.All]
        view_list_step 81 using hc
        constructor <;> view_list_step 82 using hc
        all_goals constructor <;> view_list_step 83 using hc
        all_goals
          have hpos : 0 < s.regs.r14.toNat := by
            have hne : s.regs.r14.toNat ≠ 0 := by
              intro he
              exact hz (BitVec.eq_of_toNat_eq he)
            omega
          simpa [reject, StatusFlags.from_result, hc0, Nat.not_le_of_gt hpos,
            listState, Effects.All] using hp 1#64 _ _ _
      · simp [target, StatusFlags.from_result, hz, hc0, Effects.All]
        exact small_finish e base hc s a c _ _ _ _ P hp

end SszX86.ByteView.ListCompare
