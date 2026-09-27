import SszX86.NatCompareScan

namespace SszX86.NatCompare
open SszNative.Limbs SszNative.NatABI

set_option maxRecDepth 16384
set_option maxHeartbeats 16000000

/-- The complete comparison body, from entry through a real return instruction.
The continuation contract observes only Ordering's low byte. -/
theorem words_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (xs ys : List (BitVec 64))
    (hx : View s.dmem s.regs.rdi.toBitVec s.regs.rsi.toBitVec xs)
    (hy : View s.dmem s.regs.rdx.toBitVec s.regs.rcx.toBitVec ys)
    (P : MachineState → Prop) (hp : Exits e base s P (nativeCmp xs ys)) :
    Eventually (step e) P (s, base) := by
  have hxs := sigWords_le_length xs
  have hys := sigWords_le_length ys
  have hxb := view_bound hx
  have hyb := view_bound hy
  have hxl : sigWords xs < 2^64 := by omega
  have hyl : sigWords ys < 2^64 := by omega
  apply trim_runs e base hc s xs ys hx hy P
  intro a flags
  apply lengths_runs e base hc
  · intro he a' fl
    have hn : sigWords xs = sigWords ys := by
      have hh := congrArg BitVec.toNat he
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hxl, Nat.mod_eq_of_lt hyl] using hh
    apply equal_scan e base hc s xs ys hx hy (sigWords xs) hxs (by omega) a' _ fl P
    simpa [nativeCmp, hn] using hp
  · intro he a' fl hv
    have hn : sigWords xs ≠ sigWords ys := by
      intro hh
      apply he
      rw [hh]
    have hcmp : compare (sigWords xs) (sigWords ys) ≠ .eq := by
      intro hh
      exact hn (Nat.compare_eq_eq.mp hh)
    have hnativ : nativeCmp xs ys = compare (sigWords xs) (sigWords ys) := by
      unfold nativeCmp
      cases h : compare (sigWords xs) (sigWords ys) <;> simp_all
    apply (hp a' s.regs.rdi.toBitVec (BitVec.ofNat 64 (sigWords xs))
      (BitVec.ofNat 64 (sigWords ys)) fl _).2
    simpa only [hnativ, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hxl,
      Nat.mod_eq_of_lt hyl] using hv

/-- Exact read-only frame, actual RET pop, and the observable low-byte result.
In particular RBX, RBP and R12–R15 (the complete SysV callee-saved set) are
preserved. No constraint is imposed on the high 56 bits of RAX. -/
def Returned (s : MachineData) (ra : BitVec 64) (ord : Ordering) (t : MachineState) : Prop :=
  t.2 = Int64.ofBitVec ra ∧
  t.1.regs.rax.toBitVec.setWidth 8 = orderingByte ord ∧
  t.1.dmem = s.dmem ∧ t.1.zmms = s.zmms ∧
  t.1.regs.rsp.toBitVec = s.regs.rsp.toBitVec + 8 ∧
  ∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .r8 → r ≠ .r9 → r ≠ .rsp →
    t.1.regs.get64 r = s.regs.get64 r

theorem returned_exits (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (ra : BitVec 64) (ord : Ordering)
    (hr : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))) :
    Exits e base s (Returned s ra ord) ord := by
  intro a d x y flags ha
  apply ret_runs e base hc (state s a d x y flags) ra _ hr
  refine ⟨rfl, ha, rfl, rfl, rfl, ?_⟩
  intro r h1 h2 h3 h4 h5
  cases r <;> simp_all [state, Reg64s.get64]

/-- Full linked Nat.compare correctness on arbitrary representable operands.
Both input arrays are borrowed and may overlap each other or RET's original
mapped slot. Empty and noncanonical Large values are admitted. There is no
allocator, arena, local stack frame, relocation premise or small-only case. -/
theorem program_correct (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (lhs rhs : Nat) (ra : BitVec 64)
    (hl : SszNative.NatMemory.Pair (UintCodec.widthLoad s.dmem)
      s.regs.rdi.toBitVec s.regs.rsi.toBitVec lhs)
    (hr : SszNative.NatMemory.Pair (UintCodec.widthLoad s.dmem)
      s.regs.rdx.toBitVec s.regs.rcx.toBitVec rhs)
    (hret : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))) :
    Eventually (step e) (Returned s ra (compare lhs rhs)) (s, base) := by
  obtain ⟨xs, hx, hvaluex⟩ := pair_view s.dmem _ _ lhs hl
  obtain ⟨ys, hy, hvaluey⟩ := pair_view s.dmem _ _ rhs hr
  apply words_runs e base hc s xs ys hx hy
  rw [nativeCmp_correct, hvaluex, hvaluey]
  exact returned_exits e base hc s ra (compare lhs rhs) hret

end SszX86.NatCompare
