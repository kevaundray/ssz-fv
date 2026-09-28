import SszArm.NatAddRightTrimState

namespace SszArm.NatAdd

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def borrowHead (right : Bool) : Nat := if right then 460 else 584

def borrowGuard (right : Bool) : List Op :=
  if right then [.p460, .p464] else [.p584, .p588]

def borrowKind (right : Bool) : LoadKind :=
  if right then .normalizeRight else .normalizeLeft

def borrowTail (right : Bool) : List Op :=
  if right then [.p448, .p452, .p456] else [.p624, .p628, .p632]

def borrowPointer (right : Bool) : BitVec 5 := if right then 3#5 else 1#5

def borrowExit (right : Bool) (count : Nat) : Nat :=
  if count = 0 then (if right then 704 else 792) else (if right then 472 else 636)

def borrowRoundState (s : ArmState) (base word : BitVec 64) (right : Bool) : ArmState :=
  block base (borrowTail right)
    (loadResult (block base (borrowGuard right) s) base (borrowKind right) word)

/-- The actual sentinel guard preserves both indexed-load operands. -/
theorem borrow_guard_inputs (s : ArmState) (base : BitVec 64) (right : Bool) :
    let u := block base (borrowGuard right) s
    r (.GPR (borrowKind right).ptr) u = r (.GPR (borrowPointer right)) s ∧
      r (.GPR (borrowKind right).index) u = r (.GPR 9#5) s := by
  cases right <;>
    simp [borrowGuard, borrowKind, borrowPointer, LoadKind.ptr, LoadKind.index,
      block, Op.effect, next, state_simp_rules]

/-- Opaque register observations of either original-representation rescan. -/
theorem borrow_round_fields (s : ArmState) (base word : BitVec 64)
    (right : Bool) (n : Nat) (count : r (.GPR 9#5) s = BitVec.ofNat 64 n) :
    let t := borrowRoundState s base word right
    r (.GPR 0#5) t = r (.GPR 0#5) s ∧
      r (.GPR 8#5) t = BitVec.ofNat 64 n ∧
      r (.GPR 9#5) t = BitVec.ofNat 64 n - 1#64 ∧
      read_pc t = base + BitVec.ofNat 64
        (if word = 0#64 then borrowHead right else borrowExit right (n + 1)) := by
  by_cases zero : word = 0#64 <;> cases right <;>
    simp [borrowRoundState, borrowTail, borrowGuard, borrowKind, borrowHead,
      borrowExit, loadResult, LoadKind.start, LoadKind.dst, LoadKind.tmp,
      block, Op.effect, put, next, NatCompare.saved, state_simp_rules, count, zero]

end SszArm.NatAdd
