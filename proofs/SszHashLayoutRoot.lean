import SszHashLayoutGenerated
import SszHashLayoutStream

set_option autoImplicit false

namespace SszNative.HashLayout

open Codec (Desc Value)

abbrev Visit (input : Value) :=
  (child : Value) → child ∈ input.children → Desc → Delimited.ArenaState → Outcome Ssz.Bytes

def mixRoot (mixin : Option Ssz.Bytes) (root : Ssz.Bytes) : Ssz.Bytes :=
  match mixin with
  | none => root
  | some word => Ssz.combine root word

/-- Layout, indexed recursive leaves, actual accumulator transitions, final
capacity, and the mix-in occur in native order. No child serialization is built. -/
def rootStep (desc : Desc) (value : Value) (arena : Delimited.ArenaState)
    (visit : Visit value) : Outcome Ssz.Bytes :=
  let planned := layout desc value arena
  match success : planned.result with
  | .error reason => ⟨.error reason, planned.used, planned.effects⟩
  | .ok view =>
      let rooted := stream
        (fun index cursor => leafRoot view index cursor
          (fun childDesc child selected childArena =>
            visit child
              (Layout.Generated.at_child desc value view
                (layout_generated desc value arena view success)
                index childDesc child selected)
              childDesc childArena))
        view.count 0 (TreeState.new view.limit) { arena with used := planned.used }
      let mixed := bind rooted fun root used =>
        unchanged used (.ok (mixRoot view.mixin root))
      ⟨mixed.result, mixed.used, planned.effects ++ mixed.effects⟩

/-- Structural value descent supplies termination on every raw finite input.
There is no fuel, maximum nesting, or fallback host error in this executable. -/
def hashTreeRoot (desc : Desc) (value : Value) (arena : Delimited.ArenaState) :
    Outcome Ssz.Bytes :=
  rootStep desc value arena
    (fun child _ childDesc childArena => hashTreeRoot childDesc child childArena)
termination_by value.nesting
decreasing_by exact Value.child_nesting_lt _ _ (by assumption)

/-- Public indexed rooting of a borrowed view, including out-of-range zero roots. -/
def indexedRoot (view : Layout) (index : Nat) (arena : Delimited.ArenaState) :
    Outcome Ssz.Bytes :=
  leafRoot view index arena (fun desc value _ cursor => hashTreeRoot desc value cursor)

theorem hashTreeRoot_layout_error (desc : Desc) (value : Value)
    (arena : Delimited.ArenaState) (reason : Error)
    (failed : (layout desc value arena).result = .error reason) :
    hashTreeRoot desc value arena =
      ⟨.error reason, (layout desc value arena).used, (layout desc value arena).effects⟩ := by
  rw [hashTreeRoot]
  simp only [rootStep]
  split <;> simp_all

theorem indexedRoot_outside (view : Layout) (index : Nat) (arena : Delimited.ArenaState)
    (outside : view.count ≤ index) :
    indexedRoot view index arena = unchanged arena.used (.ok Ssz.zeroChunk) := by
  simp only [indexedRoot, leafRoot, Nat.not_lt.mpr outside, ↓reduceIte]

end SszNative.HashLayout
