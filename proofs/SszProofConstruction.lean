import SszProofTraversal
import SszIndicesFrontier

set_option autoImplicit false

namespace SszNative.Proof

/-- A completed hash slot is committed only after its helper read succeeds.
The reserved whole output and all earlier writes survive a later read error. -/
def fillHashRoots (desc : Codec.Desc) (value : Codec.Value)
    (reservation : Arena.Reservation) : List NatOperand → Nat → Delimited.ArenaState →
      Outcome (List Ssz.Bytes)
  | [], _, arena => unchanged arena.used (.ok [])
  | index :: rest, position, arena =>
      bind (nodeRoot desc value index arena) fun root used =>
        bind (⟨.ok (), used, [.initialized reservation.pointer position root]⟩ : Outcome Unit)
          fun _ used =>
            bind (fillHashRoots desc value reservation rest (position + 1)
              { arena with used := used }) fun roots used =>
                unchanged used (.ok (root :: roots))

/-- Full Hash-array reservation precedes every schema-aware helper read.
An empty helper frontier does not inspect either descriptor or value. -/
def reserveHashRoots (desc : Codec.Desc) (value : Codec.Value)
    (indices : List NatOperand) (arena : Delimited.ArenaState) : Outcome HashSlice :=
  match TypedArena.reserve hashLayout arena.base arena.capacity arena.used indices.length with
  | none => ⟨.error .scratchExhausted, arena.used,
      [.reserve hashLayout arena indices.length none]⟩
  | some reservation =>
      let filled := fillHashRoots desc value reservation indices 0
        { arena with used := reservation.used }
      ⟨filled.result.map (fun roots => ⟨roots, reservation⟩), filled.used,
        .reserve hashLayout arena indices.length (some reservation) :: filled.effects⟩

def buildProof (desc : Codec.Desc) (value : Codec.Value) (index : NatOperand)
    (arena : Delimited.ArenaState) : Outcome HashSlice :=
  bind (liftIndices arena (Indices.branchIndices index arena.base arena.capacity arena.used))
    fun branches used => reserveHashRoots desc value branches.values { arena with used := used }

def buildMultiproof (desc : Codec.Desc) (value : Codec.Value) (indices : List NatOperand)
    (arena : Delimited.ArenaState) : Outcome HashSlice :=
  bind (liftIndices arena (Indices.helperIndices indices arena.base arena.capacity arena.used))
    fun helpers used => reserveHashRoots desc value helpers.values { arena with used := used }

theorem reserveHashRoots_empty (desc : Codec.Desc) (value : Codec.Value)
    (arena : Delimited.ArenaState) :
    reserveHashRoots desc value [] arena =
      ⟨.ok ⟨[], ⟨1, arena.used⟩⟩, arena.used,
        [.reserve hashLayout arena 0 (some ⟨1, arena.used⟩)]⟩ := by
  simp only [reserveHashRoots, List.length_nil, TypedArena.reserve_zero,
    hashLayout, TypedArena.Layout.alignment, Nat.pow_zero, fillHashRoots,
    unchanged, Except.map]

theorem reserveHashRoots_reservation_error (desc : Codec.Desc) (value : Codec.Value)
    (indices : List NatOperand) (arena : Delimited.ArenaState)
    (failed : TypedArena.reserve hashLayout arena.base arena.capacity arena.used indices.length = none) :
    reserveHashRoots desc value indices arena =
      ⟨.error .scratchExhausted, arena.used, [.reserve hashLayout arena indices.length none]⟩ := by
  simp only [reserveHashRoots, failed]

theorem buildProof_indices_error (desc : Codec.Desc) (value : Codec.Value) (index : NatOperand)
    (arena : Delimited.ArenaState) (reason : Indices.Error)
    (failed : (Indices.branchIndices index arena.base arena.capacity arena.used).result = .error reason) :
    buildProof desc value index arena =
      let first := liftIndices arena (Indices.branchIndices index arena.base arena.capacity arena.used)
      ⟨.error (.indices reason), first.used, first.effects⟩ := by
  simp only [buildProof, bind, liftIndices, failed, Except.mapError]

theorem buildMultiproof_indices_error (desc : Codec.Desc) (value : Codec.Value)
    (indices : List NatOperand) (arena : Delimited.ArenaState) (reason : Indices.Error)
    (failed : (Indices.helperIndices indices arena.base arena.capacity arena.used).result = .error reason) :
    buildMultiproof desc value indices arena =
      let first := liftIndices arena (Indices.helperIndices indices arena.base arena.capacity arena.used)
      ⟨.error (.indices reason), first.used, first.effects⟩ := by
  simp only [buildMultiproof, bind, liftIndices, failed, Except.mapError]

/-- Initialized output cells only; child events contain their own nested writes. -/
def hashWrites : List Effect → List (Nat × Nat × Ssz.Bytes)
  | [] => []
  | .initialized pointer position bytes :: rest => (pointer, position, bytes) :: hashWrites rest
  | _ :: rest => hashWrites rest

theorem hashWrites_append (first second : List Effect) :
    hashWrites (first ++ second) = hashWrites first ++ hashWrites second := by
  induction first with
  | nil => rfl
  | cons effect rest ih => cases effect <;> simp only [List.cons_append, hashWrites, ih, List.cons_append]

end SszNative.Proof
