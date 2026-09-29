import SszIndicesArithmetic

set_option autoImplicit false

namespace SszNative.Indices

/-- Equality of native naturals observes value, not representation or pointer. -/
def sameValue (left right : NatOperand) : Bool :=
  Limbs.nativeCmp left.words right.words == .eq

def rejectAncestors (indices : List NatOperand) (claim : NatOperand)
    (ancestors : List NatOperand) : Except Error Unit :=
  if ancestors.any (fun ancestor => indices.any (sameValue ancestor)) then
    .error (.nestedIndex claim)
  else .ok ()

def rejectClaimPaths (indices : List NatOperand) : List NatOperand → Except Error Unit
  | [] => .ok ()
  | claim :: rest => do
      let claimDepth ← length claim
      if indices.any (fun ancestor =>
          let ancestorDepth := depth ancestor
          ancestorDepth != 0 && ancestorDepth < claimDepth &&
            prefixEqual claim (claimDepth - ancestorDepth) false ancestor 0) then
        throw (.nestedIndex claim)
      rejectClaimPaths indices rest

/-- Request-ordered duplicate pass, completed before any claim validation. -/
def repeated : List NatOperand → List NatOperand → Bool
  | _, [] => false
  | earlier, index :: rest =>
      earlier.any (sameValue index) || repeated (index :: earlier) rest

def rejectRelated (indices : List NatOperand) : Except Error Unit := do
  if indices.isEmpty then throw .emptyRequest
  if repeated [] indices then throw .repeatedIndex
  rejectClaimPaths indices indices

/-- Candidate membership compares borrowed prefixes only, with no sibling or
path allocation. `claim` is the original request position. -/
def isHelper (indices : List NatOperand) (index : NatOperand) (claim level : Nat) : Bool :=
  let nodeDepth := depth index - level
  !(indices.zipIdx.any fun pair =>
    let other := pair.1
    let otherDepth := depth other
    otherDepth >= nodeDepth &&
      (prefixEqual index level true other (otherDepth - nodeDepth) ||
        (pair.2 < claim && prefixEqual index level false other (otherDepth - nodeDepth))))

/-- The first pass increments only retained frontier entries. It never builds
an intermediate path/candidate list. -/
def countLevels (keepCandidate : Nat → Bool) : Nat → Nat → Nat → Except Error Nat
  | 0, _, count => .ok count
  | remaining + 1, level, count => do
      let next ← if keepCandidate level then
        if count + 1 < 2^64 then .ok (count + 1) else .error scratch
        else .ok count
      countLevels keepCandidate remaining (level + 1) next

def countHelpers (indices : List NatOperand) : List NatOperand → Nat → Nat → Except Error Nat
  | [], _, count => .ok count
  | index :: rest, claim, count => do
      let next ← countLevels (isHelper indices index claim) (depth index) 0 count
      countHelpers indices rest (claim + 1) next

/-- collect_path_indices validates and sums in request order before reserving.
Consequently a checked count overflow can precede a later semantic refusal. -/
def countPaths : List NatOperand → Nat → Except Error Nat
  | [], count => .ok count
  | index :: rest, count => do
      let amount ← length index
      if amount >= 2^64 then throw scratch
      if count + amount >= 2^64 then throw scratch
      countPaths rest (count + amount)

/-- Sequential slot initialization after the complete outer reservation.
On failure, completed slots survive as events and nested arithmetic survives
in the child's exact outcome. No synthetic rollback is possible. -/
def fillLevels (reservation : Arena.Reservation) (keepCandidate : Nat → Bool)
    (make : Nat → Nat → Outcome NatOperand) :
    Nat → Nat → Nat → Nat → Outcome (List NatOperand × Nat)
  | 0, _, slot, used => unchanged used (.ok ([], slot))
  | remaining + 1, level, slot, used =>
      if keepCandidate level then
        bind (make level used) fun value cursor =>
          bind (⟨.ok (), cursor, [.initialized reservation.pointer slot value]⟩ : Outcome Unit)
            fun _ cursor =>
              bind (fillLevels reservation keepCandidate make remaining (level + 1) (slot + 1) cursor)
                fun result cursor => unchanged cursor (.ok (value :: result.1, result.2))
      else fillLevels reservation keepCandidate make remaining (level + 1) slot used

def fillClaims (indices : List NatOperand) (helpers : Bool)
    (reservation : Arena.Reservation) (base capacity : Nat) :
    List NatOperand → Nat → Nat → Nat → Outcome (List NatOperand × Nat)
  | [], _, slot, used => unchanged used (.ok ([], slot))
  | index :: rest, claim, slot, used =>
      let keepCandidate := if helpers then isHelper indices index claim else fun _ => true
      let make := if helpers then fun level cursor => shiftXor index level true base capacity cursor
        else fun level cursor => arithmetic cursor (NatShift.shr index level base capacity cursor)
      bind (fillLevels reservation keepCandidate make (depth index) 0 slot used) fun first cursor =>
        bind (fillClaims indices helpers reservation base capacity rest (claim + 1) first.2 cursor)
          fun second cursor => unchanged cursor (.ok (first.1 ++ second.1, second.2))

/-- Reservation attempts are explicit even on failure and for a zero count. -/
def reserveNats (count base capacity used : Nat) : Outcome Arena.Reservation :=
  let result := TypedArena.reserve natLayout base capacity used count
  match result with
  | none => ⟨.error scratch, used, [.reserve natLayout count used none]⟩
  | some reservation =>
      ⟨.ok reservation, reservation.used, [.reserve natLayout count used (some reservation)]⟩

def pathIndices (index : NatOperand) (base capacity used : Nat) : Outcome NatSlice :=
  bind (unchanged used (length index)) fun count cursor =>
    if count >= 2^64 then unchanged cursor (.error scratch)
    else bind (reserveNats count base capacity cursor) fun reservation cursor =>
      bind (fillLevels reservation (fun _ => true)
        (fun level used => arithmetic used (NatShift.shr index level base capacity used))
        count 0 0 cursor) fun result cursor =>
          unchanged cursor (.ok ⟨result.1, reservation⟩)

def branchIndices (index : NatOperand) (base capacity used : Nat) : Outcome NatSlice :=
  bind (unchanged used (length index)) fun count cursor =>
    if count >= 2^64 then unchanged cursor (.error scratch)
    else bind (reserveNats count base capacity cursor) fun reservation cursor =>
      bind (fillLevels reservation (fun _ => true)
        (fun level used => shiftXor index level true base capacity used)
        count 0 0 cursor) fun result cursor =>
          unchanged cursor (.ok ⟨result.1, reservation⟩)

def collectPathIndices (indices : List NatOperand) (base capacity used : Nat) : Outcome NatSlice :=
  bind (unchanged used (countPaths indices 0)) fun count cursor =>
    bind (reserveNats count base capacity cursor) fun reservation cursor =>
      bind (fillClaims indices false reservation base capacity indices 0 0 cursor)
        fun result cursor => unchanged cursor (.ok ⟨result.1, reservation⟩)

def helperIndices (indices : List NatOperand) (base capacity used : Nat) : Outcome NatSlice :=
  bind (unchanged used (rejectRelated indices)) fun _ cursor =>
    bind (unchanged cursor (countHelpers indices indices 0 0)) fun count cursor =>
      bind (reserveNats count base capacity cursor) fun reservation cursor =>
        bind (fillClaims indices true reservation base capacity indices 0 0 cursor)
          fun result cursor =>
            let sorted := result.1.mergeSort (fun left right => right.value ≤ left.value)
            ⟨.ok ⟨sorted, reservation⟩, cursor, [.sorted reservation.pointer sorted]⟩

end SszNative.Indices
