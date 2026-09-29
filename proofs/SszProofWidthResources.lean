import SszProofWidths
import SszProofTraversalRange

set_option autoImplicit false

namespace SszNative.Proof

private theorem liftLayout_used_eq {α : Type} (arena : Delimited.ArenaState)
    (outcome : HashLayout.Outcome α) :
    (liftLayout arena outcome).used = outcome.used := rfl

/-- Both metadata conversions are real child traces; the actual conversion is
visited only after the expected conversion succeeds. -/
theorem countError_trace (reason : CountReason) (expected actual : Nat)
    (arena : Delimited.ArenaState) :
    TraversalTrace arena (countError reason expected actual arena).effects
      (countError reason expected actual arena).used := by
  unfold countError
  apply bind_traversalTrace
  · exact liftLayout_traversalTrace arena _ (HashLayout.fromWide_trace _ arena)
  · intro left used
    apply bind_traversalTrace
    · exact liftLayout_traversalTrace _ _ (HashLayout.fromWide_trace _ _)
    · intro right used'
      exact unchanged_traversalTrace _ _

/-- A failed first conversion retains its child event and cursor; the second
conversion is absent, not rolled back or speculatively executed. -/
theorem countError_expected_error (reason : CountReason) (expected actual : Nat)
    (arena : Delimited.ArenaState) (fault : Error)
    (failed : (liftLayout arena
      (HashLayout.fromWide (BitVec.ofNat 128 expected) arena)).result = .error fault) :
    countError reason expected actual arena =
      let first := liftLayout arena (HashLayout.fromWide (BitVec.ofNat 128 expected) arena)
      ⟨.error fault, first.used, first.effects⟩ := by
  simp only [countError, bind, failed]

/-- Failure while constructing actual metadata retains expected metadata and
both child events in source order. -/
theorem countError_actual_error (reason : CountReason) (expected actual : Nat)
    (arena : Delimited.ArenaState) (left : NatOperand) (fault : Error)
    (firstOK : (liftLayout arena
      (HashLayout.fromWide (BitVec.ofNat 128 expected) arena)).result = .ok left)
    (failed : (liftLayout
      { arena with used := (HashLayout.fromWide (BitVec.ofNat 128 expected) arena).used }
      (HashLayout.fromWide (BitVec.ofNat 128 actual)
        { arena with used := (HashLayout.fromWide (BitVec.ofNat 128 expected) arena).used })).result =
          .error fault) :
    countError reason expected actual arena =
      let first := liftLayout arena (HashLayout.fromWide (BitVec.ofNat 128 expected) arena)
      let nextArena := { arena with used := first.used }
      let second := liftLayout nextArena (HashLayout.fromWide (BitVec.ofNat 128 actual) nextArena)
      ⟨.error fault, second.used, first.effects ++ second.effects⟩ := by
  simp only [countError, bind, firstOK, liftLayout_used_eq, failed]

/-- Successful metadata construction still allocates if either conversion
requires wide storage; success here is not success of the enclosing operation. -/
theorem countError_metadata_success (reason : CountReason) (expected actual : Nat)
    (arena : Delimited.ArenaState) (left right : NatOperand)
    (firstOK : (liftLayout arena
      (HashLayout.fromWide (BitVec.ofNat 128 expected) arena)).result = .ok left)
    (secondOK : (liftLayout
      { arena with used := (HashLayout.fromWide (BitVec.ofNat 128 expected) arena).used }
      (HashLayout.fromWide (BitVec.ofNat 128 actual)
        { arena with used := (HashLayout.fromWide (BitVec.ofNat 128 expected) arena).used })).result =
          .ok right) :
    countError reason expected actual arena =
      let first := liftLayout arena (HashLayout.fromWide (BitVec.ofNat 128 expected) arena)
      let nextArena := { arena with used := first.used }
      let second := liftLayout nextArena (HashLayout.fromWide (BitVec.ofNat 128 actual) nextArena)
      ⟨.ok (.count reason left right), second.used, first.effects ++ second.effects⟩ := by
  simp only [countError, bind, firstOK, liftLayout_used_eq, secondOK, unchanged,
    List.append_nil]

/-- Raising the constructed error preserves all resource work, including any
failed metadata conversion. -/
theorem failCount_exact {α : Type} (reason : CountReason) (expected actual : Nat)
    (arena : Delimited.ArenaState) :
    failCount (α := α) reason expected actual arena =
      let metadata := countError reason expected actual arena
      ⟨(match metadata.result with | .error fault => .error fault | .ok fault => .error fault),
        metadata.used, metadata.effects⟩ := by
  cases result : (countError reason expected actual arena).result <;>
    simp only [failCount, bind, result, unchanged, List.append_nil]

theorem failCount_resources {α : Type} (reason : CountReason) (expected actual : Nat)
    (arena : Delimited.ArenaState) :
    (failCount (α := α) reason expected actual arena).used =
        (countError reason expected actual arena).used ∧
      (failCount (α := α) reason expected actual arena).effects =
        (countError reason expected actual arena).effects := by
  rw [failCount_exact]
  exact ⟨rfl, rfl⟩

theorem failCount_ne_ok {α : Type} (reason : CountReason) (expected actual : Nat)
    (arena : Delimited.ArenaState) (value : α) :
    (failCount reason expected actual arena).result ≠ .ok value := by
  rw [failCount_exact]
  change (match (countError reason expected actual arena).result with
    | .error fault => Except.error fault
    | .ok fault => Except.error fault) ≠ Except.ok value
  cases result : (countError reason expected actual arena).result <;>
    intro impossible <;> cases impossible

theorem failCount_trace {α : Type} (reason : CountReason) (expected actual : Nat)
    (arena : Delimited.ArenaState) :
    TraversalTrace arena (failCount (α := α) reason expected actual arena).effects
      (failCount (α := α) reason expected actual arena).used := by
  unfold failCount
  apply bind_traversalTrace _ _ _ (countError_trace reason expected actual arena)
  intro fault used
  exact unchanged_traversalTrace _ _

theorem checkChunk_wrong_width (node : Ssz.Bytes) (arena : Delimited.ArenaState)
    (width : node.size ≠ 32) :
    checkChunk node arena = failCount .count 32 node.size arena := by
  simp only [checkChunk, width, ↓reduceIte]

theorem checkChunk_trace (node : Ssz.Bytes) (arena : Delimited.ArenaState) :
    TraversalTrace arena (checkChunk node arena).effects (checkChunk node arena).used := by
  unfold checkChunk
  split
  · exact unchanged_traversalTrace _ _
  · exact failCount_trace _ _ _ _

theorem checkChunks_trace (nodes : List Ssz.Bytes) (arena : Delimited.ArenaState) :
    TraversalTrace arena (checkChunks nodes arena).effects (checkChunks nodes arena).used := by
  induction nodes generalizing arena with
  | nil => exact unchanged_traversalTrace _ _
  | cons node rest ih =>
      unfold checkChunks
      apply bind_traversalTrace _ _ _ (checkChunk_trace node arena)
      intro value used
      exact ih { arena with used := used }

/-- The first failing width stops the loop with that entire outcome. -/
theorem checkChunks_head_error (node : Ssz.Bytes) (rest : List Ssz.Bytes)
    (arena : Delimited.ArenaState) (fault : Error)
    (failed : (checkChunk node arena).result = .error fault) :
    checkChunks (node :: rest) arena =
      ⟨.error fault, (checkChunk node arena).used, (checkChunk node arena).effects⟩ := by
  simp only [checkChunks, bind, failed]

theorem checkChunks_head_width (node : Ssz.Bytes) (rest : List Ssz.Bytes)
    (arena : Delimited.ArenaState) (width : node.size = 32) :
    checkChunks (node :: rest) arena = checkChunks rest arena := by
  simp only [checkChunks, checkChunk_width node arena width, bind_unchanged]

theorem checkChunk_success_eq (node : Ssz.Bytes) (arena : Delimited.ArenaState)
    (success : (checkChunk node arena).result = .ok ()) :
    checkChunk node arena = unchanged arena.used (.ok ()) := by
  by_cases width : node.size = 32
  · exact checkChunk_width node arena width
  · rw [checkChunk_wrong_width node arena width] at success
    exact False.elim (failCount_ne_ok .count 32 node.size arena () success)

theorem checkChunks_success_eq (nodes : List Ssz.Bytes) (arena : Delimited.ArenaState)
    (success : (checkChunks nodes arena).result = .ok ()) :
    checkChunks nodes arena = unchanged arena.used (.ok ()) := by
  induction nodes generalizing arena with
  | nil => rfl
  | cons node rest ih =>
      unfold checkChunks at success ⊢
      cases first : (checkChunk node arena).result with
      | error fault =>
          simp only [bind, first] at success
          cases success
      | ok value =>
          cases value
          rw [checkChunk_success_eq node arena first, bind_unchanged] at success ⊢
          exact ih arena success

theorem calculateMerkleRoot_count_error (leaf : Ssz.Bytes) (proof : List Ssz.Bytes)
    (index : NatOperand) (arena : Delimited.ArenaState) (depth : Nat)
    (length : Indices.length index = .ok depth) (count : proof.length ≠ depth) :
    calculateMerkleRoot leaf proof index arena =
      failCount .branchLength depth proof.length arena := by
  simp only [calculateMerkleRoot, length]
  split
  · rfl
  · rename_i same
    exact False.elim (same (bne_iff_ne.mpr count))

theorem calculateMerkleRoot_empty (leaf : Ssz.Bytes) (index : NatOperand)
    (arena : Delimited.ArenaState) (length : Indices.length index = .ok 0) :
    calculateMerkleRoot leaf [] index arena = unchanged arena.used (.error .proofIncomplete) := by
  simp only [calculateMerkleRoot, length, List.length_nil,
    bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]

theorem calculateMerkleRoot_nonempty (leaf sibling : Ssz.Bytes) (rest : List Ssz.Bytes)
    (index : NatOperand) (arena : Delimited.ArenaState) (depth : Nat)
    (length : Indices.length index = .ok depth) (count : (sibling :: rest).length = depth) :
    calculateMerkleRoot leaf (sibling :: rest) index arena =
      unchanged arena.used (.ok (climb index 1
        (if Indices.bit index 0 then rawCombine sibling leaf else rawCombine leaf sibling) rest)) := by
  simp only [calculateMerkleRoot, length, count, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]

theorem calculateMerkleRoot_trace (leaf : Ssz.Bytes) (proof : List Ssz.Bytes)
    (index : NatOperand) (arena : Delimited.ArenaState) :
    TraversalTrace arena (calculateMerkleRoot leaf proof index arena).effects
      (calculateMerkleRoot leaf proof index arena).used := by
  unfold calculateMerkleRoot
  split
  · exact unchanged_traversalTrace _ _
  · split
    · exact failCount_trace _ _ _ _
    · split <;> exact unchanged_traversalTrace _ _

theorem verifyMerkleProof_trace (leaf : Ssz.Bytes) (proof : List Ssz.Bytes)
    (index : NatOperand) (root : Ssz.Bytes) (arena : Delimited.ArenaState) :
    TraversalTrace arena (verifyMerkleProof leaf proof index root arena).effects
      (verifyMerkleProof leaf proof index root arena).used := by
  unfold verifyMerkleProof
  apply bind_traversalTrace _ _ _ (checkChunk_trace leaf arena)
  intro leafOK used
  apply bind_traversalTrace _ _ _ (checkChunk_trace root _)
  intro rootOK used'
  apply bind_traversalTrace _ _ _ (checkChunks_trace proof _)
  intro proofOK used''
  apply bind_traversalTrace _ _ _ (calculateMerkleRoot_trace leaf proof index _)
  intro actual used'''
  exact unchanged_traversalTrace _ _

/-- A completed prefix of valid widths is allocation-free. The suffix is
visited at the original cursor, without assumptions about its future result. -/
theorem checkChunks_append_widths (prior suffix : List Ssz.Bytes)
    (arena : Delimited.ArenaState) (widths : ∀ node ∈ prior, node.size = 32) :
    checkChunks (prior ++ suffix) arena = checkChunks suffix arena := by
  induction prior with
  | nil => rfl
  | cons node rest ih =>
      rw [List.cons_append, checkChunks_head_width node (rest ++ suffix) arena
        (widths node (by simp))]
      exact ih (fun member inside => widths member (by simp [inside]))

theorem failCount_bind {α β : Type} (reason : CountReason) (expected actual : Nat)
    (arena : Delimited.ArenaState) (next : α → Nat → Outcome β) :
    bind (failCount reason expected actual arena) next =
      failCount reason expected actual arena := by
  cases result : (countError reason expected actual arena).result <;>
    simp only [failCount, bind, result, unchanged, List.append_nil]

theorem checkChunks_first_wrong_width (prior : List Ssz.Bytes) (node : Ssz.Bytes)
    (suffix : List Ssz.Bytes) (arena : Delimited.ArenaState)
    (widths : ∀ member ∈ prior, member.size = 32) (wrong : node.size ≠ 32) :
    checkChunks (prior ++ node :: suffix) arena = failCount .count 32 node.size arena := by
  rw [checkChunks_append_widths prior (node :: suffix) arena widths]
  simp only [checkChunks, checkChunk_wrong_width node arena wrong, failCount_bind]

theorem verifyMerkleProof_root_error (leaf : Ssz.Bytes) (proof : List Ssz.Bytes)
    (index : NatOperand) (root : Ssz.Bytes) (arena : Delimited.ArenaState) (fault : Error)
    (leafWidth : leaf.size = 32) (failed : (checkChunk root arena).result = .error fault) :
    verifyMerkleProof leaf proof index root arena =
      ⟨.error fault, (checkChunk root arena).used, (checkChunk root arena).effects⟩ := by
  unfold verifyMerkleProof
  rw [checkChunk_width leaf arena leafWidth, bind_unchanged]
  simp only [bind, failed]

theorem verifyMerkleProof_siblings_error (leaf : Ssz.Bytes) (proof : List Ssz.Bytes)
    (index : NatOperand) (root : Ssz.Bytes) (arena : Delimited.ArenaState) (fault : Error)
    (leafWidth : leaf.size = 32) (rootWidth : root.size = 32)
    (failed : (checkChunks proof arena).result = .error fault) :
    verifyMerkleProof leaf proof index root arena =
      ⟨.error fault, (checkChunks proof arena).used, (checkChunks proof arena).effects⟩ := by
  unfold verifyMerkleProof
  rw [checkChunk_width leaf arena leafWidth, bind_unchanged,
    checkChunk_width root arena rootWidth, bind_unchanged]
  simp only [bind, failed]

theorem verifyMerkleProof_reconstruction_error (leaf : Ssz.Bytes) (proof : List Ssz.Bytes)
    (index : NatOperand) (root : Ssz.Bytes) (arena : Delimited.ArenaState) (fault : Error)
    (leafWidth : leaf.size = 32) (rootWidth : root.size = 32)
    (widths : ∀ node ∈ proof, node.size = 32)
    (failed : (calculateMerkleRoot leaf proof index arena).result = .error fault) :
    verifyMerkleProof leaf proof index root arena =
      ⟨.error fault, (calculateMerkleRoot leaf proof index arena).used,
        (calculateMerkleRoot leaf proof index arena).effects⟩ := by
  rw [verifyMerkleProof_widths leaf proof index root arena leafWidth rootWidth widths]
  simp only [bind, failed]

theorem countError_cursorSafe (reason : CountReason) (expected actual : Nat)
    (arena : Delimited.ArenaState) :
    HashLayout.CursorSafe arena (countError reason expected actual arena).used :=
  (countError_trace reason expected actual arena).cursorSafe

theorem failCount_cursorSafe {α : Type} (reason : CountReason) (expected actual : Nat)
    (arena : Delimited.ArenaState) :
    HashLayout.CursorSafe arena (failCount (α := α) reason expected actual arena).used :=
  (failCount_trace (α := α) reason expected actual arena).cursorSafe

theorem checkChunk_cursorSafe (node : Ssz.Bytes) (arena : Delimited.ArenaState) :
    HashLayout.CursorSafe arena (checkChunk node arena).used :=
  (checkChunk_trace node arena).cursorSafe

theorem checkChunks_cursorSafe (nodes : List Ssz.Bytes) (arena : Delimited.ArenaState) :
    HashLayout.CursorSafe arena (checkChunks nodes arena).used :=
  (checkChunks_trace nodes arena).cursorSafe

theorem calculateMerkleRoot_cursorSafe (leaf : Ssz.Bytes) (proof : List Ssz.Bytes)
    (index : NatOperand) (arena : Delimited.ArenaState) :
    HashLayout.CursorSafe arena (calculateMerkleRoot leaf proof index arena).used :=
  (calculateMerkleRoot_trace leaf proof index arena).cursorSafe

theorem verifyMerkleProof_cursorSafe (leaf : Ssz.Bytes) (proof : List Ssz.Bytes)
    (index : NatOperand) (root : Ssz.Bytes) (arena : Delimited.ArenaState) :
    HashLayout.CursorSafe arena (verifyMerkleProof leaf proof index root arena).used :=
  (verifyMerkleProof_trace leaf proof index root arena).cursorSafe

private theorem unitBind_success {α : Type} (first : Outcome Unit)
    (next : Unit → Nat → Outcome α) (value : α)
    (success : (bind first next).result = .ok value) : first.result = .ok () := by
  cases result : first.result with
  | error fault => simp only [bind, result] at success; cases success
  | ok value => cases value; rfl

/-- Width checks and successful reconstruction consume no arena resources,
regardless of whether the final root comparison is true or false. -/
theorem verifyMerkleProof_success_resources (leaf : Ssz.Bytes) (proof : List Ssz.Bytes)
    (index : NatOperand) (root : Ssz.Bytes) (arena : Delimited.ArenaState) (answer : Bool)
    (success : (verifyMerkleProof leaf proof index root arena).result = .ok answer) :
    (verifyMerkleProof leaf proof index root arena).used = arena.used ∧
      (verifyMerkleProof leaf proof index root arena).effects = [] := by
  unfold verifyMerkleProof at success ⊢
  have leafOK := unitBind_success _ _ _ success
  rw [checkChunk_success_eq leaf arena leafOK, bind_unchanged] at success ⊢
  have rootOK := unitBind_success _ _ _ success
  rw [checkChunk_success_eq root arena rootOK, bind_unchanged] at success ⊢
  have proofOK := unitBind_success _ _ _ success
  rw [checkChunks_success_eq proof arena proofOK, bind_unchanged] at success ⊢
  cases result : (calculateMerkleRoot leaf proof index arena).result with
  | error fault => simp only [bind, result] at success; cases success
  | ok actual =>
      obtain ⟨used, effects⟩ := calculateMerkleRoot_success_resources leaf proof index arena actual result
      simp only [bind, result, unchanged, used, effects, List.nil_append, and_self]

end SszNative.Proof
