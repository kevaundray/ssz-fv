import SszProofTraversalRange
import SszHashLayoutIndexedRefinement

set_option autoImplicit false

namespace SszNative.Proof

private theorem liftLayout_refines_range {α β : Type} (relation : α → β → Prop)
    (arena : Delimited.ArenaState) (actual : HashLayout.Outcome α)
    (expected : Except Ssz.Err β) (refined : HashLayout.Refines relation actual expected) :
    Refines relation (liftLayout arena actual) expected := by
  rcases actual with ⟨result, used, effects⟩
  cases refined with
  | exhausted expected => exact .exhausted _ (by trivial) expected
  | ok left right related => exact .ok left right related
  | error actual expected same => exact .error (.layout actual) expected same

private theorem merkle_refines_range {α : Type} (actual : Except MerkleAccumulator.Error α)
    (expected : Except Ssz.Err α)
    (same : MerkleAccumulator.eraseResult actual = .ok expected) :
    ResultRefines Eq (actual.mapError (fun reason => Error.layout (.merkle reason))) expected := by
  cases actual with
  | ok value =>
      have equal : Except.ok value = expected := Except.ok.inj same
      subst expected
      exact .ok value value rfl
  | error reason =>
      cases reason with
      | merkleizeLimit count capacity =>
          have equal : Except.error (Ssz.Err.merkleizeLimit count.value capacity.value) = expected :=
            Except.ok.inj same
          subst expected
          exact .error _ _ rfl
      | outputTooSmall => cases same

/-- Ordered collection of an actual half-open slice, including the first nested
child error. This is a specification identity, not an operational allocation. -/
theorem collect_layout_range (budget : Nat) (view : Ssz.MerkleLayout)
    (start stop : Nat) (ordered : start ≤ stop) (inside : stop ≤ view.leaves.count) :
    (HashLayout.collect (HashLayout.specLeaf budget view) (stop - start) start).map List.toArray =
      Ssz.layoutChunksAt budget view start (some stop) := by
  cases view with
  | mk leaves limit mixin =>
      cases leaves with
      | packed chunks =>
          let slots := (chunks.toList.drop start).take (stop - start)
          have length : slots.length = stop - start := by
            simp only [slots, List.length_take, List.length_drop, Array.length_toList]
            apply Nat.min_eq_left
            change stop ≤ chunks.size at inside
            omega
          have collected := HashLayout.collect_list slots start
            (HashLayout.specLeaf budget ⟨.packed chunks, limit, mixin⟩)
            (fun node => Except.ok (ε := Ssz.Err) node) (by
              intro offset within
              have bound : start + offset < chunks.size := by
                rw [length] at within
                change stop ≤ chunks.size at inside
                omega
              simp only [HashLayout.specLeaf, Array.getElem?_eq_getElem bound,
                Option.getD_some, slots, List.getElem_take, List.getElem_drop,
                Array.getElem_toList])
          rw [length] at collected
          have mapped : slots.mapM (fun node => Except.ok (ε := Ssz.Err) node) = .ok slots := by
            have identity := List.mapM_pure (m := Except Ssz.Err) (l := slots) (f := id)
            change slots.mapM (fun node => Except.ok (ε := Ssz.Err) node) =
              Except.ok (slots.map id) at identity
            simpa only [List.map_id] using identity
          rw [collected, mapped]
          simp only [Ssz.layoutChunksAt, Option.getD_some, Except.map, Pure.pure, Except.pure]
          change Except.ok slots.toArray = Except.ok (chunks.extract start stop)
          congr 1
          apply Array.ext'
          simp [slots, Array.toList_extract, List.extract_eq_take_drop]
      | nested values =>
          let slots := (values.drop start).take (stop - start)
          let root : Option (Ssz.Desc × Ssz.Value) → Except Ssz.Err Ssz.Bytes := fun slot =>
            match slot with
            | none => .ok Ssz.zeroChunk
            | some (desc, value) => Ssz.hashTreeRootAt budget desc value
          have length : slots.length = stop - start := by
            simp only [slots, List.length_take, List.length_drop]
            apply Nat.min_eq_left
            change stop ≤ values.length at inside
            omega
          have collected := HashLayout.collect_list slots start
            (HashLayout.specLeaf budget ⟨.nested values, limit, mixin⟩) root (by
              intro offset within
              have bound : start + offset < values.length := by
                rw [length] at within
                change stop ≤ values.length at inside
                omega
              simp only [HashLayout.specLeaf, List.getElem?_eq_getElem bound,
                Option.getD_some, slots, List.getElem_take, List.getElem_drop, root]
              cases values[start + offset] with
              | none => rfl
              | some pair => rcases pair with ⟨childDesc, childValue⟩; rfl)
          rw [length] at collected
          rw [collected]
          simp only [Ssz.layoutChunksAt, Option.getD_some, Pure.pure, Except.pure]
          change (slots.mapM root).map List.toArray =
            (slots.mapM root >>= fun chunks => .ok chunks.toArray)
          cases slots.mapM root <;> rfl

/-- Mathematical observation of range finishing at the requested logical depth. -/
def rangeSpec (leaf : Nat → Except Ssz.Err Ssz.Bytes) (depth : Nat) :
    Nat → Nat → Array Ssz.Bytes → Except Ssz.Err Ssz.Bytes
  | 0, _, chunks => Ssz.merkleizeBounded chunks (some (2 ^ depth))
  | remaining + 1, index, chunks => do
      let node ← leaf index
      rangeSpec leaf depth remaining (index + 1) (chunks.push node)

private theorem rangeSpec_collect (leaf : Nat → Except Ssz.Err Ssz.Bytes)
    (depth remaining index : Nat) (chunks : Array Ssz.Bytes) :
    rangeSpec leaf depth remaining index chunks =
      (HashLayout.collect leaf remaining index >>= fun nodes =>
        Ssz.merkleizeBounded (chunks ++ nodes.toArray) (some (2 ^ depth))) := by
  induction remaining generalizing index chunks with
  | zero => simp [rangeSpec, HashLayout.collect]
  | succ remaining ih =>
      cases first : leaf index with
      | error reason => simp [rangeSpec, HashLayout.collect, first]
      | ok node =>
          simp only [rangeSpec, HashLayout.collect, first, ih]
          cases rest : HashLayout.collect leaf remaining (index + 1) with
          | error reason => rfl
          | ok nodes =>
              change Ssz.merkleizeBounded (chunks.push node ++ nodes.toArray) (some (2 ^ depth)) =
                Ssz.merkleizeBounded (chunks ++ (node :: nodes).toArray) (some (2 ^ depth))
              congr 1
              apply Array.ext'
              simp only [Array.toList_append, Array.toList_push]
              change (chunks.toList ++ [node]) ++ nodes = chunks.toList ++ (node :: nodes)
              exact List.append_assoc chunks.toList [node] nodes

private theorem rangeLoop_refines (view : HashLayout.Layout)
    (leaf : Nat → Except Ssz.Err Ssz.Bytes) (depth remaining start : Nat)
    (tree : MerkleAccumulator.Accumulator Ssz.Bytes) (chunks : Array Ssz.Bytes)
    (arena : Delimited.ArenaState)
    (valid : MerkleAccumulator.Occupied Ssz.combine Ssz.zeroChunk chunks tree)
    (physical : chunks.size + remaining ≤ MerkleAccumulator.maxCount)
    (each : ∀ index cursor, HashLayout.Refines Eq (HashLayout.indexedRoot view index cursor)
      (leaf index)) :
    Refines Eq (rangeLoop view depth remaining start tree arena)
      (rangeSpec leaf depth remaining start chunks) := by
  have combineEq : rawCombine = Ssz.combine := funext fun left => funext fun right => rawCombine_eq left right
  induction remaining generalizing start tree chunks arena with
  | zero =>
      change ResultRefines Eq
        ((MerkleAccumulator.finishDepth rawCombine Ssz.zeroChunk tree depth).mapError
          (fun reason => Error.layout (.merkle reason)))
        (Ssz.merkleizeBounded chunks (some (2 ^ depth)))
      rw [combineEq]
      exact merkle_refines_range _ _ (MerkleAccumulator.finishDepth_refines chunks tree depth valid)
  | succ remaining ih =>
      simp only [rangeLoop, rangeSpec]
      apply ResultRefines.bind Eq Eq _ _ _ _ (liftLayout_refines_range Eq arena _ _ (each start arena))
      intro node expectedNode same used
      subst expectedNode
      have notFull : tree.count ≠ MerkleAccumulator.maxCount := by
        have counted := valid.1
        omega
      have pushed := MerkleAccumulator.push_occupied Ssz.combine Ssz.zeroChunk chunks tree node valid
      simp only [notFull, ↓reduceIte] at pushed
      simp only [combineEq, pushed.1, Except.mapError, bind_unchanged]
      apply ih (start + 1) _ (chunks.push node) { arena with used := used } pushed.2
      simp only [Array.size_push]
      omega

/-- Source-faithful half-open range refinement. The provenance is the completed
layout operation; no later child success or readable-root premise is required.
Logical depth is unrestricted, including an undersized merkleization error. -/
theorem rangeRoot_refines (desc : Codec.Desc) (value : Codec.Value)
    (layoutArena arena : Delimited.ArenaState) (view : HashLayout.Layout)
    (start stop depth budget : Nat)
    (safe : HashLayout.SafeWidths desc) (descPhysical : desc.Physical)
    (valuePhysical : value.Physical)
    (laidOut : (HashLayout.layout desc value layoutArena).result = .ok view)
    (enough : desc.nesting ≤ budget + 1) (ordered : start ≤ stop) (inside : stop ≤ view.count) :
    ∃ expected, Ssz.merkleLayout desc.erase value.erase = .ok expected ∧
      Refines Eq (rangeRoot view start stop depth arena)
        (Ssz.layoutChunksAt budget expected start (some stop) >>= fun chunks =>
          Ssz.merkleizeBounded chunks (some (2 ^ depth))) := by
  obtain ⟨expected, layoutEq, related⟩ := HashLayout.layout_success desc value layoutArena
    safe descPhysical valuePhysical view laidOut
  refine ⟨expected, layoutEq, ?_⟩
  have countBound := HashLayout.layout_count_physical desc value layoutArena view
    descPhysical valuePhysical laidOut
  have physical : (#[] : Array Ssz.Bytes).size + (stop - start) ≤ MerkleAccumulator.maxCount := by
    simp only [Array.size_empty, Nat.zero_add, MerkleAccumulator.maxCount, MerkleAccumulator.treeLevels]
    omega
  have each : ∀ index cursor, HashLayout.Refines Eq (HashLayout.indexedRoot view index cursor)
      (HashLayout.specLeaf budget expected index) := by
    intro index cursor
    obtain ⟨other, otherEq, refined⟩ := HashLayout.indexedRoot_refines desc value layoutArena cursor
      view index budget safe descPhysical valuePhysical laidOut enough
    rw [layoutEq] at otherEq
    cases Except.ok.inj otherEq
    exact refined
  have refined := rangeLoop_refines view (HashLayout.specLeaf budget expected) depth
    (stop - start) start (MerkleAccumulator.new Ssz.zeroChunk) #[] arena
    (MerkleAccumulator.new_occupied Ssz.combine Ssz.zeroChunk) physical each
  rw [rangeSpec_collect] at refined
  have collected := collect_layout_range budget expected start stop ordered (by
    rw [← HashLayout.LayoutRefines.count view expected related]
    exact inside)
  rw [← collected]
  cases roots : HashLayout.collect (HashLayout.specLeaf budget expected) (stop - start) start <;>
    simpa only [rangeRoot, roots, Except.map, Bind.bind, Except.bind, Array.empty_append] using refined

/-- The explicit-layout form avoids existential unpacking at traversal callers. -/
theorem rangeRoot_refines_layout (desc : Codec.Desc) (value : Codec.Value)
    (layoutArena arena : Delimited.ArenaState) (view : HashLayout.Layout)
    (expected : Ssz.MerkleLayout) (start stop depth budget : Nat)
    (safe : HashLayout.SafeWidths desc) (descPhysical : desc.Physical)
    (valuePhysical : value.Physical)
    (laidOut : (HashLayout.layout desc value layoutArena).result = .ok view)
    (layoutEq : Ssz.merkleLayout desc.erase value.erase = .ok expected)
    (enough : desc.nesting ≤ budget + 1) (ordered : start ≤ stop) (inside : stop ≤ view.count) :
    Refines Eq (rangeRoot view start stop depth arena)
      (Ssz.layoutChunksAt budget expected start (some stop) >>= fun chunks =>
        Ssz.merkleizeBounded chunks (some (2 ^ depth))) := by
  obtain ⟨other, otherEq, refined⟩ := rangeRoot_refines desc value layoutArena arena view
    start stop depth budget safe descPhysical valuePhysical laidOut enough ordered inside
  rw [layoutEq] at otherEq
  cases Except.ok.inj otherEq
  exact refined

end SszNative.Proof
