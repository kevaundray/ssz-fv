import SszHashLayoutRefinementCore

set_option autoImplicit false

namespace SszNative.HashLayout

/-- Mathematical observation of an indexed leaf, used only in refinement. -/
def specLeaf (budget : Nat) (view : Ssz.MerkleLayout) (index : Nat) :
    Except Ssz.Err Ssz.Bytes :=
  match view.leaves with
  | .packed chunks => .ok (chunks[index]?.getD Ssz.zeroChunk)
  | .nested slots =>
      match slots[index]?.getD none with
      | none => .ok Ssz.zeroChunk
      | some (desc, value) => Ssz.hashTreeRootAt budget desc value

/-- This mathematical list exists only on the specification side. -/
def collect (leaf : Nat → Except Ssz.Err Ssz.Bytes) :
    Nat → Nat → Except Ssz.Err (List Ssz.Bytes)
  | 0, _ => .ok []
  | remaining + 1, index => do
      let first ← leaf index
      let rest ← collect leaf remaining (index + 1)
      return first :: rest

def streamSpec (leaf : Nat → Except Ssz.Err Ssz.Bytes) :
    Nat → Nat → Array Ssz.Bytes → Option NatOperand → Except Ssz.Err Ssz.Bytes
  | 0, _, chunks, limit => mathematicalRoot chunks limit
  | remaining + 1, index, chunks, limit => do
      let node ← leaf index
      streamSpec leaf remaining (index + 1) (chunks.push node) limit

/-- The generic generated traversal proof uses the accepted actual-state
invariants at each push. Its callback premise is instantiated by structural
recursive induction at the public endpoint, never assumed of that caller. -/
theorem stream_refines (leaf : Nat → Delimited.ArenaState → Outcome Ssz.Bytes)
    (expected : Nat → Except Ssz.Err Ssz.Bytes)
    (remaining index : Nat) (tree : TreeState) (chunks : Array Ssz.Bytes)
    (arena : Delimited.ArenaState) (valid : tree.Invariant chunks)
    (physical : chunks.size + remaining ≤ MerkleAccumulator.maxCount)
    (each : ∀ i cursor, Refines Eq (leaf i cursor) (expected i)) :
    Refines Eq (stream leaf remaining index tree arena)
      (streamSpec expected remaining index chunks tree.limit) := by
  induction remaining generalizing index tree chunks arena with
  | zero =>
      have refined := TreeState.finish_refines chunks tree valid
      change ResultRefines Eq tree.finish (mathematicalRoot chunks tree.limit)
      exact ResultRefines.of_erased_map tree.finish (mathematicalRoot chunks tree.limit) id
        (by simpa only [Except.map_id, id_eq] using refined)
  | succ remaining ih =>
      unfold stream streamSpec
      apply ResultRefines.bind Eq Eq _ _ _ _ (each index arena)
      intro node expectedNode same used
      subst expectedNode
      obtain ⟨next, pushed, invariant, limit⟩ := TreeState.push_invariant chunks tree node valid (by omega)
      simp only [lift, pushed, bind_ok]
      rw [← limit]
      apply ih (index + 1) next (chunks.push node) { arena with used := used } invariant
      simp only [Array.size_push]
      omega

 theorem streamSpec_collect (leaf : Nat → Except Ssz.Err Ssz.Bytes)
    (remaining index : Nat) (chunks : Array Ssz.Bytes) (limit : Option NatOperand) :
    streamSpec leaf remaining index chunks limit =
      (collect leaf remaining index >>= fun nodes => mathematicalRoot (chunks ++ nodes.toArray) limit) := by
  induction remaining generalizing index chunks with
  | zero => simp [streamSpec, collect]
  | succ remaining ih =>
      cases first : leaf index with
      | error reason => simp [streamSpec, collect, first]
      | ok node =>
          simp only [streamSpec, collect, first, ih]
          cases rest : collect leaf remaining (index + 1) with
          | error reason => rfl
          | ok nodes =>
              change mathematicalRoot (chunks.push node ++ nodes.toArray) limit =
                mathematicalRoot (chunks ++ (node :: nodes).toArray) limit
              apply congrArg (fun leaves => mathematicalRoot leaves limit)
              apply Array.ext'
              simp only [Array.toList_append, Array.toList_push]
              change (chunks.toList ++ [node]) ++ nodes = chunks.toList ++ (node :: nodes)
              exact List.append_assoc chunks.toList [node] nodes

 theorem collect_list {α : Type} (slots : List α) (index : Nat)
    (leaf : Nat → Except Ssz.Err Ssz.Bytes) (root : α → Except Ssz.Err Ssz.Bytes)
    (each : ∀ offset (inside : offset < slots.length),
      leaf (index + offset) = root (slots[offset]'inside)) :
    collect leaf slots.length index = slots.mapM root := by
  induction slots generalizing index with
  | nil => rfl
  | cons first rest ih =>
      have firstEq := each 0 (by simp)
      simp only [Nat.add_zero, List.getElem_cons_zero] at firstEq
      have tailEq : collect leaf rest.length (index + 1) = rest.mapM root := by
        apply ih
        intro offset inside
        have result := each (offset + 1) (by simpa using Nat.succ_lt_succ inside)
        simpa only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm 1 offset] using result
      simp only [List.length_cons, collect, firstEq, tailEq, List.mapM_cons]

 theorem collect_layout (budget : Nat) (view : Ssz.MerkleLayout) :
    (collect (specLeaf budget view) view.leaves.count 0).map List.toArray =
      Ssz.layoutChunksAt budget view := by
  cases view with
  | mk leaves limit mixin =>
      cases leaves with
      | packed chunks =>
          have collected := collect_list chunks.toList 0
            (specLeaf budget ⟨.packed chunks, limit, mixin⟩) (fun node => .ok node)
            (by
              intro offset inside
              have bound : offset < chunks.size := by simpa using inside
              simp only [specLeaf, Nat.zero_add, Array.getElem?_eq_getElem bound,
                Option.getD_some, Array.getElem_toList])
          have mapped : chunks.toList.mapM (fun node => Except.ok (ε := Ssz.Err) node) =
              .ok chunks.toList := by
            have identity := List.mapM_pure (m := Except Ssz.Err) (l := chunks.toList) (f := id)
            change chunks.toList.mapM (fun node => Except.ok (ε := Ssz.Err) node) =
              Except.ok (chunks.toList.map id) at identity
            rw [List.map_id] at identity
            exact identity
          rw [mapped] at collected
          simpa [Ssz.Leaves.count, Ssz.layoutChunksAt, Except.map] using
            congrArg (fun result => result.map List.toArray) collected
      | nested slots =>
          let root : Option (Ssz.Desc × Ssz.Value) → Except Ssz.Err Ssz.Bytes := fun slot =>
            match slot with
            | none => .ok Ssz.zeroChunk
            | some (desc, value) => Ssz.hashTreeRootAt budget desc value
          have collected := collect_list slots 0
            (specLeaf budget ⟨.nested slots, limit, mixin⟩) root
            (by
              intro offset inside
              simp only [specLeaf, Nat.zero_add, List.getElem?_eq_getElem inside,
                Option.getD_some, root])
          simp only [Ssz.Leaves.count, Ssz.layoutChunksAt, Option.getD_none,
            List.drop_zero, Nat.sub_zero, List.take_length, collected]
          change (slots.mapM root).map List.toArray =
            (slots.mapM root >>= fun chunks => .ok chunks.toArray)
          cases slots.mapM root <;> rfl

 theorem leafRoot_refines (actual : Layout) (expected : Ssz.MerkleLayout)
    (related : LayoutRefines actual expected) (budget index : Nat)
    (arena : Delimited.ArenaState)
    (visit : (desc : Codec.Desc) → (value : Codec.Value) →
      actual.nested index = some (desc, value) → Delimited.ArenaState → Outcome Ssz.Bytes)
    (children : ∀ desc value selected cursor,
      Refines Eq (visit desc value selected cursor)
        (Ssz.hashTreeRootAt budget desc.erase value.erase)) :
    Refines Eq (leafRoot actual index arena visit) (specLeaf budget expected index) := by
  have count := LayoutRefines.count actual expected related
  by_cases inside : index < actual.count
  · simp only [leafRoot, inside, ↓reduceIte]
    cases actual with
    | mk leaves limit mixin =>
      cases expected with
      | mk expectedLeaves expectedLimit expectedMixin =>
        cases related.1 with
        | packed view chunks counted each =>
            have within : index < view.count := inside
            have expectedInside : index < chunks.size := by omega
            simp only [each index within, lift, unchanged, specLeaf,
              Array.getElem?_eq_getElem expectedInside, Option.getD_some]
            exact .ok _ _ rfl
        | nested view slots counted each =>
            change Refines Eq
              (match selected : view.at index with
              | none => unchanged arena.used (.ok Ssz.zeroChunk)
              | some (desc, value) =>
                  visit desc value (by
                    change view.at index = some (desc, value)
                    exact selected) arena)
              (specLeaf budget ⟨.nested slots, expectedLimit, expectedMixin⟩ index)
            split
            · rename_i selected
              have absent : slots[index]?.getD none = none := by
                simpa only [selected, Option.map_none] using (each index).symm
              simp only [specLeaf, absent]
              exact .ok _ _ rfl
            · rename_i desc value selected
              have present : slots[index]?.getD none = some (desc.erase, value.erase) := by
                simpa only [selected, Option.map_some, erasePair] using (each index).symm
              simp only [specLeaf, present]
              exact children desc value _ arena
  · have outside : expected.leaves.count ≤ index := by omega
    simp only [leafRoot, inside, ↓reduceIte, unchanged]
    cases expected with
    | mk leaves limit mixin =>
      cases leaves with
      | packed chunks =>
          have past : chunks.size ≤ index := outside
          simp only [specLeaf, Array.getElem?_eq_none past, Option.getD_none]
          exact .ok _ _ rfl
      | nested slots =>
          have past : slots.length ≤ index := outside
          simp only [specLeaf, List.getElem?_eq_none past, Option.getD_none]
          exact .ok _ _ rfl

end SszNative.HashLayout
