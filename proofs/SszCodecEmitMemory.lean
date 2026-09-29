import SszCodecEmit

set_option autoImplicit false

namespace SszNative.CodecEmit

open Codec (Desc Value)
open CodecMeasure (Plan Parts)

@[simp] theorem applyWrites_nil (before : Nat → Option UInt8) :
    applyWrites before [] = before := rfl

@[simp] theorem applyWrites_cons (before : Nat → Option UInt8)
    (write : Write) (rest : List Write) :
    applyWrites before (write :: rest) = applyWrites (applyWrite before write) rest := rfl

@[simp] theorem applyWrites_singleton (before : Nat → Option UInt8) (write : Write) :
    applyWrites before [write] = applyWrite before write := rfl

theorem applyWrites_append (before : Nat → Option UInt8) (first second : List Write) :
    applyWrites before (first ++ second) = applyWrites (applyWrites before first) second := by
  induction first generalizing before with
  | nil => rfl
  | cons write rest ih => exact ih (applyWrite before write)

theorem bind_writes_of_ok {α β : Type} (first : Emitted α) (next : α → Emitted β)
    (value : α) (success : first.result = .ok value) :
    (bind first next).writes = first.writes ++ (next value).writes := by
  simp only [bind, success]

theorem bind_writes_of_error {α β : Type} (first : Emitted α) (next : α → Emitted β)
    (reason : Fault) (failed : first.result = .error reason) :
    (bind first next).writes = first.writes := by
  simp only [bind, failed]

theorem applyWrite_inside (before : Nat → Option UInt8) (write : Write)
    (address : Nat) (lower : write.address ≤ address)
    (upper : address < write.address + write.bytes.size) :
    applyWrite before write address = some (write.bytes[address - write.address]'(by omega)) := by
  simp only [applyWrite, lower, upper, and_self, ↓reduceIte]
  exact Array.getElem?_eq_getElem (by omega)

theorem applyWrite_outside (before : Nat → Option UInt8) (write : Write)
    (address : Nat) (outside : address < write.address ∨ write.address + write.bytes.size ≤ address) :
    applyWrite before write address = before address := by
  have absent : ¬ (write.address ≤ address ∧ address < write.address + write.bytes.size) := by
    omega
  simp only [applyWrite, absent, ↓reduceIte]

@[simp] theorem applyWrite_empty (before : Nat → Option UInt8) (address : Nat) :
    applyWrite before ⟨address, #[]⟩ = before := by
  funext index
  apply applyWrite_outside
  simp only [Array.size_empty]
  omega

/-- A copy never uses the old value at a cell it covers. -/
theorem applyWrite_no_output_reads (before after : Nat → Option UInt8) (write : Write)
    (address : Nat) (lower : write.address ≤ address)
    (upper : address < write.address + write.bytes.size) :
    applyWrite before write address = applyWrite after write address := by
  rw [applyWrite_inside before write address lower upper,
    applyWrite_inside after write address lower upper]

/-- At each address a trace either preserves that one old cell, or supplies a
fixed byte independent of every old output cell. -/
theorem applyWrites_cell (writes : List Write) (address : Nat) :
    (∀ before, applyWrites before writes address = before address) ∨
      ∃ byte, ∀ before, applyWrites before writes address = some byte := by
  induction writes with
  | nil => exact Or.inl (fun _ => rfl)
  | cons write rest ih =>
      rcases ih with unchanged | ⟨byte, initialized⟩
      · by_cases inside : write.address ≤ address ∧ address < write.address + write.bytes.size
        · refine Or.inr ⟨write.bytes[address - write.address]'(by omega), ?_⟩
          intro before
          rw [applyWrites_cons, unchanged]
          exact applyWrite_inside before write address inside.1 inside.2
        · apply Or.inl
          intro before
          rw [applyWrites_cons, unchanged]
          apply applyWrite_outside
          omega
      · exact Or.inr ⟨byte, fun before => initialized (applyWrite before write)⟩

theorem applyWrites_uninitialized (writes : List Write) (address : Nat)
    (blank : applyWrites (fun _ => none) writes address = none)
    (before : Nat → Option UInt8) :
    applyWrites before writes address = before address := by
  rcases applyWrites_cell writes address with unchanged | ⟨byte, initialized⟩
  · exact unchanged before
  · have impossible := initialized (fun _ => none)
    rw [blank] at impossible
    cases impossible

theorem applyWrites_initialized (writes : List Write) (address : Nat) (byte : UInt8)
    (blank : applyWrites (fun _ => none) writes address = some byte)
    (before : Nat → Option UInt8) :
    applyWrites before writes address = some byte := by
  rcases applyWrites_cell writes address with unchanged | ⟨written, initialized⟩
  · have impossible := unchanged (fun _ => none)
    rw [blank] at impossible
    cases impossible
  · rw [initialized before, ← initialized (fun _ => none), blank]

/-- Reads at other output addresses cannot influence the result at this address. -/
theorem applyWrites_pointwise (before after : Nat → Option UInt8) (writes : List Write)
    (address : Nat) (same : before address = after address) :
    applyWrites before writes address = applyWrites after writes address := by
  rcases applyWrites_cell writes address with unchanged | ⟨byte, initialized⟩
  · rw [unchanged before, unchanged after, same]
  · rw [initialized before, initialized after]

/-- Disjoint addressed copies commute, including empty payloads. -/
theorem applyWrite_commute (before : Nat → Option UInt8) (first second : Write)
    (apart : first.address + first.bytes.size ≤ second.address ∨
      second.address + second.bytes.size ≤ first.address) :
    applyWrite (applyWrite before first) second = applyWrite (applyWrite before second) first := by
  funext address
  by_cases left : first.address ≤ address ∧ address < first.address + first.bytes.size
  · have right : ¬ (second.address ≤ address ∧ address < second.address + second.bytes.size) := by
      omega
    simp only [applyWrite, left, right, ↓reduceIte]
  · simp only [applyWrite, left, ↓reduceIte]

/-- Adjacent contiguous copies are exactly one array-concatenation copy. -/
theorem applyWrite_append (before : Nat → Option UInt8) (address : Nat)
    (front back : Ssz.Bytes) :
    applyWrite (applyWrite before ⟨address, front⟩) ⟨address + front.size, back⟩ =
      applyWrite before ⟨address, front ++ back⟩ := by
  funext index
  by_cases lower : index < address
  · rw [applyWrite_outside _ _ _ (Or.inl (show index < address + front.size by omega)),
      applyWrite_outside _ _ _ (Or.inl lower),
      applyWrite_outside _ _ _ (Or.inl lower)]
  · have start : address ≤ index := by omega
    by_cases inFront : index < address + front.size
    · have inAll : index < address + (front ++ back).size := by
        simp only [Array.size_append]
        omega
      rw [applyWrite_outside _ _ _ (Or.inl inFront),
        applyWrite_inside _ _ _ start inFront, applyWrite_inside _ _ _ start inAll]
      have frontIndex : index - address < front.size := by omega
      simp [frontIndex]
    · have backStart : address + front.size ≤ index := by omega
      by_cases inBack : index < address + front.size + back.size
      · have inAll : index < address + (front ++ back).size := by
          simp only [Array.size_append]
          omega
        rw [applyWrite_inside _ _ _ backStart inBack,
          applyWrite_inside _ _ _ start inAll]
        have afterFront : ¬ index - address < front.size := by omega
        simp [Array.getElem_append, afterFront, Nat.sub_sub]
      · have afterAll : address + (front ++ back).size ≤ index := by
          simp only [Array.size_append]
          omega
        rw [applyWrite_outside _ _ _
            (Or.inr (show address + front.size + back.size ≤ index by omega)),
          applyWrite_outside _ _ _ (Or.inr backStart),
          applyWrite_outside _ _ _ (Or.inr afterAll)]

theorem Encodes.singleton (address : Nat) (bytes : Ssz.Bytes) :
    Encodes [⟨address, bytes⟩] address bytes := fun _ => rfl

@[simp] theorem Encodes.empty (address : Nat) : Encodes [] address #[] := by
  intro before
  simp only [applyWrites_nil, applyWrite_empty]

theorem copy_encodes (out : Slice) (bytes : Ssz.Bytes) (fits : bytes.size ≤ out.length) :
    Encodes (copy out bytes).writes out.address bytes := by
  simpa only [copy, fits, ↓reduceIte] using Encodes.singleton out.address bytes

theorem Encodes.initialized {writes : List Write} {address : Nat} {bytes : Ssz.Bytes}
    (encoded : Encodes writes address bytes) (before : Nat → Option UInt8)
    (index : Nat) (inside : index < bytes.size) :
    applyWrites before writes (address + index) = some bytes[index] := by
  rw [encoded before, applyWrite_inside _ _ _
    (show address ≤ address + index by omega)
    (show address + index < address + bytes.size by omega)]
  simp only [Nat.add_sub_cancel_left]

theorem Encodes.frame {writes : List Write} {address : Nat} {bytes : Ssz.Bytes}
    (encoded : Encodes writes address bytes) (before : Nat → Option UInt8)
    (index : Nat) (outside : index < address ∨ address + bytes.size ≤ index) :
    applyWrites before writes index = before index := by
  rw [encoded before]
  exact applyWrite_outside before _ index outside

theorem Encodes.no_output_reads {writes : List Write} {address : Nat} {bytes : Ssz.Bytes}
    (encoded : Encodes writes address bytes) (before after : Nat → Option UInt8)
    (index : Nat) (inside : index < bytes.size) :
    applyWrites before writes (address + index) = applyWrites after writes (address + index) := by
  rw [encoded.initialized before index inside, encoded.initialized after index inside]

/-- Exact initialized prefix and exterior framing characterize the memory contract. -/
theorem encodes_iff (writes : List Write) (address : Nat) (bytes : Ssz.Bytes) :
    Encodes writes address bytes ↔
      (∀ before index, (inside : index < bytes.size) →
        applyWrites before writes (address + index) = some bytes[index]) ∧
      (∀ before index, index < address ∨ address + bytes.size ≤ index →
        applyWrites before writes index = before index) := by
  constructor
  · intro encoded
    exact ⟨encoded.initialized, encoded.frame⟩
  · rintro ⟨initialized, frame⟩ before
    funext index
    by_cases inside : address ≤ index ∧ index < address + bytes.size
    · have bound : index - address < bytes.size := by omega
      have atIndex := initialized before (index - address) bound
      rw [show address + (index - address) = index by omega] at atIndex
      rw [atIndex, applyWrite_inside _ _ _ inside.1 inside.2]
    · have outside : index < address ∨ address + bytes.size ≤ index := by omega
      rw [frame before index outside, applyWrite_outside _ _ _ outside]

/-- Empty execution encodes exactly the empty byte array. -/
@[simp] theorem Encodes.empty_iff (address : Nat) (bytes : Ssz.Bytes) :
    Encodes [] address bytes ↔ bytes = #[] := by
  constructor
  · intro encoded
    have zero : bytes.size = 0 := by
      by_cases zero : bytes.size = 0
      · exact zero
      · have inside : 0 < bytes.size := by omega
        have impossible := encoded.initialized (fun _ => none) 0 inside
        change none = some bytes[0] at impossible
        cases impossible
    apply Array.ext
    · simpa only [Array.size_empty] using zero
    · intro index inside _
      omega
  · rintro rfl
    exact Encodes.empty address

theorem Encodes.append {first second : List Write} {address : Nat} {front back : Ssz.Bytes}
    (frontEncoded : Encodes first address front)
    (backEncoded : Encodes second (address + front.size) back) :
    Encodes (first ++ second) address (front ++ back) := by
  intro before
  rw [applyWrites_append, backEncoded, frontEncoded, applyWrite_append]

theorem Encodes.append_commute {first second : List Write} {left right : Nat}
    {front back : Ssz.Bytes} (frontEncoded : Encodes first left front)
    (backEncoded : Encodes second right back)
    (apart : left + front.size ≤ right ∨ right + back.size ≤ left)
    (before : Nat → Option UInt8) :
    applyWrites before (first ++ second) = applyWrites before (second ++ first) := by
  rw [applyWrites_append, applyWrites_append, backEncoded, frontEncoded,
    frontEncoded, backEncoded]
  exact applyWrite_commute before _ _ apart

/-- A table writes a growing header and a separately positioned body. -/
def EncodesParts (writes : List Write) (head body : Nat) (front back : Ssz.Bytes) : Prop :=
  ∀ before, applyWrites before writes =
    applyWrite (applyWrite before ⟨head, front⟩) ⟨body, back⟩

@[simp] theorem EncodesParts.empty (head body : Nat) :
    EncodesParts [] head body #[] #[] := by
  intro before
  simp only [applyWrites_nil, applyWrite_empty]

theorem EncodesParts.of_encodes_front {writes : List Write} {head : Nat}
    {front : Ssz.Bytes} (encoded : Encodes writes head front) (body : Nat) :
    EncodesParts writes head body front #[] := by
  intro before
  rw [encoded before, applyWrite_empty]

theorem EncodesParts.of_encodes_back {writes : List Write} {body : Nat}
    {back : Ssz.Bytes} (encoded : Encodes writes body back) (head : Nat) :
    EncodesParts writes head body #[] back := by
  intro before
  rw [encoded before, applyWrite_empty]

theorem EncodesParts.of_append {first second : List Write} {head body : Nat}
    {front back : Ssz.Bytes} (frontEncoded : Encodes first head front)
    (backEncoded : Encodes second body back) :
    EncodesParts (first ++ second) head body front back := by
  intro before
  rw [applyWrites_append, backEncoded, frontEncoded]

/-- Inline fields extend only the header region. -/
theorem EncodesParts.inline {first rest : List Write} {head body : Nat}
    {bytes front back : Ssz.Bytes} (firstEncoded : Encodes first head bytes)
    (restEncoded : EncodesParts rest (head + bytes.size) body front back) :
    EncodesParts (first ++ rest) head body (bytes ++ front) back := by
  intro before
  rw [applyWrites_append, restEncoded, firstEncoded, applyWrite_append]

/-- An offset precedes its body in the trace; the remaining header is disjoint
from that body and therefore can be regrouped with the offset copy. -/
theorem EncodesParts.variable {first child rest : List Write} {head body : Nat}
    {offset bytes front back : Ssz.Bytes} (firstEncoded : Encodes first head offset)
    (childEncoded : Encodes child body bytes)
    (restEncoded : EncodesParts rest (head + offset.size) (body + bytes.size) front back)
    (separated : head + offset.size + front.size ≤ body) :
    EncodesParts (first ++ child ++ rest) head body (offset ++ front) (bytes ++ back) := by
  intro before
  simp only [applyWrites_append]
  rw [restEncoded, childEncoded, firstEncoded,
    applyWrite_commute (applyWrite before ⟨head, offset⟩)
    ⟨body, bytes⟩ ⟨head + offset.size, front⟩ (Or.inr separated),
    applyWrite_append, applyWrite_append]

theorem EncodesParts.contiguous {writes : List Write} {head body : Nat}
    {front back : Ssz.Bytes} (encoded : EncodesParts writes head body front back)
    (adjacent : head + front.size = body) :
    Encodes writes head (front ++ back) := by
  intro before
  rw [encoded before, ← adjacent, applyWrite_append]

/-- Geometric containment is required even for an empty copy's address. -/
def WriteWithin (out : Slice) (write : Write) : Prop :=
  out.address ≤ write.address ∧ write.address + write.bytes.size ≤ out.address + out.length

def WritesWithin (out : Slice) (writes : List Write) : Prop :=
  ∀ write, write ∈ writes → WriteWithin out write

def SliceWithin (inner outer : Slice) : Prop :=
  outer.address ≤ inner.address ∧ inner.address + inner.length ≤ outer.address + outer.length

@[simp] theorem writesWithin_nil (out : Slice) : WritesWithin out [] := by
  intro write member
  cases member

theorem writesWithin_append (out : Slice) (first second : List Write) :
    WritesWithin out (first ++ second) ↔ WritesWithin out first ∧ WritesWithin out second := by
  simp only [WritesWithin, List.mem_append, or_imp, forall_and]

theorem WritesWithin.mono {inner outer : Slice} {writes : List Write}
    (contained : SliceWithin inner outer) (bounded : WritesWithin inner writes) :
    WritesWithin outer writes := by
  intro write member
  have bound := bounded write member
  unfold SliceWithin at contained
  unfold WriteWithin at bound ⊢
  omega

theorem WritesWithin.frame {out : Slice} {writes : List Write}
    (bounded : WritesWithin out writes) (before : Nat → Option UInt8) (address : Nat)
    (outside : address < out.address ∨ out.address + out.length ≤ address) :
    applyWrites before writes address = before address := by
  induction writes generalizing before with
  | nil => rfl
  | cons write rest ih =>
      have first := bounded write (by simp)
      have remaining : WritesWithin out rest := by
        intro next member
        exact bounded next (List.mem_cons_of_mem _ member)
      rw [applyWrites_cons, ih remaining]
      apply applyWrite_outside
      unfold WriteWithin at first
      omega

theorem pure_writesWithin {α : Type} (out : Slice) (value : α) :
    WritesWithin out (pure value).writes := writesWithin_nil out

theorem fail_writesWithin {α : Type} (out : Slice) (reason : Fault) :
    WritesWithin out (fail (α := α) reason).writes := writesWithin_nil out

theorem returned_writesWithin {α : Type} (out : Slice) (result : Except Codec.Error α) :
    WritesWithin out (returned result).writes := writesWithin_nil out

theorem bind_writesWithin {α β : Type} (out : Slice) (first : Emitted α)
    (next : α → Emitted β) (firstBounded : WritesWithin out first.writes)
    (nextBounded : ∀ value, first.result = .ok value → WritesWithin out (next value).writes) :
    WritesWithin out (bind first next).writes := by
  unfold bind
  split
  · exact firstBounded
  · rename_i value success
    exact (writesWithin_append out _ _).mpr ⟨firstBounded, nextBounded value success⟩

theorem sub_writes (out : Slice) (start count : Nat) : (sub out start count).writes = [] := by
  unfold sub
  split <;> rfl

theorem suffix_writes (out : Slice) (start : Nat) : (suffix out start).writes = [] := by
  unfold suffix
  split <;> rfl

theorem sub_success_within (out : Slice) (start count : Nat) (target : Slice)
    (success : (sub out start count).result = .ok target) : SliceWithin target out := by
  unfold sub at success
  split at success
  · rename_i bound
    simp only [pure, Except.ok.injEq] at success
    cases success
    unfold SliceWithin
    dsimp only
    omega
  · cases success

theorem suffix_success_within (out : Slice) (start : Nat) (target : Slice)
    (success : (suffix out start).result = .ok target) : SliceWithin target out := by
  unfold suffix at success
  split at success
  · rename_i bound
    simp only [pure, Except.ok.injEq] at success
    cases success
    unfold SliceWithin
    dsimp only
    omega
  · cases success

theorem copy_writesWithin (out : Slice) (bytes : Ssz.Bytes) :
    WritesWithin out (copy out bytes).writes := by
  unfold copy
  split
  · rename_i bound
    intro write member
    simp only [List.mem_singleton] at member
    cases member
    unfold WriteWithin
    dsimp only
    omega
  · exact writesWithin_nil out

theorem nextPart_writes (parts : Parts) : (nextPart parts).writes = [] := by
  cases parts with
  | repeated element => rfl
  | fields fields => cases fields <;> rfl

theorem primitive_writesWithin (desc : Serialize.Desc) (value : Value) (out : Slice) :
    WritesWithin out (primitive desc value out).writes := by
  cases desc <;> cases value <;> simp only [primitive]
  all_goals first
    | exact copy_writesWithin _ _
    | exact fail_writesWithin _ _
    | (apply bind_writesWithin _ _ _ (returned_writesWithin _ _)
       intro _ _
       exact copy_writesWithin _ _)

/-- All visited writes stay in the original output slice, even after an error. -/
theorem sequential_writesWithin (parts : Parts) (values : List Value) (visit : Visit values)
    (out : Slice) (position : Nat)
    (visitBounded : ∀ value member desc plan target,
      WritesWithin target (visit value member desc plan target).writes) :
    WritesWithin out (sequential parts values visit out position).writes := by
  induction values generalizing parts position with
  | nil =>
      rw [sequential]
      exact pure_writesWithin _ _
  | cons value rest ih =>
      rw [sequential]
      apply bind_writesWithin _ _ _
        (by rw [nextPart_writes]; exact writesWithin_nil out)
      intro entry _
      apply bind_writesWithin _ _ _
        (by rw [suffix_writes]; exact writesWithin_nil out)
      intro target reached
      apply bind_writesWithin _ _ _
        (WritesWithin.mono (suffix_success_within out position target reached)
          (visitBounded value (by simp) entry.1 none target))
      intro size _
      apply ih
      intro child member desc plan target
      exact visitBounded child (List.mem_cons_of_mem _ member) desc plan target

theorem table_writesWithin (parts : Parts) (values : List Value) (visit : Visit values)
    (children : List Plan) (out : Slice) (head body : Nat)
    (visitBounded : ∀ value member desc plan target,
      WritesWithin target (visit value member desc plan target).writes) :
    WritesWithin out (table parts values visit children out head body).writes := by
  induction values generalizing parts children head body with
  | nil =>
      rw [table]
      exact pure_writesWithin _ _
  | cons value rest ih =>
      cases children with
      | nil =>
          rw [table]
          · exact pure_writesWithin _ _
          · intro _ impossible
            cases impossible
      | cons child children =>
          rw [table]
          apply bind_writesWithin _ _ _
            (by rw [nextPart_writes]; exact writesWithin_nil out)
          intro entry _
          apply bind_writesWithin _ _ _ (returned_writesWithin _ _)
          intro size _
          split
          · apply bind_writesWithin _ _ _
              (by rw [sub_writes]; exact writesWithin_nil out)
            intro target reached
            apply bind_writesWithin _ _ _
              (WritesWithin.mono (sub_success_within out head size target reached)
                (visitBounded value (by simp) entry.1 (some child) target))
            intro _ _
            apply ih
            intro value member desc plan target
            exact visitBounded value (List.mem_cons_of_mem _ member) desc plan target
          · apply bind_writesWithin _ _ _
              (by rw [sub_writes]; exact writesWithin_nil out)
            intro offsetTarget offsetReached
            apply bind_writesWithin _ _ _
              (WritesWithin.mono (sub_success_within out head 4 offsetTarget offsetReached)
                (copy_writesWithin offsetTarget _))
            intro _ _
            apply bind_writesWithin _ _ _
              (by rw [sub_writes]; exact writesWithin_nil out)
            intro target reached
            apply bind_writesWithin _ _ _
              (WritesWithin.mono (sub_success_within out body size target reached)
                (visitBounded value (by simp) entry.1 (some child) target))
            intro _ _
            apply ih
            intro value member desc plan target
            exact visitBounded value (List.mem_cons_of_mem _ member) desc plan target

theorem emitParts_writesWithin (parts : Parts) (values : List Value) (visit : Visit values)
    (plan : Option Plan) (out : Slice)
    (visitBounded : ∀ value member desc plan target,
      WritesWithin target (visit value member desc plan target).writes) :
    WritesWithin out (emitParts parts values visit plan out).writes := by
  unfold emitParts
  split
  · exact sequential_writesWithin _ _ _ _ _ visitBounded
  · exact table_writesWithin _ _ _ _ _ _ _ visitBounded

theorem emitStep_writesWithin (desc : Desc) (value : Value) (plan : Option Plan) (out : Slice)
    (visit : Visit value.children)
    (visitBounded : ∀ child member desc plan target,
      WritesWithin target (visit child member desc plan target).writes) :
    WritesWithin out (emitStep desc value plan out visit).writes := by
  cases desc <;> cases value <;> simp only [emitStep]
  all_goals first
    | exact primitive_writesWithin _ _ _
    | exact fail_writesWithin _ _
    | exact emitParts_writesWithin _ _ _ _ _ visitBounded
    | (apply bind_writesWithin _ _ _ (copy_writesWithin _ _)
       intro _ _
       apply bind_writesWithin _ _ _ (returned_writesWithin _ _)
       intro chosen _
       apply bind_writesWithin _ _ _
         (by rw [suffix_writes]; exact writesWithin_nil out)
       intro target reached
       apply bind_writesWithin _ _ _
         (WritesWithin.mono (suffix_success_within out 1 target reached)
           (visitBounded _ _ chosen _ target))
       intro size _
       exact pure_writesWithin _ _)

/-- Slice checks alone bound every actual write. No successful result, physical
value, generated plan, or measurement invariant is assumed. -/
theorem emit_writesWithin (desc : Desc) (value : Value) (plan : Option Plan) (out : Slice) :
    WritesWithin out (emit desc value plan out).writes := by
  rw [emit]
  apply emitStep_writesWithin
  intro child _member desc plan target
  exact emit_writesWithin desc child plan target
termination_by value.nesting
decreasing_by exact Value.child_nesting_lt _ _ (by assumption)

theorem emit_frame (desc : Desc) (value : Value) (plan : Option Plan) (out : Slice)
    (before : Nat → Option UInt8) (address : Nat)
    (outside : address < out.address ∨ out.address + out.length ≤ address) :
    applyWrites before (emit desc value plan out).writes address = before address :=
  (emit_writesWithin desc value plan out).frame before address outside

end SszNative.CodecEmit
