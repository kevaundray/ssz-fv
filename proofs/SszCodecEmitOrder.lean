import SszCodecEmit

set_option autoImplicit false

namespace SszNative.CodecEmit

open Codec (Desc Value Error)
open CodecMeasure (Plan Parts)

/-- The no-children shortcut still traverses every input value with None. -/
theorem emitParts_sequential (parts : Parts) (values : List Value) (visit : Visit values)
    (plan : Option Plan) (out : Slice) (empty : children plan = []) :
    emitParts parts values visit plan out = sequential parts values visit out 0 := by
  simp only [emitParts, empty, List.isEmpty_nil, ↓reduceIte]

/-- A retained nonempty plan selects the offset-positioned traversal, whose
body starts at the actual measured leading field. -/
theorem emitParts_table (parts : Parts) (values : List Value) (visit : Visit values)
    (plan : Option Plan) (out : Slice) (nonempty : children plan ≠ []) :
    emitParts parts values visit plan out = table parts values visit (children plan) out 0 (leading plan) := by
  cases equation : children plan with
  | nil => exact False.elim (nonempty equation)
  | cons child rest => simp only [emitParts, equation, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]

/-- A failed child host-size conversion precedes every write for that child,
including its offset. Earlier iterations, if any, remain in the caller's bind. -/
theorem table_host_failure (parts remaining : Parts) (desc : Desc)
    (value : Value) (values : List Value) (visit : Visit (value :: values))
    (child : Plan) (plans : List Plan) (out : Slice) (head body : Nat) (reason : Error)
    (next : nextPart parts = pure (desc, remaining))
    (failed : (CodecMeasure.hostSize child.size 0).result = .error reason) :
    table parts (value :: values) visit (child :: plans) out head body =
      ⟨.error (.returned reason), []⟩ := by
  simp only [table, next, pure, bind, returned, failed, Except.mapError, List.nil_append]

/-- A variable child's offset is copied before its recursive body. The two
independent indices advance only after successful recursive emission. -/
theorem table_variable_order (parts remaining : Parts) (desc : Desc)
    (value : Value) (values : List Value) (visit : Visit (value :: values))
    (child : Plan) (plans : List Plan) (out : Slice) (head body size : Nat)
    (next : nextPart parts = pure (desc, remaining))
    (converted : (CodecMeasure.hostSize child.size 0).result = .ok size)
    (outOfLine : inline parts desc = false) :
    table parts (value :: values) visit (child :: plans) out head body =
      bind (sub out head 4) (fun offset =>
        bind (copy offset (Ssz.uintBytes 4 body)) (fun _ =>
          bind (sub out body size) (fun target =>
            bind (visit value (by simp) desc (some child) target) (fun _ =>
              table remaining values
                (fun value member => visit value (List.mem_cons_of_mem _ member))
                plans out (head + 4) (body + size))))) := by
  simp only [table, next, pure, bind, returned, converted, Except.mapError,
    List.nil_append, outOfLine, Bool.false_eq_true, ↓reduceIte]

/-- The selector write really precedes option lookup in private emit. Public
serialization performs lookup earlier in measure and therefore writes nothing
on this rejection; this theorem is about the native private helper order. -/
theorem union_lookup_failure (variants : List (NatOperand × Desc)) (selector : NatOperand)
    (value : Value) (plan : Option Plan) (out : Slice) (reason : Error)
    (fits : 1 ≤ out.length) (failed : CodecMeasure.option variants selector = .error reason) :
    emit (.compatibleUnion variants) (.union selector value) plan out =
      ⟨.error (.returned reason), [⟨out.address, #[UInt8.ofNat selector.value]⟩]⟩ := by
  rw [emit]
  simp only [emitStep, copy, Array.size_singleton, fits, ↓reduceIte, bind,
    returned, failed, Except.mapError, List.append_nil]

end SszNative.CodecEmit
