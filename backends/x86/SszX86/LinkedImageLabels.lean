module

public import SszX86.LinkedImageLookup
public import Kraken.X64.Semantics
public import Init.Data.List.Impl

@[expose] public section

namespace SszX86.LinkedImage

/-- Exactly the optional search used by `Executable.labels`, before its default. -/
def findLabel (rows : List Addressed) (name : String) : Option Int64 :=
  rows.findSome? (fun (pc, directive, _) =>
    if directive = Directive.label name then some pc else none)

/-- Only label directives survive; duplicate names retain their original order. -/
def labelTable (rows : List Addressed) : List (String × Int64) :=
  rows.filterMap (fun (pc, directive, _) => match directive with
    | .label name => some (name, pc)
    | _ => none)

def findTableLabel (table : List (String × Int64)) (name : String) : Option Int64 :=
  table.findSome? (fun item => if item.1 = name then some item.2 else none)

@[simp] theorem findLabel_nil (name : String) : findLabel [] name = none := rfl

@[simp] theorem labelTable_nil : labelTable [] = [] := rfl

@[simp] theorem findTableLabel_nil (name : String) : findTableLabel [] name = none := rfl

/-- The first occurrence wins across concatenated chunks, including duplicate labels. -/
theorem findLabel_append (xs ys : List Addressed) (name : String) :
    findLabel (xs ++ ys) name = (findLabel xs name).or (findLabel ys name) := by
  exact List.findSome?_append

theorem labelTable_append (xs ys : List Addressed) :
    labelTable (xs ++ ys) = labelTable xs ++ labelTable ys := by
  exact List.filterMap_append

theorem findTableLabel_append (xs ys : List (String × Int64)) (name : String) :
    findTableLabel (xs ++ ys) name =
      (findTableLabel xs name).or (findTableLabel ys name) := by
  exact List.findSome?_append

/-- Filtering instructions and data does not change the original label query. -/
theorem findLabel_eq_findTableLabel (rows : List Addressed) (name : String) :
    findLabel rows name = findTableLabel (labelTable rows) name := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    rcases row with ⟨pc, directive, size⟩
    cases directive with
    | instr instruction =>
      simpa [findLabel, labelTable, findTableLabel, List.findSome?, List.filterMap_cons]
        using ih
    | byteArray bytes =>
      simpa [findLabel, labelTable, findTableLabel, List.findSome?, List.filterMap_cons]
        using ih
    | label labelName =>
      by_cases heq : labelName = name
      · simp [findLabel, labelTable, findTableLabel, List.findSome?, heq]
      · simpa [findLabel, labelTable, findTableLabel, List.findSome?, List.filterMap_cons, heq]
          using ih

theorem labelTable_append_of_eq (xs ys : List Addressed)
    (left right : List (String × Int64))
    (hleft : labelTable xs = left) (hright : labelTable ys = right) :
    labelTable (xs ++ ys) = left ++ right := by
  rw [labelTable_append, hleft, hright]

theorem labels_eq_findLabel (e : Executable) (name : String) :
    e.labels.label name = (findLabel e.withAddresses name).getD (-1) := rfl

theorem labels_eq_findTableLabel (e : Executable) (name : String) :
    e.labels.label name = (findTableLabel (labelTable e.withAddresses) name).getD (-1) := by
  rw [labels_eq_findLabel, findLabel_eq_findTableLabel]

/-- The global label check needs only the composed, filtered table certificate. -/
theorem labels_of_rows_table (e : Executable) (rows : List Addressed)
    (table : List (String × Int64)) (hrows : e.withAddresses = rows)
    (htable : labelTable rows = table) (name : String) :
    e.labels.label name = (findTableLabel table name).getD (-1) := by
  rw [labels_eq_findTableLabel, hrows, htable]

end SszX86.LinkedImage
