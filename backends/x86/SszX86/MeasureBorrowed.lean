import SszX86.MeasurePost

namespace SszX86.Measure
open SszNative SszNative.Serialize

/-- Every original active observation and every borrowed limb/backing byte is
outside the exact outcome-dependent writes. Readonly aliases are unrestricted. -/
theorem Owned.borrowed_untouched {s : MachineData} {base : Int64} {desc : Desc} {value : Value}
    {buffer address capacity used ra : BitVec 64} {retain : Bool}
    (owned : Owned s base desc value buffer address capacity used ra retain)
    (a : BitVec 64) (borrowed : Borrowed s desc value buffer a) :
    ¬ Writable s (measure desc value (arenaState address capacity used)) a := by
  intro writes
  apply owned.readonly a borrowed
  rcases writes with result | allocation | ⟨_, cursor⟩ | activation
  · exact Or.inl (resultWrites_span _ _ _ result)
  · exact Or.inr (Or.inr (Or.inl (allocation_in_free desc value address capacity used a allocation)))
  · exact Or.inr (Or.inl cursor)
  · exact Or.inr (Or.inr (Or.inr activation))

theorem Post.borrowed_frame {s : MachineData} {base : Int64} {desc : Desc} {value : Value}
    {buffer address capacity used ra : BitVec 64} {retain : Bool} {t : MachineState}
    (post : Post s desc value buffer address capacity used ra t)
    (owned : Owned s base desc value buffer address capacity used ra retain)
    (a : BitVec 64) (borrowed : Borrowed s desc value buffer a) :
    t.1.dmem.get? a = s.dmem.get? a :=
  post.frame a (owned.borrowed_untouched a borrowed)

end SszX86.Measure
