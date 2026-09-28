"""Generate structural chunk certificates for a complete Kraken executable."""
import json


def bounded_image(segments, labels):
    """Keep real bytes while bounding every concrete address/label computation."""
    groups = []
    cursor = 0
    for pc, width, source in segments:
        if pc != cursor or width < 0:
            raise ValueError("noncontiguous executable segments")
        if not groups or groups[-1][0][0] != pc:
            groups.append([])
        groups[-1].append((pc, width, source))
        cursor += width
    if not groups or not groups[-1][-1][1]:
        raise ValueError("executable ends with an empty label group")
    # A label run and its following instruction/data must stay in the same chunk.
    parts = [[segment for group in groups[at:at + 32] for segment in group]
             for at in range(0, len(groups), 32)]
    declarations, locations, bounds = [], {}, []
    for index, part in enumerate(parts):
        lo, hi = part[0][0], part[-1][0] + part[-1][1]
        bounds.append((lo, hi))
        for pc, _, _ in part:
            locations[pc] = index
        records = ", ".join(f"(Int64.ofNat {pc}, {source})" for pc, _, source in part)
        table = ", ".join(f"({json.dumps(name)}, Int64.ofNat {pc})"
                          for name, pc in labels if lo <= pc < hi)
        declarations.append(f"""
noncomputable def imageInput{index} : List (Int64 × List (Directive × Nat)) := [{records}]
noncomputable def imageRows{index} : List Addressed := imageInput{index}.flatMap
  (fun item => item.2.map (fun row => (item.1, row)))
noncomputable def imageCode{index} : List (Directive × Nat) := imageRows{index}.map Prod.snd
noncomputable def imageLabels{index} : List (String × Int64) := [{table}]
theorem imageWidth{index} : SszX86.LinkedImage.width imageCode{index} = Int64.ofNat {hi - lo} := by decide
theorem imageAt{index} : Kraken.Executable.withAddresses
    (Int64.ofNat {lo}, imageCode{index}) = imageRows{index} := by
  exact withAddresses_of_sequential (Int64.ofNat {lo}) imageRows{index} (by decide)
theorem imageRange{index} : InRange imageRows{index} {lo} {hi} := by decide
theorem imageLabelsOk{index} : labelTable imageRows{index} = imageLabels{index} := by rfl
""")
    end = len(parts)
    declarations.append(f"""
noncomputable def imageCodeTail{end} : List (Directive × Nat) := []
noncomputable def imageRowsTail{end} : List Addressed := []
noncomputable def imageLabelsTail{end} : List (String × Int64) := []
theorem imageTailAt{end} : Kraken.Executable.withAddresses
    (Int64.ofNat {cursor}, imageCodeTail{end}) = imageRowsTail{end} := by
  simp only [imageCodeTail{end}, imageRowsTail{end}, Kraken.Executable.withAddresses]
theorem imageTailRange{end} : InRange imageRowsTail{end} {cursor} {cursor} := by decide
theorem imageTailLabels{end} : labelTable imageRowsTail{end} = imageLabelsTail{end} := by rfl
""")
    for index in reversed(range(end)):
        lo, hi = bounds[index]
        following = index + 1
        declarations.append(f"""
noncomputable def imageCodeTail{index} : List (Directive × Nat) :=
  imageCode{index} ++ imageCodeTail{following}
noncomputable def imageRowsTail{index} : List Addressed := imageRows{index} ++ imageRowsTail{following}
noncomputable def imageLabelsTail{index} : List (String × Int64) :=
  imageLabels{index} ++ imageLabelsTail{following}
theorem imageTailAt{index} : Kraken.Executable.withAddresses
    (Int64.ofNat {lo}, imageCodeTail{index}) = imageRowsTail{index} := by
  change Kraken.Executable.withAddresses (Int64.ofNat {lo}, imageCode{index} ++ imageCodeTail{following}) =
    imageRows{index} ++ imageRowsTail{following}
  apply withAddresses_append_of_eq imageCode{index} imageCodeTail{following}
    (Int64.ofNat {lo}) (Int64.ofNat {hi - lo}) imageRows{index} imageRowsTail{following}
    imageWidth{index} imageAt{index}
  rw [show Int64.ofNat {lo} + Int64.ofNat {hi - lo} = Int64.ofNat {hi} from by decide]
  exact imageTailAt{following}
theorem imageTailRange{index} : InRange imageRowsTail{index} {lo} {cursor} := by
  exact inRange_append (by decide) (by decide) imageRange{index} imageTailRange{following}
theorem imageTailLabels{index} : labelTable imageRowsTail{index} = imageLabelsTail{index} := by
  exact labelTable_append_of_eq imageRows{index} imageRowsTail{following}
    imageLabels{index} imageLabelsTail{following} imageLabelsOk{index} imageTailLabels{following}
""")
    declarations.append("""
noncomputable def bound : Executable := (0, imageCodeTail0)
theorem boundRows : bound.withAddresses = imageRowsTail0 := imageTailAt0
theorem boundLabel (name : String) : bound.labels.label name =
    (findTableLabel imageLabelsTail0 name).getD (-1) :=
  labels_of_rows_table bound imageRowsTail0 imageLabelsTail0 boundRows imageTailLabels0 name
noncomputable def imageBefore0 : List Addressed := []
theorem imageBeforeRange0 : InRange imageBefore0 0 0 := by decide
theorem imageSplit0 : imageRowsTail0 = imageBefore0 ++ imageRowsTail0 := by rfl
""")
    for index, (lo, hi) in enumerate(bounds):
        if index:
            previous = index - 1
            declarations.append(f"""
noncomputable def imageBefore{index} : List Addressed := imageBefore{previous} ++ imageRows{previous}
theorem imageBeforeRange{index} : InRange imageBefore{index} 0 {lo} := by
  exact inRange_append (by decide) (by decide) imageBeforeRange{previous} imageRange{previous}
theorem imageSplit{index} : imageRowsTail0 = imageBefore{index} ++ imageRowsTail{index} := by
  calc
    imageRowsTail0 = imageBefore{previous} ++ imageRowsTail{previous} := imageSplit{previous}
    _ = imageBefore{index} ++ imageRowsTail{index} := by
      simp only [imageRowsTail{previous}, imageBefore{index}, List.append_assoc]
""")
        declarations.append(f"""
theorem imageFocus{index} (pc : Int64) (hlo : {lo} ≤ pc.toBitVec.toNat)
    (hhi : pc.toBitVec.toNat < {hi}) :
    bound.directivesAtAddress pc = lookup imageRows{index} pc := by
  apply directivesAtAddress_focus bound imageBefore{index} imageRows{index} imageRowsTail{index + 1}
    pc 0 {lo} {hi} {cursor}
  · rw [boundRows, imageSplit{index}]
    simp only [imageRowsTail{index}, List.append_assoc]
  · exact imageBeforeRange{index}
  · exact imageTailRange{index + 1}
  · exact hlo
  · exact hhi
""")
    return declarations, locations
