"""Bind the complete recursive x86 codec to its actual linked instruction image.

Translation uses the canonical decoder.  Only the lowering's two original DIV
fault boundaries remain byte data; they are not assigned executable semantics.
"""
import json

from codec_binding import NAMES as FUNCTIONS, dispatch_tables, selected_rows, validate
from decoder_x86_binding import _byte_segments, _image_parts
from decoder_x86_image import bounded_image
from sha_binding import LIST_BINDING_HEADER, list_binding


def _stem(name):
    return "Codec" + "".join(word.title() for word in name.split("_"))


def _prefix(name):
    if name == "deserialize":
        return ""
    return (name if name in ("serialize", "measure", "emit") else "codec_" + name) + "_"


def _raw_segments(segments, raw, address):
    for at, part in zip(range(0, len(raw), 256), _byte_segments(raw)):
        segments.append((address + at, min(256, len(raw) - at), part))


def _all_certificate(name, source, predicate, facts):
    branches = "\n".join(f"  · exact decide_eq_true {fact}" for fact in facts)
    return f"""
theorem {name} : {source}.all ({predicate}) = true := by
  apply List.all_eq_true.mpr
  intro row member
  simp only [{source}, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with {' | '.join('rfl' for _ in facts)}
{branches}
"""


def _all_append_proof(source, checks):
    if len(checks) == 1:
        return f"exact {checks[0]}"
    return (f"simp only [{source}, List.all_append, "
            f"{', '.join(checks)}, Bool.and_true]")


def _component(declarations, locations, name, body, rows, names, expressions):
    stem, base = _stem(name), body["address"]
    namespace = f"SszX86.{stem}"
    program_chunks, fetch_checks = [], []
    for number, at in enumerate(range(0, len(rows), 64)):
        chunk = f"actual{stem}Chunk{number}"
        program_chunks.append(chunk)
        bindings, parts = list_binding(
            chunk, "(Nat × Nat × Program)", f"{namespace}.programChunk{number}",
            expressions[at:at + 64])
        declarations.extend(bindings)
        part_checks = []
        for part_number, part in enumerate(parts):
            start = at + 32 * part_number
            facts = []
            for row, expr in zip(rows[start:min(start + 32, at + 64)],
                                 expressions[start:min(start + 32, at + 64)]):
                pc = base + row["pc"]
                fact = f"bound{stem}Row{row['pc']}"
                facts.append(fact)
                declarations.append(f"""
theorem {fact} :
    bound.directivesAtAddress ({base} + Int64.ofNat {row['pc']}) =
      {namespace}.directives {expr} := by
  rw [show ({base} : Int64) + Int64.ofNat {row['pc']} = Int64.ofNat {pc} from by decide]
  rw [imageFocus{locations[pc]} (Int64.ofNat {pc}) (by decide) (by decide)]
  decide
""")
            check = f"bound{stem}Chunk{number}Part{part_number}Fetch"
            part_checks.append(check)
            predicate = (f"fun row => decide (bound.directivesAtAddress "
                         f"({base} + Int64.ofNat row.1) = {namespace}.directives row)")
            declarations.append(_all_certificate(check, part, predicate, facts))
        check = f"bound{stem}Chunk{number}Fetch"
        fetch_checks.append(check)
        declarations.append(f"""
theorem {check} : {chunk}.all (fun row =>
    decide (bound.directivesAtAddress ({base} + Int64.ofNat row.1) =
      {namespace}.directives row)) = true := by
  {_all_append_proof(chunk, part_checks)}
""")
    label_name = f"actual{stem}Labels"
    label_values = [f"({json.dumps(label)}, {pc})" for label, pc in names]
    label_bindings, label_parts = list_binding(
        label_name, "(String × Nat)", f"{namespace}.labels", label_values, chunk_size=16)
    declarations.extend(label_bindings)
    label_checks = []
    for number, part in enumerate(label_parts):
        facts = []
        for label, pc in names[16 * number:16 * (number + 1)]:
            fact = f"bound{stem}Label{pc}"
            facts.append(fact)
            declarations.append(f"""
theorem {fact} : bound.labels.label {json.dumps(label)} =
    {base} + Int64.ofNat {pc} := by
  simp only [boundLabel]
  decide
""")
        check = f"bound{stem}Labels{number}"
        label_checks.append(check)
        predicate = (f"fun row => decide (bound.labels.label row.1 = "
                     f"{base} + Int64.ofNat row.2)")
        declarations.append(_all_certificate(check, part, predicate, facts))
    declarations.append(f"""
def actual{stem} : List (Nat × Nat × Program) := {' ++ '.join(program_chunks)}
theorem actual{stem}_eq : actual{stem} = {namespace}.program := by
  simp only [actual{stem}, {namespace}.program,
    {', '.join(chunk + '_eq' for chunk in program_chunks)}]
example : {namespace}.entry = 0 := by decide
example : {namespace}.linkedAddress = {base} := by decide
example : {namespace}.machineSize = {body['size']} := by decide

theorem bound{stem}Targets : {namespace}.labels.all (fun item =>
    decide (bound.labels.label item.1 = {base} + Int64.ofNat item.2)) = true := by
  rw [← {label_name}_eq]
  {_all_append_proof(label_name, label_checks)}

theorem bound{stem}CodeAt : {namespace}.CodeAt bound {base} := by
  constructor
  · have checked : actual{stem}.all (fun row =>
        decide (bound.directivesAtAddress ({base} + Int64.ofNat row.1) =
          {namespace}.directives row)) = true := by
      {_all_append_proof(f'actual{stem}', fetch_checks)}
    intro row member
    rw [← actual{stem}_eq] at member
    exact of_decide_eq_true (List.all_eq_true.mp checked row member)
  · intro item member
    exact of_decide_eq_true (List.all_eq_true.mp bound{stem}Targets item member)
""")


def _tables(image, declarations):
    declarations.append("""
def codecSignedTableDestinations (offset : Int) (bytes : List UInt8) : List Int :=
  (List.range (bytes.length / 4)).map fun i =>
    let displacement := (bytes.getD (4 * i) 0).toNat +
      256 * (bytes.getD (4 * i + 1) 0).toNat +
      65536 * (bytes.getD (4 * i + 2) 0).toNat +
      16777216 * (bytes.getD (4 * i + 3) 0).toNat
    offset + (if displacement < 2147483648 then Int.ofNat displacement
      else Int.ofNat displacement - 4294967296)
""")
    for symbol, table in dispatch_tables(image).items():
        name, address = table["function"], table["address"]
        field = "table1" if symbol == ".LJTI84_1" else "table"
        raw = bytes.fromhex(table["raw"])
        body = image["functions"][name]
        relative = address - body["address"]
        destinations = table["targets"]
        namespace, stem = f"SszX86.{_stem(name)}", _stem(name) + field.title()
        bindings, _ = list_binding(f"actual{stem}Bytes", "UInt8", f"{namespace}.{field}Bytes",
                                   list(map(str, raw)))
        declarations.extend(bindings)
        declarations.append(f"""
example : {namespace}.{field}Offset = ({relative} : Int) := by decide
example : {namespace}.{field}Address {body['address']} = BitVec.ofNat 64 {address} := by decide
example : {namespace}.{field}Destinations = [{', '.join(map(str, destinations))}] := by decide
theorem bound{stem}SignedDestinations :
    codecSignedTableDestinations {namespace}.{field}Offset {namespace}.{field}Bytes =
      {namespace}.{field}Destinations.map Int.ofNat := by decide
""")


def source(image):
    """Return a default-limit Lean certificate; never invoke extraction or Lean."""
    validate("x86", image)
    origin, text = image["textAddress"], bytes.fromhex(image["textRaw"])
    segments, image_labels, components, faults = [], [], [], []
    cursor = origin
    for name, body in sorted(image["functions"].items(), key=lambda item: item[1]["address"]):
        base, raw = body["address"], bytes.fromhex(body["raw"])
        if base < cursor or base - origin != body["offset"] or text[base - origin:base - origin + len(raw)] != raw:
            raise ValueError(f"codec function disagrees with linked text: {name}")
        rows = selected_rows("x86", name, body)
        selected_pcs = {row["pc"] for row in rows}
        fault_rows = [(row["pc"], bytes.fromhex(row["encoding"]))
                      for row in body["rows"] if row["pc"] not in selected_pcs]
        names, expressions, pieces, positions = _image_parts(rows, raw, _prefix(name))
        _raw_segments(segments, text[cursor - origin:base - origin], cursor)
        segments.extend((base + pc, width, part) for (pc, width), part in zip(positions, pieces))
        image_labels.extend((label, base + pc) for label, pc in names)
        components.append((name, body, rows, names, expressions))
        faults.extend((base, pc, encoded) for pc, encoded in fault_rows)
        cursor = base + len(raw)
    _raw_segments(segments, text[cursor - origin:], cursor)
    # Model labels prioritize legacy Boolean aliases; image label tables instead
    # follow the physical directive order required by labelTable's certificate.
    image_labels.sort(key=lambda item: item[1])
    declarations, locations = bounded_image(segments, image_labels, origin=origin)
    declarations.append(LIST_BINDING_HEADER)
    for component in components:
        _component(declarations, locations, *component)
    fault_literal = ", ".join(f"({pc}, [{', '.join(map(str, encoded))}])"
                              for _, pc, encoded in faults)
    declarations.append(f"""
example : SszX86.CodecDecodeList.faultingInstructions = [{fault_literal}] := by decide
""")
    for base, pc, encoded in faults:
        byte_literal = ", ".join(map(str, encoded))
        declarations.append(f"""
theorem boundCodecDecodeListFault{pc} :
    bound.directivesAtAddress (Int64.ofNat {base + pc}) =
      [(.byteArray (ByteArray.mk #[{byte_literal}]), {len(encoded)})] := by
  rw [imageFocus{locations[base + pc]} (Int64.ofNat {base + pc}) (by decide) (by decide)]
  decide
""")
    _tables(image, declarations)
    imports = "\n".join(f"import SszX86.{_stem(name)}Impl" for name in FUNCTIONS)
    return imports + """
import SszX86.LinkedImage
import SszX86.LinkedImageSequential
import ProofAudit
open Kraken.X64.Parser SszX86.LinkedImage
""" + "\n".join(declarations) + "\naudit_native\n"
