use crate::json::{object_value, parse_number};
use crate::{Arena, Desc, Error, Field, Json, Nat, Reason, Result, Spelling, Variant};

const OPAQUE: Spelling<'static> = Spelling::Plain(&[]);

fn field<'a>(document: &Json<'a>, name: &str) -> Option<&'a Json<'a>> {
    match *document {
        Json::Object(fields) => object_value(fields, name),
        _ => None,
    }
}

fn required<'a>(document: &Json<'a>, name: &str) -> Result<'a, &'a Json<'a>> {
    field(document, name).ok_or(Error::new(Reason::Undeclared))
}

fn is_uint_kind(kind: &str) -> bool {
    kind.strip_prefix("Uint")
        .is_some_and(|width| !width.is_empty() && width.bytes().all(|byte| byte.is_ascii_digit()))
}

fn entitled_keys(kind: &str) -> Result<'static, &'static [&'static str]> {
    match kind {
        "Boolean" => Ok(&[]),
        "ProgressiveBitList" => Ok(&["limit"]),
        "Byte" => Ok(&["bits"]),
        "BitVector" | "ByteVector" => Ok(&["length"]),
        "BitList" | "ByteList" => Ok(&["limit"]),
        "Vector" => Ok(&["length", "elementType"]),
        "List" | "ProgressiveList" => Ok(&["limit", "elementType"]),
        "Container" => Ok(&["fields"]),
        "ProgressiveContainer" => Ok(&["activeFields", "fields"]),
        "CompatibleUnion" => Ok(&["options"]),
        _ if is_uint_kind(kind) => Ok(&["bits"]),
        _ => Err(Error::new(Reason::BadDeclaration)),
    }
}

fn numeric_error<'a>(error: Error<'a>, reason: Reason) -> Error<'a> {
    if error.reason == Reason::WrongType { Error::new(reason) } else { error }
}

fn count<'a>(document: &Json<'a>, arena: &mut Arena<'a>) -> Result<'a, Nat<'a>> {
    let Json::Number(text) = document else {
        return Err(Error::new(Reason::BadDeclaration));
    };
    let number = parse_number(text, arena)
        .map_err(|error| numeric_error(error, Reason::BadDeclaration))?;
    if number.negative {
        Err(Error::new(Reason::CapacityNegative))
    } else if !number.exponent.is_zero() {
        Err(Error::new(Reason::BadDeclaration))
    } else {
        Ok(number.mantissa)
    }
}

fn stated<'a>(document: &Json<'a>, name: &str, arena: &mut Arena<'a>) -> Result<'a, Nat<'a>> {
    count(required(document, name)?, arena)
}

fn bound<'a>(document: &Json<'a>, arena: &mut Arena<'a>) -> Result<'a, Option<Nat<'a>>> {
    field(document, "limit").map(|value| count(value, arena)).transpose()
}

fn layout_bit<'a>(document: &Json<'a>, arena: &mut Arena<'a>) -> Result<'a, bool> {
    match document {
        Json::Bool(bit) => Ok(*bit),
        Json::Number(text) => {
            let number = parse_number(text, arena)
                .map_err(|error| numeric_error(error, Reason::LayoutNotBits))?;
            // Reader.layoutBit inspects the signed mantissa, not its exponent.
            if number.mantissa.is_zero() {
                Ok(false)
            } else if !number.negative && number.mantissa == Nat::ONE {
                Ok(true)
            } else {
                Err(Error::new(Reason::LayoutNotBits))
            }
        }
        _ => Err(Error::new(Reason::LayoutNotBits)),
    }
}

#[derive(Clone, Copy)]
struct Held<'a> {
    label: &'a Json<'a>,
    desc: Desc<'a>,
    spelling: Spelling<'a>,
}

fn held<'a>(document: &Json<'a>, key: &str, marker: &str, arena: &mut Arena<'a>) -> Result<'a, &'a [Held<'a>]> {
    let Json::Array(parts) = *required(document, key)? else {
        return Err(Error::new(Reason::BadDeclaration));
    };
    // Finish every nested declaration before converting any field name or
    // selector. A malformed later child takes precedence over an earlier label.
    arena.slice_with(parts.len(), |index, arena| {
        let label = required(&parts[index], marker)?;
        let declared = required(&parts[index], "type")?;
        let (desc, spelling) = read_descriptor(declared, arena)?;
        Ok(Held { label, desc, spelling })
    })
}

fn fields<'a>(parts: &'a [Held<'a>], arena: &mut Arena<'a>) -> Result<'a, &'a [Field<'a>]> {
    arena.slice_with(parts.len(), |index, _| {
        let part = &parts[index];
        let Json::String(name) = *part.label else {
            return Err(Error::new(Reason::BadDeclaration));
        };
        Ok(Field { name, desc: &part.desc })
    })
}

fn spelling<'a>(parts: &[Held<'a>], arena: &mut Arena<'a>) -> Result<'a, Spelling<'a>> {
    Ok(Spelling::Plain(arena.slice_with(parts.len(), |index, _| Ok(parts[index].spelling))?))
}

/// Read a conformance declaration and retain its byte-alias spelling.
///
/// This is the shape parser, not declaration validation: call `schema::validate`
/// separately to enforce SSZ widths, nonempty vectors, layouts, and union rules.
/// JSON object lookup has Lean's last-duplicate-wins semantics.
pub fn read_descriptor<'a>(document: &Json<'a>, arena: &mut Arena<'a>) -> Result<'a, (Desc<'a>, Spelling<'a>)> {
    let Json::Object(carried) = *document else {
        return Err(Error::new(Reason::BadDeclaration));
    };
    let Json::String(kind) = *required(document, "kind")? else {
        return Err(Error::new(Reason::BadDeclaration));
    };
    let allowed = entitled_keys(kind)?;
    // Unknown keys precede missing entitled keys. The refusal has no key
    // payload, so traversing the borrowed map needs no sorted scratch copy.
    for (name, _) in carried {
        if *name != "kind" && !allowed.contains(name) {
            return Err(Error::new(Reason::NotEntitled));
        }
    }
    for name in allowed {
        let optional = *name == "limit" && matches!(kind, "ProgressiveBitList" | "ProgressiveList");
        if !optional && field(document, name).is_none() {
            return Err(Error::new(Reason::Undeclared));
        }
    }

    match kind {
        "Boolean" => Ok((Desc::Bool, OPAQUE)),
        // The bits key is required by the envelope, but Byte ignores its value.
        "Byte" => Ok((Desc::Uint(Nat::ONE), Spelling::Byte)),
        "BitVector" => Ok((Desc::BitVector(stated(document, "length", arena)?), OPAQUE)),
        "BitList" => Ok((Desc::BitList(stated(document, "limit", arena)?), OPAQUE)),
        "ProgressiveBitList" => Ok((Desc::ProgressiveBitList(bound(document, arena)?), OPAQUE)),
        "ByteVector" => Ok((Desc::ByteVector(stated(document, "length", arena)?), OPAQUE)),
        "ByteList" => Ok((Desc::ByteList(stated(document, "limit", arena)?), OPAQUE)),
        "Vector" | "List" | "ProgressiveList" => {
            let (element, child_spelling) = read_descriptor(required(document, "elementType")?, arena)?;
            let desc = match kind {
                "Vector" => {
                    let length = stated(document, "length", arena)?;
                    Desc::Vector(arena.one(element)?, length)
                }
                "List" => {
                    let limit = stated(document, "limit", arena)?;
                    Desc::List(arena.one(element)?, limit)
                }
                _ => {
                    let limit = bound(document, arena)?;
                    Desc::ProgressiveList(arena.one(element)?, limit)
                }
            };
            Ok((desc, Spelling::Plain(arena.copy(&[child_spelling])?)))
        }
        "Container" => {
            let parts = held(document, "fields", "name", arena)?;
            let desc = Desc::Container(fields(parts, arena)?);
            Ok((desc, spelling(parts, arena)?))
        }
        "ProgressiveContainer" => {
            let Json::Array(positions) = *required(document, "activeFields")? else {
                return Err(Error::new(Reason::LayoutNotBits));
            };
            let active = arena.slice_with(positions.len(), |index, arena| layout_bit(&positions[index], arena))?;
            let parts = held(document, "fields", "name", arena)?;
            let desc = Desc::ProgressiveContainer { active, fields: fields(parts, arena)? };
            Ok((desc, spelling(parts, arena)?))
        }
        "CompatibleUnion" => {
            let parts = held(document, "options", "selector", arena)?;
            let variants = arena.slice_with(parts.len(), |index, arena| {
                let part = &parts[index];
                Ok(Variant { selector: count(part.label, arena)?, desc: &part.desc })
            })?;
            Ok((Desc::CompatibleUnion(variants), spelling(parts, arena)?))
        }
        _ => {
            // entitled_keys already established that this is a Uint digit kind.
            let bits = stated(document, "bits", arena)?;
            if bits.is_zero() || bits.word(0) & 7 != 0 {
                return Err(Error::one(Reason::UintWidth, bits));
            }
            let (width, _) = bits.div_rem_small(8, arena)?;
            Ok((Desc::Uint(width), OPAQUE))
        }
    }
}

#[derive(Clone, Copy)]
enum WrittenStep<'a> {
    Named(&'a str),
    At { negative: bool, position: Nat<'a> },
    Word(&'a str),
}

fn path_text<'a>(document: &Json<'a>) -> Result<'a, &'a str> {
    match *document {
        Json::String(text) => Ok(text),
        _ => Err(Error::new(Reason::BadRepresentation)),
    }
}

fn path_position<'a>(document: &Json<'a>, nonnegative: bool, arena: &mut Arena<'a>) -> Result<'a, WrittenStep<'a>> {
    let Json::Number(text) = document else {
        return Err(Error::new(Reason::BadRepresentation));
    };
    let number = parse_number(text, arena)
        .map_err(|error| numeric_error(error, Reason::BadRepresentation))?;
    if !number.exponent.is_zero() || (nonnegative && number.negative) {
        return Err(Error::new(Reason::BadRepresentation));
    }
    Ok(WrittenStep::At { negative: number.negative, position: number.mantissa })
}

fn written_step<'a>(document: &Json<'a>, proof_format: bool, arena: &mut Arena<'a>) -> Result<'a, WrittenStep<'a>> {
    if proof_format {
        // readProofStep chooses the first present key, even when several exist.
        if let Some(name) = field(document, "field") {
            return Ok(WrittenStep::Named(path_text(name)?));
        }
        if let Some(position) = field(document, "position") {
            return path_position(position, true, arena);
        }
        if let Some(word) = field(document, "mixin") {
            return Ok(WrittenStep::Word(path_text(word)?));
        }
        return Err(Error::new(Reason::BadRepresentation));
    }
    match document {
        Json::String(name) => Ok(WrittenStep::Named(name)),
        Json::Number(_) => path_position(document, false, arena),
        Json::Object(_) => {
            let word = field(document, "mixin").ok_or(Error::new(Reason::BadRepresentation))?;
            Ok(WrittenStep::Word(path_text(word)?))
        }
        _ => Err(Error::new(Reason::BadRepresentation)),
    }
}

fn read_word<'a>(name: &str) -> Result<'a, crate::types::PathStep<'a>> {
    use crate::types::PathStep;

    match name {
        "elementCount" | "__len__" => Ok(PathStep::Length),
        "fieldLayout" | "__active_fields__" => Ok(PathStep::ActiveFields),
        "typeSelector" | "__selector__" => Ok(PathStep::Selector),
        _ => Err(Error::new(Reason::NoMixin)),
    }
}

/// Parse a conformance path, then resolve names while walking its declaration.
///
/// `proof_format` selects `{field}`, `{position}`, and `{mixin}` steps; otherwise
/// names and positions are bare strings and numbers. Invalid fixture syntax is
/// a host representation error; semantic path refusals retain their SSZ reason.
/// Index validation itself remains the responsibility of `generalized_index`.
pub fn read_path<'a>(
    desc: &Desc<'a>,
    written: &Json<'a>,
    proof_format: bool,
    arena: &mut Arena<'a>,
) -> Result<'a, &'a [crate::types::PathStep<'a>]> {
    use crate::types::PathStep;

    let Json::Array(entries) = *written else {
        return Err(Error::new(Reason::BadRepresentation));
    };
    // Cases.indexOfSteps parses all syntax before Reader.readPath can refuse a
    // semantic step. Keep that phase ordering for mixed malformed requests.
    let steps = arena.slice_with(entries.len(), |index, arena| {
        written_step(&entries[index], proof_format, arena)
    })?;
    let mut reached = Some(*desc);
    arena.slice_with(steps.len(), |index, arena| {
        let resolved = match steps[index] {
            WrittenStep::Word(name) => read_word(name)?,
            WrittenStep::At { negative: true, .. } => {
                return Err(Error::one(Reason::NoSuchPosition, Nat::ZERO));
            }
            WrittenStep::At { position, .. } => PathStep::Position(position),
            WrittenStep::Named(name) => match reached {
                Some(Desc::Container(fields) | Desc::ProgressiveContainer { fields, .. }) => {
                    let ordinal = fields.iter().position(|field| field.name == name)
                        .ok_or(Error::one(Reason::NoSuchField, Nat::ZERO))?;
                    PathStep::Position(Nat::from_u128(ordinal as u128, arena)?)
                }
                Some(_) => return Err(Error::new(Reason::NotAPosition)),
                None => PathStep::Position(Nat::ZERO),
            },
        };
        if let Some(current) = reached {
            reached = match crate::indices::resolve_step(&current, resolved, arena) {
                Ok((_, child)) => child,
                Err(error) if error.is_host() => return Err(error),
                Err(_) => None,
            };
        }
        Ok(resolved)
    })
}

#[cfg(test)]
mod tests {
    use core::mem::MaybeUninit;

    use super::*;

    const BOOLEAN: Json<'static> = Json::Object(&[("kind", Json::String("Boolean"))]);
    const BYTE: Json<'static> = Json::Object(&[
        ("kind", Json::String("Byte")), ("bits", Json::Null),
    ]);

    #[test]
    fn descriptor_envelope_precedes_shape_contents() {
        let mut storage = [MaybeUninit::uninit(); 4096];
        let mut arena = Arena::new(&mut storage);
        let cases = [
            (Json::Null, Reason::BadDeclaration),
            (Json::Object(&[("extra", Json::Null)]), Reason::Undeclared),
            (Json::Object(&[("kind", Json::Null), ("extra", Json::Null)]), Reason::BadDeclaration),
            (Json::Object(&[("kind", Json::String("Unknown")), ("extra", Json::Null)]), Reason::BadDeclaration),
            (Json::Object(&[("kind", Json::String("Vector")), ("extra", Json::Null)]), Reason::NotEntitled),
            (Json::Object(&[("kind", Json::String("Vector")), ("elementType", Json::Null)]), Reason::Undeclared),
            (Json::Object(&[("kind", Json::String("Byte"))]), Reason::Undeclared),
        ];
        for (document, reason) in cases {
            assert_eq!(read_descriptor(&document, &mut arena).unwrap_err().reason, reason);
        }
        let duplicate = Json::Object(&[
            ("kind", Json::Null), ("kind", Json::String("Boolean")),
        ]);
        assert!(matches!(read_descriptor(&duplicate, &mut arena).unwrap().0, Desc::Bool));
        assert!(matches!(read_descriptor(&BYTE, &mut arena).unwrap(), (Desc::Uint(Nat::Small(1)), Spelling::Byte)));
    }

    #[test]
    fn count_keeps_lean_mantissa_and_exponent_distinct() {
        let mut storage = [MaybeUninit::uninit(); 8192];
        let mut arena = Arena::new(&mut storage);
        for (token, reason) in [
            ("-1.0", Reason::CapacityNegative),
            ("1.0", Reason::BadDeclaration),
            ("0e-1", Reason::BadDeclaration),
            ("-0.0", Reason::BadDeclaration),
        ] {
            assert_eq!(count(&Json::Number(token), &mut arena).unwrap_err().reason, reason);
        }
        for (token, expected) in [("-0", 0), ("1.0e1", 10), ("123e2", 12300)] {
            assert_eq!(count(&Json::Number(token), &mut arena).unwrap(), Nat::Small(expected));
        }
        let huge = count(&Json::Number("184467440737095516160"), &mut arena).unwrap();
        assert_eq!(huge.to_u128(), Some(184467440737095516160));
        assert_eq!(layout_bit(&Json::Number("0.1"), &mut arena), Ok(true));
        assert_eq!(layout_bit(&Json::Number("1e-2"), &mut arena), Ok(true));
        assert_eq!(layout_bit(&Json::Number("-0.0"), &mut arena), Ok(false));
        assert_eq!(layout_bit(&Json::Number("1.0"), &mut arena).unwrap_err().reason, Reason::LayoutNotBits);
    }

    #[test]
    fn every_child_is_read_before_any_label_is_converted() {
        let mut storage = [MaybeUninit::uninit(); 8192];
        let mut arena = Arena::new(&mut storage);
        let invalid_child = Json::Object(&[
            ("kind", Json::String("ByteList")), ("limit", Json::Number("-1")),
        ]);
        let fields = [
            Json::Object(&[("name", Json::Null), ("type", BOOLEAN)]),
            Json::Object(&[("name", Json::String("later")), ("type", invalid_child)]),
        ];
        let container = Json::Object(&[
            ("kind", Json::String("Container")), ("fields", Json::Array(&fields)),
        ]);
        assert_eq!(read_descriptor(&container, &mut arena).unwrap_err().reason, Reason::CapacityNegative);
        let options = [
            Json::Object(&[("selector", Json::Number("-1")), ("type", BOOLEAN)]),
            Json::Object(&[("selector", Json::Number("2")), ("type", Json::Null)]),
        ];
        let union = Json::Object(&[
            ("kind", Json::String("CompatibleUnion")), ("options", Json::Array(&options)),
        ]);
        assert_eq!(read_descriptor(&union, &mut arena).unwrap_err().reason, Reason::BadDeclaration);
        let vector = Json::Object(&[
            ("kind", Json::String("Vector")), ("length", Json::Number("-1")), ("elementType", Json::Null),
        ]);
        assert_eq!(read_descriptor(&vector, &mut arena).unwrap_err().reason, Reason::BadDeclaration);
    }

    #[test]
    fn nested_aliases_and_unbounded_progressive_shapes_survive_registration() {
        let mut storage = [MaybeUninit::uninit(); 8192];
        let mut arena = Arena::new(&mut storage);
        let list = Json::Object(&[
            ("kind", Json::String("ProgressiveList")), ("elementType", BYTE),
        ]);
        let fields = [
            Json::Object(&[("name", Json::String("bytes")), ("type", list)]),
            Json::Object(&[("name", Json::String("bit")), ("type", BOOLEAN)]),
        ];
        let layout = [Json::Number("0.1"), Json::Bool(false), Json::Bool(true)];
        let container = Json::Object(&[
            ("kind", Json::String("ProgressiveContainer")),
            ("activeFields", Json::Array(&layout)), ("fields", Json::Array(&fields)),
        ]);
        let (Desc::ProgressiveContainer { active, fields }, Spelling::Plain(spellings)) =
            read_descriptor(&container, &mut arena).unwrap() else { panic!("wrong container shape"); };
        assert_eq!(active, &[true, false, true]);
        assert_eq!(fields[0].name, "bytes");
        assert_eq!(fields[1].name, "bit");
        assert!(matches!(fields[0].desc, Desc::ProgressiveList(Desc::Uint(Nat::Small(1)), None)));
        assert!(matches!(spellings[0], Spelling::Plain([Spelling::Byte])));
        assert!(matches!(spellings[1], Spelling::Plain([])));
    }

    #[test]
    fn registration_leaves_schema_validation_separate() {
        let mut storage = [MaybeUninit::uninit(); 8192];
        let mut arena = Arena::new(&mut storage);
        let uint = Json::Object(&[("kind", Json::String("Uint999")), ("bits", Json::Number("24"))]);
        let (desc, _) = read_descriptor(&uint, &mut arena).unwrap();
        assert!(matches!(desc, Desc::Uint(Nat::Small(3))));
        assert_eq!(crate::schema::validate(&desc, &mut arena), Err(Error::one(Reason::UintWidth, Nat::Small(3))));
        let odd = Json::Object(&[("kind", Json::String("Uint8")), ("bits", Json::Number("9"))]);
        assert_eq!(read_descriptor(&odd, &mut arena).unwrap_err(), Error::one(Reason::UintWidth, Nat::Small(9)));
        let empty = Json::Object(&[("kind", Json::String("ByteVector")), ("length", Json::Number("0"))]);
        let (desc, _) = read_descriptor(&empty, &mut arena).unwrap();
        assert_eq!(crate::schema::validate(&desc, &mut arena), Err(Error::new(Reason::VectorEmpty)));
    }

    #[test]
    fn paths_keep_named_positions_and_mixin_transitions() {
        use crate::types::PathStep;

        let mut storage = [MaybeUninit::uninit(); 8192];
        let mut arena = Arena::new(&mut storage);
        let boolean = Desc::Bool;
        let list = Desc::List(&boolean, Nat::Small(8));
        let fields = [Field { name: "items", desc: &list }];
        let desc = Desc::Container(&fields);
        let steps = [
            Json::String("items"),
            Json::Object(&[("mixin", Json::String("__len__"))]),
            Json::String("past the mixin"),
        ];
        assert_eq!(
            read_path(&desc, &Json::Array(&steps), false, &mut arena).unwrap(),
            &[PathStep::Position(Nat::ZERO), PathStep::Length, PathStep::Position(Nat::ZERO)],
        );
        let proof_steps = [
            Json::Object(&[("field", Json::String("items")), ("position", Json::Number("-1"))]),
            Json::Object(&[("position", Json::Number("3"))]),
        ];
        assert_eq!(
            read_path(&desc, &Json::Array(&proof_steps), true, &mut arena).unwrap(),
            &[PathStep::Position(Nat::ZERO), PathStep::Position(Nat::Small(3))],
        );
        let missing = [Json::String("absent")];
        assert_eq!(
            read_path(&desc, &Json::Array(&missing), false, &mut arena),
            Err(Error::one(Reason::NoSuchField, Nat::ZERO)),
        );
        assert_eq!(
            read_path(&boolean, &Json::Array(&missing), false, &mut arena),
            Err(Error::new(Reason::NotAPosition)),
        );
    }

    #[test]
    fn path_syntax_is_parsed_before_semantic_refusal() {
        let mut storage = [MaybeUninit::uninit(); 8192];
        let mut arena = Arena::new(&mut storage);
        let desc = Desc::Bool;
        let bad_syntax = [
            Json::Object(&[("mixin", Json::String("unknown"))]),
            Json::Null,
        ];
        assert_eq!(
            read_path(&desc, &Json::Array(&bad_syntax), false, &mut arena),
            Err(Error::new(Reason::BadRepresentation)),
        );
        let unknown_word = [Json::Object(&[("mixin", Json::String("unknown"))])];
        assert_eq!(
            read_path(&desc, &Json::Array(&unknown_word), false, &mut arena),
            Err(Error::new(Reason::NoMixin)),
        );
        let negative = [Json::Number("-1")];
        assert_eq!(
            read_path(&desc, &Json::Array(&negative), false, &mut arena),
            Err(Error::one(Reason::NoSuchPosition, Nat::ZERO)),
        );
        let negative_proof = [Json::Object(&[("position", Json::Number("-1"))])];
        assert_eq!(
            read_path(&desc, &Json::Array(&negative_proof), true, &mut arena),
            Err(Error::new(Reason::BadRepresentation)),
        );
        let fractional = [Json::Number("1.0")];
        assert_eq!(
            read_path(&desc, &Json::Array(&fractional), false, &mut arena),
            Err(Error::new(Reason::BadRepresentation)),
        );
    }

    #[test]
    fn failed_shape_steps_leave_later_names_for_index_validation() {
        use crate::types::PathStep;

        let mut storage = [MaybeUninit::uninit(); 8192];
        let mut arena = Arena::new(&mut storage);
        let boolean = Desc::Bool;
        let desc = Desc::Vector(&boolean, Nat::ONE);
        let steps = [Json::Number("4"), Json::String("no shape left")];
        let path = read_path(&desc, &Json::Array(&steps), false, &mut arena).unwrap();
        assert_eq!(path, &[PathStep::Position(Nat::Small(4)), PathStep::Position(Nat::ZERO)]);
        assert_eq!(
            crate::indices::generalized_index(&desc, path, &mut arena),
            Err(Error::one(Reason::NoSuchPosition, Nat::Small(4))),
        );
    }
}
