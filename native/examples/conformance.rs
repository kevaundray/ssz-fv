//! Execute the candidate native implementation against all six upstream formats.
//! std/serde allocations belong to this test driver, not the no_std SSZ library.
use std::{collections::BTreeMap, fs, mem::MaybeUninit, path::{Path, PathBuf}};
use ssz_fv_native as ssz;
use ssz::{Arena, Desc, Json, Nat, Value};

type Check<T> = std::result::Result<T, String>;

fn native<T>(what: &str, result: ssz::Result<'_, T>) -> Check<T> {
    result.map_err(|e| format!("{what}: {} {:?}", e.reason.as_str(), e.args))
}

fn lift<'a>(input: &'a serde_json::Value, arena: &mut Arena<'a>) -> Check<Json<'a>> {
    Ok(match input {
        serde_json::Value::Null => Json::Null,
        serde_json::Value::Bool(b) => Json::Bool(*b),
        serde_json::Value::Number(n) => Json::Number(native("number storage", arena.utf8(&n.to_string()))?),
        serde_json::Value::String(s) => Json::String(s),
        serde_json::Value::Array(items) => {
            let values = native("array storage", arena.mutable_slice(items.len(), Json::Null))?;
            for (out, item) in values.iter_mut().zip(items) { *out = lift(item, arena)?; }
            Json::Array(values)
        }
        serde_json::Value::Object(object) => {
            let pairs = native("object storage", arena.mutable_slice(object.len(), ("", Json::Null)))?;
            for (out, (name, value)) in pairs.iter_mut().zip(object) { *out = (name.as_str(), lift(value, arena)?); }
            Json::Object(pairs)
        }
    })
}

fn optional<'a>(object: &Json<'a>, name: &str) -> Option<Json<'a>> {
    match object {
        Json::Object(pairs) => pairs.iter().rev().find(|(key, _)| *key == name).map(|(_, value)| *value),
        _ => None,
    }
}
fn field<'a>(object: &Json<'a>, name: &str) -> Check<Json<'a>> {
    optional(object, name).ok_or_else(|| format!("missing fixture field {name}"))
}
fn text(value: Json<'_>) -> Check<&str> {
    match value { Json::String(s) => Ok(s), _ => Err("expected fixture string".into()) }
}
fn entries<'a>(value: Json<'a>) -> Check<&'a [Json<'a>]> {
    match value { Json::Array(items) => Ok(items), _ => Err("expected fixture array".into()) }
}
fn boolean(value: Json<'_>) -> Check<bool> {
    match value { Json::Bool(b) => Ok(b), _ => Err("expected fixture boolean".into()) }
}

// Decode oracle bytes independently of the candidate's SSZ JSON/hex helpers.
fn oracle_hex<'a>(value: Json<'a>, arena: &mut Arena<'a>) -> Check<&'a [u8]> {
    let source = text(value)?.strip_prefix("0x").ok_or("fixture hex lacks prefix")?;
    if source.len() % 2 != 0 || !source.is_ascii() { return Err("invalid fixture hex".into()); }
    let bytes: Check<Vec<u8>> = (0..source.len()).step_by(2).map(|i|
        u8::from_str_radix(&source[i..i+2], 16).map_err(|e| e.to_string())).collect();
    native("oracle byte storage", arena.copy(&bytes?))
}
fn hex_field<'a>(object: &Json<'a>, name: &str, arena: &mut Arena<'a>) -> Check<&'a [u8]> {
    oracle_hex(field(object, name)?, arena)
}
fn hex_list<'a>(object: &Json<'a>, name: &str, arena: &mut Arena<'a>) -> Check<&'a [&'a [u8]]> {
    let items = entries(field(object, name)?)?;
    let out = native("oracle node storage", arena.mutable_slice(items.len(), &[][..]))?;
    for (slot, item) in out.iter_mut().zip(items) { *slot = oracle_hex(*item, arena)?; }
    Ok(out)
}
fn number<'a>(value: Json<'a>, arena: &mut Arena<'a>) -> Check<Nat<'a>> {
    native("fixture number", Nat::from_decimal(text(value)?, arena))
}
fn number_field<'a>(object: &Json<'a>, name: &str, arena: &mut Arena<'a>) -> Check<Nat<'a>> {
    number(field(object, name)?, arena)
}
fn number_list<'a>(object: &Json<'a>, name: &str, arena: &mut Arena<'a>) -> Check<&'a [Nat<'a>]> {
    let items = entries(field(object, name)?)?;
    let out = native("oracle index storage", arena.mutable_slice(items.len(), Nat::ZERO))?;
    for (slot, item) in out.iter_mut().zip(items) { *slot = number(*item, arena)?; }
    Ok(out)
}
fn same_bytes(what: &str, actual: &[u8], expected: &[u8]) -> Check<()> {
    if actual == expected { Ok(()) } else { Err(format!("{what}: {actual:02x?} != {expected:02x?}")) }
}
fn same_number<'a>(what: &str, actual: Nat<'a>, expected: Json<'a>, arena: &mut Arena<'a>) -> Check<()> {
    let expected = match expected { Json::String(s) | Json::Number(s) => s, _ => return Err("expected numeric fixture claim".into()) };
    let actual = native("number rendering", actual.decimal(arena))?;
    if actual == expected { Ok(()) } else { Err(format!("{what}: {actual} != {expected}")) }
}
fn same_numbers<'a>(what: &str, actual: &[Nat<'a>], expected: Json<'a>, arena: &mut Arena<'a>) -> Check<()> {
    let expected = entries(expected)?;
    if actual.len() != expected.len() { return Err(format!("{what}: different list lengths")); }
    for (got, want) in actual.iter().zip(expected) { same_number(what, *got, *want, arena)?; }
    Ok(())
}
fn same_nodes(what: &str, actual: &[[u8; 32]], expected: &[&[u8]]) -> Check<()> {
    if actual.len() != expected.len() { return Err(format!("{what}: different node counts")); }
    for (got, want) in actual.iter().zip(expected) { same_bytes(what, got, want)?; }
    Ok(())
}
fn refused<T>(result: ssz::Result<'_, T>, expected: &str) -> Check<()> {
    match result {
        Err(error) if error.reason.as_str() == expected => Ok(()),
        Err(error) => Err(format!("refused with {}, expected {expected}", error.reason.as_str())),
        Ok(_) => Err(format!("accepted input that requires {expected}")),
    }
}
fn refusal<'a>(vector: &Json<'a>) -> Check<&'a str> { text(field(vector, "rejectionReason")?) }

fn encoded<'a>(shape: &Desc<'a>, value: &Value<'a>, expected: &[u8], arena: &mut Arena<'a>) -> Check<()> {
    let size = native("encoded size", ssz::codec::encoded_size(shape, value, arena))?;
    if size != expected.len() { return Err(format!("encoded size {size} != {}", expected.len())); }
    let mut out = vec![0xa5; size.checked_add(8).ok_or("oracle buffer overflow")?];
    // SAFETY: initialized u8 storage is also valid MaybeUninit<u8> storage.
    // Serialization only initializes bytes; it cannot invalidate the u8 buffer.
    let output = unsafe { std::slice::from_raw_parts_mut(out.as_mut_ptr().cast::<MaybeUninit<u8>>(), out.len()) };
    let written = native("encoding", ssz::codec::serialize(shape, value, output, arena))?;
    if written != size { return Err(format!("written {written} != planned {size}")); }
    same_bytes("encoding", &out[..written], expected)?;
    if out[written..].iter().any(|&b| b != 0xa5) { return Err("encoding overwrote output tail".into()); }
    Ok(())
}
fn subject<'a>(shape: &Desc<'a>, value: &Value<'a>, vector: &Json<'a>, root: &[u8], arena: &mut Arena<'a>) -> Check<()> {
    let bytes = hex_field(vector, "serialized", arena)?;
    encoded(shape, value, bytes, arena)?;
    same_bytes("root", &native("rooting", ssz::layout::hash_tree_root(shape, value, arena))?, root)
}
fn path_index<'a>(shape: &Desc<'a>, written: &Json<'a>, proof: bool, arena: &mut Arena<'a>) -> ssz::Result<'a, Nat<'a>> {
    let path = ssz::descriptor::read_path(shape, written, proof, arena)?;
    ssz::indices::generalized_index(shape, path, arena)
}

fn check_vector<'a>(format: &str, vector: &Json<'a>, arena: &mut Arena<'a>) -> Check<()> {
    let valid = boolean(field(vector, "valid")?)?;
    let descriptor = field(vector, "typeDescriptor")?;
    if format == "ssz_type_rejection" {
        return refused(ssz::descriptor::read_descriptor(&descriptor, arena)
            .and_then(|(shape, _)| ssz::schema::validate(&shape, arena)), refusal(vector)?);
    }
    let (shape, spelling) = native("declaration", ssz::descriptor::read_descriptor(&descriptor, arena))?;
    native("declaration validity", ssz::schema::validate(&shape, arena))?;
    match format {
        "ssz_test" => {
            let bytes = hex_field(vector, "serialized", arena)?;
            if !valid { return refused(ssz::codec::deserialize(&shape, bytes, arena), refusal(vector)?); }
            let value = native("value", ssz::json::value_of(&shape, spelling, &field(vector, "value")?, arena))?;
            let root = hex_field(vector, "root", arena)?;
            encoded(&shape, &value, bytes, arena)?;
            same_bytes("root", &native("rooting", ssz::layout::hash_tree_root(&shape, &value, arena))?, root)?;
            let decoded = native("decoding", ssz::codec::deserialize(&shape, bytes, arena))?;
            if decoded != value { return Err("decoded value differs from oracle value".into()); }
        }
        "ssz_gindex_test" => {
            if let Some(count) = optional(vector, "chunkCount") {
                let chunks = native("chunk count", ssz::indices::chunk_count(&shape, arena))?;
                same_number("chunk count", chunks, count, arena)?;
                let width = native("tree width", ssz::indices::next_pow2(chunks, arena))?;
                same_number("tree width", width, field(vector, "treeWidth")?, arena)?;
            }
            let resolved = path_index(&shape, &field(vector, "path")?, false, arena);
            if !valid { return refused(resolved, refusal(vector)?); }
            let index = native("path", resolved)?;
            same_number("index", index, field(vector, "gindex")?, arena)?;
            let depth = native("index depth", ssz::indices::checked_depth(index))?;
            let depth = native("depth representation", Nat::from_u128(depth, arena))?;
            same_number("depth", depth, field(vector, "depth")?, arena)?;
        }
        "ssz_json_test" => {
            let document = field(vector, "document")?;
            let parsed = ssz::json::value_of(&shape, spelling, &document, arena);
            if !valid { return refused(parsed, refusal(vector)?); }
            let value = native("JSON parsing", parsed)?;
            let written = native("JSON writing", ssz::json::json_of(&shape, spelling, &value, arena))?;
            if written != document { return Err(format!("JSON writing: {written:?} != {document:?}")); }
            let bytes = hex_field(vector, "serialized", arena)?;
            encoded(&shape, &value, bytes, arena)?;
        }
        "proof_test" => {
            let value = native("value", ssz::json::value_of(&shape, spelling, &field(vector, "value")?, arena))?;
            let root = hex_field(vector, "root", arena)?;
            let index = number_field(vector, "index", arena)?;
            subject(&shape, &value, vector, root, arena)?;
            let resolved = native("path", path_index(&shape, &field(vector, "path")?, true, arena))?;
            same_number("path index", resolved, field(vector, "index")?, arena)?;
            let Some(leaf) = optional(vector, "leaf") else {
                return refused(ssz::proof::node_root(&shape, &value, index, arena), refusal(vector)?);
            };
            let leaf = oracle_hex(leaf, arena)?;
            let branch = hex_list(vector, "branch", arena)?;
            let verified = ssz::verify::verify_merkle_proof(leaf, branch, index, root, arena);
            if let Some(reason) = optional(vector, "rejectionReason") { return refused(verified, text(reason)?); }
            if valid {
                same_bytes("node", &native("node", ssz::proof::node_root(&shape, &value, index, arena))?, leaf)?;
                let built = native("branch construction", ssz::proof::build_proof(&shape, &value, index, arena))?;
                same_nodes("branch", built, branch)?;
                let order = native("branch indices", ssz::indices::branch_indices(index, arena))?;
                same_numbers("branch order", order, field(vector, "branchIndices")?, arena)?;
            }
            if native("branch verification", verified)? != valid { return Err("wrong branch verification verdict".into()); }
        }
        "multiproof_test" => {
            let value = native("value", ssz::json::value_of(&shape, spelling, &field(vector, "value")?, arena))?;
            let root = hex_field(vector, "root", arena)?;
            let indices = number_list(vector, "indices", arena)?;
            let leaves = hex_list(vector, "leaves", arena)?;
            let supplied = hex_list(vector, "proof", arena)?;
            same_bytes("root", &native("rooting", ssz::layout::hash_tree_root(&shape, &value, arena))?, root)?;
            let paths = entries(field(vector, "paths")?)?;
            if paths.len() != indices.len() { return Err("path/index counts differ".into()); }
            for (path, expected) in paths.iter().zip(indices) {
                let got = native("path", path_index(&shape, path, true, arena))?;
                if got != *expected { return Err("multiproof path resolved to wrong index".into()); }
            }
            let verified = ssz::verify::verify_merkle_multiproof(leaves, supplied, indices, root, arena);
            if let Some(reason) = optional(vector, "rejectionReason") { return refused(verified, text(reason)?); }
            if valid {
                let built = native("multiproof construction", ssz::proof::build_multiproof(&shape, &value, indices, arena))?;
                same_nodes("multiproof", built, supplied)?;
                let order = native("helper indices", ssz::indices::helper_indices(indices, arena))?;
                same_numbers("helper order", order, field(vector, "helperIndices")?, arena)?;
            }
            if native("multiproof verification", verified)? != valid { return Err("wrong multiproof verification verdict".into()); }
        }
        _ => return Err(format!("unknown fixture format {format}")),
    }
    Ok(())
}

fn check_diff<'a>(section: &str, entry: &Json<'a>, arena: &mut Arena<'a>) -> Check<()> {
    if section == "compatible" {
        let (left, _) = native("left declaration", ssz::descriptor::read_descriptor(&field(entry, "left")?, arena))?;
        let (right, _) = native("right declaration", ssz::descriptor::read_descriptor(&field(entry, "right")?, arena))?;
        return if ssz::schema::compatible(&left, &right) == boolean(field(entry, "compatible")?)? {
            Ok(())
        } else { Err("compatibility disagrees".into()) };
    }
    let (shape, spelling) = native("declaration", ssz::descriptor::read_descriptor(&field(entry, "typeDescriptor")?, arena))?;
    let valid = ssz::schema::validate(&shape, arena);
    if valid.as_ref().is_err_and(|e| e.is_host()) {
        return native("declaration resources", valid);
    }
    if valid.is_ok() != boolean(field(entry, "wellFormed")?)? { return Err("well-formedness disagrees".into()); }
    let document = field(entry, "value")?;
    let value = native("value", ssz::json::value_of(&shape, spelling, &document, arena))?;
    if !ssz::schema::fits(&shape, &value) { return Err("oracle value does not fit declaration".into()); }
    let written = native("JSON writing", ssz::json::json_of(&shape, spelling, &value, arena))?;
    if written != document { return Err(format!("JSON writing: {written:?} != {document:?}")); }
    let root = hex_field(entry, "root", arena)?;
    subject(&shape, &value, entry, root, arena)?;
    let bytes = hex_field(entry, "serialized", arena)?;
    if native("decoding", ssz::codec::deserialize(&shape, bytes, arena))? != value {
        return Err("decoded value differs from oracle value".into());
    }
    if let Some(written) = optional(entry, "default") {
        let expected = native("oracle default", ssz::json::value_of(&shape, spelling, &written, arena))?;
        if native("default", ssz::schema::default_value(&shape, arena))? != expected {
            return Err("default disagrees".into());
        }
        if native("zero classification", ssz::schema::is_zero(&shape, &value, arena))? != (value == expected) {
            return Err("zero classification disagrees".into());
        }
    } else {
        refused(ssz::schema::default_value(&shape, arena), "WRONG_TYPE")?;
        refused(ssz::schema::is_zero(&shape, &value, arena), "WRONG_TYPE")?;
    }
    for claim in entries(field(entry, "paths")?)? {
        let resolved = path_index(&shape, &field(claim, "path")?, true, arena);
        let Some(written_index) = optional(claim, "gindex") else {
            match resolved {
                Err(error) if !error.is_host() => continue,
                Err(error) => return Err(format!("path resources: {error:?}")),
                Ok(index) => {
                    let node = ssz::proof::node_root(&shape, &value, index, arena);
                    let branch = ssz::proof::build_proof(&shape, &value, index, arena);
                    if node.as_ref().is_err_and(|e| e.is_host()) || branch.as_ref().is_err_and(|e| e.is_host()) {
                        return Err("node/proof exhausted host resources".into());
                    }
                    if node.is_ok() && branch.is_ok() { return Err("accepted a path the oracle refuses".into()); }
                    continue;
                }
            }
        };
        let index = native("path", resolved)?;
        same_number("index", index, written_index, arena)?;
        let node = native("node", ssz::proof::node_root(&shape, &value, index, arena))?;
        same_bytes("node", &node, hex_field(claim, "node", arena)?)?;
        let branch = native("branch", ssz::proof::build_proof(&shape, &value, index, arena))?;
        let expected_branch = hex_list(claim, "proof", arena)?;
        same_nodes("branch", branch, expected_branch)?;
        if !native("branch verification", ssz::verify::verify_merkle_proof(&node, expected_branch, index, root, arena))? {
            return Err("oracle branch does not verify".into());
        }
    }
    if let Some(claim) = optional(entry, "multiproof") {
        let indices = number_list(&claim, "indices", arena)?;
        let expected = hex_list(&claim, "proof", arena)?;
        let built = native("multiproof", ssz::proof::build_multiproof(&shape, &value, indices, arena))?;
        same_nodes("multiproof", built, expected)?;
        let leaves = native("leaf storage", arena.mutable_slice(indices.len(), &[][..]))?;
        for (leaf, index) in leaves.iter_mut().zip(indices) {
            let node = native("node", ssz::proof::node_root(&shape, &value, *index, arena))?;
            *leaf = native("node storage", arena.copy(&node))?;
        }
        if !native("multiproof verification", ssz::verify::verify_merkle_multiproof(leaves, expected, indices, root, arena))? {
            return Err("oracle multiproof does not verify".into());
        }
    }
    Ok(())
}

fn run_diff(path: &Path, scratch: usize) -> Check<()> {
    let document: serde_json::Value = serde_json::from_slice(&fs::read(path).map_err(|e| e.to_string())?)
        .map_err(|e| e.to_string())?;
    let mut passed = 0usize;
    let mut failed = 0usize;
    for section in ["cases", "compatible"] {
        let Some(entries) = document.get(section) else { continue };
        for entry in entries.as_array().ok_or("differential section is not an array")? {
            let mut storage = vec![MaybeUninit::<u8>::uninit(); scratch];
            let mut arena = Arena::new(&mut storage);
            let lifted = lift(entry, &mut arena)?;
            match check_diff(section, &lifted, &mut arena) {
                Ok(()) => passed += 1,
                Err(error) => {
                    failed += 1;
                    eprintln!("{section} {}: {error}", entry.get("name").and_then(|x| x.as_str()).unwrap_or("?"));
                }
            }
        }
    }
    println!("native SSZ differential: {passed} passed, {failed} failed");
    if failed == 0 && passed != 0 { Ok(()) } else { Err("native differential conformance failed or corpus empty".into()) }
}

fn walk(path: &Path, files: &mut Vec<PathBuf>) -> Check<()> {
    for entry in fs::read_dir(path).map_err(|e| e.to_string())? {
        let path = entry.map_err(|e| e.to_string())?.path();
        if path.is_dir() { walk(&path, files)?; }
        else if path.extension().is_some_and(|x| x == "json")
            && !matches!(path.file_name().and_then(|x| x.to_str()), Some("manifest.json" | "index.json")) {
            files.push(path);
        }
    }
    Ok(())
}

fn run() -> Check<()> {
    let mut args = std::env::args().skip(1);
    let first = args.next().ok_or("usage: conformance [--diff] FIXTURES_OR_CORPUS [SCRATCH_BYTES]")?;
    let differential = first == "--diff";
    let root = PathBuf::from(if differential { args.next().ok_or("--diff requires a corpus")? } else { first });
    let scratch: usize = args.next().map(|s| s.parse().map_err(|e| format!("invalid scratch bytes: {e}")))
        .transpose()?.unwrap_or(32 * 1024 * 1024);
    if args.next().is_some() { return Err("too many arguments".into()); }
    if differential { return run_diff(&root, scratch); }
    let manifest: serde_json::Value = serde_json::from_slice(&fs::read(root.join("manifest.json")).map_err(|e| e.to_string())?)
        .map_err(|e| e.to_string())?;
    let declared = manifest.get("caseCount").and_then(|v| v.as_u64()).ok_or("invalid manifest caseCount")?;
    let mut files = Vec::new();
    walk(&root, &mut files)?;
    files.sort();
    if files.len() as u64 != declared { return Err(format!("found {} cases; manifest declares {declared}", files.len())); }
    let mut passed = 0usize;
    let mut failures = 0usize;
    let mut formats = BTreeMap::<String, usize>::new();
    for path in files {
        let result = (|| -> Check<String> {
            let document: serde_json::Value = serde_json::from_slice(&fs::read(&path).map_err(|e| e.to_string())?)
                .map_err(|e| e.to_string())?;
            let format = document.get("_info").and_then(|v| v.get("fixtureFormat"))
                .and_then(|v| v.as_str()).ok_or("missing fixture format")?.to_owned();
            let mut storage = vec![MaybeUninit::<u8>::uninit(); scratch];
            let mut arena = Arena::new(&mut storage);
            let lifted = lift(&document, &mut arena)?;
            check_vector(&format, &lifted, &mut arena)?;
            Ok(format)
        })();
        match result {
            Ok(format) => { passed += 1; *formats.entry(format).or_default() += 1; }
            Err(error) => { failures += 1; eprintln!("{}: {error}", path.display()); }
        }
    }
    for (format, count) in formats { println!("{format}: {count} passed"); }
    println!("native SSZ candidate: {passed} passed, {failures} failed (manifest {declared})");
    if failures == 0 { Ok(()) } else { Err("native conformance failed".into()) }
}

fn main() {
    if let Err(error) = run() { eprintln!("{error}"); std::process::exit(1); }
}
