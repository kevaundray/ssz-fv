"""Extract and validate the shipped SHA code/data closure before ISA binding."""
import ast
import hashlib
import json

from decoder_binding import FUNCTIONS, extract, linked_span, output
from native_build import ROOT


PINS = {
    "x86": (0x212B20, -912, 128911,
            "5acfabb572ac1fe85ff057546fb6f0307aeb444da411da182486dbba07917a51",
            "b248dc02d8530d0431cdbde7e2ee5c3771c1a8d9af1075e10d0b6d730a6f2830",
            -74056, -74024),
    "arm": (0x22BE24, -1800, 138792,
            "896ee2876ae41bc9d205158d70de2d79c4d38e4cfe87a895b011e8d2958d1459",
            "5e9905407a37f19ea643b03e90098a0cc0008051f4d892a60e4115f955393b8a",
            -178684, -178652),
}
TABLES = (
    ("initial", ".61", 32, "5a33fcfec23c49d91bcf58ce2472dc9f3662cd086bd29fc44af2e14567238a30"),
    ("rounds", ".66", 256, "74ef7306e7452d6859b6463ce496b8df30925f69e1b2969e1f3f34bbc9c6af04"),
)


def validate(arch, image):
    root, origin, size, span_digest, body_digest, initial, rounds = PINS[arch]
    span = bytes.fromhex(image["span"])
    if (image["root_address"], image["origin"], len(span)) != (root, origin, size):
        raise ValueError("SHA linked-image extent changed")
    if hashlib.sha256(span).hexdigest() != span_digest or image["sha256"] != span_digest:
        raise ValueError("SHA linked-image bytes changed")
    metadata = json.dumps(image["bodies"], sort_keys=True, separators=(",", ":")).encode()
    if hashlib.sha256(metadata).hexdigest() != body_digest:
        raise ValueError("SHA instruction/callee/frontier metadata changed")
    for body in image["bodies"].values():
        raw = bytes.fromhex(body["raw"])
        start = body["offset"] - origin
        if start < 0 or span[start:start + len(raw)] != raw:
            raise ValueError("SHA body does not match linked bytes")
    if set(image["tables"]) != {"initial", "rounds"}:
        raise ValueError("SHA table set changed")
    for (name, _, length, digest), offset in zip(TABLES, (initial, rounds)):
        table = image["tables"][name]
        raw = bytes.fromhex(table["raw"])
        if (table["offset"], len(raw), table["sha256"], hashlib.sha256(raw).hexdigest()) != (
                offset, length, digest, digest):
            raise ValueError(f"SHA {name} table bytes/address changed")


def extract_image(temp, arch):
    bodies = {}
    for key in ("sha_compress", "memcpy", "memset", "sha_finalize", "sha_combine"):
        calls = {
            "sha_finalize": ("sha_compress", "memset"),
            "sha_combine": ("sha_compress", "sha_finalize", "memcpy"),
        }.get(key, ())
        terminals = (".LBB68_5", ".LBB68_6") if key == "sha_finalize" else ()
        bodies[key] = extract(temp, arch, key, [(FUNCTIONS[key][arch], 0)], terminals,
                              [FUNCTIONS[child][arch] for child in calls])
    elf_path = temp / f"{arch}.elf"
    symbols = {parts[-1]: parts for line in output(
        "llvm-nm-18", "-S", "--defined-only", str(elf_path)).splitlines()
        if (parts := line.split())}
    root = int(symbols[FUNCTIONS["sha_combine"][arch]][0], 16)
    closure, serialized = {}, {}
    for key, body in bodies.items():
        symbol = FUNCTIONS[key][arch]
        offset = int(symbols[symbol][0], 16) - root
        serialized[key] = dict(symbol=symbol, offset=offset, rows=body[0], entries=body[1],
                               raw=body[2].hex(), frontiers=body[3], callees=body[4])
        if key != "sha_combine":
            closure[symbol] = dict(offset=offset, size=len(body[2]), raw=body[2].hex())
    origin, span = linked_span(temp, arch, "sha_combine", bodies["sha_combine"][2], closure)
    headers = json.loads(output("llvm-readobj-18", "--sections", "--elf-output-style=JSON", str(elf_path)))
    elf = elf_path.read_bytes()
    assembly = (ROOT / "asm" / arch / "ssz.s").read_text()
    stem = ".Lanon." + ("5e4d147869fa0e69eb158a9b4d00cf49" if arch == "x86" else
                       "e5114a71975970376d7771b3050001c4")
    tables = {}
    for name, suffix, size, _ in TABLES:
        symbol = stem + suffix
        declaration = assembly.split("\n" + symbol + ":\n", 1)[1].splitlines()[0].strip()
        if not declaration.startswith(".ascii"):
            raise ValueError(f"unexpected SHA table directive: {symbol}")
        raw = ast.literal_eval("b" + declaration[len(".ascii"):].strip())
        if not isinstance(raw, bytes) or len(raw) != size:
            raise ValueError(f"unexpected SHA table size: {symbol}")
        # The linker may merge a local table symbol away. Locate its complete
        # bytes uniquely in addressed sections, checking surviving symbols too.
        matches = []
        for item in headers[0]["Sections"]:
            section = item["Section"]
            if not section["Address"]:
                continue
            data = elf[section["Offset"]:section["Offset"] + section["Size"]]
            position = data.find(raw)
            while position != -1:
                matches.append(section["Address"] + position)
                position = data.find(raw, position + 1)
        if len(matches) != 1:
            raise ValueError(f"SHA table is not uniquely linked: {symbol}: {matches}")
        address = matches[0]
        if symbol in symbols and (int(symbols[symbol][0], 16), int(symbols[symbol][1], 16)) != (address, size):
            raise ValueError(f"SHA table symbol disagrees with linked bytes: {symbol}")
        tables[name] = dict(symbol=symbol, offset=address - root, raw=raw.hex(),
                            sha256=hashlib.sha256(raw).hexdigest())
    image = dict(root_address=root, origin=origin, span=span.hex(),
                 sha256=hashlib.sha256(span).hexdigest(), bodies=serialized, tables=tables)
    validate(arch, image)
    return image


LIST_BINDING_HEADER = """
theorem boundListAppend {α : Type} {xs xs' ys ys' : List α}
    (left : xs = xs') (right : ys = ys') : xs ++ ys = xs' ++ ys' := by
  rw [left, right]
"""


def list_binding(name, element_type, source, values, chunk_size=32):
    """Prove a flat literal equals a model list without unbounded kernel reduction."""
    def appended(names):
        result = names[-1]
        for part in reversed(names[:-1]):
            result = f"({part} ++ {result})"
        return result

    parts = [values[i:i + chunk_size] for i in range(0, len(values), chunk_size)]
    chunks = [f"{name}Part{i}" for i in range(len(parts))]
    tails = [f"{name}Tail{i}" for i in range(len(parts))]
    declarations = []
    for index, (chunk, tail, values_part) in enumerate(zip(chunks, tails, parts)):
        previous = source if index == 0 else f"{tails[index - 1]}.drop {len(parts[index - 1])}"
        declarations.append(f"""
def {chunk} : List {element_type} := [{', '.join(values_part)}]
def {tail} : List {element_type} := {previous}
theorem {tail}_head : {tail}.take {len(values_part)} = {chunk} := by decide
""")
    for index in reversed(range(len(parts))):
        tail, size = tails[index], len(parts[index])
        if index + 1 < len(parts):
            proof = f"boundListAppend {tail}_head {tails[index + 1]}_eq"
        else:
            proof = (f"(boundListAppend {tail}_head "
                     f"(show {tail}.drop {size} = [] from by decide)).trans (List.append_nil _)")
        declarations.append(f"""
theorem {tail}_eq : {tail} = {appended(chunks[index:])} :=
  (List.take_append_drop {size} {tail}).symm.trans ({proof})
""")
    declarations.append(f"""
def {name} : List {element_type} := {appended(chunks)}
theorem {name}_eq : {name} = {source} := {tails[0]}_eq.symm
""")
    return declarations, chunks
