"""Bind complete recursive codec instruction inventories to pinned linked bytes.

Image equality is not a reachability or execution proof. The two retained x86
DIV instructions are real fault boundaries, never replacement no-ops.
"""
import hashlib
import json
import re

from decoder_binding import FUNCTIONS, extract, output

NAMES = ('serialize', 'measure', 'emit', 'deserialize', 'measure_parts', 'measure_child', 'emit_parts', 'is_fixed', 'measure_fixed', 'decode_fixed', 'decode_offsets', 'decode_list', 'read_offset', 'bounded', 'nat_cmp_usize', 'plan_singleton', 'decode_struct_values')

PINS = {
    "x86": "fecbe58981c7313ef3f4be22a38d4527b950a563ea9215440a0047db9db2b406",
    "arm": "2562844dc215aa224bb26fd0b8ba7f3c62d694fa9539fb061bd94f72d5e66a99"
}

TABLES = (
    ("measure", ".LJTI83_0", 13),
    ("emit", ".LJTI84_0", 4),
    ("emit", ".LJTI84_1", 5),
    ("deserialize", ".LJTI93_0", 13),
    ("is_fixed", ".LJTI86_0", 12),
    ("measure_fixed", ".LJTI99_0", 12),
)
FAULTS = {1195: ("49f7f1", "divq"), 1316: ("41f7f1", "divl")}


def extract_image(temp, arch):
    """Link once and retain every instruction, constant section and symbol."""
    if arch not in PINS:
        raise ValueError(f"Unsupported architecture: {arch}")
    extract(temp, arch, 'serialize', ())
    image = temp / f'{arch}.elf'
    symbols = [line.split() for line in output('llvm-nm-18', '-S', '--defined-only', str(image)).splitlines()]
    def unique(name):
        matches = [row for row in symbols if row[-1] == name]
        if len(matches) != 1:
            raise ValueError((arch, name, matches))
        return matches[0]
    headers = json.loads(output('llvm-readobj-18', '--sections', '--elf-output-style=JSON', str(image)))[0]['Sections']
    text_headers = [row['Section'] for row in headers if row['Section']['Name']['Name'] == '.text']
    if len(text_headers) != 1:
        raise ValueError('Ambiguous .text')
    text_base = text_headers[0]['Address']
    text_bytes = (temp / f'{arch}.bin').read_bytes()
    functions = {}
    known = {int(unique(symbols_by_arch[arch])[0], 16): name for name, symbols_by_arch in FUNCTIONS.items()}
    for name in NAMES:
        symbol = FUNCTIONS[name][arch]
        row = unique(symbol)
        if len(row) != 4 or row[-2] not in ('t', 'T'):
            raise ValueError(('Not a sized function', row))
        start, size = int(row[0], 16), int(row[1], 16)
        raw = text_bytes[start-text_base:start-text_base+size]
        if size <= 0 or len(raw) != size:
            raise ValueError(('Invalid function extent', name))
        extent = [f'--start-address={start}', f'--stop-address={start+size}']
        if arch == 'x86':
            disassembly = output('objdump', '-d', '-M', 'att,suffix', '--insn-width=15', '--disassemble-zeroes', *extent, str(image))
            pattern = r'\s*([0-9a-f]+):\s+((?:[0-9a-f]{2}\s+)+)(\S.*)'
        else:
            disassembly = output('llvm-objdump-18', '-d', '--disassemble-zeroes', *extent, str(image))
            pattern = r'\s*([0-9a-f]+):\s+([0-9a-f]{8})\s+(\S.*)'
        instructions, end = [], 0
        for line in disassembly.splitlines():
            if not re.match(r'\s*[0-9a-f]+:', line):
                continue
            match = re.fullmatch(pattern, line)
            if match is None:
                raise ValueError(('Unparsed instruction', line))
            pc = int(match[1], 16)-start
            encoded = bytes.fromhex(match[2]) if arch == 'x86' else int(match[2], 16).to_bytes(4, 'little')
            if pc != end or raw[pc:pc+len(encoded)] != encoded:
                raise ValueError(('Instruction extent mismatch', name, pc))
            instruction = {'pc': pc, 'width': len(encoded), 'encoding': match[2].strip(), 'asm': match[3].strip()}
            parts = instruction['asm'].split(None, 1)
            opcode, operands = parts[0], parts[1] if len(parts)>1 else ''
            if opcode == 'addr32':
                parts = operands.split(None, 1)
                opcode, operands = parts[0], parts[1] if len(parts)>1 else ''
            branch = opcode.startswith('j') if arch == 'x86' else opcode == 'b' or opcode.startswith('b.') or opcode in ('cbz','cbnz','tbz','tbnz')
            call = opcode.startswith('call') if arch == 'x86' else opcode == 'bl'
            if branch or call:
                target = re.search(r'(?:^|,\s*)(?:0x)?([0-9a-f]+)\s*(?:<|$)', operands)
                if target is None:
                    instruction['indirect'] = True
                else:
                    address = int(target[1], 16)
                    instruction['target'] = address-start
                    instruction['targetAddress'] = address
                    if address in known:
                        instruction['callee'] = known[address]
                    instruction['targetSymbols'] = [entry[-1] for entry in symbols if int(entry[0],16)==address]
            instructions.append(instruction)
            end += len(encoded)
        if end != size:
            raise ValueError(('Incomplete disassembly', name, end, size))
        functions[name] = {'symbol': symbol, 'address': start, 'offset': start-text_base, 'size': size, 'raw': raw.hex(), 'rows': instructions}
    constants = {}
    for wrapped in headers:
        section = wrapped['Section']
        name = section['Name']['Name']
        if name not in ('.rodata', '.data.rel.ro', '.data') or section['Size'] == 0:
            continue
        path = temp / f'{arch}-{name[1:]}.bin'
        output('llvm-objcopy-18', f'--dump-section={name}={path}', str(image), str(temp/f'{arch}-constant-copy.elf'))
        raw = path.read_bytes()
        if len(raw) != section['Size']:
            raise ValueError(('Constant extent mismatch', name))
        constants[name] = {'address': section['Address'], 'raw': raw.hex()}
    return {'textAddress': text_base, 'textRaw': text_bytes.hex(), 'functions': functions, 'constants': constants, 'symbols': [{'address': int(row[0],16), 'name': row[-1]} for row in symbols]}


def selected_rows(arch, name, body):
    """Exclude only the two byte-pinned original DIV fault instructions."""
    if arch not in PINS:
        raise ValueError(f"Unsupported architecture: {arch}")
    if arch != "x86" or name != "decode_list":
        return body["rows"]
    found, selected = set(), []
    for row in body["rows"]:
        if row["pc"] in FAULTS:
            encoded, opcode = FAULTS[row["pc"]]
            if (bytes.fromhex(row["encoding"]).hex(), row["asm"].split()[0]) != (encoded, opcode):
                raise ValueError("Original DIV fault boundary changed")
            found.add(row["pc"])
        else:
            selected.append(row)
    if found != FAULTS.keys():
        raise ValueError("Original DIV fault boundary missing")
    return selected


def dispatch_tables(image):
    """Read the six signed x86 jump tables at their actual symbol addresses."""
    result = {}
    for function, symbol, count in TABLES:
        matches = [item for item in image["symbols"] if item["name"] == symbol]
        if len(matches) != 1:
            raise ValueError(f"Missing/ambiguous dispatch symbol: {symbol}")
        address = matches[0]["address"]
        matches = []
        for section in image["constants"].values():
            raw = bytes.fromhex(section["raw"])
            offset = address - section["address"]
            if 0 <= offset and offset + count * 4 <= len(raw):
                matches.append(raw[offset:offset + count * 4])
        if len(matches) != 1:
            raise ValueError(f"Dispatch table is outside one constant section: {symbol}")
        raw = matches[0]
        displacements = [int.from_bytes(raw[pos:pos+4], "little", signed=True)
                         for pos in range(0, len(raw), 4)]
        body = image["functions"][function]
        targets = [address + displacement - body["address"] for displacement in displacements]
        boundaries = {row["pc"] for row in body["rows"]}
        if any(target not in boundaries for target in targets):
            raise ValueError(f"Dispatch target is not an instruction boundary: {symbol}")
        result[symbol] = {"function": function, "address": address, "raw": raw.hex(),
                          "displacements": displacements, "targets": targets}
    return result


def validate(arch, image):
    """Reject any changed byte, address, instruction, callee or symbol metadata."""
    if arch not in PINS:
        raise ValueError(f"Unsupported architecture: {arch}")
    metadata = json.dumps(image, sort_keys=True, separators=(",", ":")).encode()
    if hashlib.sha256(metadata).hexdigest() != PINS[arch]:
        raise ValueError("Recursive codec linked bytes or metadata changed")
    if set(image["functions"]) != set(NAMES):
        raise ValueError("Recursive codec function inventory changed")
    text = bytes.fromhex(image["textRaw"])
    for name, body in image["functions"].items():
        raw = bytes.fromhex(body["raw"])
        offset = body["address"] - image["textAddress"]
        if offset < 0 or offset != body["offset"] or len(raw) != body["size"] or text[offset:offset+len(raw)] != raw:
            raise ValueError(f"Recursive codec function extent changed: {name}")
        end = 0
        for row in body["rows"]:
            encoded = (bytes.fromhex(row["encoding"]) if arch == "x86"
                       else int(row["encoding"], 16).to_bytes(4, "little"))
            if row["pc"] != end or len(encoded) != row["width"] or raw[end:end+len(encoded)] != encoded:
                raise ValueError(f"Recursive codec instruction extent changed: {name}/{end}")
            if "targetAddress" in row and row["targetAddress"] != body["address"] + row["target"]:
                raise ValueError("Recursive codec direct-target address changed")
            end += len(encoded)
        if end != len(raw):
            raise ValueError(f"Incomplete recursive codec function: {name}")
        selected_rows(arch, name, body)
    if arch == "x86":
        dispatch_tables(image)
