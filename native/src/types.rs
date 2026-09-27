use crate::Nat;

macro_rules! reasons {
    ($($name:ident = $code:expr => $label:literal),+ $(,)?) => {
        #[repr(u32)]
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub enum Reason { $($name = $code),+ }
        impl Reason {
            pub const fn as_str(self) -> &'static str {
                match self { $(Self::$name => $label),+ }
            }
        }
    };
}

reasons! {
    WrongType = 1 => "WRONG_TYPE",
    Limit = 2 => "LIMIT",
    Scope = 3 => "SCOPE",
    ScopeTooSmall = 4 => "SCOPE_TOO_SMALL",
    ScopeUndivided = 5 => "SCOPE_UNDIVIDED",
    ScopeWidthless = 6 => "SCOPE_WIDTHLESS",
    FirstOffset = 7 => "FIRST_OFFSET",
    OffsetUnordered = 8 => "OFFSET_UNORDERED",
    OffsetPastScope = 9 => "OFFSET_PAST_SCOPE",
    OffsetUnaligned = 10 => "OFFSET_UNALIGNED",
    OffsetBelowTable = 11 => "OFFSET_BELOW_TABLE",
    Truncated = 12 => "TRUNCATED",
    NotABit = 13 => "NOT_A_BIT",
    Count = 14 => "COUNT",
    PaddingBits = 15 => "PADDING_BITS",
    EmptyEncoding = 16 => "EMPTY_ENCODING",
    NoDelimiter = 17 => "NO_DELIMITER",
    TrailingZeros = 18 => "TRAILING_ZEROS",
    NoSelector = 19 => "NO_SELECTOR",
    UnknownSelector = 20 => "UNKNOWN_SELECTOR",
    OffsetOverflow = 21 => "OFFSET_OVERFLOW",
    BadDeclaration = 22 => "BAD_DECLARATION",
    NotAPosition = 23 => "NOT_A_POSITION",
    NotEntitled = 24 => "NOT_ENTITLED",
    Undeclared = 25 => "UNDECLARED",
    CapacityNegative = 26 => "CAPACITY_NEGATIVE",
    LayoutNotBits = 27 => "LAYOUT_NOT_BITS",
    VectorEmpty = 28 => "VECTOR_EMPTY",
    LayoutWidth = 29 => "LAYOUT_WIDTH",
    LayoutTrailingGap = 30 => "LAYOUT_TRAILING_GAP",
    LayoutTooWide = 31 => "LAYOUT_TOO_WIDE",
    LayoutFieldCount = 32 => "LAYOUT_FIELD_COUNT",
    UnionEmpty = 33 => "UNION_EMPTY",
    UnionSelectorRange = 34 => "UNION_SELECTOR_RANGE",
    UnionIncompatible = 35 => "UNION_INCOMPATIBLE",
    UnionSelectorRepeated = 36 => "UNION_SELECTOR_REPEATED",
    UintWidth = 37 => "UINT_WIDTH",
    ContainerEmpty = 38 => "CONTAINER_EMPTY",
    NotAGindex = 39 => "NOT_A_GINDEX",
    RootHasNoBranch = 40 => "ROOT_HAS_NO_BRANCH",
    EmptyRequest = 41 => "EMPTY_REQUEST",
    RepeatedIndex = 42 => "REPEATED_INDEX",
    NestedIndex = 43 => "NESTED_INDEX",
    BranchLength = 44 => "BRANCH_LENGTH",
    LeafCount = 45 => "LEAF_COUNT",
    ProofLength = 46 => "PROOF_LENGTH",
    ProofIncomplete = 47 => "PROOF_INCOMPLETE",
    PathIntoMixin = 48 => "PATH_INTO_MIXIN",
    PathIntoPacked = 49 => "PATH_INTO_PACKED",
    PathIntoGap = 50 => "PATH_INTO_GAP",
    PathPastSpine = 51 => "PATH_PAST_SPINE",
    NoParts = 52 => "NO_PARTS",
    NoPartsMixin = 53 => "NO_PARTS_MIXIN",
    NoMixin = 54 => "NO_MIXIN",
    NoChunkCount = 55 => "NO_CHUNK_COUNT",
    NotSteppable = 56 => "NOT_STEPPABLE",
    NoSuchField = 57 => "NO_SUCH_FIELD",
    NoSuchOption = 58 => "NO_SUCH_OPTION",
    NoSuchPosition = 59 => "NO_SUCH_POSITION",
    MerkleizeLimit = 60 => "MERKLEIZE_LIMIT",
    ZeroTreeWidth = 61 => "ZERO_TREE_WIDTH",
    HexPrefix = 62 => "HEX_PREFIX",
    HexDigits = 63 => "HEX_DIGITS",
    HexLength = 64 => "HEX_LENGTH",
    BitfieldPadding = 65 => "BITFIELD_PADDING",
    BitfieldDelimiter = 66 => "BITFIELD_DELIMITER",
    BitfieldTrailingZeros = 67 => "BITFIELD_TRAILING_ZEROS",
    UintRange = 68 => "UINT_RANGE",
    OverLimit = 69 => "OVER_LIMIT",
    ElementKind = 70 => "ELEMENT_KIND",
    NoDefault = 71 => "NO_DEFAULT",
    UndeclaredField = 72 => "UNDECLARED_FIELD",
    MissingField = 73 => "MISSING_FIELD",
    StructNotAnObject = 74 => "STRUCT_NOT_AN_OBJECT",
    UndeclaredSelector = 75 => "UNDECLARED_SELECTOR",
    ScratchExhausted = 0x8000 => "HOST_SCRATCH_EXHAUSTED",
    OutputTooSmall = 0x8001 => "HOST_OUTPUT_TOO_SMALL",
    BadRepresentation = 0x8002 => "HOST_BAD_REPRESENTATION"
}

/// Semantic failures preserve the upstream reason and natural-number payloads.
/// HOST_* failures describe native resources/representation, never SSZ refusal.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Error<'a> {
    pub reason: Reason,
    pub args: [Nat<'a>; 3],
    pub text: &'a str,
}

impl<'a> Error<'a> {
    pub const fn new(reason: Reason) -> Self {
        Self { reason, args: [Nat::ZERO; 3], text: "" }
    }
    pub const fn one(reason: Reason, first: Nat<'a>) -> Self {
        Self { reason, args: [first, Nat::ZERO, Nat::ZERO], text: "" }
    }
    pub const fn two(reason: Reason, first: Nat<'a>, second: Nat<'a>) -> Self {
        Self { reason, args: [first, second, Nat::ZERO], text: "" }
    }
    pub const fn three(reason: Reason, a: Nat<'a>, b: Nat<'a>, c: Nat<'a>) -> Self {
        Self { reason, args: [a, b, c], text: "" }
    }
    pub const fn named(reason: Reason, text: &'a str) -> Self {
        Self { reason, args: [Nat::ZERO; 3], text }
    }
    pub const fn is_host(self) -> bool { self.reason as u32 >= 0x8000 }
}

pub type Result<'a, T> = core::result::Result<T, Error<'a>>;

/// Names are retained for schema validation, compatibility, and JSON mapping.
#[derive(Clone, Copy, Debug)]
pub struct Field<'a> {
    pub name: &'a str,
    pub desc: &'a Desc<'a>,
}

#[derive(Clone, Copy, Debug)]
pub struct Variant<'a> {
    pub selector: Nat<'a>,
    pub desc: &'a Desc<'a>,
}

/// Finite borrowed declaration tree. Logical capacities are never truncated to
/// pointer widths. Field/option pairs keep their source order.
#[derive(Clone, Copy, Debug)]
pub enum Desc<'a> {
    Bool,
    Uint(Nat<'a>),
    ByteVector(Nat<'a>),
    ByteList(Nat<'a>),
    BitVector(Nat<'a>),
    BitList(Nat<'a>),
    ProgressiveBitList(Option<Nat<'a>>),
    Vector(&'a Desc<'a>, Nat<'a>),
    List(&'a Desc<'a>, Nat<'a>),
    ProgressiveList(&'a Desc<'a>, Option<Nat<'a>>),
    Container(&'a [Field<'a>]),
    ProgressiveContainer { active: &'a [bool], fields: &'a [Field<'a>] },
    CompatibleUnion(&'a [Variant<'a>]),
}

/// Packed representation of exactly `len` logical bits, low bit first.
/// Unused high bits of the last byte do not belong to the logical value.
#[derive(Clone, Copy, Debug)]
pub struct Bits<'a> {
    bytes: &'a [u8],
    len: u128,
}

impl<'a> Bits<'a> {
    pub fn new(bytes: &'a [u8], len: u128) -> Result<'a, Self> {
        let needed = len / 8 + u128::from(len % 8 != 0);
        if needed != bytes.len() as u128 {
            return Err(Error::new(Reason::BadRepresentation));
        }
        Ok(Self { bytes, len })
    }
    pub const fn len(self) -> u128 { self.len }
    pub const fn is_empty(self) -> bool { self.len == 0 }
    pub const fn bytes(self) -> &'a [u8] { self.bytes }
    pub fn byte(self, index: usize) -> u8 {
        let byte = self.bytes[index];
        if index + 1 == self.bytes.len() && self.len % 8 != 0 {
            byte & ((1u8 << (self.len % 8) as u32) - 1)
        } else { byte }
    }
    pub fn bit(self, index: u128) -> bool {
        index < self.len && (self.bytes[(index / 8) as usize] >> (index % 8) as u32) & 1 != 0
    }
}

impl PartialEq for Bits<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.len == other.len && (0..self.bytes.len()).all(|i| self.byte(i) == other.byte(i))
    }
}
impl Eq for Bits<'_> {}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Value<'a> {
    Bool(bool),
    Uint(Nat<'a>),
    Bytes(&'a [u8]),
    Bits(Bits<'a>),
    Seq(&'a [Value<'a>]),
    Union(Nat<'a>, &'a Value<'a>),
}

/// JSON syntax has already been parsed by the caller. The SSZ JSON mapping acts
/// on this tree, just as the Lean model acts on Lean.Json, not on source text.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Json<'a> {
    Null,
    Bool(bool),
    Number(&'a str),
    String(&'a str),
    Array(&'a [Json<'a>]),
    Object(&'a [(&'a str, Json<'a>)]),
}

#[derive(Clone, Copy, Debug)]
pub enum Spelling<'a> {
    Byte,
    Plain(&'a [Spelling<'a>]),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PathStep<'a> {
    Position(Nat<'a>),
    Length,
    ActiveFields,
    Selector,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ChunkPosition<'a> {
    pub chunk: Nat<'a>,
    pub start: Nat<'a>,
    pub stop: Nat<'a>,
}
