import Base
import ../lawful-words/defs.bend as W
import ../lawful-arrays/defs.bend as A

# lawful-bytes definitions: the Bytes type and what it means. The operations
# are in bytes.bend, the laws in LAWS.bend.

# Bytes packed four to a word, little-endian, in a block of 2^d words: byte i
# is byte i & 3 of word i >> 2. len is the number of bytes in use; the bytes
# past len are unspecified.
type Bytes is Type:
  Bytes{len: U32, buf: Array<U32>}

# The four bytes of each word, in order.
def unpack(ws: List<&2, U32>) -> List<&2, U32>:
  match ws:
    case Nil{}:
      Nil{}
    case Con{+w, t}:
      List.append(&2, U32, [W.byte(w, 0n), W.byte(w, 1n), W.byte(w, 2n), W.byte(w, 3n)], unpack(t))

# What a Bytes holds: its first len bytes.
def view(b: Bytes) -> List<&2, U32>:
  Bytes{len, buf} = b
  List.take(&2, U32, unpack(A.view(U32, buf)), U32.to_nat(len))

# The number of bytes in use.
def size(b: Bytes) -> Nat:
  Bytes{len, buf} = b
  U32.to_nat(len)

# How many bytes fit: four per word.
def cap(b: Bytes) -> Nat:
  Bytes{len, buf} = b
  Nat.mul(4n, List.length(&2, U32, A.view(U32, buf)))

# b is well formed with a block of depth d: a perfect block of 2^d words,
# d <= 29, and len within the block. A buffer holds at most 2^31 bytes (2 GiB),
# so every index and length fits in a U32; the laws' hypotheses keep sums of
# lengths in range too. Larger files are read in pieces.
def ok(b: Bytes, +d: Nat) -> Bool:
  Bytes{len, buf} = b
  A.full(U32, buf, d) && (Nat.is_le(d, 29n) && Nat.is_le(U32.to_nat(len), Nat.mul(4n, Nat.pow(2n, d))))

# Every element is a byte (below 256).
def all_bytes(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, t}:
      U32.is_lt(x, 256) && all_bytes(t)

# n elements from index i.
def slice(xs: List<&2, U32>, +i: Nat, +n: Nat) -> List<&2, U32>:
  List.take(&2, U32, List.drop(&2, U32, xs, i), n)

# How many leading elements are not c.
def run_len(xs: List<&2, U32>, +c: U32) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{+x, t}:
      Bool.pick(Nat, U32.is_eq(x, c), 0n, Nat.add(1n, run_len(t, c)))

# How many leading elements are neither c1 nor c2.
def run_len2(xs: List<&2, U32>, +c1: U32, +c2: U32) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{+x, t}:
      Bool.pick(Nat, U32.is_eq(x, c1) || U32.is_eq(x, c2), 0n, Nat.add(1n, run_len2(t, c1, c2)))

# The first index j with from <= j < to where xs has c; to if there is none
# (for from <= to <= length(xs), as the laws assume).
def first(xs: List<&2, U32>, +from: Nat, +to: Nat, +c: U32) -> Nat:
  Nat.add(from, run_len(slice(xs, from, Nat.sub(to, from)), c))

# The same for either of two values (same assumptions).
def first2(xs: List<&2, U32>, +from: Nat, +to: Nat, +c1: U32, +c2: U32) -> Nat:
  Nat.add(from, run_len2(slice(xs, from, Nat.sub(to, from)), c1, c2))

# Two lists are equal, element by element.
def list_eq(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, xt} Con{y, yt}:
      U32.is_eq(x, y) && list_eq(xt, yt)
    case Nil{} Con{y, yt}:
      False{}
    case Con{x, xt} Nil{}:
      False{}

# xs has c at index k.
def is_some(m: Maybe<&2, U32>, +c: U32) -> Bool:
  match m:
    case Some{x}:
      U32.is_eq(x, c)
    case None{}:
      False{}

def has(xs: List<&2, U32>, +k: Nat, +c: U32) -> Bool:
  is_some(List.get(&2, U32, xs, k), c)

# xs has c1 or c2 at index k.
def has2(+xs: List<&2, U32>, +k: Nat, +c1: U32, +c2: U32) -> Bool:
  is_some(List.get(&2, U32, xs, k), c1) || is_some(List.get(&2, U32, xs, k), c2)
