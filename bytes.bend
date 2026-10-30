import Base
import lawful-words@0.1.0.0/defs.bend as W
import ./defs.bend as D

# lawful-bytes operations. This is the reference version: a byte at a time,
# simple to prove. Faster versions (a word at a time) replace these bodies
# under the same laws. Loops here read one byte ahead and discard it at the
# end; reads past len stay inside the block (Base wraps indexes), and the
# value read never reaches a result.

# An empty Bytes with room for 4 * 2^d bytes.
def empty(+d: Nat) -> D.Bytes:
  D.Bytes{0, Array.new(U32, d, 0)}

def at.fin(+len: U32, +i: U32, r: Array<U32> & U32) -> D.Bytes & U32:
  (buf, +w) = r
  (D.Bytes{len, buf}, W.byte(w, U32.to_nat((i .&. 3 : U32))))

# Byte i (for i < len).
def at(b: D.Bytes, +i: U32) -> D.Bytes & U32:
  D.Bytes{+len, buf} = b
  at.fin(len, i, Array.get(U32, buf, (i >> 2n : U32)))

def set.fin(+len: U32, +i: U32, +v: U32, r: Array<U32> & U32) -> D.Bytes:
  (buf, +w) = r
  D.Bytes{len, Array.set(U32, buf, (i >> 2n : U32), W.put_byte(w, U32.to_nat((i .&. 3 : U32)), v))}

# Byte i set to v (for i < len and v < 256).
def set(b: D.Bytes, +i: U32, +v: U32) -> D.Bytes:
  D.Bytes{+len, buf} = b
  set.fin(len, i, v, Array.get(U32, buf, (i >> 2n : U32)))

def push.fin(+len: U32, +v: U32, r: Array<U32> & U32) -> D.Bytes:
  (buf, +w) = r
  D.Bytes{(len + 1 : U32), Array.set(U32, buf, (len >> 2n : U32), W.put_byte(w, U32.to_nat((len .&. 3 : U32)), v))}

# v added at the end (for len < cap and v < 256).
def push(b: D.Bytes, +v: U32) -> D.Bytes:
  D.Bytes{+len, buf} = b
  push.fin(len, v, Array.get(U32, buf, (len >> 2n : U32)))

# n more bytes of src, from s; r holds src's byte s.
def append.go(n: Nat, dst: D.Bytes, r: D.Bytes & U32, +s: U32) -> D.Bytes & D.Bytes:
  match n:
    case 0n:
      (src, x) = r
      (dst, src)
    case 1n+k:
      (src, +x) = r
      append.go(k, push(dst, x), at(src, (s + 1 : U32)), (s + 1 : U32))

# dst with bytes s .. s+n-1 of src added at the end; src handed back.
def append(dst: D.Bytes, src: D.Bytes, +s: U32, +n: U32) -> D.Bytes & D.Bytes:
  append.go(U32.to_nat(n), dst, at(src, s), s)

# Word i onwards copied into dst; r holds word i of the old block.
def grow.go(n: Nat, r: Array<U32> & U32, dst: Array<U32>, +i: U32) -> Array<U32>:
  match n:
    case 0n:
      (src, w) = r
      dst
    case 1n+k:
      (src, +w) = r
      grow.go(k, Array.get(U32, src, (i + 1 : U32)), Array.set(U32, dst, i, w), (i + 1 : U32))

def grow.fin(+len: U32, +e: Nat, r: Array<U32> & U32) -> D.Bytes:
  (buf, +n) = r
  D.Bytes{len, grow.go(U32.to_nat(n), Array.get(U32, buf, 0), Array.new(U32, e, 0), 0)}

# The same bytes in a block of 2^e words (for e at least the current depth).
def grow(b: D.Bytes, +e: Nat) -> D.Bytes:
  D.Bytes{+len, buf} = b
  grow.fin(len, e, Array.size(U32, buf))

# hit says byte j is c; r holds byte j + 1; n counts positions left from j.
def find.go(n: Nat, hit: Bool, r: D.Bytes & U32, +j: U32, +to: U32, +c: U32) -> D.Bytes & U32:
  match n hit:
    case 0n _:
      (b, x) = r
      (b, to)
    case 1n+k True{}:
      (b, x) = r
      (b, j)
    case 1n+k False{}:
      (b, +x) = r
      find.go(k, U32.is_eq(x, c), at(b, (j + 2 : U32)), (j + 1 : U32), to, c)

def find.start(n: Nat, r: D.Bytes & U32, +from: U32, +to: U32, +c: U32) -> D.Bytes & U32:
  (b, +x) = r
  find.go(n, U32.is_eq(x, c), at(b, (from + 1 : U32)), from, to, c)

# The first index j with from <= j < to where byte j is c; to if none.
def find(b: D.Bytes, +from: U32, +to: U32, +c: U32) -> D.Bytes & U32:
  find.start(Nat.sub(U32.to_nat(to), U32.to_nat(from)), at(b, from), from, to, c)

def find2.go(n: Nat, hit: Bool, r: D.Bytes & U32, +j: U32, +to: U32, +c1: U32, +c2: U32) -> D.Bytes & U32:
  match n hit:
    case 0n _:
      (b, x) = r
      (b, to)
    case 1n+k True{}:
      (b, x) = r
      (b, j)
    case 1n+k False{}:
      (b, +x) = r
      find2.go(k, U32.is_eq(x, c1) || U32.is_eq(x, c2), at(b, (j + 2 : U32)), (j + 1 : U32), to, c1, c2)

def find2.start(n: Nat, r: D.Bytes & U32, +from: U32, +to: U32, +c1: U32, +c2: U32) -> D.Bytes & U32:
  (b, +x) = r
  find2.go(n, U32.is_eq(x, c1) || U32.is_eq(x, c2), at(b, (from + 1 : U32)), from, to, c1, c2)

# The first index j with from <= j < to where byte j is c1 or c2; to if none.
def find2(b: D.Bytes, +from: U32, +to: U32, +c1: U32, +c2: U32) -> D.Bytes & U32:
  find2.start(Nat.sub(U32.to_nat(to), U32.to_nat(from)), at(b, from), from, to, c1, c2)

# ra, rb hold byte i of a and byte j of b; acc says all bytes so far matched.
def same.go(n: Nat, ra: D.Bytes & U32, rb: D.Bytes & U32, +i: U32, +j: U32, acc: Bool) -> D.Bytes & (D.Bytes & Bool):
  match n:
    case 0n:
      (a, x) = ra
      (b, y) = rb
      (a, (b, acc))
    case 1n+k:
      (a, +x) = ra
      (b, +y) = rb
      same.go(k, at(a, (i + 1 : U32)), at(b, (j + 1 : U32)), (i + 1 : U32), (j + 1 : U32), acc && U32.is_eq(x, y))

# Bytes i .. i+n-1 of a equal bytes j .. j+n-1 of b; both handed back.
def same(a: D.Bytes, +i: U32, b: D.Bytes, +j: U32, +n: U32) -> D.Bytes & (D.Bytes & Bool):
  same.go(U32.to_nat(n), at(a, i), at(b, j), i, j, True{})

# The number of bytes in use.
def len(b: D.Bytes) -> D.Bytes & U32:
  D.Bytes{+n, buf} = b
  (D.Bytes{n, buf}, n)

def capacity.fin(+n: U32, r: Array<U32> & U32) -> D.Bytes & U32:
  (buf, +w) = r
  (D.Bytes{n, buf}, (w << 2n : U32))

# How many bytes fit (4 per word).
def capacity(b: D.Bytes) -> D.Bytes & U32:
  D.Bytes{+n, buf} = b
  capacity.fin(n, Array.size(U32, buf))

# Only the first n bytes kept (for n <= len).
def truncate(b: D.Bytes, +n: U32) -> D.Bytes:
  D.Bytes{len, buf} = b
  D.Bytes{n, buf}

# Bytes j + k onwards moved to j; r holds byte j + k.
def shift.go(n: Nat, r: D.Bytes & U32, +j: U32, +k: U32) -> D.Bytes:
  match n:
    case 0n:
      (b, x) = r
      b
    case 1n+m:
      (b, +x) = r
      shift.go(m, at(set(b, j, x), ((j + 1 : U32) + k : U32)), (j + 1 : U32), k)

# The first k bytes dropped, the rest moved to the start (for k <= len).
def shift(b: D.Bytes, +k: U32) -> D.Bytes:
  D.Bytes{+n, buf} = b
  truncate(shift.go(Nat.sub(U32.to_nat(n), U32.to_nat(k)), at(D.Bytes{n, buf}, k), 0, k), (n - k : U32))

def of_list.go(xs: List<&2, U32>, b: D.Bytes) -> D.Bytes:
  match xs:
    case Nil{}:
      b
    case Con{x, t}:
      of_list.go(t, push(b, x))

# A Bytes in a block of 2^d words holding the bytes of xs (Base's file
# reads give such lists).
def of_list(+d: Nat, xs: List<&2, U32>) -> D.Bytes:
  of_list.go(xs, empty(d))

def to_list.cons(+x: U32, r: D.Bytes & List<&2, U32>) -> D.Bytes & List<&2, U32>:
  (b, t) = r
  (b, Con{x, t})

# r holds byte s.
def to_list.go(n: Nat, r: D.Bytes & U32, +s: U32) -> D.Bytes & List<&2, U32>:
  match n:
    case 0n:
      (b, x) = r
      (b, Nil{})
    case 1n+m:
      (b, +x) = r
      to_list.cons(x, to_list.go(m, at(b, (s + 1 : U32)), (s + 1 : U32)))

# Bytes s .. s+n-1 as a list (Base's file writes take such lists).
def to_list(b: D.Bytes, +s: U32, +n: U32) -> D.Bytes & List<&2, U32>:
  to_list.go(U32.to_nat(n), at(b, s), s)

def at2.fin2(+x: U32, r: D.Bytes & U32) -> D.Bytes & (U32 & U32):
  (b, +y) = r
  (b, (x, y))

def at2.fin(+j: U32, r: D.Bytes & U32) -> D.Bytes & (U32 & U32):
  (b, +x) = r
  at2.fin2(x, at(b, j))

# Bytes i and j.
def at2(b: D.Bytes, +i: U32, +j: U32) -> D.Bytes & (U32 & U32):
  at2.fin(j, at(b, i))

# r holds bytes i and j; acc says all bytes so far matched.
def same1.go(n: Nat, r: D.Bytes & (U32 & U32), +i: U32, +j: U32, acc: Bool) -> D.Bytes & Bool:
  match n:
    case 0n:
      (b, q) = r
      (b, acc)
    case 1n+m:
      (b, q) = r
      (x, y) = q
      same1.go(m, at2(b, (i + 1 : U32), (j + 1 : U32)), (i + 1 : U32), (j + 1 : U32), acc && U32.is_eq(x, y))

# Bytes i .. i+n-1 equal bytes j .. j+n-1 of the same buffer.
def same1(b: D.Bytes, +i: U32, +j: U32, +n: U32) -> D.Bytes & Bool:
  same1.go(U32.to_nat(n), at2(b, i, j), i, j, True{})
