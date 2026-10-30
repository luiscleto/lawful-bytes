import Base
import lawful-words@0.1.0.0/defs.bend as W
import ./defs.bend as D
import ./bytes.bend as B

# lawful-bytes operations a word at a time: the same names, signatures and
# results as bytes.bend's (a later pass proves each equal to it). Loops read
# whole words; reads past the block's end wrap (Base wraps indexes) and what
# they read never reaches a result.

# 0x80 at each byte of v that is 0, exact at the lowest such byte (a byte
# above a 0 byte may be flagged too).
def zb(+v: U32) -> U32:
  ((v - 16843009 : U32) .&. (U32.not(v) .&. 2155905152 : U32) : U32)

# c in all four bytes of a word.
def rep(+c: U32) -> U32:
  (c * 16843009 : U32)

def b2u(b: Bool) -> U32:
  match b:
    case True{}:
      1
    case False{}:
      0

# The place (0-3) of the lowest flagged byte of a nonzero mask.
def bidx(+m: U32) -> U32:
  (b2u(U32.is_zero((m .&. 128 : U32))) + b2u(U32.is_zero((m .&. 32896 : U32))) + b2u(U32.is_zero((m .&. 8421504 : U32))) : U32)

# The bytes of a word at or above byte i's place. The first word of a search
# sets the bytes below the start to 0xFF before the zero-byte test (not the
# flags after it): zb is exact only at its lowest zero byte, and a match below
# the start would otherwise borrow and flag the byte at the start (found by the
# proof agent: "A@BC" searched for 'A' from 1).
def low(+i: U32) -> U32:
  U32.shln(4294967295, U32.to_nat(((i .&. 3 : U32) << 3n : U32)))

# How many words hold bytes from .. to-1 (0 when to <= from).
def words(+from: U32, +to: U32) -> Nat:
  Bool.pick(Nat, U32.is_le(to, from), 0n, U32.to_nat(((((to - 1 : U32) >> 2n : U32) - (from >> 2n : U32) : U32) + 1 : U32)))

# ---------------------------------------------------------------------------
# find, find2
# ---------------------------------------------------------------------------

def find.fin(+to: U32, r: Array<U32> & U32) -> Array<U32> & U32:
  (a, +j) = r
  (a, U32.min(j, to))

# m flags word wi's hits; z: m is 0; r holds word wi + 1; n counts the words
# left, wi's included. Answers the offset of the first hit, or 2^32 - 1.
def find.go(n: Nat, z: Bool, r: Array<U32> & U32, +wi: U32, +m: U32, +rc: U32) -> Array<U32> & U32:
  match n z:
    case 0n _:
      (a, w) = r
      (a, 4294967295)
    case 1n+k True{}:
      (a, +w) = r
      +m2 = zb((w .^. rc : U32))
      find.go(k, U32.is_zero(m2), Array.get(U32, a, (wi + 2 : U32)), (wi + 1 : U32), m2, rc)
    case 1n+k False{}:
      (a, w) = r
      (a, ((wi << 2n : U32) + bidx(m) : U32))

def find.start(n: Nat, r: Array<U32> & U32, +from: U32, +rc: U32) -> Array<U32> & U32:
  (a, +w) = r
  +wi = (from >> 2n : U32)
  +lo = U32.not(low(from))
  +m = zb(((w .^. rc : U32) .|. lo : U32))
  find.go(n, U32.is_zero(m), Array.get(U32, a, (wi + 1 : U32)), wi, m, rc)

def find.k(+len: U32, r: Array<U32> & U32) -> D.Bytes & U32:
  (buf, +j) = r
  (D.Bytes{len, buf}, j)

# The first index j with from <= j < to where byte j is c; to if none.
def find(b: D.Bytes, +from: U32, +to: U32, +c: U32) -> D.Bytes & U32:
  D.Bytes{+len, buf} = b
  find.k(len, find.fin(to, find.start(words(from, to), Array.get(U32, buf, (from >> 2n : U32)), from, rep(c))))

def find2.go(n: Nat, z: Bool, r: Array<U32> & U32, +wi: U32, +m: U32, +r1: U32, +r2: U32) -> Array<U32> & U32:
  match n z:
    case 0n _:
      (a, w) = r
      (a, 4294967295)
    case 1n+k True{}:
      (a, +w) = r
      +m2 = (zb((w .^. r1 : U32)) .|. zb((w .^. r2 : U32)) : U32)
      find2.go(k, U32.is_zero(m2), Array.get(U32, a, (wi + 2 : U32)), (wi + 1 : U32), m2, r1, r2)
    case 1n+k False{}:
      (a, w) = r
      (a, ((wi << 2n : U32) + bidx(m) : U32))

def find2.start(n: Nat, r: Array<U32> & U32, +from: U32, +r1: U32, +r2: U32) -> Array<U32> & U32:
  (a, +w) = r
  +wi = (from >> 2n : U32)
  +lo = U32.not(low(from))
  +m = (zb(((w .^. r1 : U32) .|. lo : U32)) .|. zb(((w .^. r2 : U32) .|. lo : U32)) : U32)
  find2.go(n, U32.is_zero(m), Array.get(U32, a, (wi + 1 : U32)), wi, m, r1, r2)

# The first index j with from <= j < to where byte j is c1 or c2; to if none.
def find2(b: D.Bytes, +from: U32, +to: U32, +c1: U32, +c2: U32) -> D.Bytes & U32:
  D.Bytes{+len, buf} = b
  find.k(len, find.fin(to, find2.start(words(from, to), Array.get(U32, buf, (from >> 2n : U32)), from, rep(c1), rep(c2))))

# ---------------------------------------------------------------------------
# append
# ---------------------------------------------------------------------------

# n words to dst from word di on, taken from src's bytes at a shift of sh
# bits: lo is src word si, r holds word si + 1.
def append.words(n: Nat, r: Array<U32> & U32, +lo: U32, dst: Array<U32>, +si: U32, +di: U32, +sh: Nat) -> Array<U32> & Array<U32>:
  match n:
    case 0n:
      (src, w) = r
      (dst, src)
    case 1n+k:
      (src, +hi) = r
      append.words(k, Array.get(U32, src, (si + 2 : U32)), hi, Array.set(U32, dst, di, (U32.shrn(lo, sh) .|. U32.shln(hi, Nat.sub(32n, sh)) : U32)), (si + 1 : U32), (di + 1 : U32), sh)

def append.fin(+dl: U32, +sl: U32, r: Array<U32> & Array<U32>) -> D.Bytes & D.Bytes:
  (db, sb) = r
  (D.Bytes{dl, db}, D.Bytes{sl, sb})

def append.w(+dl: U32, +n: U32, +q: U32, db: Array<U32>, +sl: U32, r: Array<U32> & U32) -> D.Bytes & D.Bytes:
  (sb, +lo) = r
  append.fin((dl + n : U32), sl, append.words(U32.to_nat(((n + 3 : U32) >> 2n : U32)), Array.get(U32, sb, ((q >> 2n : U32) + 1 : U32)), lo, db, (q >> 2n : U32), (dl >> 2n : U32), U32.to_nat(((q .&. 3 : U32) << 3n : U32))))

# dst's length is now a multiple of 4: n more bytes of src from q, a word at a
# time (up to 3 bytes past the new length are overwritten too).
def append.k(+n: U32, +q: U32, r: D.Bytes & D.Bytes) -> D.Bytes & D.Bytes:
  (dst, src) = r
  D.Bytes{+dl, db} = dst
  D.Bytes{+sl, sb} = src
  append.w(dl, n, q, db, sl, Array.get(U32, sb, (q >> 2n : U32)))

# dst with bytes s .. s+n-1 of src added at the end; src handed back. The
# first bytes, up to dst's next word boundary, go one at a time, the rest a
# word at a time.
def append(dst: D.Bytes, src: D.Bytes, +s: U32, +n: U32) -> D.Bytes & D.Bytes:
  D.Bytes{+dl, db} = dst
  +h = U32.min(((4 - (dl .&. 3 : U32) : U32) .&. 3 : U32), n)
  append.k((n - h : U32), (s + h : U32), B.append(D.Bytes{dl, db}, src, s, h))
