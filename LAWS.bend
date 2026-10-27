import Base
import ./defs.bend as D
import ./bytes.bend as B
import ./fast.bend as FA

# lawful-bytes: bytes packed four to a word in an Array<U32> block. Every law
# describes an operation by what it does to the list of bytes a Bytes holds
# (D.view). Hypotheses D.ok(b, d) say b is well formed with a block of 2^d
# words; every operation keeps it so.

# ==========================================================================
# What a Bytes holds
# ==========================================================================

law view_size:
  for b: D.Bytes
  for d: Nat
  for h: {D.ok(b, d) == True{} : Bool}
  {List.length(&2, U32, D.view(b)) == D.size(b) : Nat}

law view_bytes:
  for b: D.Bytes
  {D.all_bytes(D.view(b)) == True{} : Bool}

law cap_ok:
  for b: D.Bytes
  for d: Nat
  for h: {D.ok(b, d) == True{} : Bool}
  {D.cap(b) == Nat.mul(4n, Nat.pow(2n, d)) : Nat}

# ==========================================================================
# Making
# ==========================================================================

law empty_view:
  for d: Nat
  {D.view(B.empty(d)) == Nil{} : List<&2, U32>}

law empty_ok:
  for d: Nat
  for hd: {Nat.is_le(d, 29n) == True{} : Bool}
  {D.ok(B.empty(d), d) == True{} : Bool}

# grow keeps the bytes in a larger block.
law grow_view:
  for b: D.Bytes
  for d: Nat
  for e: Nat
  for h: {D.ok(b, d) == True{} : Bool}
  for he: {Nat.is_le(d, e) == True{} : Bool}
  for he29: {Nat.is_le(e, 29n) == True{} : Bool}
  {D.view(B.grow(b, e)) == D.view(b) : List<&2, U32>}

law grow_ok:
  for b: D.Bytes
  for d: Nat
  for e: Nat
  for h: {D.ok(b, d) == True{} : Bool}
  for he: {Nat.is_le(d, e) == True{} : Bool}
  for he29: {Nat.is_le(e, 29n) == True{} : Bool}
  {D.ok(B.grow(b, e), e) == True{} : Bool}

# ==========================================================================
# Reading
# ==========================================================================

law at_view:
  for b: D.Bytes
  for d: Nat
  for i: U32
  for h: {D.ok(b, d) == True{} : Bool}
  for hi: {Nat.is_lt(U32.to_nat(i), D.size(b)) == True{} : Bool}
  {Some{Pair.snd(D.Bytes, U32, B.at(b, i))} == List.get(&2, U32, D.view(b), U32.to_nat(i)) : Maybe<&2, U32>}

# The result as a literal pair: the same Bytes and the value (for rewriting).
law at_pair:
  for b: D.Bytes
  for i: U32
  {B.at(b, i) == (b, Pair.snd(D.Bytes, U32, B.at(b, i))) : D.Bytes & U32}

# find answers the first index in from .. to-1 holding c, or to. c must be a
# byte value: a word-at-a-time search compares 8 bits per byte.
law find_view:
  for b: D.Bytes
  for d: Nat
  for from: U32
  for to: U32
  for c: U32
  for h: {D.ok(b, d) == True{} : Bool}
  for hft: {U32.is_le(from, to) == True{} : Bool}
  for ht: {Nat.is_le(U32.to_nat(to), D.size(b)) == True{} : Bool}
  for hc: {U32.is_lt(c, 256) == True{} : Bool}
  {U32.to_nat(Pair.snd(D.Bytes, U32, B.find(b, from, to, c))) == D.first(D.view(b), U32.to_nat(from), U32.to_nat(to), c) : Nat}

# The result as a literal pair: the same Bytes and the value (for rewriting).
law find_pair:
  for b: D.Bytes
  for from: U32
  for to: U32
  for c: U32
  {B.find(b, from, to, c) == (b, Pair.snd(D.Bytes, U32, B.find(b, from, to, c))) : D.Bytes & U32}

law find2_view:
  for b: D.Bytes
  for d: Nat
  for from: U32
  for to: U32
  for c1: U32
  for c2: U32
  for h: {D.ok(b, d) == True{} : Bool}
  for hft: {U32.is_le(from, to) == True{} : Bool}
  for ht: {Nat.is_le(U32.to_nat(to), D.size(b)) == True{} : Bool}
  for hc1: {U32.is_lt(c1, 256) == True{} : Bool}
  for hc2: {U32.is_lt(c2, 256) == True{} : Bool}
  {U32.to_nat(Pair.snd(D.Bytes, U32, B.find2(b, from, to, c1, c2))) == D.first2(D.view(b), U32.to_nat(from), U32.to_nat(to), c1, c2) : Nat}

# The result as a literal pair: the same Bytes and the value (for rewriting).
law find2_pair:
  for b: D.Bytes
  for from: U32
  for to: U32
  for c1: U32
  for c2: U32
  {B.find2(b, from, to, c1, c2) == (b, Pair.snd(D.Bytes, U32, B.find2(b, from, to, c1, c2))) : D.Bytes & U32}

# same compares two ranges of equal length, n bytes each.
law same_view:
  for a: D.Bytes
  for b: D.Bytes
  for d: Nat
  for e: Nat
  for i: U32
  for j: U32
  for n: U32
  for ha: {D.ok(a, d) == True{} : Bool}
  for hb: {D.ok(b, e) == True{} : Bool}
  for hi: {Nat.is_le(Nat.add(U32.to_nat(i), U32.to_nat(n)), D.size(a)) == True{} : Bool}
  for hj: {Nat.is_le(Nat.add(U32.to_nat(j), U32.to_nat(n)), D.size(b)) == True{} : Bool}
  {Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, B.same(a, i, b, j, n))) == D.list_eq(D.slice(D.view(a), U32.to_nat(i), U32.to_nat(n)), D.slice(D.view(b), U32.to_nat(j), U32.to_nat(n))) : Bool}

# same hands both buffers back (as a literal tuple, for rewriting).
law same_pair:
  for a: D.Bytes
  for b: D.Bytes
  for i: U32
  for j: U32
  for n: U32
  {B.same(a, i, b, j, n) == (a, (b, Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, B.same(a, i, b, j, n))))) : D.Bytes & (D.Bytes & Bool)}

# ==========================================================================
# Writing
# ==========================================================================

law set_view:
  for b: D.Bytes
  for d: Nat
  for i: U32
  for v: U32
  for h: {D.ok(b, d) == True{} : Bool}
  for hi: {Nat.is_lt(U32.to_nat(i), D.size(b)) == True{} : Bool}
  for hv: {U32.is_lt(v, 256) == True{} : Bool}
  {D.view(B.set(b, i, v)) == List.set(&2, U32, D.view(b), U32.to_nat(i), v) : List<&2, U32>}

law set_ok:
  for b: D.Bytes
  for d: Nat
  for i: U32
  for v: U32
  for h: {D.ok(b, d) == True{} : Bool}
  {D.ok(B.set(b, i, v), d) == True{} : Bool}

law push_view:
  for b: D.Bytes
  for d: Nat
  for v: U32
  for h: {D.ok(b, d) == True{} : Bool}
  for hc: {Nat.is_lt(D.size(b), D.cap(b)) == True{} : Bool}
  for hv: {U32.is_lt(v, 256) == True{} : Bool}
  {D.view(B.push(b, v)) == List.append(&2, U32, D.view(b), [v]) : List<&2, U32>}

law push_ok:
  for b: D.Bytes
  for d: Nat
  for v: U32
  for h: {D.ok(b, d) == True{} : Bool}
  for hc: {Nat.is_lt(D.size(b), D.cap(b)) == True{} : Bool}
  {D.ok(B.push(b, v), d) == True{} : Bool}

# append adds n bytes of src, from s, at the end of dst.
law append_view:
  for dst: D.Bytes
  for src: D.Bytes
  for d: Nat
  for e: Nat
  for s: U32
  for n: U32
  for hd: {D.ok(dst, d) == True{} : Bool}
  for he: {D.ok(src, e) == True{} : Bool}
  for hs: {Nat.is_le(Nat.add(U32.to_nat(s), U32.to_nat(n)), D.size(src)) == True{} : Bool}
  for hc: {Nat.is_le(Nat.add(D.size(dst), U32.to_nat(n)), D.cap(dst)) == True{} : Bool}
  {D.view(Pair.fst(D.Bytes, D.Bytes, B.append(dst, src, s, n))) == List.append(&2, U32, D.view(dst), D.slice(D.view(src), U32.to_nat(s), U32.to_nat(n))) : List<&2, U32>}

law append_ok:
  for dst: D.Bytes
  for src: D.Bytes
  for d: Nat
  for s: U32
  for n: U32
  for hd: {D.ok(dst, d) == True{} : Bool}
  for hc: {Nat.is_le(Nat.add(D.size(dst), U32.to_nat(n)), D.cap(dst)) == True{} : Bool}
  {D.ok(Pair.fst(D.Bytes, D.Bytes, B.append(dst, src, s, n)), d) == True{} : Bool}

# append hands src back (as a literal pair, for rewriting).
law append_pair:
  for dst: D.Bytes
  for src: D.Bytes
  for s: U32
  for n: U32
  {B.append(dst, src, s, n) == (Pair.fst(D.Bytes, D.Bytes, B.append(dst, src, s, n)), src) : D.Bytes & D.Bytes}

# ==========================================================================
# Length, capacity, trimming
# ==========================================================================

law len_view:
  for b: D.Bytes
  {U32.to_nat(Pair.snd(D.Bytes, U32, B.len(b))) == D.size(b) : Nat}

law len_pair:
  for b: D.Bytes
  {B.len(b) == (b, Pair.snd(D.Bytes, U32, B.len(b))) : D.Bytes & U32}

law capacity_view:
  for b: D.Bytes
  for d: Nat
  for h: {D.ok(b, d) == True{} : Bool}
  {U32.to_nat(Pair.snd(D.Bytes, U32, B.capacity(b))) == D.cap(b) : Nat}

law capacity_pair:
  for b: D.Bytes
  {B.capacity(b) == (b, Pair.snd(D.Bytes, U32, B.capacity(b))) : D.Bytes & U32}

law truncate_view:
  for b: D.Bytes
  for n: U32
  for h: {Nat.is_le(U32.to_nat(n), D.size(b)) == True{} : Bool}
  {D.view(B.truncate(b, n)) == List.take(&2, U32, D.view(b), U32.to_nat(n)) : List<&2, U32>}

law truncate_ok:
  for b: D.Bytes
  for d: Nat
  for n: U32
  for h: {D.ok(b, d) == True{} : Bool}
  for hn: {Nat.is_le(U32.to_nat(n), D.size(b)) == True{} : Bool}
  {D.ok(B.truncate(b, n), d) == True{} : Bool}

# shift drops the first k bytes and moves the rest to the start (for reusing a
# buffer when reading a stream in pieces).
law shift_view:
  for b: D.Bytes
  for d: Nat
  for k: U32
  for h: {D.ok(b, d) == True{} : Bool}
  for hk: {Nat.is_le(U32.to_nat(k), D.size(b)) == True{} : Bool}
  {D.view(B.shift(b, k)) == List.drop(&2, U32, D.view(b), U32.to_nat(k)) : List<&2, U32>}

law shift_ok:
  for b: D.Bytes
  for d: Nat
  for k: U32
  for h: {D.ok(b, d) == True{} : Bool}
  for hk: {Nat.is_le(U32.to_nat(k), D.size(b)) == True{} : Bool}
  {D.ok(B.shift(b, k), d) == True{} : Bool}

# ==========================================================================
# Lists (Base's file reads and writes use List<U32>)
# ==========================================================================

law of_list_view:
  for d: Nat
  for xs: List<&2, U32>
  for hd: {Nat.is_le(d, 29n) == True{} : Bool}
  for hn: {Nat.is_le(List.length(&2, U32, xs), Nat.mul(4n, Nat.pow(2n, d))) == True{} : Bool}
  for hb: {D.all_bytes(xs) == True{} : Bool}
  {D.view(B.of_list(d, xs)) == xs : List<&2, U32>}

law of_list_ok:
  for d: Nat
  for xs: List<&2, U32>
  for hd: {Nat.is_le(d, 29n) == True{} : Bool}
  for hn: {Nat.is_le(List.length(&2, U32, xs), Nat.mul(4n, Nat.pow(2n, d))) == True{} : Bool}
  {D.ok(B.of_list(d, xs), d) == True{} : Bool}

law to_list_view:
  for b: D.Bytes
  for d: Nat
  for s: U32
  for n: U32
  for h: {D.ok(b, d) == True{} : Bool}
  for hs: {Nat.is_le(Nat.add(U32.to_nat(s), U32.to_nat(n)), D.size(b)) == True{} : Bool}
  {Pair.snd(D.Bytes, List<&2, U32>, B.to_list(b, s, n)) == D.slice(D.view(b), U32.to_nat(s), U32.to_nat(n)) : List<&2, U32>}

law to_list_pair:
  for b: D.Bytes
  for s: U32
  for n: U32
  {B.to_list(b, s, n) == (b, Pair.snd(D.Bytes, List<&2, U32>, B.to_list(b, s, n))) : D.Bytes & List<&2, U32>}

# ==========================================================================
# Comparing two ranges of one buffer
# ==========================================================================

law same1_view:
  for b: D.Bytes
  for d: Nat
  for i: U32
  for j: U32
  for n: U32
  for h: {D.ok(b, d) == True{} : Bool}
  for hi: {Nat.is_le(Nat.add(U32.to_nat(i), U32.to_nat(n)), D.size(b)) == True{} : Bool}
  for hj: {Nat.is_le(Nat.add(U32.to_nat(j), U32.to_nat(n)), D.size(b)) == True{} : Bool}
  {Pair.snd(D.Bytes, Bool, B.same1(b, i, j, n)) == D.list_eq(D.slice(D.view(b), U32.to_nat(i), U32.to_nat(n)), D.slice(D.view(b), U32.to_nat(j), U32.to_nat(n))) : Bool}

law same1_pair:
  for b: D.Bytes
  for i: U32
  for j: U32
  for n: U32
  {B.same1(b, i, j, n) == (b, Pair.snd(D.Bytes, Bool, B.same1(b, i, j, n))) : D.Bytes & Bool}

# ==========================================================================
# Facts about the search and comparison definitions (for proofs of parsers)
# ==========================================================================

law first_range:
  for xs: List<&2, U32>
  for from: Nat
  for to: Nat
  for c: U32
  for hft: {Nat.is_le(from, to) == True{} : Bool}
  for ht: {Nat.is_le(to, List.length(&2, U32, xs)) == True{} : Bool}
  {(Nat.is_le(from, D.first(xs, from, to, c)) && Nat.is_le(D.first(xs, from, to, c), to)) == True{} : Bool}

# Below to, the answer holds c.
law first_hit:
  for xs: List<&2, U32>
  for from: Nat
  for to: Nat
  for c: U32
  for hft: {Nat.is_le(from, to) == True{} : Bool}
  for ht: {Nat.is_le(to, List.length(&2, U32, xs)) == True{} : Bool}
  for hlt: {Nat.is_lt(D.first(xs, from, to, c), to) == True{} : Bool}
  {D.has(xs, D.first(xs, from, to, c), c) == True{} : Bool}

# No index from from up to the answer holds c.
law first_miss:
  for xs: List<&2, U32>
  for from: Nat
  for to: Nat
  for c: U32
  for k: Nat
  for hk1: {Nat.is_le(from, k) == True{} : Bool}
  for hk2: {Nat.is_lt(k, D.first(xs, from, to, c)) == True{} : Bool}
  {D.has(xs, k, c) == False{} : Bool}

law first2_range:
  for xs: List<&2, U32>
  for from: Nat
  for to: Nat
  for c1: U32
  for c2: U32
  for hft: {Nat.is_le(from, to) == True{} : Bool}
  for ht: {Nat.is_le(to, List.length(&2, U32, xs)) == True{} : Bool}
  {(Nat.is_le(from, D.first2(xs, from, to, c1, c2)) && Nat.is_le(D.first2(xs, from, to, c1, c2), to)) == True{} : Bool}

law first2_hit:
  for xs: List<&2, U32>
  for from: Nat
  for to: Nat
  for c1: U32
  for c2: U32
  for hft: {Nat.is_le(from, to) == True{} : Bool}
  for ht: {Nat.is_le(to, List.length(&2, U32, xs)) == True{} : Bool}
  for hlt: {Nat.is_lt(D.first2(xs, from, to, c1, c2), to) == True{} : Bool}
  {D.has2(xs, D.first2(xs, from, to, c1, c2), c1, c2) == True{} : Bool}

law first2_miss:
  for xs: List<&2, U32>
  for from: Nat
  for to: Nat
  for c1: U32
  for c2: U32
  for k: Nat
  for hk1: {Nat.is_le(from, k) == True{} : Bool}
  for hk2: {Nat.is_lt(k, D.first2(xs, from, to, c1, c2)) == True{} : Bool}
  {D.has2(xs, k, c1, c2) == False{} : Bool}

# A passed list_eq test gives equal lists.
law list_eq_true:
  for xs: List<&2, U32>
  for ys: List<&2, U32>
  for h: {D.list_eq(xs, ys) == True{} : Bool}
  {xs == ys : List<&2, U32>}

# Equal lists pass list_eq.
law list_eq_refl:
  for xs: List<&2, U32>
  {D.list_eq(xs, xs) == True{} : Bool}

# ==========================================================================
# Fast versions (fast.bend: a word at a time)
# ==========================================================================

# The word-at-a-time find gives exactly the reference result (the same Bytes
# and the same index). c must be a byte value: the search compares 8 bits per
# byte.
law fast_find:
  for b: D.Bytes
  for d: Nat
  for from: U32
  for to: U32
  for c: U32
  for h: {D.ok(b, d) == True{} : Bool}
  for hft: {U32.is_le(from, to) == True{} : Bool}
  for ht: {Nat.is_le(U32.to_nat(to), D.size(b)) == True{} : Bool}
  for hc: {U32.is_lt(c, 256) == True{} : Bool}
  {FA.find(b, from, to, c) == B.find(b, from, to, c) : D.Bytes & U32}

law fast_find2:
  for b: D.Bytes
  for d: Nat
  for from: U32
  for to: U32
  for c1: U32
  for c2: U32
  for h: {D.ok(b, d) == True{} : Bool}
  for hft: {U32.is_le(from, to) == True{} : Bool}
  for ht: {Nat.is_le(U32.to_nat(to), D.size(b)) == True{} : Bool}
  for hc1: {U32.is_lt(c1, 256) == True{} : Bool}
  for hc2: {U32.is_lt(c2, 256) == True{} : Bool}
  {FA.find2(b, from, to, c1, c2) == B.find2(b, from, to, c1, c2) : D.Bytes & U32}

# The fast searches hand back the same Bytes, for any arguments (as find_pair
# and find2_pair say of the reference).
law fast_find_pair:
  for b: D.Bytes
  for from: U32
  for to: U32
  for c: U32
  {FA.find(b, from, to, c) == (b, Pair.snd(D.Bytes, U32, FA.find(b, from, to, c))) : D.Bytes & U32}

law fast_find2_pair:
  for b: D.Bytes
  for from: U32
  for to: U32
  for c1: U32
  for c2: U32
  {FA.find2(b, from, to, c1, c2) == (b, Pair.snd(D.Bytes, U32, FA.find2(b, from, to, c1, c2))) : D.Bytes & U32}

# The word-at-a-time append writes whole words, so up to 3 bytes past the new
# length differ from the reference's: its laws are append's, on the view.
law fast_append_view:
  for dst: D.Bytes
  for src: D.Bytes
  for d: Nat
  for e: Nat
  for s: U32
  for n: U32
  for hd: {D.ok(dst, d) == True{} : Bool}
  for he: {D.ok(src, e) == True{} : Bool}
  for hs: {Nat.is_le(Nat.add(U32.to_nat(s), U32.to_nat(n)), D.size(src)) == True{} : Bool}
  for hc: {Nat.is_le(Nat.add(D.size(dst), U32.to_nat(n)), D.cap(dst)) == True{} : Bool}
  {D.view(Pair.fst(D.Bytes, D.Bytes, FA.append(dst, src, s, n))) == List.append(&2, U32, D.view(dst), D.slice(D.view(src), U32.to_nat(s), U32.to_nat(n))) : List<&2, U32>}

law fast_append_ok:
  for dst: D.Bytes
  for src: D.Bytes
  for d: Nat
  for s: U32
  for n: U32
  for hd: {D.ok(dst, d) == True{} : Bool}
  for hc: {Nat.is_le(Nat.add(D.size(dst), U32.to_nat(n)), D.cap(dst)) == True{} : Bool}
  {D.ok(Pair.fst(D.Bytes, D.Bytes, FA.append(dst, src, s, n)), d) == True{} : Bool}

law fast_append_pair:
  for dst: D.Bytes
  for src: D.Bytes
  for s: U32
  for n: U32
  {FA.append(dst, src, s, n) == (Pair.fst(D.Bytes, D.Bytes, FA.append(dst, src, s, n)), src) : D.Bytes & D.Bytes}
