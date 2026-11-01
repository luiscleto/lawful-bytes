# lawful-bytes

Byte buffers for Bend 2: bytes packed four to a `U32` word in one flat array, so scanning a large
file takes seconds where a list of characters takes minutes. Every operation has laws, checked by
Bend's proof checker, that say what it does to the plain list of bytes the buffer holds, so code
built on it can be proven by reasoning about lists while it runs on words. The word-at-a-time
`find`, `find2` and `append` are proven to give the same results as the simple ones.

## Use

Bend fetches these imports from [BendHub](https://hub.bend-lang.com/name/lawful-bytes) by name:

```python
import lawful-bytes@0.1.1.0/defs.bend as D   # the Bytes type, and view: its bytes as a list
import lawful-bytes@0.1.1.0/bytes.bend as B  # the operations
import lawful-bytes@0.1.1.0/fast.bend as FA  # find, find2 and append, a word at a time
import lawful-bytes@0.1.1.0/LAWS.bend as L   # the laws, for your own proofs
import lawful-bytes@0.1.1.0/PROOF.bend as P  # their proofs, needed when a proof uses a law
```

A `Bytes` can be used only once, so every read hands the buffer back along with its answer. Each
pair is taken apart in its own small def. This program returns the first line of `"hi\nyo\n"`:

```python
import Base
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/bytes.bend as B
import lawful-bytes@0.1.1.0/fast.bend as FA

# r holds the buffer and the index of its first newline.
def first_line.fin(r: D.Bytes & U32) -> List<&2, U32>:
  (b, +i) = r
  Pair.snd(D.Bytes, List<&2, U32>, B.to_list(b, 0, i))

# r holds the buffer and its length.
def first_line.go(r: D.Bytes & U32) -> List<&2, U32>:
  (b, +n) = r
  first_line.fin(FA.find(b, 0, n, 10))

# The bytes before the first newline (10).
def first_line(b: D.Bytes) -> List<&2, U32>:
  first_line.go(B.len(b))

def main() -> List<&2, U32>:
  first_line(B.of_list(1n, [104, 105, 10, 121, 111, 10]))  # "hi\nyo\n"
```

```
$ bend first_line.bend
[104, 105]
```

## What's in it

A buffer made with depth `d` has a block of 2^d words, which holds 4 · 2^d bytes (`d` ≤ 29, so up
to 2 GiB). Indexes and lengths are `U32`, and byte values are `U32`s below 256.

| operation | signature | what it does |
|---|---|---|
| `empty` | `empty(d) -> Bytes` | an empty buffer with room for 4 · 2^d bytes |
| `of_list` | `of_list(d, xs) -> Bytes` | a buffer holding the bytes of a list (Base's file reads give lists) |
| `grow` | `grow(b, e) -> Bytes` | the same bytes in a larger block of 2^e words |
| `len` | `len(b) -> Bytes & U32` | the number of bytes held |
| `capacity` | `capacity(b) -> Bytes & U32` | how many bytes fit |
| `at` | `at(b, i) -> Bytes & U32` | byte `i` |
| `set` | `set(b, i, v) -> Bytes` | byte `i` replaced by `v` |
| `push` | `push(b, v) -> Bytes` | `v` added at the end (needs room) |
| `append` | `append(dst, src, s, n) -> Bytes & Bytes` | `n` bytes of `src` from `s` added to the end of `dst` (needs room), `src` handed back |
| `find` | `find(b, from, to, c) -> Bytes & U32` | the first index in `from .. to-1` holding `c`, or `to` if none does |
| `find2` | `find2(b, from, to, c1, c2) -> Bytes & U32` | the same for either of two values |
| `same` | `same(a, i, b, j, n) -> Bytes & (Bytes & Bool)` | `n` bytes of `a` from `i` equal `n` bytes of `b` from `j` |
| `same1` | `same1(b, i, j, n) -> Bytes & Bool` | the same for two ranges of one buffer |
| `truncate` | `truncate(b, n) -> Bytes` | only the first `n` bytes kept |
| `shift` | `shift(b, k) -> Bytes` | the first `k` bytes dropped and the rest moved to the start (for reading a stream in pieces) |
| `to_list` | `to_list(b, s, n) -> Bytes & List<U32>` | `n` bytes from `s` as a list (Base's file writes take lists) |

`fast.bend` has `find`, `find2` and `append` with the same signatures, working a word at a time.

Each law is named after its operation. `find_view` states `find`'s answer in terms of the bytes
held (`D.view(b)`), `set_ok` and the other `_ok` laws say a result stays well formed
(`D.ok(b, d)`), and `fast_find` says `FA.find` equals `B.find`. A law is a function: you call it
with its arguments and hypotheses, and it returns its equation.

```python
# Searching for a newline a word at a time gives the same result as a byte at a time.
def newline_at(b: D.Bytes, +d: Nat, +n: U32, h: {D.ok(b, d) == True{} : Bool}, hn: {U32.is_le(0, n) == True{} : Bool}, ht: {Nat.is_le(U32.to_nat(n), D.size(b)) == True{} : Bool}) ->
  {FA.find(b, 0, n, 10) == B.find(b, 0, n, 10) : D.Bytes & U32}:
  L.fast_find(b, d, 0, n, 10, h, hn, ht, {==})
```

A `Bytes` can be used only once in a proof as well. To apply several laws to one buffer, go
through the mirror in `proof_core.bend` (`bmirror`).

The laws are proven. Below version 1.0 they have been reviewed by AI models but not yet by a human
expert. [docs/LAWS.md](docs/LAWS.md) lists every law in plain words.

## License

MIT (see `LICENSE`).
