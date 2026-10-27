You are reviewing a draft specification for `lawful-bytes`, a Bend 2 package that will be published
on BendHub. It holds bytes packed four to a `U32` (little-endian) in an `Array<U32>` block, which
the runtime stores as one flat buffer: a measured prototype read, split and judged a 2.8 GB file in
6 s this way, where a list of characters took about 10 minutes. Every law describes an operation by
what it does to the plain list of bytes a buffer holds (`D.view`). The laws will be proven; then
faster code (four bytes at a time) replaces the current simple bodies under the same laws, and a
VCF normalizer is rebuilt on it. A wrong law means a false proof downstream; a missing or unusable
law means downstream code cannot be proven.

Read these files in `../lawful-bytes` (read-only; do not modify anything):
- `LAWS.bend`: the 22 laws (the main object of review).
- `defs.bend`: the `Bytes` type and the definitions the laws use (`view`, `size`, `cap`, `ok`,
  `slice`, `first`, `first2`, `list_eq`, the projections).
- `bytes.bend`: the operations (empty, at, set, push, append, grow, find, find2, same), written a
  byte at a time as the reference version. Judge the laws as the contract for any implementation.
- It builds on `../lawful-words` (laws about U32: `defs.bend` has `byte`, `put_byte`) and
  `../lawful-arrays` (laws about `Array`: `defs.bend` has `full`, `view`), both reviewed earlier.
- `test/spot.bend` evaluates both sides of many laws (`bend test/spot.bend` from `../lawful-bytes`;
  24 checks, all pass). `bend LAWS.bend --check-only` reports 22 unproven laws, as expected.

Bend notes: `law name:` followed by `for x: T` lines is a claim for every x; `for h: {a == b : T}` is a
hypothesis; `{a == b : T}` is equality; `+x` only marks a variable as reusable. `Nat.sub` truncates.
A `Bytes` value has exactly one owner, so every read hands it back (`Bytes & U32`).

For each definition and law, answer:
(a) Does the Bend mean exactly what its English comment says?
(b) Is it true of the definitions as written? Counterexamples worked from the code.
(c) Edge cases: empty buffers, ranges of length 0, `from == to`, `to == len`, the last word of the
    block, a byte value of 256 or more, depth 0 and depth 29 (the bound), U32 wrap of `i + n`.
(d) Is the API right for its use: splitting a VCF into lines (find LF) and fields (find TAB or LF),
    comparing a REF allele with reference bytes (same), building output by appending ranges of the
    input (append) and a few rewritten bytes (push)? What is missing for that, or for a general
    byte-buffer library?
(e) Will these laws survive a word-at-a-time implementation (the bytes past `len` in the last word
    are unspecified; copies may write past the end within the capacity)?

Report a numbered list of findings. For each: the law or definition; severity (blocker / should fix
/ minor); the problem; a concrete example where possible; a suggested fix. Be concrete and brief. If
something is correct, you do not need to say so. End with the full report as your final message.
