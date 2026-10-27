# Proof notes: lawful-bytes

## Status (2026-10-27)

All 44 laws of `LAWS.bend` are proven. `./check.sh` runs both gate commands
(`--check-only`, then `--verdict` with the BendTT kernel), and both print ALL
PROOFS CHECK. Nothing in the import graph uses `@unsafe` or foreign code.
`bend test/spot.bend` is still all True (44 checks). A copy of PROOF.bend with
one proof broken on purpose fails, so the pass is not a cached result.
`LAWS.bend`, `defs.bend`, `bytes.bend` and `fast.bend` are untouched. There
are about 4400 lines of proof.

Files:
- `proof_core.bend`: the mirror and the byte level.
  - `BT(len, t)` is a Bytes whose block is `P.fromT(t)` for a `Tree<U32>`.
    `bmirror` and `BMirror(b)` show every Bytes is one, and `tr` transports a
    hypothesis to the mirror.
  - `at_pair_t` and `at_val` describe a read. `unpack_get`/`unpack_get_i`
    give byte i as byte `i & 3` of word `i >> 2`, and `unpack_set`/
    `unpack_set_i` describe a word write (with `wbp`, generated: put_byte
    on each of the four bytes). `at_view_t` describes a read through the view.
  - The ok parts: `ok_full`, `ok_d`, `ok_len` take ok apart and `ok_mk`
    builds it.
  - `wd_get`, `wl_set` and `full_set` cover word k in a block (via
    lawful-arrays' mirror lemmas).
  - Bounds: `four_lt_e`, `fits_e`, `he32`, `add_fits`, `inc_fits` and
    `succ_le` (see 2^32 below).
- `proof_seq.bend`: list facts for take, set, append and unpack (lengths,
  all_bytes).
- `proof_ops.bend`: the laws that do not loop, on the mirror (`name_t`):
  view_size, view_bytes, cap_ok, set, push, capacity, truncate. Also
  `set_eq_t` and `push_eq_t`, which name the mirror after a write.
- `proof_append.bend`: append. dst is a mirror that changes at each push:
  `PT` is the new tree and `step_*` are the per-step bounds.
- `proof_shift.bend`: shift. `SGT` is the tree the loop leaves, and
  `shift_go_eq` shows `shift.go(...) == BT(len, SGT(...))`. The view
  invariant `sv` is then about a Data function: bytes below j are `xs` from k
  on, bytes from j on are unchanged (`SV`).
- `proof_find.bend`: find and find2, with `add11`:
  `(j + 1) + 1 == j + 2` for any word, through from_nat, without 2^32.
- `proof_same.bend`: same, same1 and to_list.
- `proof_grow.bend`: grow, empty and of_list. `tnew` mirrors Array.new and
  `gtree` mirrors grow.go.
- `proof_list.bend`: the pure list laws (first, first2, list_eq).
- `PROOF.bend`: one `.go` wrapper per law about a Bytes. Each wrapper mirrors
  every Bytes parameter, rewrites the goal and transports each hypothesis,
  then calls `name_t`. The wrappers were written mechanically from LAWS.bend:
  a law with Bytes `b` maps to a lemma with `b` replaced by `len, t` in
  place.

## Dependencies (read this before committing)

Like ../lawful-arrays, the proofs import the dependencies' proof files
directly, not their PROOF.bend files. Every lemma there restates a law with
reusable variables:
- `../lawful-words/proof_nat.bend`, `proof_u32.bend` and `proof_bytes.bend`.
- `../lawful-arrays/proof_base.bend`, `proof_tree.bend` (`Tree`, `mirror`,
  `get_pair_t`, `size_eta`, `size_tree`, `view_length`), `proof_index.bend`
  (`get_view_t`, `set_view_t`, `set_tree`, `set_tree_eq`, `slot_small_t`,
  `size_n`, `unsome`) and `proof_shape.bend` (`set_full`).

If one of those names changes, this gate breaks.

## Where it got hard (research data)

- **Bytes is a Type.** It holds an Array, so a proof can use a Bytes once.
  The fix is the lawful-arrays mirror one level up: every lemma is about
  `BT(len, t)`, with len and t reusable, and each law calls `C.bmirror` once.
  Lemmas may also take an erased `-b: D.Bytes` and pass it to other erased
  parameters freely. A live use of an erased variable is refused.
- **Loops whose buffer changes** (append's dst, shift, grow's dst,
  of_list): name the next mirror instead of carrying the Bytes. Either an
  equation `push(BT(l, t), v) == BT(l + 1, PT(l, t, v))`, so the induction
  hypothesis applies to the new mirror, or a Data function mirroring the
  whole loop (`SGT`, `gtree`) plus one lemma equating the loop to it. The
  second keeps the invariant proof free of Bytes and reads better.
- **Read-ahead pairs.** Each loop gets its read pair as the literal
  `B.at(BT, j)`. A rewrite with `at_pair_t` turns it into a pair, so the
  destructuring `(b, +x) = r` reduces. find reads `j + 2` while its
  invariant needs `(j + 1) + 1`; `add11` bridges the two for every word, so no
  range reasoning is needed.
- **2^32.** Index steps need `to_nat(j + 1) = to_nat(j) + 1`, which comes
  from `to_nat_add_fits_p` with a bound below `Nat.pow(2n, 32n)`. bend2
  evaluates two terms that differ, and evaluating 2^32 overflows. So
  `four_lt_e` and `fits_e` are proven for a variable exponent e, and
  `add_fits` instantiates e = 32n only in a type that meets the
  dependency's hypothesis syntactically. The 4 * 2^d = 2^(d+2) step uses
  `mul_assoc(2, 2, 2^d)` with d a variable, so no conversion unfolds a big
  number.
- **Rewrite direction** was again the most common error, about 15 times.
  `%e : M` needs `e : {new == old}`, and M with `_` set to old must be the
  goal. A second error class was passing a and b in the wrong order to
  `Equal.sym(A, a, b, e)` (e : {a == b}).
- **Smaller traps.** A match cannot follow a let or a rewrite, so case-split
  first and rewrite in each branch. `+x =` refuses an Array or a Bytes, so
  those are written inline. A fuel matched `1n+k` needs `+n` when k is used
  twice. `GT` clashes with Cmp's constructor.
- **Parallel work.** The pure list laws, find/find2, same/same1/to_list and
  grow/empty/of_list were proven by forked agents on top of the core files,
  each in its own file, while the core, append and shift were done in the
  main thread. Each fork checked first or second time, because the core
  lemmas (`at_pair_t`, `at_view_t`, `inc_fits`, the ok parts) already had
  the shape every loop needed.
- **Nothing false found.** Every law held as stated, and no hypothesis was
  unusable. `find_view`/`find2_view` do not need `c < 256` for the
  reference version (it is there for the word-at-a-time version).
  `set_view` needs `i < len` only so that word `i >> 2` lies inside the
  block. `append_ok` and the pair laws need nothing about src.

## Plan for fast.bend (not done here)

`fast.bend` is to be proven against `bytes.bend`. The mirror (`BT`), the
byte/word lemmas (`unpack_get_i`, `unpack_set_i`, `wd_get`, `wl_set`) and the
bounds (`add_fits`) are what a word-at-a-time proof will need. Its loops step
over words, so they will want an `unpack` lemma for a whole word at index
4q (`unpack_get` already has the 4q + r form).
