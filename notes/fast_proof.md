# Proof notes: fast.bend

## Status (2026-10-27)

All five new laws in LAWS.bend's section "Fast versions" are proven.
`./check.sh` prints ALL PROOFS CHECK for both `bend` (`--check-only`) and
`--verdict`, with 49 laws in all (44 + 5). Nothing in the import graph uses
`@unsafe` or foreign code. `test/spot.bend` gives 44 True and
`test/fast_spot.bend` 13 True. A copy of PROOF.bend with one fast proof
broken fails, so the pass is not a cached result. `fast.bend` was not
edited by me (the lead applied the find/find2 fix below).

The new laws:
- `fast_find`: `FA.find(b, from, to, c) == B.find(b, from, to, c)`, the
  same Bytes and the same index. The hypotheses are the reference
  find_view's: ok, from <= to, to <= size and c < 256. All are needed:
  - from <= to: with to < from, fast answers to while the reference answers
    from.
  - c < 256: rep(c) broadcasts a byte.
- `fast_find2`: the same for find2 (c1, c2 < 256).
- `fast_append_view`, `fast_append_ok`, `fast_append_pair`: append_view,
  append_ok and append_pair restated for `FA.append`. These are view-level
  laws, not an equation of Bytes: the word loop writes up to 3 bytes past
  the new length (from src bytes past s + n), so the blocks differ there.

### History: a bug found and fixed

The first fast.bend masked the first word's zero-byte flags with low(from)
after the test. zb is exact only at its lowest zero byte, and a match below
from borrowed and flagged the byte at from. Counterexample: "A@BC" searched
for 'A' from 1 gave 1 (the reference gives 4). find2 had the same bug. The fix
ORs U32.not(low(from)) into the word before zb, so the bytes below from are
0xFF: never flagged, and they never borrow. The lead committed it (45f3219)
with six regression cases in test/fast_spot.bend.

## Files

- `proof_fast_word.bend`: the word facts, with `P0(v)` = place of the
  first zero byte (4 if none).
  - `zb_none`/`zb_bidx`: the flags are clear iff there is no zero byte, and
    bidx finds the first one.
  - `zb2_none`/`zb2_bidx`: the same for the or of two flag words, at
    min(P1, P2).
  - `p0_xor`: searching w for c is searching w xor rep(c) for 0.
  - `p0_low`: in the first word, the bytes below from's place are skipped.
- `proof_fast_w1.bend`: fast.zb equals lawful-words' zb (and is
  associative), and the k-byte masked tests `tk1`..`tk3` via a 256-case
  per-byte lemma (`zbk_byte`).
- `proof_fast_w2.bend`: or facts, `rep(c) == pack4(c, c, c, c)` (through
  to_nat, with 2^8/2^16/2^24/2^32 kept abstract), the mask bytes of
  low(i), and the generated Bool tables `bt_*` (16 and 256 cases).
- `proof_fast_find.bend`: find.
  - `FG` mirrors find.go as a function of the tree (`fg_eq`).
  - `fast_eq` turns fast find into (BT, min(FG(...), to)).
  - The invariant `fi` covers 1 + k words left. Its cases are `fhit` (the
    word has a c: the answer is min(start + run, to)), `fnone0` (last word,
    no c: to) and `fskip` (no c: go on at the next word).
  - `fview_lt`/`fview_go` handle the word count `words(from, to)` and the
    empty range.
  - `fast_find_t` uses `to_nat_inj` against lawful-bytes' find_view_t and
    find_pair_t.
  - List facts: `drop_word` (byte 4q + o on is the rest of word q, then the
    later words) and `run_hit`/`run_skip`/`run_none`.
  - The "no hit" answer 4294967295 is handled by `min_top`
    (min(4294967295, to) == to), with 2^32 abstract (`gtop`).
- `proof_fast_find2.bend`: find2. It was derived from find's proof by a
  mechanical substitution:
  - one mask becomes an or of two;
  - run_len becomes run_len2 and first becomes first2;
  - three new facts: `min_run` (min of two runs is run_len2), `min_add` and
    `p0_low2`.
  It checked on the first run.
- `proof_fast_append.bend`: append.
  - `fa_eq` splits fast append into the reference prefix
    (X.append_pair_t), then dst's mirror, then the word loop as a tree
    function `AWT` (`aw_eq`).
  - The invariant `av`, with `avf` for the last partial word.
  - `mrg` turns the code's shifts into W.merge, and `mb_lo`/`mb_hi`/`win`
    place the bytes.
  - `align` makes dst's length a multiple of 4.
  - `x3_lt_e` bounds n' + 3 < 2^32 (abstract exponent).
- `PROOF.bend`, section "Fast versions": the generated wrappers.

## Where it got hard

- **Finding the bug** took less than proving: thinking about what zb's flags
  mean (exact only at the lowest zero byte) gave the counterexample before
  any proof was written.
- **The zero-byte flags.** Base's Bool.and/or match their first argument
  only, so whole-word brute force is impossible. bidx's three tests each
  depend only on the low k bytes, and lawful-words' byte-by-byte
  decomposition (app8, zf, allz) with one 256-case lemma covers them.
- **2^32 everywhere it appears** (the 4294967295 sentinel, rep's product,
  n + 3): every such fact is proven for an abstract bound and instantiated
  at 2^32 only in a type that matches syntactically. The lawful-fields notes
  explain why any other conversion crashes the checker.
- **Mirroring loops as Data functions** (FG, FG2, AWT) again kept the
  invariants free of Bytes.
- **Rewrite direction** stayed the most common slip, about ten in
  proof_fast_find.bend.
- **Parallel work.** The word facts and the append laws were proven by forked
  agents in parallel with find in the main thread, against a fixed set of
  statements (proof_fast_word.bend was written first with `?TODO` bodies).
  While the word file was in progress, the main thread checked against a
  private copy of those statements.
