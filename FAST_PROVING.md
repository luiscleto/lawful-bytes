# Proving lawful-bytes' fast.bend: brief

`fast.bend` holds word-at-a-time versions of `find`, `find2` and `append`, with the same signatures
as the reference operations in `bytes.bend`. It was written for framebender's speed (see
`../framebender/notes/bytes.md`, "lawful-bytes bodies replaced"). `test/fast_spot.bend` checks them
against the reference bodies.

## Goal

Prove that each fast operation gives exactly the reference operation's result, as an equation of
results, Bytes included: `fast.find(b, from, to, c) == bytes.find(b, from, to, c)` under the
reference laws' hypotheses (`D.ok(b, d)`, ranges, `c < 256`), and likewise for the others. Then
every lawful-bytes law holds for fast.bend too.

Add the equations to `LAWS.bend` as new laws, in a section "Fast versions". Keep them minimal:
only the hypotheses the proofs need, and no change to any existing law. The lead will send the
additions to the reviewers. Put the proofs in `proof_fast*.bend` and fill them from `PROOF.bend`.
`./check.sh` must pass with `bend` and `--verdict`.

The proofs need lawful-words' `zb_zero` (the zero-byte test), `byte_xor`, `bcast`/`byte_pack4`,
and `merge` with `byte_merge_lo`/`byte_merge_hi` (the shifted-word copy).

If a fast body is not equal to the reference (a real bug), stop and report it with a
counterexample: framebender depends on it. Do not change `fast.bend` yourself.

## Rules

As before: `nice -n 19` and a `timeout` for every check; one heavy check at a time; no commits; keep
`notes/fast_proof.md`. Report when done, or after about four hours.
