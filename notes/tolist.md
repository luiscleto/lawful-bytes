# to_list in constant stack (2026-11-01)

## Why

`to_list.go` was `to_list.cons(x, to_list.go(...))`: not a tail call, so the
runtime pushed a two-word continuation per byte on its 2 GiB pool stack. A
slice of more than about 134M bytes (2^31 / 16) hit the guard page:
"bend: memory fault (machine stack overflow?)", exit 139. framebender
`norm -c w -w 2000000 --threads 1 data/kg/sub.vcf` did this in
`norm_run.to_spec`, which lists the whole output buffer `ob` (VCF text, over
134M bytes) when the run switches to the String mode. It was not the reference
slice in `serve.known`. The core showed `sp - io_stk = 2^31 - 8`, with the
stack full of `to_list.go` frames holding VCF bytes.

## What changed

- `bytes.bend`: `to_list.go(n, r, j, acc)` reads from the last byte back and
  conses each byte onto `acc`: a tail call, compiled to a loop with no
  continuation. `to_list(b, s, n)` starts at `j = (s + n) - 1` with `Nil`.
  `to_list.cons` is gone. No law changed.
- `proof_same.bend`: new `tl_pair`, `tl_view` (reading at `j = m + s` with
  `1 + m` bytes left gives `slice(view, s, 1 + m) ++ acc`) and `tl_view_k`
  (splits on `n`), plus list lemmas `append_nil`, `get_drop`, `take_snoc`,
  `slice_snoc`, and index lemmas `tl_val`, `tl_dec` (`j - 1` does not wrap
  for `j >= 1`), `tl_lt`. `to_list_pair_t` and `to_list_view_t` keep their
  statements, so PROOF.bend is unchanged.

## Checked

- `./check.sh`: ALL PROOFS CHECK for `--check-only` and `--verdict`, as on
  HEAD; no `?TODO`, no `@unsafe`. A copy with `tl_pair` broken fails.
- `test/spot.bend` 44 True, `test/fast_spot.bend` 13 True.
- Every other runtime op (bytes.bend, fast.bend) was already a tail loop: a
  program calling all of them compiles with no continuation segment from
  this package. The old to_list gave `to_list_go_k`. defs.bend's recursive
  functions (unpack, all_bytes, run_len, list_eq, ...) are specification
  only: none is compiled into framebender.
- Scratch harness (fill, to_list, fold the list), capped at 6 GB:
  - 100M bytes: old 1.12 s, 3184 MB peak; new 0.67 s, 1658 MB.
  - 10M bytes: old 0.09 s, 442 MB; new 0.07 s, 288 MB.
  - The results are the same.

## For framebender (not changed here)

- The lawful-bytes fix alone does not stop the `-w 2000000` crash. The new
  build lists `ob` and then overflows in `norm_run.chars` (the same frame
  per byte). Under a 6 GB cap it is OOM-killed within 3 s at -w 2M and 100M.
  Uncapped it reached 16 GB RSS: one list cell and then one String node per
  byte of `ob`. `to_spec` holding all of `ob` as a list is the real cost.
- `proof_b_cache.bend:434` rewrites `BY.to_list.go(U32.to_nat(0), _, S)`, the
  old 3-argument loop. It needs updating when framebender moves to this
  version (`SM.to_list_view_t`/`to_list_pair_t` are unchanged).
