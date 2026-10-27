# Fast versions: review (2026-10-27)

Five laws added with the fast.bend proofs (`fast_find`, `fast_find2`, `fast_append_view`,
`fast_append_ok`, `fast_append_pair`), reviewed by Claude, GPT and Grok after they were proven:
- Grok: ACCEPT.
- Claude and GPT, should fix: `fast_find`/`fast_find2` carry the reference results only under
  their hypotheses, while `find_pair`/`find2_pair` hold for any arguments, so code calling the fast
  versions could not use those two at full generality. Added `fast_find_pair` and `fast_find2_pair`
  (unconditional), proven from `fast_eq`/`fast2_eq`.
- Follow-up: Claude and GPT ACCEPT. Stating append on the view only is right: whole-buffer equality
  would constrain unspecified padding (GPT).

The proof itself first found a bug in fast find/find2 (fixed in 45f3219); see `notes/fast_proof.md`.
