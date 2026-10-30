# lawful-bytes

Bytes packed four to a `U32` word in an `Array<U32>` block, with laws that a proof checker
verifies. The runtime stores the block as one flat buffer, so scanning a 2.8 GB file this way takes
seconds where a list of characters takes minutes. Every law states what an operation does to the
plain list of bytes a buffer holds (`view`), so code using this package is proven against lists
while running on words.

Operations: `empty`, `grow`, `len`, `capacity`, `at`, `set`, `push`, `append` (a range of another
buffer), `find` / `find2` (the first of one or two byte values in a range), `same` / `same1`
(compare two ranges), `truncate`, `shift` (drop a prefix, for streaming), `of_list` / `to_list`
(Base's file I/O uses lists). A buffer holds up to 2^31 bytes.

Status: the laws (`LAWS.bend`, definitions in `defs.bend`) were reviewed in two rounds by Claude,
GPT and Grok (`reviews/`), and all 51 are proven (`PROOF.bend`; `./check.sh` runs `bend` and the
Lean-proven kernel, `--verdict`). `bytes.bend` is the reference implementation (a byte at a time);
`fast.bend` has `find`, `find2` and `append` working a word at a time, proven to give the same
results.

`bend test/spot.bend` evaluates both sides of the laws on small buffers, including garbage padding.
Builds on `lawful-words` and `lawful-arrays`, imported from BendHub.

## Use

Published on [BendHub](https://hub.bend-lang.com/name/lawful-bytes) with its laws and proofs. Bend fetches
an import by name and checks it against the package's hash:

```python
import lawful-bytes@0.1.0.0/bytes.bend as B  # the operations
import lawful-bytes@0.1.0.0/fast.bend as FA  # find, find2 and append, a word at a time
import lawful-bytes@0.1.0.0/LAWS.bend as L   # the laws, to use in your own proofs
import lawful-bytes@0.1.0.0/PROOF.bend as P  # their proofs, which a proof using a law needs loaded
```

Versions below 1.0 have laws reviewed by three AI models but not yet by a human expert.

MIT (see `LICENSE`).
