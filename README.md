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
GPT and Grok (`reviews/`). `bytes.bend` is the reference implementation (a byte at a time); proofs,
then a word-at-a-time implementation under the same laws, are next.

`bend test/spot.bend` evaluates both sides of the laws on small buffers, including garbage padding.
Builds on `lawful-words` and `lawful-arrays`.

MIT (see `LICENSE`).
