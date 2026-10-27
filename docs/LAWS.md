# lawful-bytes: a guide to the laws

`LAWS.bend` holds 51 laws about `Bytes{len, buf}`: bytes packed four to a `U32` word,
little-endian, in a block of 2^d words. Byte i is byte `i & 3` of word `i >> 2`.
- **`view(b)`:** the first `len` bytes. Every law describes an operation by what it does to the
  view, so code is proven against a plain list while it runs on words.
- **`ok(b, d)`:** b is well formed. Its block is perfect with 2^d words, d <= 29, and
  `len <= 4 * 2^d`.
- **The size limit:** a buffer holds at most 2^31 bytes (2 GiB). Every index and length then fits
  a U32, and no law needs overflow hypotheses. Larger files are read in pieces.
- **Results:** a `Bytes` has exactly one owner, so every read hands it back: `Bytes & U32`. The
  `*_pair` laws say what comes back is the same buffer.

| group | laws | in plain terms |
|---|---|---|
| What a buffer holds | `view_size`, `view_bytes`, `cap_ok` | the view has len bytes, all below 256; capacity is 4 * 2^d |
| Making | `empty_view`, `empty_ok`, `grow_view`, `grow_ok`, `of_list_view`, `of_list_ok` | an empty buffer; the same bytes in a bigger block; a buffer from a list of bytes (Base's file reads give lists) |
| Reading | `at_view`, `at_pair`, `len_view`, `len_pair`, `capacity_view`, `capacity_pair`, `to_list_view`, `to_list_pair` | byte i; the length; the capacity; a range as a list |
| Searching | `find_view`, `find_pair`, `find2_view`, `find2_pair` | the first index in `from .. to-1` holding c (or either of c1, c2), or to if there is none. The value must be a byte (c < 256) |
| Comparing | `same_view`, `same_pair`, `same1_view`, `same1_pair` | two ranges of equal length are equal: across two buffers, or within one |
| Writing | `set_view`, `set_ok`, `push_view`, `push_ok`, `append_view`, `append_ok`, `append_pair` | set byte i; add a byte at the end; add a range of another buffer at the end (room required) |
| Trimming | `truncate_view`, `truncate_ok`, `shift_view`, `shift_ok` | keep the first n bytes; drop the first k and move the rest down (for reading a stream in pieces) |
| Facts for parsers | `first_range`, `first_hit`, `first_miss`, the `first2_*` three, `list_eq_true`, `list_eq_refl` | a search's answer lies in the range, holds the value when below `to`, and no earlier index does; `list_eq` is equality |
| Fast versions | `fast_find`, `fast_find2`, `fast_find_pair`, `fast_find2_pair`, `fast_append_view`, `fast_append_ok`, `fast_append_pair` | `fast.bend`'s word-at-a-time search gives exactly the reference result; its copy meets the reference copy's laws on the view |

## Where to look hardest

- **`c < 256` on the searches.** A word-at-a-time search compares 8 bits per byte, so a value
  of 266 would match an LF.
- **Fast append is stated on the view only.** It writes whole words, so up to 3 bytes past the new
  length differ from the reference's. Those bytes are outside the view by definition.
- **The fast search's bug.** The proof found it before proving anything: a search starting
  mid-word, just after a match, could answer a wrong index. It is fixed, with regression tests,
  and described in `../NOTES.md`.

## Left out on purpose

- **Buffers over 2 GiB.** Keeping the limit keeps every law free of overflow hypotheses.
- **Case-insensitive comparison and decimal numbers:** these are in lawful-fields, or in the
  caller.
- **Exact padding bytes past `len`:** they are unspecified, so faster code may write them freely.
