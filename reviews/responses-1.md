# Round 1: responses (2026-10-27)

Reviewers: Claude (Opus 5.5), GPT (GPT-6.1-Sol), Grok (4.7). No law was false of the reference code.

| finding | raised by | change |
|---|---|---|
| `find`/`find2` allow c >= 256; a word-at-a-time search compares 8 bits per byte and would match 266 against LF | Claude (GPT's tests too) | hypotheses `c < 256` (`hc`, `hc1`, `hc2`) |
| No pair-shaped laws for rewriting destructured results; own projections duplicate `Pair.fst/snd` | Claude | `at_pair`, `find_pair`, `find2_pair`, `append_pair`, `same_pair`, and pairs for every new operation; laws use `Pair.fst/snd` |
| Length and capacity can only be read by consuming the buffer | Claude, GPT | `len` (`len_view`, `len_pair`) and `capacity` (`capacity_view`, `capacity_pair`) |
| No facts about `first`/`first2` for parser proofs; `list_eq` soundness | Claude, GPT | `first_range`, `first_hit`, `first_miss` and the `first2_*` three (with defs `has`, `has2`); `list_eq_true` |
| No bridge to Base's file I/O (List<U32>) | Claude | `of_list` (`of_list_view`, `of_list_ok`), `to_list` (`to_list_view`, `to_list_pair`) |
| One buffer cannot hold the 2.8 GB file (cap 2^31 bytes); streaming needs trimming | Claude, GPT, Grok | kept the cap (pieces are read separately; every length stays far from 2^32, so no extra sum hypotheses); added `truncate` and `shift` (drop the first k bytes, move the rest down) with view and ok laws |
| `same` cannot compare two ranges of one buffer (REF/ALT trimming) | Claude | `same1` (`same1_view`, `same1_pair`) |
| `first`/`first2` comments hold only for from <= to <= length | Claude, GPT, Grok | comments state the domain |
| `ok` comment says sums fit; two 2^31 lengths wrap | Claude, GPT | comment rewritten: hypotheses keep sums in range |
| Reference loops read one byte ahead | GPT | documented in `bytes.bend`'s header (reads stay in the block, never reach a result) |
| Spot coverage for padding and edge cases | GPT | 20 cases added: garbage padding (`Bytes{1, ALeaf{0xFFFFFF41}}`), searching for 0 in a zero-padded word, empty range at len, last-byte write, zero-length append, the new operations (44 in all) |

Not taken:
- depth 30 with extra sum hypotheses on push/append (Grok, GPT): a 4 GiB buffer is not needed, since files are
  read in pieces, and depth 29 keeps every law free of overflow hypotheses;
- `push_size`/`append_size` (Claude): `view_size` with the view laws gives them;
- case-insensitive comparison and decimal numbers (Claude): they belong to lawful-fields;
- package imports by BendHub hash instead of sibling paths (Claude): at publishing time.
