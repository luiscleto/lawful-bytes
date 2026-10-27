# Proving lawful-bytes: brief for the proof agent

## Goal

Prove every law in `LAWS.bend`: 44 laws about packed byte buffers (`D.Bytes`), stated on the list
of bytes a buffer holds (`D.view`), for the reference operations in `bytes.bend`. Three reviewers
from different model families accepted the statements, so they are frozen: never edit
`LAWS.bend`, `defs.bend` or `bytes.bend`. If a law looks false or unprovable as stated, stop and
report it with the reason.

Another agent may add a `fast.bend` here (faster word-at-a-time versions of some operations). Do
not touch it; it is proven later, against `bytes.bend`.

Proofs go in `PROOF.bend` (imports `LAWS.bend` and fills every law, as `def name(...) -> {...}:`
with the law's name) plus helper files `proof_*.bend`. Gate, in a `check.sh` (copy
`../lawful-arrays/check.sh`): `bend PROOF.bend --check-only`, then `--verdict`. Both must print
ALL PROOFS CHECK, with no `@unsafe` and no foreign code anywhere in the import graph.
`bend test/spot.bend` must stay all True.

## What you can use

Both dependencies are fully proven:
- `../lawful-words`: 83 laws about U32 as numbers.
  - Import its `PROOF.bend`, or its proof files.
  - Of interest: `to_nat_shrn`, `to_nat_and_mask`, `to_nat_split`, `byte_put_same`,
    `byte_put_other`, `to_nat_byte`, `byte_lt`, `is_eq_true`, `is_lt_to_nat`, `to_nat_inc_lt`, the
    Nat section.
  - Its notes (`../lawful-words/notes/proof.md`) explain how it handled 2^32 without evaluating it:
    read them.
- `../lawful-arrays`: 21 laws about `Array`: `get_view`, `set_view`, `get_pair`, `size_pair`,
  `get_new`, `new_view`, `view_inj`, `slot_small`...
  - Its notes (`../lawful-arrays/notes/proof.md`) explain the affinity workaround: mirror an array
    as a reusable tree. You will need the same for `Bytes`.

Laws of a dependency are proven, so you can call them.

## Hints

- `D.view(b)` is `take(len, unpack(A.view(buf)))`. Byte i is byte `i & 3` of word `i >> 2`. Most
  laws reduce to lawful-arrays' get/set laws plus list facts about `unpack` and `take`.
- The loops (`find.go`, `same.go`, `append.go`, `shift.go`, ...) carry the pair for the next
  step as a parameter. Prove each by induction on its fuel, with an invariant relating the current
  index to a list position.
- `first`/`first2`/`list_eq` laws are pure list facts.

## Bend proof notes (from the framebender and minebender proofs)

- `%e : G` rewrites with `e : {new == old}`: `G` is the goal with `_` where `old` is; the rest of the
  def proves `G` with `new` there. Use `Equal.sym` to turn an equation around. `Equal.trans`,
  `Equal.cong` are in Base. Rewrite direction was the most frequent error in every earlier proof.
- `match` only inspects parameters or pattern-bound variables; a computed value needs a helper def
  that takes it as a parameter. Matches follow parameter order (`match a b:` for both). No match
  after a let.
- No mutual recursion, no forward references (define helpers first). Termination: the first argument
  that changes must shrink structurally; put it first. Eliminators take the induction hypothesis
  as a function argument.
- Unfilled laws are dead claims: a proof cannot call an open law. Prove in dependency order.
- A law's `for x` without `+` cannot be reused in its proof: restate with `+` where needed (same
  statement otherwise). Every equation used twice needs `+`. Function-typed hypotheses are affine.
- Refuting `{True{} == False{}}` or `{1n+n == 0n}`: rewrite through a `disc` motive that sends one
  constructor to `Empty` and the other to `Unit`, answer `Unit{}`.
- `Bool.pick`, `&&`, `||` evaluate both sides; to reason about them, case-split.
- Recursive defs do not unfold on variables: a lemma about `f(x)` for variable `x` needs a case
  split on `x` first.
- `?name` prints the goal at that point; `?TODO` leaves a hole. Errors print expected/observed terms.
- Every operator needs its type: `(a + b : U32)`. Bare constructors in a let need an annotation.
- `../framebender/proof_base.bend` and `../framebender/proof_machine_nat.bend` have proven Nat and
  Word facts you may copy (same author; MIT). `String.eq` soundness down to `Word.cmp` was proven
  there twice.

## Rules

- Use `nice -n 19` and a `timeout` for every check. No benchmarks. Another agent (`fb-bytes`)
  benchmarks on this machine, so keep heavy checks to one at a time.
- Never edit files in `../lawful-words` or `../lawful-arrays`.
- No git commits; the lead commits.
- Keep `notes/proof.md`: what is proven, the plan for the rest, and short bullets on where the
  proofs got hard and why.
- Stop when every law is proven and both gate commands pass, or after about five hours, and report:
  - what is proven;
  - what is left, and why;
  - any law you believe is false or unusable as stated.
