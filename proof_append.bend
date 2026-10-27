import Base
import ./defs.bend as D
import ./bytes.bend as B
import ./proof_seq.bend as Q
import ./proof_core.bend as C
import ./proof_ops.bend as O
import ../lawful-words/defs.bend as W
import ../lawful-words/proof_nat.bend as N
import ../lawful-words/proof_bytes.bend as Y
import ../lawful-arrays/proof_base.bend as AB
import ../lawful-arrays/proof_tree.bend as P
import ../lawful-arrays/proof_index.bend as I

# append: n pushes onto dst of bytes s.. of src, and shift, laws on the mirror
# (named as in proof_ops.bend). The loop lemmas take dst as a mirror that changes
# at every push (O.push_eq_t names the new one) and src as a fixed mirror.

# Lists
# =====

law append_nil:
  for +xs: List<&2, U32>
  {List.append(&2, U32, xs, Nil{}) == xs : List<&2, U32>}

def append_nil(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, t}:
      %append_nil(t) : {x <> List.append(&2, U32, t, Nil{}) == x <> _ : List<&2, U32>}
      {==}

law append_assoc:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +zs: List<&2, U32>
  {List.append(&2, U32, List.append(&2, U32, xs, ys), zs) == List.append(&2, U32, xs, List.append(&2, U32, ys, zs)) : List<&2, U32>}

def append_assoc(xs, ys, zs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, t}:
      %append_assoc(t, ys, zs) :
        {x <> List.append(&2, U32, List.append(&2, U32, t, ys), zs) == x <> _ : List<&2, U32>}
      {==}

law drop_zero:
  for +xs: List<&2, U32>
  {List.drop(&2, U32, xs, 0n) == xs : List<&2, U32>}

def drop_zero(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      {==}

def is_some_t(m: Maybe<&2, U32>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

law none_some:
  for -x: U32
  for e: {None{} == Some{x} : Maybe<&2, U32>}
  Empty

def none_some(x, e):
  %e : is_some_t(_)
  Unit{}

law some_inj:
  for +x: U32
  for +y: U32
  for +e: {Some{x} == Some{y} : Maybe<&2, U32>}
  {x == y : U32}

def some_inj(x, y, e):
  Equal.cong(Maybe<&2, U32>, U32, m => I.unsome(U32, x, m), Some{x}, Some{y}, e)

law slice_zero:
  for +xs: List<&2, U32>
  for +i: Nat
  {D.slice(xs, i, 0n) == Nil{} : List<&2, U32>}

def slice_zero(xs, i):
  Q.take_zero(List.drop(&2, U32, xs, i))

# A slice of 1 + k from i starts with element i.
law slice_cons:
  for +xs: List<&2, U32>
  for +i: Nat
  for +k: Nat
  for +x: U32
  for +h: {List.get(&2, U32, xs, i) == Some{x} : Maybe<&2, U32>}
  {D.slice(xs, i, 1n+k) == x <> D.slice(xs, Nat.add(i, 1n), k) : List<&2, U32>}

def slice_cons(xs, i, k, x, h):
  match xs i:
    case Nil{} _:
      Empty.absurd({D.slice(Nil{}, i, 1n+k) == x <> D.slice(Nil{}, Nat.add(i, 1n), k) : List<&2, U32>}, none_some(x, h))
    case Con{+y, t} 0n:
      %some_inj(y, x, h) : {y <> List.take(&2, U32, t, k) == _ <> List.take(&2, U32, List.drop(&2, U32, t, 0n), k) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, List.drop(&2, U32, t, 0n), t, drop_zero(t)) :
        {y <> List.take(&2, U32, t, k) == y <> List.take(&2, U32, _, k) : List<&2, U32>}
      {==}
    case Con{y, t} 1n+p:
      slice_cons(t, p, k, x, h)

# Nat order
# =========

law le_split:
  for +a: Nat
  for +k: Nat
  for +m: Nat
  for +h: {Nat.is_le(Nat.add(a, 1n+k), m) == True{} : Bool}
  {Nat.is_lt(a, m) == True{} : Bool}

def le_split(a, k, m, h):
  +h2 = AB.subst(Nat, y => {Nat.is_le(y, m) == True{} : Bool}, Nat.add(a, 1n+k), 1n+Nat.add(a, k), N.add_succ(a, k), h)
  N.le_lt_trans(a, Nat.add(a, k), m, N.le_add_r(a, k),
    Equal.trans(Bool, Nat.is_lt(Nat.add(a, k), m), Nat.is_le(1n+Nat.add(a, k), m), True{},
      Equal.sym(Bool, Nat.is_le(1n+Nat.add(a, k), m), Nat.is_lt(Nat.add(a, k), m), N.le_succ_lt(Nat.add(a, k), m)), h2))

law le_shift:
  for +a: Nat
  for +k: Nat
  for +m: Nat
  for +h: {Nat.is_le(Nat.add(a, 1n+k), m) == True{} : Bool}
  {Nat.is_le(Nat.add(Nat.add(a, 1n), k), m) == True{} : Bool}

def le_shift(a, k, m, h):
  %Equal.sym(Nat, Nat.add(Nat.add(a, 1n), k), Nat.add(a, Nat.add(1n, k)), N.add_assoc(a, 1n, k)) : {Nat.is_le(_, m) == True{} : Bool}
  h

# One push
# ========

# The tree after pushing x onto BT(ld, td).
def PT(+ld: U32, +td: P.Tree<U32>, +x: U32) -> P.Tree<U32>:
  I.set_tree(U32, td, (ld >> 2n : U32), W.put_byte(C.WD(td, (ld >> 2n : U32)), U32.to_nat((ld .&. 3 : U32)), x))

law step_room:
  for +ld: U32
  for +td: P.Tree<U32>
  for +d: Nat
  for +k: Nat
  for +hd: {D.ok(C.BT(ld, td), d) == True{} : Bool}
  for +hc: {Nat.is_le(Nat.add(U32.to_nat(ld), 1n+k), D.cap(C.BT(ld, td))) == True{} : Bool}
  {Nat.is_lt(U32.to_nat(ld), Nat.mul(4n, Nat.pow(2n, d))) == True{} : Bool}

def step_room(ld, td, d, k, hd, hc):
  +M = Nat.mul(4n, Nat.pow(2n, d))
  le_split(U32.to_nat(ld), k, M,
    AB.subst(Nat, y => {Nat.is_le(Nat.add(U32.to_nat(ld), 1n+k), y) == True{} : Bool}, D.cap(C.BT(ld, td)), M, O.cap_ok_t(ld, td, d, hd), hc))

law step_lt:
  for +ld: U32
  for +td: P.Tree<U32>
  for +d: Nat
  for +k: Nat
  for +hd: {D.ok(C.BT(ld, td), d) == True{} : Bool}
  for +hc: {Nat.is_le(Nat.add(U32.to_nat(ld), 1n+k), D.cap(C.BT(ld, td))) == True{} : Bool}
  {Nat.is_lt(D.size(C.BT(ld, td)), D.cap(C.BT(ld, td))) == True{} : Bool}

def step_lt(ld, td, d, k, hd, hc):
  le_split(U32.to_nat(ld), k, D.cap(C.BT(ld, td)), hc)

law step_ok:
  for +ld: U32
  for +td: P.Tree<U32>
  for +d: Nat
  for +x: U32
  for +k: Nat
  for +hd: {D.ok(C.BT(ld, td), d) == True{} : Bool}
  for +hc: {Nat.is_le(Nat.add(U32.to_nat(ld), 1n+k), D.cap(C.BT(ld, td))) == True{} : Bool}
  {D.ok(C.BT((ld + 1 : U32), PT(ld, td, x)), d) == True{} : Bool}

def step_ok(ld, td, d, x, k, hd, hc):
  AB.subst(D.Bytes, y => {D.ok(y, d) == True{} : Bool}, B.push(C.BT(ld, td), x), C.BT((ld + 1 : U32), PT(ld, td, x)),
    O.push_eq_t(ld, td, x), O.push_ok_t(ld, td, d, x, hd, step_lt(ld, td, d, k, hd, hc)))

law step_cap:
  for +ld: U32
  for +td: P.Tree<U32>
  for +d: Nat
  for +x: U32
  for +k: Nat
  for +hd: {D.ok(C.BT(ld, td), d) == True{} : Bool}
  for +hc: {Nat.is_le(Nat.add(U32.to_nat(ld), 1n+k), D.cap(C.BT(ld, td))) == True{} : Bool}
  {Nat.is_le(Nat.add(U32.to_nat((ld + 1 : U32)), k), D.cap(C.BT((ld + 1 : U32), PT(ld, td, x)))) == True{} : Bool}

def step_cap(ld, td, d, x, k, hd, hc):
  +M = Nat.mul(4n, Nat.pow(2n, d))
  +hr = step_room(ld, td, d, k, hd, hc)
  %Equal.sym(Nat, D.cap(C.BT((ld + 1 : U32), PT(ld, td, x))), M, O.cap_ok_t((ld + 1 : U32), PT(ld, td, x), d, step_ok(ld, td, d, x, k, hd, hc))) :
    {Nat.is_le(Nat.add(U32.to_nat((ld + 1 : U32)), k), _) == True{} : Bool}
  %Equal.sym(Nat, U32.to_nat((ld + 1 : U32)), Nat.add(U32.to_nat(ld), 1n), C.inc_fits(ld, d, C.ok_d(ld, td, d, hd), hr)) :
    {Nat.is_le(Nat.add(_, k), M) == True{} : Bool}
  le_shift(U32.to_nat(ld), k, M,
    AB.subst(Nat, y => {Nat.is_le(Nat.add(U32.to_nat(ld), 1n+k), y) == True{} : Bool}, D.cap(C.BT(ld, td)), M, O.cap_ok_t(ld, td, d, hd), hc))

# One read of src
# ===============

law read_lt:
  for +ls: U32
  for +s: U32
  for +k: Nat
  for +hs: {Nat.is_le(Nat.add(U32.to_nat(s), 1n+k), U32.to_nat(ls)) == True{} : Bool}
  {Nat.is_lt(U32.to_nat(s), U32.to_nat(ls)) == True{} : Bool}

def read_lt(ls, s, k, hs):
  le_split(U32.to_nat(s), k, U32.to_nat(ls), hs)

law read_inc:
  for +ls: U32
  for +ts: P.Tree<U32>
  for +e: Nat
  for +s: U32
  for +k: Nat
  for +he: {D.ok(C.BT(ls, ts), e) == True{} : Bool}
  for +hs: {Nat.is_le(Nat.add(U32.to_nat(s), 1n+k), U32.to_nat(ls)) == True{} : Bool}
  {U32.to_nat((s + 1 : U32)) == Nat.add(U32.to_nat(s), 1n) : Nat}

def read_inc(ls, ts, e, s, k, he, hs):
  C.inc_fits(s, e, C.ok_d(ls, ts, e, he),
    N.lt_le_trans(U32.to_nat(s), U32.to_nat(ls), Nat.mul(4n, Nat.pow(2n, e)), read_lt(ls, s, k, hs), C.ok_len(ls, ts, e, he)))

law read_next:
  for +ls: U32
  for +ts: P.Tree<U32>
  for +e: Nat
  for +s: U32
  for +k: Nat
  for +he: {D.ok(C.BT(ls, ts), e) == True{} : Bool}
  for +hs: {Nat.is_le(Nat.add(U32.to_nat(s), 1n+k), U32.to_nat(ls)) == True{} : Bool}
  {Nat.is_le(Nat.add(U32.to_nat((s + 1 : U32)), k), U32.to_nat(ls)) == True{} : Bool}

def read_next(ls, ts, e, s, k, he, hs):
  %Equal.sym(Nat, U32.to_nat((s + 1 : U32)), Nat.add(U32.to_nat(s), 1n), read_inc(ls, ts, e, s, k, he, hs)) :
    {Nat.is_le(Nat.add(_, k), U32.to_nat(ls)) == True{} : Bool}
  le_shift(U32.to_nat(s), k, U32.to_nat(ls), hs)

# append
# ======

law append_go_pair:
  for +n: Nat
  for -dst: D.Bytes
  for +ls: U32
  for +ts: P.Tree<U32>
  for +s: U32
  {B.append.go(n, dst, B.at(C.BT(ls, ts), s), s) == (Pair.fst(D.Bytes, D.Bytes, B.append.go(n, dst, B.at(C.BT(ls, ts), s), s)), C.BT(ls, ts)) : D.Bytes & D.Bytes}

def append_go_pair(n, dst, ls, ts, s):
  match n:
    case 0n:
      %Equal.sym(D.Bytes & U32, B.at(C.BT(ls, ts), s), (C.BT(ls, ts), C.AT(ls, ts, s)), C.at_pair_t(ls, ts, s)) :
        {B.append.go(0n, dst, _, s) == (Pair.fst(D.Bytes, D.Bytes, B.append.go(0n, dst, _, s)), C.BT(ls, ts)) : D.Bytes & D.Bytes}
      {==}
    case 1n+k:
      %Equal.sym(D.Bytes & U32, B.at(C.BT(ls, ts), s), (C.BT(ls, ts), C.AT(ls, ts, s)), C.at_pair_t(ls, ts, s)) :
        {B.append.go(1n+k, dst, _, s) == (Pair.fst(D.Bytes, D.Bytes, B.append.go(1n+k, dst, _, s)), C.BT(ls, ts)) : D.Bytes & D.Bytes}
      append_go_pair(k, B.push(dst, C.AT(ls, ts, s)), ls, ts, (s + 1 : U32))

law append_pair_t:
  for +ld: U32
  for +td: P.Tree<U32>
  for +ls: U32
  for +ts: P.Tree<U32>
  for +s: U32
  for +n: U32
  {B.append(C.BT(ld, td), C.BT(ls, ts), s, n) == (Pair.fst(D.Bytes, D.Bytes, B.append(C.BT(ld, td), C.BT(ls, ts), s, n)), C.BT(ls, ts)) : D.Bytes & D.Bytes}

def append_pair_t(ld, td, ls, ts, s, n):
  append_go_pair(U32.to_nat(n), C.BT(ld, td), ls, ts, s)

law append_go_ok:
  for +n: Nat
  for +ld: U32
  for +td: P.Tree<U32>
  for +ls: U32
  for +ts: P.Tree<U32>
  for +d: Nat
  for +s: U32
  for +hd: {D.ok(C.BT(ld, td), d) == True{} : Bool}
  for +hc: {Nat.is_le(Nat.add(U32.to_nat(ld), n), D.cap(C.BT(ld, td))) == True{} : Bool}
  {D.ok(Pair.fst(D.Bytes, D.Bytes, B.append.go(n, C.BT(ld, td), B.at(C.BT(ls, ts), s), s)), d) == True{} : Bool}

def append_go_ok(n, ld, td, ls, ts, d, s, hd, hc):
  match n:
    case 0n:
      %Equal.sym(D.Bytes & U32, B.at(C.BT(ls, ts), s), (C.BT(ls, ts), C.AT(ls, ts, s)), C.at_pair_t(ls, ts, s)) :
        {D.ok(Pair.fst(D.Bytes, D.Bytes, B.append.go(0n, C.BT(ld, td), _, s)), d) == True{} : Bool}
      hd
    case 1n+k:
      +x = C.AT(ls, ts, s)
      %Equal.sym(D.Bytes & U32, B.at(C.BT(ls, ts), s), (C.BT(ls, ts), x), C.at_pair_t(ls, ts, s)) :
        {D.ok(Pair.fst(D.Bytes, D.Bytes, B.append.go(1n+k, C.BT(ld, td), _, s)), d) == True{} : Bool}
      %Equal.sym(D.Bytes, B.push(C.BT(ld, td), x), C.BT((ld + 1 : U32), PT(ld, td, x)), O.push_eq_t(ld, td, x)) :
        {D.ok(Pair.fst(D.Bytes, D.Bytes, B.append.go(k, _, B.at(C.BT(ls, ts), (s + 1 : U32)), (s + 1 : U32))), d) == True{} : Bool}
      append_go_ok(k, (ld + 1 : U32), PT(ld, td, x), ls, ts, d, (s + 1 : U32), step_ok(ld, td, d, x, k, hd, hc), step_cap(ld, td, d, x, k, hd, hc))

law append_ok_t:
  for +ld: U32
  for +td: P.Tree<U32>
  for +ls: U32
  for +ts: P.Tree<U32>
  for +d: Nat
  for +s: U32
  for +n: U32
  for +hd: {D.ok(C.BT(ld, td), d) == True{} : Bool}
  for +hc: {Nat.is_le(Nat.add(D.size(C.BT(ld, td)), U32.to_nat(n)), D.cap(C.BT(ld, td))) == True{} : Bool}
  {D.ok(Pair.fst(D.Bytes, D.Bytes, B.append(C.BT(ld, td), C.BT(ls, ts), s, n)), d) == True{} : Bool}

def append_ok_t(ld, td, ls, ts, d, s, n, hd, hc):
  append_go_ok(U32.to_nat(n), ld, td, ls, ts, d, s, hd, hc)

law append_go_view:
  for +n: Nat
  for +ld: U32
  for +td: P.Tree<U32>
  for +ls: U32
  for +ts: P.Tree<U32>
  for +d: Nat
  for +e: Nat
  for +s: U32
  for +hd: {D.ok(C.BT(ld, td), d) == True{} : Bool}
  for +he: {D.ok(C.BT(ls, ts), e) == True{} : Bool}
  for +hs: {Nat.is_le(Nat.add(U32.to_nat(s), n), U32.to_nat(ls)) == True{} : Bool}
  for +hc: {Nat.is_le(Nat.add(U32.to_nat(ld), n), D.cap(C.BT(ld, td))) == True{} : Bool}
  {D.view(Pair.fst(D.Bytes, D.Bytes, B.append.go(n, C.BT(ld, td), B.at(C.BT(ls, ts), s), s))) == List.append(&2, U32, D.view(C.BT(ld, td)), D.slice(D.view(C.BT(ls, ts)), U32.to_nat(s), n)) : List<&2, U32>}

def append_go_view(n, ld, td, ls, ts, d, e, s, hd, he, hs, hc):
  match n:
    case 0n:
      +V = D.view(C.BT(ld, td))
      +xs = D.view(C.BT(ls, ts))
      %Equal.sym(D.Bytes & U32, B.at(C.BT(ls, ts), s), (C.BT(ls, ts), C.AT(ls, ts, s)), C.at_pair_t(ls, ts, s)) :
        {D.view(Pair.fst(D.Bytes, D.Bytes, B.append.go(0n, C.BT(ld, td), _, s))) == List.append(&2, U32, V, D.slice(xs, U32.to_nat(s), 0n)) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, D.slice(xs, U32.to_nat(s), 0n), Nil{}, slice_zero(xs, U32.to_nat(s))) :
        {V == List.append(&2, U32, V, _) : List<&2, U32>}
      Equal.sym(List<&2, U32>, List.append(&2, U32, V, Nil{}), V, append_nil(V))
    case 1n+k:
      +x = C.AT(ls, ts, s)
      +s1 = (s + 1 : U32)
      +ld1 = (ld + 1 : U32)
      +td1 = PT(ld, td, x)
      +V = D.view(C.BT(ld, td))
      +xs = D.view(C.BT(ls, ts))
      +RHS = List.append(&2, U32, V, D.slice(xs, U32.to_nat(s), 1n+k))
      %Equal.sym(D.Bytes & U32, B.at(C.BT(ls, ts), s), (C.BT(ls, ts), x), C.at_pair_t(ls, ts, s)) :
        {D.view(Pair.fst(D.Bytes, D.Bytes, B.append.go(1n+k, C.BT(ld, td), _, s))) == RHS : List<&2, U32>}
      %Equal.sym(D.Bytes, B.push(C.BT(ld, td), x), C.BT(ld1, td1), O.push_eq_t(ld, td, x)) :
        {D.view(Pair.fst(D.Bytes, D.Bytes, B.append.go(k, _, B.at(C.BT(ls, ts), s1), s1))) == RHS : List<&2, U32>}
      +hd1 = step_ok(ld, td, d, x, k, hd, hc)
      %Equal.sym(List<&2, U32>, D.view(Pair.fst(D.Bytes, D.Bytes, B.append.go(k, C.BT(ld1, td1), B.at(C.BT(ls, ts), s1), s1))),
        List.append(&2, U32, D.view(C.BT(ld1, td1)), D.slice(xs, U32.to_nat(s1), k)),
        append_go_view(k, ld1, td1, ls, ts, d, e, s1, hd1, he, read_next(ls, ts, e, s, k, he, hs), step_cap(ld, td, d, x, k, hd, hc))) :
        {_ == RHS : List<&2, U32>}
      +hv = AB.subst(U32, y => {U32.is_lt(y, 256) == True{} : Bool}, W.byte(C.WD(ts, (s >> 2n : U32)), U32.to_nat((s .&. 3 : U32))), x,
        Equal.sym(U32, x, W.byte(C.WD(ts, (s >> 2n : U32)), U32.to_nat((s .&. 3 : U32))), C.at_val(ls, ts, s)),
        Y.byte_lt(C.WD(ts, (s >> 2n : U32)), U32.to_nat((s .&. 3 : U32))))
      +pv = AB.subst(D.Bytes, y => {D.view(y) == List.append(&2, U32, V, [x]) : List<&2, U32>}, B.push(C.BT(ld, td), x), C.BT(ld1, td1),
        O.push_eq_t(ld, td, x), O.push_view_t(ld, td, d, x, hd, step_lt(ld, td, d, k, hd, hc), hv))
      %Equal.sym(List<&2, U32>, D.view(C.BT(ld1, td1)), List.append(&2, U32, V, [x]), pv) :
        {List.append(&2, U32, _, D.slice(xs, U32.to_nat(s1), k)) == RHS : List<&2, U32>}
      %Equal.sym(Nat, U32.to_nat(s1), Nat.add(U32.to_nat(s), 1n), read_inc(ls, ts, e, s, k, he, hs)) :
        {List.append(&2, U32, List.append(&2, U32, V, [x]), D.slice(xs, _, k)) == RHS : List<&2, U32>}
      +hx = Equal.sym(Maybe<&2, U32>, Some{x}, List.get(&2, U32, xs, U32.to_nat(s)),
        C.at_view_t(ls, ts, e, s, C.ok_full(ls, ts, e, he), C.ok_d(ls, ts, e, he), C.ok_len(ls, ts, e, he), read_lt(ls, s, k, hs)))
      %Equal.sym(List<&2, U32>, D.slice(xs, U32.to_nat(s), 1n+k), x <> D.slice(xs, Nat.add(U32.to_nat(s), 1n), k),
        slice_cons(xs, U32.to_nat(s), k, x, hx)) :
        {List.append(&2, U32, List.append(&2, U32, V, [x]), D.slice(xs, Nat.add(U32.to_nat(s), 1n), k)) == List.append(&2, U32, V, _) : List<&2, U32>}
      append_assoc(V, [x], D.slice(xs, Nat.add(U32.to_nat(s), 1n), k))

law append_view_t:
  for +ld: U32
  for +td: P.Tree<U32>
  for +ls: U32
  for +ts: P.Tree<U32>
  for +d: Nat
  for +e: Nat
  for +s: U32
  for +n: U32
  for +hd: {D.ok(C.BT(ld, td), d) == True{} : Bool}
  for +he: {D.ok(C.BT(ls, ts), e) == True{} : Bool}
  for +hs: {Nat.is_le(Nat.add(U32.to_nat(s), U32.to_nat(n)), D.size(C.BT(ls, ts))) == True{} : Bool}
  for +hc: {Nat.is_le(Nat.add(D.size(C.BT(ld, td)), U32.to_nat(n)), D.cap(C.BT(ld, td))) == True{} : Bool}
  {D.view(Pair.fst(D.Bytes, D.Bytes, B.append(C.BT(ld, td), C.BT(ls, ts), s, n))) == List.append(&2, U32, D.view(C.BT(ld, td)), D.slice(D.view(C.BT(ls, ts)), U32.to_nat(s), U32.to_nat(n))) : List<&2, U32>}

def append_view_t(ld, td, ls, ts, d, e, s, n, hd, he, hs, hc):
  append_go_view(U32.to_nat(n), ld, td, ls, ts, d, e, s, hd, he, hs, hc)
