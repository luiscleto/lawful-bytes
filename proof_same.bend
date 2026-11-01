import Base
import ./defs.bend as D
import ./bytes.bend as B
import ./proof_seq.bend as Q
import ./proof_core.bend as C
import lawful-words@0.1.0.0/defs.bend as W
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U
import lawful-arrays@0.1.0.0/defs.bend as A
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-arrays@0.1.0.0/proof_tree.bend as P
import lawful-arrays@0.1.0.0/proof_index.bend as I

# The reading loops: to_list, same and same1, on the mirror C.BT(len, t)
# (law-shaped, as in proof_ops.bend). Each loop carries the read pair
# B.at(BT, s) literally: C.at_pair_t turns it into (BT, AT) so the loop steps,
# and the next call reads B.at(BT, s + 1), the same form one index on.

# List and index facts
# ====================

def mdisc(m: Maybe<&2, U32>) -> Type:
  match m:
    case None{}:
      Empty
    case Some{x}:
      Unit

law none_some:
  for -x: U32
  for e: {None{} == Some{x} : Maybe<&2, U32>}
  Empty

def none_some(x, e):
  %Equal.sym(Maybe<&2, U32>, None{}, Some{x}, e) : mdisc(_)
  Unit{}

law drop_zero:
  for +xs: List<&2, U32>
  {List.drop(&2, U32, xs, 0n) == xs : List<&2, U32>}

def drop_zero(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      {==}

# Dropping j elements, when element j is x: x, then the rest.
law drop_get:
  for +xs: List<&2, U32>
  for +j: Nat
  for +x: U32
  for +h: {List.get(&2, U32, xs, j) == Some{x} : Maybe<&2, U32>}
  {List.drop(&2, U32, xs, j) == x <> List.drop(&2, U32, xs, Nat.add(j, 1n)) : List<&2, U32>}

def drop_get(xs, j, x, h):
  match xs j:
    case Nil{} _:
      Empty.absurd({List.drop(&2, U32, Nil{}, j) == x <> List.drop(&2, U32, Nil{}, Nat.add(j, 1n)) : List<&2, U32>},
        none_some(x, h))
    case Con{+y, t} 0n:
      +yx = Equal.cong(Maybe<&2, U32>, U32, m => I.unsome(U32, y, m), Some{y}, Some{x}, h)
      %Equal.sym(List<&2, U32>, List.drop(&2, U32, t, 0n), t, drop_zero(t)) : {y <> t == x <> _ : List<&2, U32>}
      %Equal.sym(U32, y, x, yx) : {_ <> t == x <> t : List<&2, U32>}
      {==}
    case Con{y, t} 1n+p:
      drop_get(t, p, x, h)

law slice_cons:
  for +xs: List<&2, U32>
  for +j: Nat
  for +k: Nat
  for +x: U32
  for +h: {List.get(&2, U32, xs, j) == Some{x} : Maybe<&2, U32>}
  {D.slice(xs, j, 1n+k) == x <> D.slice(xs, Nat.add(j, 1n), k) : List<&2, U32>}

def slice_cons(xs, j, k, x, h):
  %Equal.sym(List<&2, U32>, List.drop(&2, U32, xs, j), x <> List.drop(&2, U32, xs, Nat.add(j, 1n)), drop_get(xs, j, x, h)) :
    {List.take(&2, U32, _, 1n+k) == x <> D.slice(xs, Nat.add(j, 1n), k) : List<&2, U32>}
  {==}

# a + 1 + m <= b gives a < b.
law lt_of_le:
  for +a: Nat
  for +m: Nat
  for +b: Nat
  for +h: {Nat.is_le(Nat.add(a, 1n+m), b) == True{} : Bool}
  {Nat.is_lt(a, b) == True{} : Bool}

def lt_of_le(a, m, b, h):
  +h1 = AB.subst(Nat, x => {Nat.is_le(x, b) == True{} : Bool}, Nat.add(a, 1n+m), 1n+Nat.add(a, m), AB.add_succ(a, m), h)
  +h2 = N.le_trans(1n+a, 1n+Nat.add(a, m), b, N.le_add_r(a, m), h1)
  Equal.trans(Bool, Nat.is_lt(a, b), Nat.is_le(1n+a, b), True{}, Equal.sym(Bool, Nat.is_le(1n+a, b), Nat.is_lt(a, b), N.le_succ_lt(a, b)), h2)

# a + 1 + m <= b gives (a + 1) + m <= b.
law le_step:
  for +a: Nat
  for +m: Nat
  for +b: Nat
  for +h: {Nat.is_le(Nat.add(a, 1n+m), b) == True{} : Bool}
  {Nat.is_le(Nat.add(Nat.add(a, 1n), m), b) == True{} : Bool}

def le_step(a, m, b, h):
  AB.subst(Nat, x => {Nat.is_le(x, b) == True{} : Bool}, Nat.add(a, Nat.add(1n, m)), Nat.add(Nat.add(a, 1n), m),
    Equal.sym(Nat, Nat.add(Nat.add(a, 1n), m), Nat.add(a, Nat.add(1n, m)), N.add_assoc(a, 1n, m)), h)

# One step of a read loop at index s with n + 1 left, within a Bytes of size len:
# byte s is read, s + 1 does not wrap, and the bound holds one index on.
law step_val:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +s: U32
  for +m: Nat
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hs: {Nat.is_le(Nat.add(U32.to_nat(s), 1n+m), U32.to_nat(len)) == True{} : Bool}
  {List.get(&2, U32, D.view(C.BT(len, t)), U32.to_nat(s)) == Some{C.AT(len, t, s)} : Maybe<&2, U32>}

def step_val(len, t, d, s, m, h, hs):
  Equal.sym(Maybe<&2, U32>, Some{C.AT(len, t, s)}, List.get(&2, U32, D.view(C.BT(len, t)), U32.to_nat(s)),
    C.at_view_t(len, t, d, s, C.ok_full(len, t, d, h), C.ok_d(len, t, d, h), C.ok_len(len, t, d, h),
      lt_of_le(U32.to_nat(s), m, U32.to_nat(len), hs)))

law step_inc:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +s: U32
  for +m: Nat
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hs: {Nat.is_le(Nat.add(U32.to_nat(s), 1n+m), U32.to_nat(len)) == True{} : Bool}
  {U32.to_nat((s + 1 : U32)) == Nat.add(U32.to_nat(s), 1n) : Nat}

def step_inc(len, t, d, s, m, h, hs):
  C.inc_fits(s, d, C.ok_d(len, t, d, h),
    N.lt_le_trans(U32.to_nat(s), U32.to_nat(len), Nat.mul(4n, Nat.pow(2n, d)), lt_of_le(U32.to_nat(s), m, U32.to_nat(len), hs),
      C.ok_len(len, t, d, h)))

law step_le:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +s: U32
  for +m: Nat
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hs: {Nat.is_le(Nat.add(U32.to_nat(s), 1n+m), U32.to_nat(len)) == True{} : Bool}
  {Nat.is_le(Nat.add(U32.to_nat((s + 1 : U32)), m), U32.to_nat(len)) == True{} : Bool}

def step_le(len, t, d, s, m, h, hs):
  AB.subst(Nat, x => {Nat.is_le(Nat.add(x, m), U32.to_nat(len)) == True{} : Bool}, Nat.add(U32.to_nat(s), 1n), U32.to_nat((s + 1 : U32)),
    Equal.sym(Nat, U32.to_nat((s + 1 : U32)), Nat.add(U32.to_nat(s), 1n), step_inc(len, t, d, s, m, h, hs)),
    le_step(U32.to_nat(s), m, U32.to_nat(len), hs))

# to_list
# =======

# to_list reads from the last byte back, putting each in front of acc, so its
# loop is a tail call. The invariant: reading at j = m + s with 1 + m bytes
# left gives slice(view, s, 1 + m) followed by acc.

law tl_pair:
  for +n: Nat
  for +len: U32
  for +t: P.Tree<U32>
  for +j: U32
  for +acc: List<&2, U32>
  {B.to_list.go(n, B.at(C.BT(len, t), j), j, acc) == (C.BT(len, t), Pair.snd(D.Bytes, List<&2, U32>, B.to_list.go(n, B.at(C.BT(len, t), j), j, acc))) : D.Bytes & List<&2, U32>}

def tl_pair(n, len, t, j, acc):
  match n:
    case 0n:
      %Equal.sym(D.Bytes & U32, B.at(C.BT(len, t), j), (C.BT(len, t), C.AT(len, t, j)), C.at_pair_t(len, t, j)) :
        {B.to_list.go(0n, _, j, acc) == (C.BT(len, t), Pair.snd(D.Bytes, List<&2, U32>, B.to_list.go(0n, _, j, acc))) : D.Bytes & List<&2, U32>}
      {==}
    case 1n+m:
      %Equal.sym(D.Bytes & U32, B.at(C.BT(len, t), j), (C.BT(len, t), C.AT(len, t, j)), C.at_pair_t(len, t, j)) :
        {B.to_list.go(1n+m, _, j, acc) == (C.BT(len, t), Pair.snd(D.Bytes, List<&2, U32>, B.to_list.go(1n+m, _, j, acc))) : D.Bytes & List<&2, U32>}
      tl_pair(m, len, t, (j - 1 : U32), C.AT(len, t, j) <> acc)

law append_nil:
  for +xs: List<&2, U32>
  {List.append(&2, U32, xs, Nil{}) == xs : List<&2, U32>}

def append_nil(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, t}:
      Equal.cong(List<&2, U32>, List<&2, U32>, z => x <> z, List.append(&2, U32, t, Nil{}), t, append_nil(t))

law get_drop:
  for +xs: List<&2, U32>
  for +i: Nat
  for +k: Nat
  {List.get(&2, U32, List.drop(&2, U32, xs, i), k) == List.get(&2, U32, xs, Nat.add(i, k)) : Maybe<&2, U32>}

def get_drop(xs, i, k):
  match xs i:
    case Nil{} _:
      {==}
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+p:
      get_drop(t, p, k)

# Taking k + 1 elements then acc is taking k then element k, then acc.
law take_snoc:
  for +ys: List<&2, U32>
  for +k: Nat
  for +x: U32
  for +acc: List<&2, U32>
  for +h: {List.get(&2, U32, ys, k) == Some{x} : Maybe<&2, U32>}
  {List.append(&2, U32, List.take(&2, U32, ys, 1n+k), acc) == List.append(&2, U32, List.take(&2, U32, ys, k), x <> acc) : List<&2, U32>}

def take_snoc(ys, k, x, acc, h):
  match ys k:
    case Nil{} _:
      Empty.absurd({List.append(&2, U32, List.take(&2, U32, Nil{}, 1n+k), acc) == List.append(&2, U32, List.take(&2, U32, Nil{}, k), x <> acc) : List<&2, U32>},
        none_some(x, h))
    case Con{+y, t} 0n:
      +yx = Equal.cong(Maybe<&2, U32>, U32, m => I.unsome(U32, y, m), Some{y}, Some{x}, h)
      %Equal.sym(List<&2, U32>, List.take(&2, U32, t, 0n), Nil{}, Q.take_zero(t)) : {y <> List.append(&2, U32, _, acc) == x <> acc : List<&2, U32>}
      %Equal.sym(U32, y, x, yx) : {_ <> acc == x <> acc : List<&2, U32>}
      {==}
    case Con{+y, t} 1n+p:
      Equal.cong(List<&2, U32>, List<&2, U32>, z => y <> z, List.append(&2, U32, List.take(&2, U32, t, 1n+p), acc),
        List.append(&2, U32, List.take(&2, U32, t, p), x <> acc), take_snoc(t, p, x, acc, h))

law slice_snoc:
  for +xs: List<&2, U32>
  for +i: Nat
  for +k: Nat
  for +x: U32
  for +acc: List<&2, U32>
  for +h: {List.get(&2, U32, xs, Nat.add(k, i)) == Some{x} : Maybe<&2, U32>}
  {List.append(&2, U32, D.slice(xs, i, 1n+k), acc) == List.append(&2, U32, D.slice(xs, i, k), x <> acc) : List<&2, U32>}

def slice_snoc(xs, i, k, x, acc, h):
  +ys = List.drop(&2, U32, xs, i)
  +g = AB.subst(Nat, z => {List.get(&2, U32, ys, k) == List.get(&2, U32, xs, z) : Maybe<&2, U32>}, Nat.add(i, k), Nat.add(k, i),
    N.add_comm(i, k), get_drop(xs, i, k))
  take_snoc(ys, k, x, acc, Equal.trans(Maybe<&2, U32>, List.get(&2, U32, ys, k), List.get(&2, U32, xs, Nat.add(k, i)), Some{x}, g, h))

# Byte j, for j = m + s below len, is element m + s of the view.
law tl_val:
  for +m: Nat
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +s: U32
  for +j: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hj: {U32.to_nat(j) == Nat.add(m, U32.to_nat(s)) : Nat}
  for +hs: {Nat.is_lt(Nat.add(m, U32.to_nat(s)), U32.to_nat(len)) == True{} : Bool}
  {List.get(&2, U32, D.view(C.BT(len, t)), Nat.add(m, U32.to_nat(s))) == Some{C.AT(len, t, j)} : Maybe<&2, U32>}

def tl_val(m, len, t, d, s, j, h, hj, hs):
  +a = Nat.add(m, U32.to_nat(s))
  +hi = AB.subst(Nat, z => {Nat.is_lt(z, U32.to_nat(len)) == True{} : Bool}, a, U32.to_nat(j), Equal.sym(Nat, U32.to_nat(j), a, hj), hs)
  +e = Equal.sym(Maybe<&2, U32>, Some{C.AT(len, t, j)}, List.get(&2, U32, D.view(C.BT(len, t)), U32.to_nat(j)),
    C.at_view_t(len, t, d, j, C.ok_full(len, t, d, h), C.ok_d(len, t, d, h), C.ok_len(len, t, d, h), hi))
  AB.subst(Nat, z => {List.get(&2, U32, D.view(C.BT(len, t)), z) == Some{C.AT(len, t, j)} : Maybe<&2, U32>}, U32.to_nat(j), a, hj, e)

# j - 1 for j = 1 + m + s.
law tl_dec:
  for +m: Nat
  for +s: U32
  for +j: U32
  for +hj: {U32.to_nat(j) == 1n+Nat.add(m, U32.to_nat(s)) : Nat}
  {U32.to_nat((j - 1 : U32)) == Nat.add(m, U32.to_nat(s)) : Nat}

def tl_dec(m, s, j, hj):
  +a = Nat.add(m, U32.to_nat(s))
  +hle = Equal.trans(Bool, U32.is_le(1, j), Nat.is_le(U32.to_nat(1), U32.to_nat(j)), True{}, U.is_le_to_nat(1, j),
    AB.subst(Nat, z => {Nat.is_le(U32.to_nat(1), z) == True{} : Bool}, 1n+a, U32.to_nat(j), Equal.sym(Nat, U32.to_nat(j), 1n+a, hj), N.le_zero_l(a)))
  %Equal.sym(Nat, U32.to_nat((j - 1 : U32)), Nat.sub(U32.to_nat(j), U32.to_nat(1)), U.to_nat_sub_le(j, 1, hle)) : {_ == a : Nat}
  %Equal.sym(Nat, U32.to_nat(j), 1n+a, hj) : {Nat.sub(_, U32.to_nat(1)) == a : Nat}
  N.sub_zero(a)

law tl_lt:
  for +a: Nat
  for +b: Nat
  for +h: {Nat.is_lt(1n+a, b) == True{} : Bool}
  {Nat.is_lt(a, b) == True{} : Bool}

def tl_lt(a, b, h):
  Equal.trans(Bool, Nat.is_lt(a, b), Nat.is_le(1n+a, b), True{}, Equal.sym(Bool, Nat.is_le(1n+a, b), Nat.is_lt(a, b), N.le_succ_lt(a, b)),
    N.lt_to_le(1n+a, b, h))

law tl_view:
  for +m: Nat
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +s: U32
  for +j: U32
  for +acc: List<&2, U32>
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hj: {U32.to_nat(j) == Nat.add(m, U32.to_nat(s)) : Nat}
  for +hs: {Nat.is_lt(Nat.add(m, U32.to_nat(s)), U32.to_nat(len)) == True{} : Bool}
  {Pair.snd(D.Bytes, List<&2, U32>, B.to_list.go(1n+m, B.at(C.BT(len, t), j), j, acc)) == List.append(&2, U32, D.slice(D.view(C.BT(len, t)), U32.to_nat(s), 1n+m), acc) : List<&2, U32>}

def tl_view(m, len, t, d, s, j, acc, h, hj, hs):
  match m:
    case 0n:
      +x = C.AT(len, t, j)
      +j1 = (j - 1 : U32)
      +xs = D.view(C.BT(len, t))
      +ys = List.drop(&2, U32, xs, U32.to_nat(s))
      %Equal.sym(D.Bytes & U32, B.at(C.BT(len, t), j), (C.BT(len, t), x), C.at_pair_t(len, t, j)) :
        {Pair.snd(D.Bytes, List<&2, U32>, B.to_list.go(1n, _, j, acc)) == List.append(&2, U32, D.slice(xs, U32.to_nat(s), 1n), acc) : List<&2, U32>}
      %Equal.sym(D.Bytes & U32, B.at(C.BT(len, t), j1), (C.BT(len, t), C.AT(len, t, j1)), C.at_pair_t(len, t, j1)) :
        {Pair.snd(D.Bytes, List<&2, U32>, B.to_list.go(0n, _, j1, x <> acc)) == List.append(&2, U32, D.slice(xs, U32.to_nat(s), 1n), acc) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, List.append(&2, U32, D.slice(xs, U32.to_nat(s), 1n), acc), List.append(&2, U32, D.slice(xs, U32.to_nat(s), 0n), x <> acc),
        slice_snoc(xs, U32.to_nat(s), 0n, x, acc, tl_val(0n, len, t, d, s, j, h, hj, hs))) :
        {x <> acc == _ : List<&2, U32>}
      %Equal.sym(List<&2, U32>, List.take(&2, U32, ys, 0n), Nil{}, Q.take_zero(ys)) : {x <> acc == List.append(&2, U32, _, x <> acc) : List<&2, U32>}
      {==}
    case 1n+p:
      +x = C.AT(len, t, j)
      +j1 = (j - 1 : U32)
      +xs = D.view(C.BT(len, t))
      %Equal.sym(D.Bytes & U32, B.at(C.BT(len, t), j), (C.BT(len, t), x), C.at_pair_t(len, t, j)) :
        {Pair.snd(D.Bytes, List<&2, U32>, B.to_list.go(1n+(1n+p), _, j, acc)) == List.append(&2, U32, D.slice(xs, U32.to_nat(s), 1n+(1n+p)), acc) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, List.append(&2, U32, D.slice(xs, U32.to_nat(s), 1n+(1n+p)), acc), List.append(&2, U32, D.slice(xs, U32.to_nat(s), 1n+p), x <> acc),
        slice_snoc(xs, U32.to_nat(s), 1n+p, x, acc, tl_val(1n+p, len, t, d, s, j, h, hj, hs))) :
        {Pair.snd(D.Bytes, List<&2, U32>, B.to_list.go(1n+p, B.at(C.BT(len, t), j1), j1, x <> acc)) == _ : List<&2, U32>}
      tl_view(p, len, t, d, s, j1, x <> acc, h, tl_dec(p, s, j, hj), tl_lt(Nat.add(p, U32.to_nat(s)), U32.to_nat(len), hs))

# to_list(BT, s, n) with k = n bytes: none, or 1 + p read from s + n - 1.
law tl_view_k:
  for +k: Nat
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +s: U32
  for +n: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hk: {U32.to_nat(n) == k : Nat}
  for +hs: {Nat.is_le(Nat.add(U32.to_nat(s), U32.to_nat(n)), U32.to_nat(len)) == True{} : Bool}
  {Pair.snd(D.Bytes, List<&2, U32>, B.to_list.go(k, B.at(C.BT(len, t), ((s + n : U32) - 1 : U32)), ((s + n : U32) - 1 : U32), Nil{})) == D.slice(D.view(C.BT(len, t)), U32.to_nat(s), k) : List<&2, U32>}

def tl_view_k(k, len, t, d, s, n, h, hk, hs):
  match k:
    case 0n:
      +e = ((s + n : U32) - 1 : U32)
      +xs = D.view(C.BT(len, t))
      +ys = List.drop(&2, U32, xs, U32.to_nat(s))
      %Equal.sym(D.Bytes & U32, B.at(C.BT(len, t), e), (C.BT(len, t), C.AT(len, t, e)), C.at_pair_t(len, t, e)) :
        {Pair.snd(D.Bytes, List<&2, U32>, B.to_list.go(0n, _, e, Nil{})) == D.slice(xs, U32.to_nat(s), 0n) : List<&2, U32>}
      Equal.sym(List<&2, U32>, List.take(&2, U32, ys, 0n), Nil{}, Q.take_zero(ys))
    case 1n+p:
      +e = ((s + n : U32) - 1 : U32)
      +xs = D.view(C.BT(len, t))
      +a = Nat.add(p, U32.to_nat(s))
      +sn = Nat.add(U32.to_nat(s), U32.to_nat(n))
      +E = Equal.trans(Nat, sn, Nat.add(U32.to_nat(s), 1n+p), 1n+a,
        Equal.cong(Nat, Nat, z => Nat.add(U32.to_nat(s), z), U32.to_nat(n), 1n+p, hk),
        Equal.trans(Nat, Nat.add(U32.to_nat(s), 1n+p), 1n+Nat.add(U32.to_nat(s), p), 1n+a, N.add_succ(U32.to_nat(s), p),
          Equal.cong(Nat, Nat, z => 1n+z, Nat.add(U32.to_nat(s), p), a, N.add_comm(U32.to_nat(s), p))))
      +hsum = C.add_fits(s, n, d, C.ok_d(len, t, d, h), N.le_trans(sn, U32.to_nat(len), Nat.mul(4n, Nat.pow(2n, d)), hs, C.ok_len(len, t, d, h)))
      +hj = tl_dec(p, s, (s + n : U32), Equal.trans(Nat, U32.to_nat((s + n : U32)), sn, 1n+a, hsum, E))
      +hlt = Equal.trans(Bool, Nat.is_lt(a, U32.to_nat(len)), Nat.is_le(1n+a, U32.to_nat(len)), True{},
        Equal.sym(Bool, Nat.is_le(1n+a, U32.to_nat(len)), Nat.is_lt(a, U32.to_nat(len)), N.le_succ_lt(a, U32.to_nat(len))),
        AB.subst(Nat, z => {Nat.is_le(z, U32.to_nat(len)) == True{} : Bool}, sn, 1n+a, E, hs))
      +sl = D.slice(xs, U32.to_nat(s), 1n+p)
      Equal.trans(List<&2, U32>, Pair.snd(D.Bytes, List<&2, U32>, B.to_list.go(1n+p, B.at(C.BT(len, t), e), e, Nil{})), List.append(&2, U32, sl, Nil{}), sl,
        tl_view(p, len, t, d, s, e, Nil{}, h, hj, hlt), append_nil(sl))

law to_list_pair_t:
  for +len: U32
  for +t: P.Tree<U32>
  for +s: U32
  for +n: U32
  {B.to_list(C.BT(len, t), s, n) == (C.BT(len, t), Pair.snd(D.Bytes, List<&2, U32>, B.to_list(C.BT(len, t), s, n))) : D.Bytes & List<&2, U32>}

def to_list_pair_t(len, t, s, n):
  tl_pair(U32.to_nat(n), len, t, ((s + n : U32) - 1 : U32), Nil{})

law to_list_view_t:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +s: U32
  for +n: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hs: {Nat.is_le(Nat.add(U32.to_nat(s), U32.to_nat(n)), D.size(C.BT(len, t))) == True{} : Bool}
  {Pair.snd(D.Bytes, List<&2, U32>, B.to_list(C.BT(len, t), s, n)) == D.slice(D.view(C.BT(len, t)), U32.to_nat(s), U32.to_nat(n)) : List<&2, U32>}

def to_list_view_t(len, t, d, s, n, h, hs):
  tl_view_k(U32.to_nat(n), len, t, d, s, n, h, {==}, hs)

# same
# ====

law and_assoc:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  {Bool.and(Bool.and(a, b), c) == Bool.and(a, Bool.and(b, c)) : Bool}

def and_assoc(a, b, c):
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

# Comparing n more bytes from i of A and from j of B, after an empty prefix:
# acc and the comparison of the two slices.
law lists_end:
  for +acc: Bool
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  {acc == Bool.and(acc, D.list_eq(List.take(&2, U32, xs, 0n), List.take(&2, U32, ys, 0n))) : Bool}

def lists_end(acc, xs, ys):
  %Equal.sym(List<&2, U32>, List.take(&2, U32, xs, 0n), Nil{}, Q.take_zero(xs)) :
    {acc == Bool.and(acc, D.list_eq(_, List.take(&2, U32, ys, 0n))) : Bool}
  %Equal.sym(List<&2, U32>, List.take(&2, U32, ys, 0n), Nil{}, Q.take_zero(ys)) :
    {acc == Bool.and(acc, D.list_eq(Nil{}, _)) : Bool}
  Equal.sym(Bool, Bool.and(acc, True{}), acc, N.and_true_r_id(acc))

# One step of a comparison loop: the two slices from x and y, with the
# accumulated test rebracketed.
law lists_step:
  for +acc: Bool
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +i: Nat
  for +j: Nat
  for +i1: U32
  for +j1: U32
  for +k: Nat
  for +x: U32
  for +y: U32
  for +hx: {List.get(&2, U32, xs, i) == Some{x} : Maybe<&2, U32>}
  for +hy: {List.get(&2, U32, ys, j) == Some{y} : Maybe<&2, U32>}
  for +ei: {U32.to_nat(i1) == Nat.add(i, 1n) : Nat}
  for +ej: {U32.to_nat(j1) == Nat.add(j, 1n) : Nat}
  {Bool.and(Bool.and(acc, U32.is_eq(x, y)), D.list_eq(D.slice(xs, U32.to_nat(i1), k), D.slice(ys, U32.to_nat(j1), k)))
    == Bool.and(acc, D.list_eq(D.slice(xs, i, 1n+k), D.slice(ys, j, 1n+k))) : Bool}

def lists_step(acc, xs, ys, i, j, i1, j1, k, x, y, hx, hy, ei, ej):
  +LHS = Bool.and(Bool.and(acc, U32.is_eq(x, y)), D.list_eq(D.slice(xs, U32.to_nat(i1), k), D.slice(ys, U32.to_nat(j1), k)))
  %Equal.sym(List<&2, U32>, D.slice(xs, i, 1n+k), x <> D.slice(xs, Nat.add(i, 1n), k), slice_cons(xs, i, k, x, hx)) :
    {LHS == Bool.and(acc, D.list_eq(_, D.slice(ys, j, 1n+k))) : Bool}
  %Equal.sym(List<&2, U32>, D.slice(ys, j, 1n+k), y <> D.slice(ys, Nat.add(j, 1n), k), slice_cons(ys, j, k, y, hy)) :
    {LHS == Bool.and(acc, D.list_eq(x <> D.slice(xs, Nat.add(i, 1n), k), _)) : Bool}
  %ei : {LHS == Bool.and(acc, Bool.and(U32.is_eq(x, y), D.list_eq(D.slice(xs, _, k), D.slice(ys, Nat.add(j, 1n), k)))) : Bool}
  %ej : {LHS == Bool.and(acc, Bool.and(U32.is_eq(x, y), D.list_eq(D.slice(xs, U32.to_nat(i1), k), D.slice(ys, _, k)))) : Bool}
  and_assoc(acc, U32.is_eq(x, y), D.list_eq(D.slice(xs, U32.to_nat(i1), k), D.slice(ys, U32.to_nat(j1), k)))

law sm_pair:
  for +n: Nat
  for +la: U32
  for +ta: P.Tree<U32>
  for +lb: U32
  for +tb: P.Tree<U32>
  for +i: U32
  for +j: U32
  for +acc: Bool
  {B.same.go(n, B.at(C.BT(la, ta), i), B.at(C.BT(lb, tb), j), i, j, acc) == (C.BT(la, ta), (C.BT(lb, tb),
    Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, B.same.go(n, B.at(C.BT(la, ta), i), B.at(C.BT(lb, tb), j), i, j, acc))))) : D.Bytes & (D.Bytes & Bool)}

def sm_pair(n, la, ta, lb, tb, i, j, acc):
  match n:
    case 0n:
      %Equal.sym(D.Bytes & U32, B.at(C.BT(la, ta), i), (C.BT(la, ta), C.AT(la, ta, i)), C.at_pair_t(la, ta, i)) :
        {B.same.go(0n, _, B.at(C.BT(lb, tb), j), i, j, acc) == (C.BT(la, ta), (C.BT(lb, tb),
          Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, B.same.go(0n, _, B.at(C.BT(lb, tb), j), i, j, acc))))) : D.Bytes & (D.Bytes & Bool)}
      %Equal.sym(D.Bytes & U32, B.at(C.BT(lb, tb), j), (C.BT(lb, tb), C.AT(lb, tb, j)), C.at_pair_t(lb, tb, j)) :
        {B.same.go(0n, (C.BT(la, ta), C.AT(la, ta, i)), _, i, j, acc) == (C.BT(la, ta), (C.BT(lb, tb),
          Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, B.same.go(0n, (C.BT(la, ta), C.AT(la, ta, i)), _, i, j, acc))))) : D.Bytes & (D.Bytes & Bool)}
      {==}
    case 1n+k:
      %Equal.sym(D.Bytes & U32, B.at(C.BT(la, ta), i), (C.BT(la, ta), C.AT(la, ta, i)), C.at_pair_t(la, ta, i)) :
        {B.same.go(1n+k, _, B.at(C.BT(lb, tb), j), i, j, acc) == (C.BT(la, ta), (C.BT(lb, tb),
          Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, B.same.go(1n+k, _, B.at(C.BT(lb, tb), j), i, j, acc))))) : D.Bytes & (D.Bytes & Bool)}
      %Equal.sym(D.Bytes & U32, B.at(C.BT(lb, tb), j), (C.BT(lb, tb), C.AT(lb, tb, j)), C.at_pair_t(lb, tb, j)) :
        {B.same.go(1n+k, (C.BT(la, ta), C.AT(la, ta, i)), _, i, j, acc) == (C.BT(la, ta), (C.BT(lb, tb),
          Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, B.same.go(1n+k, (C.BT(la, ta), C.AT(la, ta, i)), _, i, j, acc))))) : D.Bytes & (D.Bytes & Bool)}
      sm_pair(k, la, ta, lb, tb, (i + 1 : U32), (j + 1 : U32), acc && U32.is_eq(C.AT(la, ta, i), C.AT(lb, tb, j)))

law sm_view:
  for +n: Nat
  for +la: U32
  for +ta: P.Tree<U32>
  for +lb: U32
  for +tb: P.Tree<U32>
  for +d: Nat
  for +e: Nat
  for +i: U32
  for +j: U32
  for +acc: Bool
  for +ha: {D.ok(C.BT(la, ta), d) == True{} : Bool}
  for +hb: {D.ok(C.BT(lb, tb), e) == True{} : Bool}
  for +hi: {Nat.is_le(Nat.add(U32.to_nat(i), n), U32.to_nat(la)) == True{} : Bool}
  for +hj: {Nat.is_le(Nat.add(U32.to_nat(j), n), U32.to_nat(lb)) == True{} : Bool}
  {Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, B.same.go(n, B.at(C.BT(la, ta), i), B.at(C.BT(lb, tb), j), i, j, acc)))
    == Bool.and(acc, D.list_eq(D.slice(D.view(C.BT(la, ta)), U32.to_nat(i), n), D.slice(D.view(C.BT(lb, tb)), U32.to_nat(j), n))) : Bool}

def sm_view(n, la, ta, lb, tb, d, e, i, j, acc, ha, hb, hi, hj):
  match n:
    case 0n:
      +xa = D.view(C.BT(la, ta))
      +xb = D.view(C.BT(lb, tb))
      +RHS = Bool.and(acc, D.list_eq(D.slice(xa, U32.to_nat(i), 0n), D.slice(xb, U32.to_nat(j), 0n)))
      %Equal.sym(D.Bytes & U32, B.at(C.BT(la, ta), i), (C.BT(la, ta), C.AT(la, ta, i)), C.at_pair_t(la, ta, i)) :
        {Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, B.same.go(0n, _, B.at(C.BT(lb, tb), j), i, j, acc))) == RHS : Bool}
      %Equal.sym(D.Bytes & U32, B.at(C.BT(lb, tb), j), (C.BT(lb, tb), C.AT(lb, tb, j)), C.at_pair_t(lb, tb, j)) :
        {Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, B.same.go(0n, (C.BT(la, ta), C.AT(la, ta, i)), _, i, j, acc))) == RHS : Bool}
      lists_end(acc, List.drop(&2, U32, xa, U32.to_nat(i)), List.drop(&2, U32, xb, U32.to_nat(j)))
    case 1n+k:
      +xa = D.view(C.BT(la, ta))
      +xb = D.view(C.BT(lb, tb))
      +x = C.AT(la, ta, i)
      +y = C.AT(lb, tb, j)
      +i1 = (i + 1 : U32)
      +j1 = (j + 1 : U32)
      +RHS = Bool.and(acc, D.list_eq(D.slice(xa, U32.to_nat(i), 1n+k), D.slice(xb, U32.to_nat(j), 1n+k)))
      %Equal.sym(D.Bytes & U32, B.at(C.BT(la, ta), i), (C.BT(la, ta), x), C.at_pair_t(la, ta, i)) :
        {Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, B.same.go(1n+k, _, B.at(C.BT(lb, tb), j), i, j, acc))) == RHS : Bool}
      %Equal.sym(D.Bytes & U32, B.at(C.BT(lb, tb), j), (C.BT(lb, tb), y), C.at_pair_t(lb, tb, j)) :
        {Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, B.same.go(1n+k, (C.BT(la, ta), x), _, i, j, acc))) == RHS : Bool}
      %Equal.sym(Bool, Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, B.same.go(k, B.at(C.BT(la, ta), i1), B.at(C.BT(lb, tb), j1), i1, j1, acc && U32.is_eq(x, y)))),
        Bool.and(acc && U32.is_eq(x, y), D.list_eq(D.slice(xa, U32.to_nat(i1), k), D.slice(xb, U32.to_nat(j1), k))),
        sm_view(k, la, ta, lb, tb, d, e, i1, j1, acc && U32.is_eq(x, y), ha, hb,
          step_le(la, ta, d, i, k, ha, hi), step_le(lb, tb, e, j, k, hb, hj))) :
        {_ == RHS : Bool}
      lists_step(acc, xa, xb, U32.to_nat(i), U32.to_nat(j), i1, j1, k, x, y,
        step_val(la, ta, d, i, k, ha, hi), step_val(lb, tb, e, j, k, hb, hj),
        step_inc(la, ta, d, i, k, ha, hi), step_inc(lb, tb, e, j, k, hb, hj))

law same_pair_t:
  for +la: U32
  for +ta: P.Tree<U32>
  for +lb: U32
  for +tb: P.Tree<U32>
  for +i: U32
  for +j: U32
  for +n: U32
  {B.same(C.BT(la, ta), i, C.BT(lb, tb), j, n) == (C.BT(la, ta), (C.BT(lb, tb), Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, B.same(C.BT(la, ta), i, C.BT(lb, tb), j, n))))) : D.Bytes & (D.Bytes & Bool)}

def same_pair_t(la, ta, lb, tb, i, j, n):
  sm_pair(U32.to_nat(n), la, ta, lb, tb, i, j, True{})

law same_view_t:
  for +la: U32
  for +ta: P.Tree<U32>
  for +lb: U32
  for +tb: P.Tree<U32>
  for +d: Nat
  for +e: Nat
  for +i: U32
  for +j: U32
  for +n: U32
  for +ha: {D.ok(C.BT(la, ta), d) == True{} : Bool}
  for +hb: {D.ok(C.BT(lb, tb), e) == True{} : Bool}
  for +hi: {Nat.is_le(Nat.add(U32.to_nat(i), U32.to_nat(n)), D.size(C.BT(la, ta))) == True{} : Bool}
  for +hj: {Nat.is_le(Nat.add(U32.to_nat(j), U32.to_nat(n)), D.size(C.BT(lb, tb))) == True{} : Bool}
  {Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, B.same(C.BT(la, ta), i, C.BT(lb, tb), j, n))) == D.list_eq(D.slice(D.view(C.BT(la, ta)), U32.to_nat(i), U32.to_nat(n)), D.slice(D.view(C.BT(lb, tb)), U32.to_nat(j), U32.to_nat(n))) : Bool}

def same_view_t(la, ta, lb, tb, d, e, i, j, n, ha, hb, hi, hj):
  sm_view(U32.to_nat(n), la, ta, lb, tb, d, e, i, j, True{}, ha, hb, hi, hj)

# same1 (two reads of one buffer per step, through at2)
# =====================================================

law at2_eq:
  for +len: U32
  for +t: P.Tree<U32>
  for +i: U32
  for +j: U32
  {B.at2(C.BT(len, t), i, j) == (C.BT(len, t), (C.AT(len, t, i), C.AT(len, t, j))) : D.Bytes & (U32 & U32)}

def at2_eq(len, t, i, j):
  %Equal.sym(D.Bytes & U32, B.at(C.BT(len, t), i), (C.BT(len, t), C.AT(len, t, i)), C.at_pair_t(len, t, i)) :
    {B.at2.fin(j, _) == (C.BT(len, t), (C.AT(len, t, i), C.AT(len, t, j))) : D.Bytes & (U32 & U32)}
  %Equal.sym(D.Bytes & U32, B.at(C.BT(len, t), j), (C.BT(len, t), C.AT(len, t, j)), C.at_pair_t(len, t, j)) :
    {B.at2.fin2(C.AT(len, t, i), _) == (C.BT(len, t), (C.AT(len, t, i), C.AT(len, t, j))) : D.Bytes & (U32 & U32)}
  {==}

law s1_pair:
  for +n: Nat
  for +len: U32
  for +t: P.Tree<U32>
  for +i: U32
  for +j: U32
  for +acc: Bool
  {B.same1.go(n, B.at2(C.BT(len, t), i, j), i, j, acc) == (C.BT(len, t), Pair.snd(D.Bytes, Bool, B.same1.go(n, B.at2(C.BT(len, t), i, j), i, j, acc))) : D.Bytes & Bool}

def s1_pair(n, len, t, i, j, acc):
  match n:
    case 0n:
      %Equal.sym(D.Bytes & (U32 & U32), B.at2(C.BT(len, t), i, j), (C.BT(len, t), (C.AT(len, t, i), C.AT(len, t, j))), at2_eq(len, t, i, j)) :
        {B.same1.go(0n, _, i, j, acc) == (C.BT(len, t), Pair.snd(D.Bytes, Bool, B.same1.go(0n, _, i, j, acc))) : D.Bytes & Bool}
      {==}
    case 1n+m:
      %Equal.sym(D.Bytes & (U32 & U32), B.at2(C.BT(len, t), i, j), (C.BT(len, t), (C.AT(len, t, i), C.AT(len, t, j))), at2_eq(len, t, i, j)) :
        {B.same1.go(1n+m, _, i, j, acc) == (C.BT(len, t), Pair.snd(D.Bytes, Bool, B.same1.go(1n+m, _, i, j, acc))) : D.Bytes & Bool}
      s1_pair(m, len, t, (i + 1 : U32), (j + 1 : U32), acc && U32.is_eq(C.AT(len, t, i), C.AT(len, t, j)))

law s1_view:
  for +n: Nat
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +i: U32
  for +j: U32
  for +acc: Bool
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hi: {Nat.is_le(Nat.add(U32.to_nat(i), n), U32.to_nat(len)) == True{} : Bool}
  for +hj: {Nat.is_le(Nat.add(U32.to_nat(j), n), U32.to_nat(len)) == True{} : Bool}
  {Pair.snd(D.Bytes, Bool, B.same1.go(n, B.at2(C.BT(len, t), i, j), i, j, acc))
    == Bool.and(acc, D.list_eq(D.slice(D.view(C.BT(len, t)), U32.to_nat(i), n), D.slice(D.view(C.BT(len, t)), U32.to_nat(j), n))) : Bool}

def s1_view(n, len, t, d, i, j, acc, h, hi, hj):
  match n:
    case 0n:
      +xs = D.view(C.BT(len, t))
      %Equal.sym(D.Bytes & (U32 & U32), B.at2(C.BT(len, t), i, j), (C.BT(len, t), (C.AT(len, t, i), C.AT(len, t, j))), at2_eq(len, t, i, j)) :
        {Pair.snd(D.Bytes, Bool, B.same1.go(0n, _, i, j, acc)) == Bool.and(acc, D.list_eq(D.slice(xs, U32.to_nat(i), 0n), D.slice(xs, U32.to_nat(j), 0n))) : Bool}
      lists_end(acc, List.drop(&2, U32, xs, U32.to_nat(i)), List.drop(&2, U32, xs, U32.to_nat(j)))
    case 1n+k:
      +xs = D.view(C.BT(len, t))
      +x = C.AT(len, t, i)
      +y = C.AT(len, t, j)
      +i1 = (i + 1 : U32)
      +j1 = (j + 1 : U32)
      +RHS = Bool.and(acc, D.list_eq(D.slice(xs, U32.to_nat(i), 1n+k), D.slice(xs, U32.to_nat(j), 1n+k)))
      %Equal.sym(D.Bytes & (U32 & U32), B.at2(C.BT(len, t), i, j), (C.BT(len, t), (x, y)), at2_eq(len, t, i, j)) :
        {Pair.snd(D.Bytes, Bool, B.same1.go(1n+k, _, i, j, acc)) == RHS : Bool}
      %Equal.sym(Bool, Pair.snd(D.Bytes, Bool, B.same1.go(k, B.at2(C.BT(len, t), i1, j1), i1, j1, acc && U32.is_eq(x, y))),
        Bool.and(acc && U32.is_eq(x, y), D.list_eq(D.slice(xs, U32.to_nat(i1), k), D.slice(xs, U32.to_nat(j1), k))),
        s1_view(k, len, t, d, i1, j1, acc && U32.is_eq(x, y), h,
          step_le(len, t, d, i, k, h, hi), step_le(len, t, d, j, k, h, hj))) :
        {_ == RHS : Bool}
      lists_step(acc, xs, xs, U32.to_nat(i), U32.to_nat(j), i1, j1, k, x, y,
        step_val(len, t, d, i, k, h, hi), step_val(len, t, d, j, k, h, hj),
        step_inc(len, t, d, i, k, h, hi), step_inc(len, t, d, j, k, h, hj))

law same1_pair_t:
  for +len: U32
  for +t: P.Tree<U32>
  for +i: U32
  for +j: U32
  for +n: U32
  {B.same1(C.BT(len, t), i, j, n) == (C.BT(len, t), Pair.snd(D.Bytes, Bool, B.same1(C.BT(len, t), i, j, n))) : D.Bytes & Bool}

def same1_pair_t(len, t, i, j, n):
  s1_pair(U32.to_nat(n), len, t, i, j, True{})

law same1_view_t:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +i: U32
  for +j: U32
  for +n: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hi: {Nat.is_le(Nat.add(U32.to_nat(i), U32.to_nat(n)), D.size(C.BT(len, t))) == True{} : Bool}
  for +hj: {Nat.is_le(Nat.add(U32.to_nat(j), U32.to_nat(n)), D.size(C.BT(len, t))) == True{} : Bool}
  {Pair.snd(D.Bytes, Bool, B.same1(C.BT(len, t), i, j, n)) == D.list_eq(D.slice(D.view(C.BT(len, t)), U32.to_nat(i), U32.to_nat(n)), D.slice(D.view(C.BT(len, t)), U32.to_nat(j), U32.to_nat(n))) : Bool}

def same1_view_t(len, t, d, i, j, n, h, hi, hj):
  s1_view(U32.to_nat(n), len, t, d, i, j, True{}, h, hi, hj)
