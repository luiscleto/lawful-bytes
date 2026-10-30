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

# find and find2 on the mirror C.BT(len, t). The loops read one byte ahead:
# r holds byte j + 1 while hit says whether byte j matched. Each lemma takes r
# as a literal pair (C.BT(len, t), byte) so the loop's destructuring computes;
# the next read is rewritten into that form with C.at_pair_t.

# Small facts
# ===========

def is_some_t(m: Maybe<&2, U32>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

law none_ne_some:
  for -x: U32
  for e: {None{} == Some{x} : Maybe<&2, U32>}
  Empty

def none_ne_some(x, e):
  AB.subst(Maybe<&2, U32>, m => is_some_t(m), None{}, Some{x}, e, Unit{})

law drop_zero:
  for +xs: List<&2, U32>
  {List.drop(&2, U32, xs, 0n) == xs : List<&2, U32>}

def drop_zero(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      {==}

# Dropping j elements from a list with x at j leaves x in front.
law drop_cons:
  for +xs: List<&2, U32>
  for +j: Nat
  for +x: U32
  for +hx: {List.get(&2, U32, xs, j) == Some{x} : Maybe<&2, U32>}
  {List.drop(&2, U32, xs, j) == x <> List.drop(&2, U32, xs, Nat.add(j, 1n)) : List<&2, U32>}

def drop_cons(xs, j, x, hx):
  match xs j:
    case Nil{} _:
      Empty.absurd({Nil{} == x <> Nil{} : List<&2, U32>}, none_ne_some(x, hx))
    case Con{+y, t} 0n:
      +yx = Equal.cong(Maybe<&2, U32>, U32, m => I.unsome(U32, y, m), Some{y}, Some{x}, hx)
      %Equal.sym(List<&2, U32>, List.drop(&2, U32, t, 0n), t, drop_zero(t)) : {y <> t == x <> _ : List<&2, U32>}
      %yx : {y <> t == _ <> t : List<&2, U32>}
      {==}
    case Con{y, t} 1n+p:
      drop_cons(t, p, x, hx)

law slice_cons:
  for +xs: List<&2, U32>
  for +j: Nat
  for +k: Nat
  for +x: U32
  for +hx: {List.get(&2, U32, xs, j) == Some{x} : Maybe<&2, U32>}
  {D.slice(xs, j, 1n+k) == x <> D.slice(xs, Nat.add(j, 1n), k) : List<&2, U32>}

def slice_cons(xs, j, k, x, hx):
  %Equal.sym(List<&2, U32>, List.drop(&2, U32, xs, j), x <> List.drop(&2, U32, xs, Nat.add(j, 1n)), drop_cons(xs, j, x, hx)) :
    {List.take(&2, U32, _, 1n+k) == x <> D.slice(xs, Nat.add(j, 1n), k) : List<&2, U32>}
  {==}

law lt_add_succ:
  for +a: Nat
  for +k: Nat
  {Nat.is_lt(a, Nat.add(a, 1n+k)) == True{} : Bool}

def lt_add_succ(a, k):
  match a:
    case 0n:
      {==}
    case 1n+p:
      lt_add_succ(p, k)

# (j + 1) + 1 is j + 2, for every word j (no range needed: through from_nat).
law add11:
  for +j: U32
  {U32.add(U32.add(j, 1), 1) == U32.add(j, 2) : U32}

def add11(j):
  +tj = U32.to_nat(j)
  %U.from_nat_to_nat(j) : {U32.add(U32.add(_, 1), 1) == U32.add(j, 2) : U32}
  %U.from_nat_add(tj, 1n) : {U32.add(_, 1) == U32.add(j, 2) : U32}
  %U.from_nat_add(Nat.add(tj, 1n), 1n) : {_ == U32.add(j, 2) : U32}
  %Equal.sym(Nat, Nat.add(Nat.add(tj, 1n), 1n), Nat.add(tj, Nat.add(1n, 1n)), N.add_assoc(tj, 1n, 1n)) :
    {U32.from_nat(_) == U32.add(j, 2) : U32}
  %U.from_nat_to_nat(j) : {U32.from_nat(Nat.add(tj, 2n)) == U32.add(_, 2) : U32}
  U.from_nat_add(tj, 2n)

# The loops hand the buffer back
# ==============================

law fgo_pair:
  for n: Nat
  for +hit: Bool
  for +len: U32
  for +t: P.Tree<U32>
  for +x: U32
  for +j: U32
  for +to: U32
  for +c: U32
  {B.find.go(n, hit, (C.BT(len, t), x), j, to, c) == (C.BT(len, t), Pair.snd(D.Bytes, U32, B.find.go(n, hit, (C.BT(len, t), x), j, to, c))) : D.Bytes & U32}

def fgo_pair(n, hit, len, t, x, j, to, c):
  match n hit:
    case 0n _:
      {==}
    case 1n+k True{}:
      {==}
    case 1n+k False{}:
      +H = U32.is_eq(x, c)
      +j2 = (j + 2 : U32)
      %Equal.sym(D.Bytes & U32, B.at(C.BT(len, t), j2), (C.BT(len, t), C.AT(len, t, j2)), C.at_pair_t(len, t, j2)) :
        {B.find.go(k, H, _, (j + 1 : U32), to, c) == (C.BT(len, t), Pair.snd(D.Bytes, U32, B.find.go(k, H, _, (j + 1 : U32), to, c))) : D.Bytes & U32}
      fgo_pair(k, H, len, t, C.AT(len, t, j2), (j + 1 : U32), to, c)

law find_pair_t:
  for +len: U32
  for +t: P.Tree<U32>
  for +from: U32
  for +to: U32
  for +c: U32
  {B.find(C.BT(len, t), from, to, c) == (C.BT(len, t), Pair.snd(D.Bytes, U32, B.find(C.BT(len, t), from, to, c))) : D.Bytes & U32}

def find_pair_t(len, t, from, to, c):
  +n = Nat.sub(U32.to_nat(to), U32.to_nat(from))
  +f1 = (from + 1 : U32)
  +H = U32.is_eq(C.AT(len, t, from), c)
  %Equal.sym(D.Bytes & U32, B.at(C.BT(len, t), from), (C.BT(len, t), C.AT(len, t, from)), C.at_pair_t(len, t, from)) :
    {B.find.start(n, _, from, to, c) == (C.BT(len, t), Pair.snd(D.Bytes, U32, B.find.start(n, _, from, to, c))) : D.Bytes & U32}
  %Equal.sym(D.Bytes & U32, B.at(C.BT(len, t), f1), (C.BT(len, t), C.AT(len, t, f1)), C.at_pair_t(len, t, f1)) :
    {B.find.go(n, H, _, from, to, c) == (C.BT(len, t), Pair.snd(D.Bytes, U32, B.find.go(n, H, _, from, to, c))) : D.Bytes & U32}
  fgo_pair(n, H, len, t, C.AT(len, t, f1), from, to, c)

law fgo2_pair:
  for n: Nat
  for +hit: Bool
  for +len: U32
  for +t: P.Tree<U32>
  for +x: U32
  for +j: U32
  for +to: U32
  for +c1: U32
  for +c2: U32
  {B.find2.go(n, hit, (C.BT(len, t), x), j, to, c1, c2) == (C.BT(len, t), Pair.snd(D.Bytes, U32, B.find2.go(n, hit, (C.BT(len, t), x), j, to, c1, c2))) : D.Bytes & U32}

def fgo2_pair(n, hit, len, t, x, j, to, c1, c2):
  match n hit:
    case 0n _:
      {==}
    case 1n+k True{}:
      {==}
    case 1n+k False{}:
      +H = U32.is_eq(x, c1) || U32.is_eq(x, c2)
      +j2 = (j + 2 : U32)
      %Equal.sym(D.Bytes & U32, B.at(C.BT(len, t), j2), (C.BT(len, t), C.AT(len, t, j2)), C.at_pair_t(len, t, j2)) :
        {B.find2.go(k, H, _, (j + 1 : U32), to, c1, c2) == (C.BT(len, t), Pair.snd(D.Bytes, U32, B.find2.go(k, H, _, (j + 1 : U32), to, c1, c2))) : D.Bytes & U32}
      fgo2_pair(k, H, len, t, C.AT(len, t, j2), (j + 1 : U32), to, c1, c2)

law find2_pair_t:
  for +len: U32
  for +t: P.Tree<U32>
  for +from: U32
  for +to: U32
  for +c1: U32
  for +c2: U32
  {B.find2(C.BT(len, t), from, to, c1, c2) == (C.BT(len, t), Pair.snd(D.Bytes, U32, B.find2(C.BT(len, t), from, to, c1, c2))) : D.Bytes & U32}

def find2_pair_t(len, t, from, to, c1, c2):
  +n = Nat.sub(U32.to_nat(to), U32.to_nat(from))
  +f1 = (from + 1 : U32)
  +x0 = C.AT(len, t, from)
  +H = U32.is_eq(x0, c1) || U32.is_eq(x0, c2)
  %Equal.sym(D.Bytes & U32, B.at(C.BT(len, t), from), (C.BT(len, t), x0), C.at_pair_t(len, t, from)) :
    {B.find2.start(n, _, from, to, c1, c2) == (C.BT(len, t), Pair.snd(D.Bytes, U32, B.find2.start(n, _, from, to, c1, c2))) : D.Bytes & U32}
  %Equal.sym(D.Bytes & U32, B.at(C.BT(len, t), f1), (C.BT(len, t), C.AT(len, t, f1)), C.at_pair_t(len, t, f1)) :
    {B.find2.go(n, H, _, from, to, c1, c2) == (C.BT(len, t), Pair.snd(D.Bytes, U32, B.find2.go(n, H, _, from, to, c1, c2))) : D.Bytes & U32}
  fgo2_pair(n, H, len, t, C.AT(len, t, f1), from, to, c1, c2)

# Index steps
# ===========

# With j + 1 + k = to <= len, byte j is in range.
law step_lt:
  for +len: U32
  for +j: U32
  for +to: U32
  for +k: Nat
  for +hn: {Nat.add(U32.to_nat(j), 1n+k) == U32.to_nat(to) : Nat}
  for +hto: {Nat.is_le(U32.to_nat(to), U32.to_nat(len)) == True{} : Bool}
  {Nat.is_lt(U32.to_nat(j), U32.to_nat(len)) == True{} : Bool}

def step_lt(len, j, to, k, hn, hto):
  +tj = U32.to_nat(j)
  N.lt_le_trans(tj, U32.to_nat(to), U32.to_nat(len),
    AB.subst(Nat, x => {Nat.is_lt(tj, x) == True{} : Bool}, Nat.add(tj, 1n+k), U32.to_nat(to), hn, lt_add_succ(tj, k)),
    hto)

law step_lt4:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +j: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hj: {Nat.is_lt(U32.to_nat(j), U32.to_nat(len)) == True{} : Bool}
  {Nat.is_lt(U32.to_nat(j), Nat.mul(4n, Nat.pow(2n, d))) == True{} : Bool}

def step_lt4(len, t, d, j, h, hj):
  N.lt_le_trans(U32.to_nat(j), U32.to_nat(len), Nat.mul(4n, Nat.pow(2n, d)), hj, C.ok_len(len, t, d, h))

law step_get:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +j: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hj: {Nat.is_lt(U32.to_nat(j), U32.to_nat(len)) == True{} : Bool}
  {List.get(&2, U32, D.view(C.BT(len, t)), U32.to_nat(j)) == Some{C.AT(len, t, j)} : Maybe<&2, U32>}

def step_get(len, t, d, j, h, hj):
  Equal.sym(Maybe<&2, U32>, Some{C.AT(len, t, j)}, List.get(&2, U32, D.view(C.BT(len, t)), U32.to_nat(j)),
    C.at_view_t(len, t, d, j, C.ok_full(len, t, d, h), C.ok_d(len, t, d, h), C.ok_len(len, t, d, h), hj))

law step_n:
  for +j: U32
  for +k: Nat
  for +to: U32
  for +d: Nat
  for +hd: {Nat.is_le(d, 29n) == True{} : Bool}
  for +hj4: {Nat.is_lt(U32.to_nat(j), Nat.mul(4n, Nat.pow(2n, d))) == True{} : Bool}
  for +hn: {Nat.add(U32.to_nat(j), 1n+k) == U32.to_nat(to) : Nat}
  {Nat.add(U32.to_nat((j + 1 : U32)), k) == U32.to_nat(to) : Nat}

def step_n(j, k, to, d, hd, hj4, hn):
  +tj = U32.to_nat(j)
  %Equal.sym(Nat, U32.to_nat((j + 1 : U32)), Nat.add(tj, 1n), C.inc_fits(j, d, hd, hj4)) :
    {Nat.add(_, k) == U32.to_nat(to) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(tj, 1n), k), Nat.add(tj, Nat.add(1n, k)), N.add_assoc(tj, 1n, k)) :
    {_ == U32.to_nat(to) : Nat}
  hn

# find
# ====

# hit says byte j is c, r holds byte j + 1, j + n = to.
law fgo_view:
  for +n: Nat
  for +hit: Bool
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +j: U32
  for +to: U32
  for +c: U32
  for +hh: {U32.is_eq(C.AT(len, t, j), c) == hit : Bool}
  for +hn: {Nat.add(U32.to_nat(j), n) == U32.to_nat(to) : Nat}
  for +hto: {Nat.is_le(U32.to_nat(to), U32.to_nat(len)) == True{} : Bool}
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  {U32.to_nat(Pair.snd(D.Bytes, U32, B.find.go(n, hit, (C.BT(len, t), C.AT(len, t, (j + 1 : U32))), j, to, c))) == Nat.add(U32.to_nat(j), D.run_len(D.slice(D.view(C.BT(len, t)), U32.to_nat(j), n), c)) : Nat}

def fgo_view(n, hit, len, t, d, j, to, c, hh, hn, hto, h):
  match n hit:
    case 0n _:
      +tj = U32.to_nat(j)
      %Equal.sym(List<&2, U32>, List.take(&2, U32, List.drop(&2, U32, D.view(C.BT(len, t)), tj), 0n), Nil{},
        Q.take_zero(List.drop(&2, U32, D.view(C.BT(len, t)), tj))) :
        {U32.to_nat(to) == Nat.add(tj, D.run_len(_, c)) : Nat}
      Equal.sym(Nat, Nat.add(tj, 0n), U32.to_nat(to), hn)
    case 1n+k True{}:
      +tj = U32.to_nat(j)
      +VW = D.view(C.BT(len, t))
      +x = C.AT(len, t, j)
      +S = D.slice(VW, Nat.add(tj, 1n), k)
      +hj = step_lt(len, j, to, k, hn, hto)
      %Equal.sym(List<&2, U32>, D.slice(VW, tj, 1n+k), x <> S, slice_cons(VW, tj, k, x, step_get(len, t, d, j, h, hj))) :
        {tj == Nat.add(tj, D.run_len(_, c)) : Nat}
      %Equal.sym(Bool, U32.is_eq(x, c), True{}, hh) :
        {tj == Nat.add(tj, Bool.pick(Nat, _, 0n, Nat.add(1n, D.run_len(S, c)))) : Nat}
      Equal.sym(Nat, Nat.add(tj, 0n), tj, AB.add_zero(tj))
    case 1n+k False{}:
      +tj = U32.to_nat(j)
      +VW = D.view(C.BT(len, t))
      +x = C.AT(len, t, j)
      +S = D.slice(VW, Nat.add(tj, 1n), k)
      +j1 = (j + 1 : U32)
      +j11 = (j1 + 1 : U32)
      +H1 = U32.is_eq(C.AT(len, t, j1), c)
      +RHS = Nat.add(tj, D.run_len(D.slice(VW, tj, 1n+k), c))
      +hd = C.ok_d(len, t, d, h)
      +hj = step_lt(len, j, to, k, hn, hto)
      +hj4 = step_lt4(len, t, d, j, h, hj)
      %add11(j) : {U32.to_nat(Pair.snd(D.Bytes, U32, B.find.go(k, H1, B.at(C.BT(len, t), _), j1, to, c))) == RHS : Nat}
      %Equal.sym(D.Bytes & U32, B.at(C.BT(len, t), j11), (C.BT(len, t), C.AT(len, t, j11)), C.at_pair_t(len, t, j11)) :
        {U32.to_nat(Pair.snd(D.Bytes, U32, B.find.go(k, H1, _, j1, to, c))) == RHS : Nat}
      +G = U32.to_nat(Pair.snd(D.Bytes, U32, B.find.go(k, H1, (C.BT(len, t), C.AT(len, t, j11)), j1, to, c)))
      %Equal.sym(List<&2, U32>, D.slice(VW, tj, 1n+k), x <> S, slice_cons(VW, tj, k, x, step_get(len, t, d, j, h, hj))) :
        {G == Nat.add(tj, D.run_len(_, c)) : Nat}
      %Equal.sym(Bool, U32.is_eq(x, c), False{}, hh) :
        {G == Nat.add(tj, Bool.pick(Nat, _, 0n, Nat.add(1n, D.run_len(S, c)))) : Nat}
      %N.add_assoc(tj, 1n, D.run_len(S, c)) : {G == _ : Nat}
      %C.inc_fits(j, d, hd, hj4) : {G == Nat.add(_, D.run_len(D.slice(VW, _, k), c)) : Nat}
      fgo_view(k, H1, len, t, d, j1, to, c, {==}, step_n(j, k, to, d, hd, hj4, hn), hto, h)

# from <= to as numbers.
law le_ft:
  for +from: U32
  for +to: U32
  for +hft: {U32.is_le(from, to) == True{} : Bool}
  {Nat.is_le(U32.to_nat(from), U32.to_nat(to)) == True{} : Bool}

def le_ft(from, to, hft):
  Equal.trans(Bool, Nat.is_le(U32.to_nat(from), U32.to_nat(to)), U32.is_le(from, to), True{},
    Equal.sym(Bool, U32.is_le(from, to), Nat.is_le(U32.to_nat(from), U32.to_nat(to)), U.is_le_to_nat(from, to)), hft)

law find_view_t:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +from: U32
  for +to: U32
  for +c: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hft: {U32.is_le(from, to) == True{} : Bool}
  for +ht: {Nat.is_le(U32.to_nat(to), D.size(C.BT(len, t))) == True{} : Bool}
  for +hc: {U32.is_lt(c, 256) == True{} : Bool}
  {U32.to_nat(Pair.snd(D.Bytes, U32, B.find(C.BT(len, t), from, to, c))) == D.first(D.view(C.BT(len, t)), U32.to_nat(from), U32.to_nat(to), c) : Nat}

def find_view_t(len, t, d, from, to, c, h, hft, ht, hc):
  +tf = U32.to_nat(from)
  +tt = U32.to_nat(to)
  +n = Nat.sub(tt, tf)
  +f1 = (from + 1 : U32)
  +H = U32.is_eq(C.AT(len, t, from), c)
  +RHS = D.first(D.view(C.BT(len, t)), tf, tt, c)
  %Equal.sym(D.Bytes & U32, B.at(C.BT(len, t), from), (C.BT(len, t), C.AT(len, t, from)), C.at_pair_t(len, t, from)) :
    {U32.to_nat(Pair.snd(D.Bytes, U32, B.find.start(n, _, from, to, c))) == RHS : Nat}
  %Equal.sym(D.Bytes & U32, B.at(C.BT(len, t), f1), (C.BT(len, t), C.AT(len, t, f1)), C.at_pair_t(len, t, f1)) :
    {U32.to_nat(Pair.snd(D.Bytes, U32, B.find.go(n, H, _, from, to, c))) == RHS : Nat}
  fgo_view(n, H, len, t, d, from, to, c, {==}, N.le_sub_add(tf, tt, le_ft(from, to, hft)), ht, h)

# find2
# =====

# hit says byte j is c1 or c2, r holds byte j + 1, j + n = to.
law fgo2_view:
  for +n: Nat
  for +hit: Bool
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +j: U32
  for +to: U32
  for +c1: U32
  for +c2: U32
  for +hh: {(U32.is_eq(C.AT(len, t, j), c1) || U32.is_eq(C.AT(len, t, j), c2)) == hit : Bool}
  for +hn: {Nat.add(U32.to_nat(j), n) == U32.to_nat(to) : Nat}
  for +hto: {Nat.is_le(U32.to_nat(to), U32.to_nat(len)) == True{} : Bool}
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  {U32.to_nat(Pair.snd(D.Bytes, U32, B.find2.go(n, hit, (C.BT(len, t), C.AT(len, t, (j + 1 : U32))), j, to, c1, c2))) == Nat.add(U32.to_nat(j), D.run_len2(D.slice(D.view(C.BT(len, t)), U32.to_nat(j), n), c1, c2)) : Nat}

def fgo2_view(n, hit, len, t, d, j, to, c1, c2, hh, hn, hto, h):
  match n hit:
    case 0n _:
      +tj = U32.to_nat(j)
      %Equal.sym(List<&2, U32>, List.take(&2, U32, List.drop(&2, U32, D.view(C.BT(len, t)), tj), 0n), Nil{},
        Q.take_zero(List.drop(&2, U32, D.view(C.BT(len, t)), tj))) :
        {U32.to_nat(to) == Nat.add(tj, D.run_len2(_, c1, c2)) : Nat}
      Equal.sym(Nat, Nat.add(tj, 0n), U32.to_nat(to), hn)
    case 1n+k True{}:
      +tj = U32.to_nat(j)
      +VW = D.view(C.BT(len, t))
      +x = C.AT(len, t, j)
      +S = D.slice(VW, Nat.add(tj, 1n), k)
      +hj = step_lt(len, j, to, k, hn, hto)
      %Equal.sym(List<&2, U32>, D.slice(VW, tj, 1n+k), x <> S, slice_cons(VW, tj, k, x, step_get(len, t, d, j, h, hj))) :
        {tj == Nat.add(tj, D.run_len2(_, c1, c2)) : Nat}
      %Equal.sym(Bool, U32.is_eq(x, c1) || U32.is_eq(x, c2), True{}, hh) :
        {tj == Nat.add(tj, Bool.pick(Nat, _, 0n, Nat.add(1n, D.run_len2(S, c1, c2)))) : Nat}
      Equal.sym(Nat, Nat.add(tj, 0n), tj, AB.add_zero(tj))
    case 1n+k False{}:
      +tj = U32.to_nat(j)
      +VW = D.view(C.BT(len, t))
      +x = C.AT(len, t, j)
      +S = D.slice(VW, Nat.add(tj, 1n), k)
      +j1 = (j + 1 : U32)
      +j11 = (j1 + 1 : U32)
      +H1 = U32.is_eq(C.AT(len, t, j1), c1) || U32.is_eq(C.AT(len, t, j1), c2)
      +RHS = Nat.add(tj, D.run_len2(D.slice(VW, tj, 1n+k), c1, c2))
      +hd = C.ok_d(len, t, d, h)
      +hj = step_lt(len, j, to, k, hn, hto)
      +hj4 = step_lt4(len, t, d, j, h, hj)
      %add11(j) : {U32.to_nat(Pair.snd(D.Bytes, U32, B.find2.go(k, H1, B.at(C.BT(len, t), _), j1, to, c1, c2))) == RHS : Nat}
      %Equal.sym(D.Bytes & U32, B.at(C.BT(len, t), j11), (C.BT(len, t), C.AT(len, t, j11)), C.at_pair_t(len, t, j11)) :
        {U32.to_nat(Pair.snd(D.Bytes, U32, B.find2.go(k, H1, _, j1, to, c1, c2))) == RHS : Nat}
      +G = U32.to_nat(Pair.snd(D.Bytes, U32, B.find2.go(k, H1, (C.BT(len, t), C.AT(len, t, j11)), j1, to, c1, c2)))
      %Equal.sym(List<&2, U32>, D.slice(VW, tj, 1n+k), x <> S, slice_cons(VW, tj, k, x, step_get(len, t, d, j, h, hj))) :
        {G == Nat.add(tj, D.run_len2(_, c1, c2)) : Nat}
      %Equal.sym(Bool, U32.is_eq(x, c1) || U32.is_eq(x, c2), False{}, hh) :
        {G == Nat.add(tj, Bool.pick(Nat, _, 0n, Nat.add(1n, D.run_len2(S, c1, c2)))) : Nat}
      %N.add_assoc(tj, 1n, D.run_len2(S, c1, c2)) : {G == _ : Nat}
      %C.inc_fits(j, d, hd, hj4) : {G == Nat.add(_, D.run_len2(D.slice(VW, _, k), c1, c2)) : Nat}
      fgo2_view(k, H1, len, t, d, j1, to, c1, c2, {==}, step_n(j, k, to, d, hd, hj4, hn), hto, h)

law find2_view_t:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +from: U32
  for +to: U32
  for +c1: U32
  for +c2: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hft: {U32.is_le(from, to) == True{} : Bool}
  for +ht: {Nat.is_le(U32.to_nat(to), D.size(C.BT(len, t))) == True{} : Bool}
  for +hc1: {U32.is_lt(c1, 256) == True{} : Bool}
  for +hc2: {U32.is_lt(c2, 256) == True{} : Bool}
  {U32.to_nat(Pair.snd(D.Bytes, U32, B.find2(C.BT(len, t), from, to, c1, c2))) == D.first2(D.view(C.BT(len, t)), U32.to_nat(from), U32.to_nat(to), c1, c2) : Nat}

def find2_view_t(len, t, d, from, to, c1, c2, h, hft, ht, hc1, hc2):
  +tf = U32.to_nat(from)
  +tt = U32.to_nat(to)
  +n = Nat.sub(tt, tf)
  +f1 = (from + 1 : U32)
  +H = U32.is_eq(C.AT(len, t, from), c1) || U32.is_eq(C.AT(len, t, from), c2)
  +RHS = D.first2(D.view(C.BT(len, t)), tf, tt, c1, c2)
  %Equal.sym(D.Bytes & U32, B.at(C.BT(len, t), from), (C.BT(len, t), C.AT(len, t, from)), C.at_pair_t(len, t, from)) :
    {U32.to_nat(Pair.snd(D.Bytes, U32, B.find2.start(n, _, from, to, c1, c2))) == RHS : Nat}
  %Equal.sym(D.Bytes & U32, B.at(C.BT(len, t), f1), (C.BT(len, t), C.AT(len, t, f1)), C.at_pair_t(len, t, f1)) :
    {U32.to_nat(Pair.snd(D.Bytes, U32, B.find2.go(n, H, _, from, to, c1, c2))) == RHS : Nat}
  fgo2_view(n, H, len, t, d, from, to, c1, c2, {==}, N.le_sub_add(tf, tt, le_ft(from, to, hft)), ht, h)
