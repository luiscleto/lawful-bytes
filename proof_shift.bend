import Base
import ./defs.bend as D
import ./bytes.bend as B
import ./proof_seq.bend as Q
import ./proof_core.bend as C
import ./proof_ops.bend as O
import ./proof_append.bend as X
import lawful-words@0.1.0.0/defs.bend as W
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U
import lawful-words@0.1.0.0/proof_bytes.bend as Y
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-arrays@0.1.0.0/proof_tree.bend as P
import lawful-arrays@0.1.0.0/proof_index.bend as I

# shift on the mirror. The loop reads byte p = j + k and writes it at j; it
# keeps len. SGT computes the tree the loop leaves (shift_go_eq), and the view
# invariant (sv) is stated on SGT, a Data function, so no Bytes is involved.

# Lists
# =====

law get_drop:
  for +xs: List<&2, U32>
  for +a: Nat
  for +b: Nat
  {List.get(&2, U32, List.drop(&2, U32, xs, a), b) == List.get(&2, U32, xs, Nat.add(a, b)) : Maybe<&2, U32>}

def get_drop(xs, a, b):
  match xs a:
    case Nil{} _:
      {==}
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+p:
      get_drop(t, p, b)

law drop_length:
  for +xs: List<&2, U32>
  for +k: Nat
  {List.length(&2, U32, List.drop(&2, U32, xs, k)) == Nat.sub(List.length(&2, U32, xs), k) : Nat}

def drop_length(xs, k):
  match xs k:
    case Nil{} _:
      {==}
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+p:
      drop_length(t, p)

# Setting the first element of drop(xs, j).
law drop_set0:
  for +xs: List<&2, U32>
  for +j: Nat
  for +x: U32
  for +h: {Nat.is_lt(j, List.length(&2, U32, xs)) == True{} : Bool}
  {List.set(&2, U32, List.drop(&2, U32, xs, j), 0n, x) == x <> List.drop(&2, U32, xs, Nat.add(j, 1n)) : List<&2, U32>}

def drop_set0(xs, j, x, h):
  match xs j:
    case Nil{} _:
      Empty.absurd({List.set(&2, U32, Nil{}, 0n, x) == x <> Nil{} : List<&2, U32>}, AB.lt_zero_absurd(j, h))
    case Con{y, t} 0n:
      %Equal.sym(List<&2, U32>, List.drop(&2, U32, t, 0n), t, X.drop_zero(t)) : {x <> t == x <> _ : List<&2, U32>}
      {==}
    case Con{y, t} 1n+p:
      drop_set0(t, p, x, h)

law take_snoc:
  for +ys: List<&2, U32>
  for +j: Nat
  for +x: U32
  for +h: {List.get(&2, U32, ys, j) == Some{x} : Maybe<&2, U32>}
  {List.take(&2, U32, ys, Nat.add(j, 1n)) == List.append(&2, U32, List.take(&2, U32, ys, j), [x]) : List<&2, U32>}

def take_snoc(ys, j, x, h):
  match ys j:
    case Nil{} _:
      Empty.absurd({Nil{} == List.append(&2, U32, Nil{}, [x]) : List<&2, U32>}, X.none_some(x, h))
    case Con{+y, t} 0n:
      %X.some_inj(y, x, h) : {y <> List.take(&2, U32, t, 0n) == [_] : List<&2, U32>}
      %Equal.sym(List<&2, U32>, List.take(&2, U32, t, 0n), Nil{}, Q.take_zero(t)) : {y <> _ == [y] : List<&2, U32>}
      {==}
    case Con{+y, t} 1n+p:
      %take_snoc(t, p, x, h) : {y <> List.take(&2, U32, t, Nat.add(p, 1n)) == y <> _ : List<&2, U32>}
      {==}

law take_all:
  for +ys: List<&2, U32>
  for +n: Nat
  for +h: {Nat.is_le(List.length(&2, U32, ys), n) == True{} : Bool}
  {List.take(&2, U32, ys, n) == ys : List<&2, U32>}

def take_all(ys, n, h):
  match ys n:
    case Nil{} _:
      {==}
    case Con{y, t} 0n:
      Empty.absurd({Nil{} == y <> t : List<&2, U32>}, AB.false_ne_true(h))
    case Con{+y, t} 1n+p:
      %take_all(t, p, h) : {y <> List.take(&2, U32, t, p) == y <> _ : List<&2, U32>}
      {==}

law sub_self:
  for +j: Nat
  {Nat.sub(j, j) == 0n : Nat}

def sub_self(j):
  match j:
    case 0n:
      {==}
    case 1n+p:
      sub_self(p)

# The loop as a tree
# ==================

def SGT(+len: U32, m: Nat, +tb: P.Tree<U32>, +j: U32, +p: U32, +k: U32) -> P.Tree<U32>:
  match m:
    case 0n:
      tb
    case 1n+n:
      +x = C.AT(len, tb, p)
      +j1 = (j + 1 : U32)
      SGT(len, n, I.set_tree(U32, tb, (j >> 2n : U32), W.put_byte(C.WD(tb, (j >> 2n : U32)), U32.to_nat((j .&. 3 : U32)), x)), j1, (j1 + k : U32), k)

law shift_go_eq:
  for +m: Nat
  for +len: U32
  for +tb: P.Tree<U32>
  for +j: U32
  for +p: U32
  for +k: U32
  {B.shift.go(m, B.at(C.BT(len, tb), p), j, k) == C.BT(len, SGT(len, m, tb, j, p, k)) : D.Bytes}

def shift_go_eq(m, len, tb, j, p, k):
  match m:
    case 0n:
      %Equal.sym(D.Bytes & U32, B.at(C.BT(len, tb), p), (C.BT(len, tb), C.AT(len, tb, p)), C.at_pair_t(len, tb, p)) :
        {B.shift.go(0n, _, j, k) == C.BT(len, tb) : D.Bytes}
      {==}
    case 1n+n:
      +x = C.AT(len, tb, p)
      +j1 = (j + 1 : U32)
      +tb1 = I.set_tree(U32, tb, (j >> 2n : U32), W.put_byte(C.WD(tb, (j >> 2n : U32)), U32.to_nat((j .&. 3 : U32)), x))
      %Equal.sym(D.Bytes & U32, B.at(C.BT(len, tb), p), (C.BT(len, tb), x), C.at_pair_t(len, tb, p)) :
        {B.shift.go(1n+n, _, j, k) == C.BT(len, SGT(len, 1n+n, tb, j, p, k)) : D.Bytes}
      %Equal.sym(D.Bytes, B.set(C.BT(len, tb), j, x), C.BT(len, tb1), O.set_eq_t(len, tb, j, x)) :
        {B.shift.go(n, B.at(_, (j1 + k : U32)), j1, k) == C.BT(len, SGT(len, n, tb1, j1, (j1 + k : U32), k)) : D.Bytes}
      shift_go_eq(n, len, tb1, j1, (j1 + k : U32), k)

law sgt_ok:
  for +m: Nat
  for +len: U32
  for +tb: P.Tree<U32>
  for +d: Nat
  for +j: U32
  for +p: U32
  for +k: U32
  for +hb: {D.ok(C.BT(len, tb), d) == True{} : Bool}
  {D.ok(C.BT(len, SGT(len, m, tb, j, p, k)), d) == True{} : Bool}

def sgt_ok(m, len, tb, d, j, p, k, hb):
  match m:
    case 0n:
      hb
    case 1n+n:
      +x = C.AT(len, tb, p)
      +j1 = (j + 1 : U32)
      +tb1 = I.set_tree(U32, tb, (j >> 2n : U32), W.put_byte(C.WD(tb, (j >> 2n : U32)), U32.to_nat((j .&. 3 : U32)), x))
      sgt_ok(n, len, tb1, d, j1, (j1 + k : U32), k,
        AB.subst(D.Bytes, y => {D.ok(y, d) == True{} : Bool}, B.set(C.BT(len, tb), j, x), C.BT(len, tb1), O.set_eq_t(len, tb, j, x),
          O.set_ok_t(len, tb, d, j, x, hb)))

# The view invariant
# ==================

# Bytes j onwards are still those of xs; bytes below j are xs from k on.
def SV(+xs: List<&2, U32>, +kk: Nat, +jj: Nat) -> List<&2, U32>:
  List.append(&2, U32, List.take(&2, U32, List.drop(&2, U32, xs, kk), jj), List.drop(&2, U32, xs, jj))

# Nat facts for one step: j + k + (1 + n) = L.
law sv_lt:
  for +jj: Nat
  for +kk: Nat
  for +n: Nat
  for +ll: Nat
  for +hm: {Nat.add(Nat.add(jj, kk), 1n+n) == ll : Nat}
  {Nat.is_lt(Nat.add(jj, kk), ll) == True{} : Bool}

def sv_lt(jj, kk, n, ll, hm):
  X.le_split(Nat.add(jj, kk), n, ll,
    AB.subst(Nat, y => {Nat.is_le(Nat.add(Nat.add(jj, kk), 1n+n), y) == True{} : Bool}, Nat.add(Nat.add(jj, kk), 1n+n), ll, hm,
      N.le_refl(Nat.add(Nat.add(jj, kk), 1n+n))))

law sv_lt_j:
  for +jj: Nat
  for +kk: Nat
  for +n: Nat
  for +ll: Nat
  for +hm: {Nat.add(Nat.add(jj, kk), 1n+n) == ll : Nat}
  {Nat.is_lt(jj, ll) == True{} : Bool}

def sv_lt_j(jj, kk, n, ll, hm):
  N.le_lt_trans(jj, Nat.add(jj, kk), ll, N.le_add_r(jj, kk), sv_lt(jj, kk, n, ll, hm))

law sv_m:
  for +jj: Nat
  for +kk: Nat
  for +n: Nat
  {Nat.add(Nat.add(Nat.add(jj, 1n), kk), n) == Nat.add(Nat.add(jj, kk), 1n+n) : Nat}

def sv_m(jj, kk, n):
  %Equal.sym(Nat, Nat.add(Nat.add(jj, 1n), kk), Nat.add(jj, 1n+kk), N.add_assoc(jj, 1n, kk)) :
    {Nat.add(_, n) == Nat.add(Nat.add(jj, kk), 1n+n) : Nat}
  %Equal.sym(Nat, Nat.add(jj, 1n+kk), 1n+Nat.add(jj, kk), N.add_succ(jj, kk)) :
    {Nat.add(_, n) == Nat.add(Nat.add(jj, kk), 1n+n) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(jj, kk), 1n+n), 1n+Nat.add(Nat.add(jj, kk), n), N.add_succ(Nat.add(jj, kk), n)) :
    {1n+Nat.add(Nat.add(jj, kk), n) == _ : Nat}
  {==}

law sv_jk1:
  for +jj: Nat
  for +kk: Nat
  for +ll: Nat
  for +h: {Nat.is_lt(Nat.add(jj, kk), ll) == True{} : Bool}
  {Nat.is_le(Nat.add(Nat.add(jj, 1n), kk), ll) == True{} : Bool}

def sv_jk1(jj, kk, ll, h):
  %Equal.sym(Nat, Nat.add(Nat.add(jj, 1n), kk), Nat.add(jj, 1n+kk), N.add_assoc(jj, 1n, kk)) : {Nat.is_le(_, ll) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(jj, 1n+kk), 1n+Nat.add(jj, kk), N.add_succ(jj, kk)) : {Nat.is_le(_, ll) == True{} : Bool}
  Equal.trans(Bool, Nat.is_le(1n+Nat.add(jj, kk), ll), Nat.is_lt(Nat.add(jj, kk), ll), True{}, N.le_succ_lt(Nat.add(jj, kk), ll), h)

# The final view: SV at j = L - k.
def SF(+xs: List<&2, U32>, +kk: Nat, +ll: Nat) -> List<&2, U32>:
  SV(xs, kk, Nat.sub(ll, kk))

# The value read at p = j + k is element j of drop(xs, k).
law sv_read:
  for +xs: List<&2, U32>
  for +jj: Nat
  for +kk: Nat
  for +hj: {Nat.is_le(jj, List.length(&2, U32, List.drop(&2, U32, xs, kk))) == True{} : Bool}
  {List.get(&2, U32, SV(xs, kk, jj), Nat.add(jj, kk)) == List.get(&2, U32, List.drop(&2, U32, xs, kk), jj) : Maybe<&2, U32>}

def sv_read(xs, jj, kk, hj):
  +A = List.take(&2, U32, List.drop(&2, U32, xs, kk), jj)
  +la = Q.take_length(List.drop(&2, U32, xs, kk), jj, hj)
  +hn = AB.subst(Nat, y => {Nat.is_lt(Nat.add(jj, kk), y) == False{} : Bool}, jj, List.length(&2, U32, A),
    Equal.sym(Nat, List.length(&2, U32, A), jj, la), N.le_not_lt(jj, Nat.add(jj, kk), N.le_add_r(jj, kk)))
  %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, List.append(&2, U32, A, List.drop(&2, U32, xs, jj)), Nat.add(jj, kk)),
    List.get(&2, U32, List.drop(&2, U32, xs, jj), Nat.sub(Nat.add(jj, kk), List.length(&2, U32, A))),
    AB.get_append_r(U32, A, List.drop(&2, U32, xs, jj), Nat.add(jj, kk), hn)) :
    {_ == List.get(&2, U32, List.drop(&2, U32, xs, kk), jj) : Maybe<&2, U32>}
  %Equal.sym(Nat, List.length(&2, U32, A), jj, la) :
    {List.get(&2, U32, List.drop(&2, U32, xs, jj), Nat.sub(Nat.add(jj, kk), _)) == List.get(&2, U32, List.drop(&2, U32, xs, kk), jj) : Maybe<&2, U32>}
  %Equal.sym(Nat, Nat.sub(Nat.add(jj, kk), jj), kk, N.sub_add_l(jj, kk)) :
    {List.get(&2, U32, List.drop(&2, U32, xs, jj), _) == List.get(&2, U32, List.drop(&2, U32, xs, kk), jj) : Maybe<&2, U32>}
  %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, List.drop(&2, U32, xs, jj), kk), List.get(&2, U32, xs, Nat.add(jj, kk)), get_drop(xs, jj, kk)) :
    {_ == List.get(&2, U32, List.drop(&2, U32, xs, kk), jj) : Maybe<&2, U32>}
  %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, List.drop(&2, U32, xs, kk), jj), List.get(&2, U32, xs, Nat.add(kk, jj)), get_drop(xs, kk, jj)) :
    {List.get(&2, U32, xs, Nat.add(jj, kk)) == _ : Maybe<&2, U32>}
  %N.add_comm(jj, kk) : {List.get(&2, U32, xs, Nat.add(jj, kk)) == List.get(&2, U32, xs, _) : Maybe<&2, U32>}
  {==}

# Writing that value at j moves the boundary to j + 1.
law sv_write:
  for +xs: List<&2, U32>
  for +jj: Nat
  for +kk: Nat
  for +x: U32
  for +hj: {Nat.is_le(jj, List.length(&2, U32, List.drop(&2, U32, xs, kk))) == True{} : Bool}
  for +hjl: {Nat.is_lt(jj, List.length(&2, U32, xs)) == True{} : Bool}
  for +hx: {List.get(&2, U32, List.drop(&2, U32, xs, kk), jj) == Some{x} : Maybe<&2, U32>}
  {List.set(&2, U32, SV(xs, kk, jj), jj, x) == SV(xs, kk, Nat.add(jj, 1n)) : List<&2, U32>}

def sv_write(xs, jj, kk, x, hj, hjl, hx):
  +A = List.take(&2, U32, List.drop(&2, U32, xs, kk), jj)
  +la = Q.take_length(List.drop(&2, U32, xs, kk), jj, hj)
  +RHS = SV(xs, kk, Nat.add(jj, 1n))
  +hn = AB.subst(Nat, y => {Nat.is_lt(jj, y) == False{} : Bool}, jj, List.length(&2, U32, A),
    Equal.sym(Nat, List.length(&2, U32, A), jj, la), N.lt_irrefl(jj))
  %Equal.sym(List<&2, U32>, List.set(&2, U32, List.append(&2, U32, A, List.drop(&2, U32, xs, jj)), jj, x),
    List.append(&2, U32, A, List.set(&2, U32, List.drop(&2, U32, xs, jj), Nat.sub(jj, List.length(&2, U32, A)), x)),
    AB.set_append_r(U32, A, List.drop(&2, U32, xs, jj), jj, x, hn)) :
    {_ == RHS : List<&2, U32>}
  %Equal.sym(Nat, List.length(&2, U32, A), jj, la) :
    {List.append(&2, U32, A, List.set(&2, U32, List.drop(&2, U32, xs, jj), Nat.sub(jj, _), x)) == RHS : List<&2, U32>}
  %Equal.sym(Nat, Nat.sub(jj, jj), 0n, sub_self(jj)) :
    {List.append(&2, U32, A, List.set(&2, U32, List.drop(&2, U32, xs, jj), _, x)) == RHS : List<&2, U32>}
  %Equal.sym(List<&2, U32>, List.set(&2, U32, List.drop(&2, U32, xs, jj), 0n, x), x <> List.drop(&2, U32, xs, Nat.add(jj, 1n)),
    drop_set0(xs, jj, x, hjl)) :
    {List.append(&2, U32, A, _) == RHS : List<&2, U32>}
  %Equal.sym(List<&2, U32>, List.take(&2, U32, List.drop(&2, U32, xs, kk), Nat.add(jj, 1n)), List.append(&2, U32, A, [x]),
    take_snoc(List.drop(&2, U32, xs, kk), jj, x, hx)) :
    {List.append(&2, U32, A, x <> List.drop(&2, U32, xs, Nat.add(jj, 1n))) == List.append(&2, U32, _, List.drop(&2, U32, xs, Nat.add(jj, 1n))) : List<&2, U32>}
  Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, A, [x]), List.drop(&2, U32, xs, Nat.add(jj, 1n))),
    List.append(&2, U32, A, List.append(&2, U32, [x], List.drop(&2, U32, xs, Nat.add(jj, 1n)))),
    X.append_assoc(A, [x], List.drop(&2, U32, xs, Nat.add(jj, 1n))))

law sub_le:
  for +a: Nat
  for +b: Nat
  {Nat.is_le(Nat.sub(a, b), a) == True{} : Bool}

def sub_le(a, b):
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      N.le_refl(1n+p)
    case 1n+p 1n+q:
      N.le_trans(Nat.sub(p, q), p, 1n+p, sub_le(p, q), N.lt_to_le(p, 1n+p,
        Equal.trans(Bool, Nat.is_lt(p, 1n+p), Nat.is_le(p, p), True{}, N.lt_succ_iff(p, p), N.le_refl(p))))

# drop(xs, k) has L - k elements.
law xl:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +kk: Nat
  for +h0: {D.ok(C.BT(len, t), d) == True{} : Bool}
  {List.length(&2, U32, List.drop(&2, U32, D.view(C.BT(len, t)), kk)) == Nat.sub(U32.to_nat(len), kk) : Nat}

def xl(len, t, d, kk, h0):
  %Equal.sym(Nat, List.length(&2, U32, List.drop(&2, U32, D.view(C.BT(len, t)), kk)), Nat.sub(List.length(&2, U32, D.view(C.BT(len, t))), kk),
    drop_length(D.view(C.BT(len, t)), kk)) :
    {_ == Nat.sub(U32.to_nat(len), kk) : Nat}
  %Equal.sym(Nat, List.length(&2, U32, D.view(C.BT(len, t))), U32.to_nat(len), O.view_size_t(len, t, d, h0)) :
    {Nat.sub(_, kk) == Nat.sub(U32.to_nat(len), kk) : Nat}
  {==}

# j <= L - k from j + k < L.
law sv_jd:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +jj: Nat
  for +kk: Nat
  for +h0: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hlt: {Nat.is_lt(Nat.add(jj, kk), U32.to_nat(len)) == True{} : Bool}
  {Nat.is_le(jj, List.length(&2, U32, List.drop(&2, U32, D.view(C.BT(len, t)), kk))) == True{} : Bool}

def sv_jd(len, t, d, jj, kk, h0, hlt):
  %Equal.sym(Nat, List.length(&2, U32, List.drop(&2, U32, D.view(C.BT(len, t)), kk)), Nat.sub(U32.to_nat(len), kk), xl(len, t, d, kk, h0)) :
    {Nat.is_le(jj, _) == True{} : Bool}
  N.le_sub_r(kk, jj, U32.to_nat(len),
    AB.subst(Nat, y => {Nat.is_le(y, U32.to_nat(len)) == True{} : Bool}, Nat.add(jj, kk), Nat.add(kk, jj), N.add_comm(jj, kk),
      N.lt_to_le(Nat.add(jj, kk), U32.to_nat(len), hlt)))

# The byte read at p is element j of drop(xs, k).
law sv_x:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +k: U32
  for +tb: P.Tree<U32>
  for +j: U32
  for +p: U32
  for +h0: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hb: {D.ok(C.BT(len, tb), d) == True{} : Bool}
  for +hp: {U32.to_nat(p) == Nat.add(U32.to_nat(j), U32.to_nat(k)) : Nat}
  for +hv: {D.view(C.BT(len, tb)) == SV(D.view(C.BT(len, t)), U32.to_nat(k), U32.to_nat(j)) : List<&2, U32>}
  for +hlt: {Nat.is_lt(Nat.add(U32.to_nat(j), U32.to_nat(k)), U32.to_nat(len)) == True{} : Bool}
  {List.get(&2, U32, List.drop(&2, U32, D.view(C.BT(len, t)), U32.to_nat(k)), U32.to_nat(j)) == Some{C.AT(len, tb, p)} : Maybe<&2, U32>}

def sv_x(len, t, d, k, tb, j, p, h0, hb, hp, hv, hlt):
  +xs = D.view(C.BT(len, t))
  +JJ = U32.to_nat(j)
  +KK = U32.to_nat(k)
  +hi = AB.subst(Nat, y => {Nat.is_lt(y, U32.to_nat(len)) == True{} : Bool}, Nat.add(JJ, KK), U32.to_nat(p),
    Equal.sym(Nat, U32.to_nat(p), Nat.add(JJ, KK), hp), hlt)
  +a1 = C.at_view_t(len, tb, d, p, C.ok_full(len, tb, d, hb), C.ok_d(len, tb, d, hb), C.ok_len(len, tb, d, hb), hi)
  %sv_read(xs, JJ, KK, sv_jd(len, t, d, JJ, KK, h0, hlt)) :
    {_ == Some{C.AT(len, tb, p)} : Maybe<&2, U32>}
  %hp : {List.get(&2, U32, SV(xs, KK, JJ), _) == Some{C.AT(len, tb, p)} : Maybe<&2, U32>}
  %hv : {List.get(&2, U32, _, U32.to_nat(p)) == Some{C.AT(len, tb, p)} : Maybe<&2, U32>}
  Equal.sym(Maybe<&2, U32>, Some{C.AT(len, tb, p)}, List.get(&2, U32, D.view(C.BT(len, tb)), U32.to_nat(p)), a1)

law sv:
  for +m: Nat
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +k: U32
  for +tb: P.Tree<U32>
  for +j: U32
  for +p: U32
  for +h0: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hb: {D.ok(C.BT(len, tb), d) == True{} : Bool}
  for +hp: {U32.to_nat(p) == Nat.add(U32.to_nat(j), U32.to_nat(k)) : Nat}
  for +hm: {Nat.add(Nat.add(U32.to_nat(j), U32.to_nat(k)), m) == U32.to_nat(len) : Nat}
  for +hv: {D.view(C.BT(len, tb)) == SV(D.view(C.BT(len, t)), U32.to_nat(k), U32.to_nat(j)) : List<&2, U32>}
  {D.view(C.BT(len, SGT(len, m, tb, j, p, k))) == SF(D.view(C.BT(len, t)), U32.to_nat(k), U32.to_nat(len)) : List<&2, U32>}

def sv(m, len, t, d, k, tb, j, p, h0, hb, hp, hm, hv):
  match m:
    case 0n:
      +xs = D.view(C.BT(len, t))
      +JJ = U32.to_nat(j)
      +KK = U32.to_nat(k)
      +eL = Equal.trans(Nat, Nat.add(JJ, KK), Nat.add(Nat.add(JJ, KK), 0n), U32.to_nat(len),
        Equal.sym(Nat, Nat.add(Nat.add(JJ, KK), 0n), Nat.add(JJ, KK), N.add_zero(Nat.add(JJ, KK))), hm)
      %Equal.sym(List<&2, U32>, D.view(C.BT(len, tb)), SV(xs, KK, JJ), hv) : {_ == SF(xs, KK, U32.to_nat(len)) : List<&2, U32>}
      %eL : {SV(xs, KK, JJ) == SV(xs, KK, Nat.sub(_, KK)) : List<&2, U32>}
      %Equal.sym(Nat, Nat.sub(Nat.add(JJ, KK), KK), JJ, N.sub_add(JJ, KK)) : {SV(xs, KK, JJ) == SV(xs, KK, _) : List<&2, U32>}
      {==}
    case 1n+n:
      +xs = D.view(C.BT(len, t))
      +JJ = U32.to_nat(j)
      +KK = U32.to_nat(k)
      +LL = U32.to_nat(len)
      +x = C.AT(len, tb, p)
      +j1 = (j + 1 : U32)
      +tb1 = I.set_tree(U32, tb, (j >> 2n : U32), W.put_byte(C.WD(tb, (j >> 2n : U32)), U32.to_nat((j .&. 3 : U32)), x))
      +M = Nat.mul(4n, Nat.pow(2n, d))
      +hd = C.ok_d(len, t, d, h0)
      +hL = C.ok_len(len, t, d, h0)
      +hlt = sv_lt(JJ, KK, n, LL, hm)
      +hltj = sv_lt_j(JJ, KK, n, LL, hm)
      +ej1 = C.inc_fits(j, d, hd, N.lt_le_trans(JJ, LL, M, hltj, hL))
      +hj1 = AB.subst(Nat, y => {Nat.is_le(Nat.add(y, KK), LL) == True{} : Bool}, Nat.add(JJ, 1n), U32.to_nat(j1),
        Equal.sym(Nat, U32.to_nat(j1), Nat.add(JJ, 1n), ej1), sv_jk1(JJ, KK, LL, hlt))
      +hp1 = C.add_fits(j1, k, d, hd, N.le_trans(Nat.add(U32.to_nat(j1), KK), LL, M, hj1, hL))
      +hm1 = AB.subst(Nat, y => {Nat.add(Nat.add(y, KK), n) == LL : Nat}, Nat.add(JJ, 1n), U32.to_nat(j1),
        Equal.sym(Nat, U32.to_nat(j1), Nat.add(JJ, 1n), ej1),
        Equal.trans(Nat, Nat.add(Nat.add(Nat.add(JJ, 1n), KK), n), Nat.add(Nat.add(JJ, KK), 1n+n), LL, sv_m(JJ, KK, n), hm))
      +hb1 = AB.subst(D.Bytes, y => {D.ok(y, d) == True{} : Bool}, B.set(C.BT(len, tb), j, x), C.BT(len, tb1), O.set_eq_t(len, tb, j, x),
        O.set_ok_t(len, tb, d, j, x, hb))
      +hx = sv_x(len, t, d, k, tb, j, p, h0, hb, hp, hv, hlt)
      +hx256 = AB.subst(U32, y => {U32.is_lt(y, 256) == True{} : Bool}, W.byte(C.WD(tb, (p >> 2n : U32)), U32.to_nat((p .&. 3 : U32))), x,
        Equal.sym(U32, x, W.byte(C.WD(tb, (p >> 2n : U32)), U32.to_nat((p .&. 3 : U32))), C.at_val(len, tb, p)),
        Y.byte_lt(C.WD(tb, (p >> 2n : U32)), U32.to_nat((p .&. 3 : U32))))
      +pv = AB.subst(D.Bytes, y => {D.view(y) == List.set(&2, U32, D.view(C.BT(len, tb)), JJ, x) : List<&2, U32>},
        B.set(C.BT(len, tb), j, x), C.BT(len, tb1), O.set_eq_t(len, tb, j, x), O.set_view_t(len, tb, d, j, x, hb, hltj, hx256))
      +hjl = AB.subst(Nat, y => {Nat.is_lt(JJ, y) == True{} : Bool}, LL, List.length(&2, U32, xs),
        Equal.sym(Nat, List.length(&2, U32, xs), LL, O.view_size_t(len, t, d, h0)), hltj)
      +sw = sv_write(xs, JJ, KK, x, sv_jd(len, t, d, JJ, KK, h0, hlt), hjl, hx)
      +hv1a = Equal.trans(List<&2, U32>, D.view(C.BT(len, tb1)), List.set(&2, U32, D.view(C.BT(len, tb)), JJ, x), SV(xs, KK, Nat.add(JJ, 1n)), pv,
        AB.subst(List<&2, U32>, y => {List.set(&2, U32, y, JJ, x) == SV(xs, KK, Nat.add(JJ, 1n)) : List<&2, U32>}, SV(xs, KK, JJ), D.view(C.BT(len, tb)),
          Equal.sym(List<&2, U32>, D.view(C.BT(len, tb)), SV(xs, KK, JJ), hv), sw))
      +hv1 = AB.subst(Nat, y => {D.view(C.BT(len, tb1)) == SV(xs, KK, y) : List<&2, U32>}, Nat.add(JJ, 1n), U32.to_nat(j1),
        Equal.sym(Nat, U32.to_nat(j1), Nat.add(JJ, 1n), ej1), hv1a)
      sv(n, len, t, d, k, tb1, j1, (j1 + k : U32), h0, hb1, hp1, hm1, hv1)

# The laws
# ========

law sv0:
  for +xs: List<&2, U32>
  for +kk: Nat
  {SV(xs, kk, 0n) == xs : List<&2, U32>}

def sv0(xs, kk):
  %Equal.sym(List<&2, U32>, List.take(&2, U32, List.drop(&2, U32, xs, kk), 0n), Nil{}, Q.take_zero(List.drop(&2, U32, xs, kk))) :
    {List.append(&2, U32, _, List.drop(&2, U32, xs, 0n)) == xs : List<&2, U32>}
  X.drop_zero(xs)

law shift_view_t:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +k: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hk: {Nat.is_le(U32.to_nat(k), D.size(C.BT(len, t))) == True{} : Bool}
  {D.view(B.shift(C.BT(len, t), k)) == List.drop(&2, U32, D.view(C.BT(len, t)), U32.to_nat(k)) : List<&2, U32>}

def shift_view_t(len, t, d, k, h, hk):
  +xs = D.view(C.BT(len, t))
  +KK = U32.to_nat(k)
  +LL = U32.to_nat(len)
  +N0 = Nat.sub(LL, KK)
  +T2 = SGT(len, N0, t, 0, k, k)
  +ys = List.drop(&2, U32, xs, KK)
  +eN = U.to_nat_sub_le(len, k, Equal.trans(Bool, U32.is_le(k, len), Nat.is_le(KK, LL), True{}, U.is_le_to_nat(k, len), hk))
  +hle = AB.subst(Nat, y => {Nat.is_le(y, LL) == True{} : Bool}, N0, U32.to_nat((len - k : U32)), Equal.sym(Nat, U32.to_nat((len - k : U32)), N0, eN), sub_le(LL, KK))
  +hyl = xl(len, t, d, KK, h)
  +hN0 = AB.subst(Nat, y => {Nat.is_le(N0, y) == True{} : Bool}, N0, List.length(&2, U32, ys), Equal.sym(Nat, List.length(&2, U32, ys), N0, hyl), N.le_refl(N0))
  %Equal.sym(D.Bytes, B.shift.go(N0, B.at(C.BT(len, t), k), 0, k), C.BT(len, T2), shift_go_eq(N0, len, t, 0, k, k)) :
    {D.view(B.truncate(_, (len - k : U32))) == ys : List<&2, U32>}
  %Equal.sym(List<&2, U32>, D.view(B.truncate(C.BT(len, T2), (len - k : U32))), List.take(&2, U32, D.view(C.BT(len, T2)), U32.to_nat((len - k : U32))),
    O.truncate_view_t(len, T2, (len - k : U32), hle)) :
    {_ == ys : List<&2, U32>}
  %Equal.sym(Nat, U32.to_nat((len - k : U32)), N0, eN) : {List.take(&2, U32, D.view(C.BT(len, T2)), _) == ys : List<&2, U32>}
  %Equal.sym(List<&2, U32>, D.view(C.BT(len, T2)), SF(xs, KK, LL),
    sv(N0, len, t, d, k, t, 0, k, h, h, {==}, N.le_sub_add(KK, LL, hk), Equal.sym(List<&2, U32>, SV(xs, KK, 0n), xs, sv0(xs, KK)))) :
    {List.take(&2, U32, _, N0) == ys : List<&2, U32>}
  +A = List.take(&2, U32, ys, N0)
  +la = Q.take_length(ys, N0, hN0)
  %Equal.sym(List<&2, U32>, List.take(&2, U32, List.append(&2, U32, A, List.drop(&2, U32, xs, N0)), N0), List.take(&2, U32, A, N0),
    Q.take_append_l(A, List.drop(&2, U32, xs, N0), N0,
      AB.subst(Nat, y => {Nat.is_le(N0, y) == True{} : Bool}, N0, List.length(&2, U32, A), Equal.sym(Nat, List.length(&2, U32, A), N0, la), N.le_refl(N0)))) :
    {_ == ys : List<&2, U32>}
  %Equal.sym(List<&2, U32>, List.take(&2, U32, A, N0), A, Q.take_take(ys, N0, N0, N.le_refl(N0))) : {_ == ys : List<&2, U32>}
  take_all(ys, N0, AB.subst(Nat, y => {Nat.is_le(y, N0) == True{} : Bool}, N0, List.length(&2, U32, ys), Equal.sym(Nat, List.length(&2, U32, ys), N0, hyl), N.le_refl(N0)))

law shift_ok_t:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +k: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hk: {Nat.is_le(U32.to_nat(k), D.size(C.BT(len, t))) == True{} : Bool}
  {D.ok(B.shift(C.BT(len, t), k), d) == True{} : Bool}

def shift_ok_t(len, t, d, k, h, hk):
  +KK = U32.to_nat(k)
  +LL = U32.to_nat(len)
  +N0 = Nat.sub(LL, KK)
  +T2 = SGT(len, N0, t, 0, k, k)
  +eN = U.to_nat_sub_le(len, k, Equal.trans(Bool, U32.is_le(k, len), Nat.is_le(KK, LL), True{}, U.is_le_to_nat(k, len), hk))
  +hle = AB.subst(Nat, y => {Nat.is_le(y, LL) == True{} : Bool}, N0, U32.to_nat((len - k : U32)), Equal.sym(Nat, U32.to_nat((len - k : U32)), N0, eN), sub_le(LL, KK))
  %Equal.sym(D.Bytes, B.shift.go(N0, B.at(C.BT(len, t), k), 0, k), C.BT(len, T2), shift_go_eq(N0, len, t, 0, k, k)) :
    {D.ok(B.truncate(_, (len - k : U32)), d) == True{} : Bool}
  O.truncate_ok_t(len, T2, d, (len - k : U32), sgt_ok(N0, len, t, d, 0, k, k, h), hle)
