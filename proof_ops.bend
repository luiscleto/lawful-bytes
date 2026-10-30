import Base
import ./defs.bend as D
import ./bytes.bend as B
import ./proof_seq.bend as Q
import ./proof_core.bend as C
import lawful-words@0.1.0.0/defs.bend as W
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-arrays@0.1.0.0/defs.bend as A
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-arrays@0.1.0.0/proof_tree.bend as P
import lawful-arrays@0.1.0.0/proof_index.bend as I

# The laws that do not loop, stated on the mirror C.BT(len, t): `name_t` is
# law `name` with each Bytes b replaced by BT(len, t) (its parameters in the
# same order, b giving len, t).

# The bytes in use fit in the block.
law ulen:
  for +t: P.Tree<U32>
  for +d: Nat
  for +hf: {A.full(U32, P.fromT(U32, t), d) == True{} : Bool}
  {List.length(&2, U32, D.unpack(C.WL(t))) == Nat.mul(4n, Nat.pow(2n, d)) : Nat}

def ulen(t, d, hf):
  %Equal.sym(Nat, List.length(&2, U32, D.unpack(C.WL(t))), Nat.mul(4n, List.length(&2, U32, C.WL(t))), Q.unpack_length(C.WL(t))) :
    {_ == Nat.mul(4n, Nat.pow(2n, d)) : Nat}
  %Equal.sym(Nat, List.length(&2, U32, C.WL(t)), Nat.pow(2n, d), P.view_length(U32, d, t, hf)) :
    {Nat.mul(4n, _) == Nat.mul(4n, Nat.pow(2n, d)) : Nat}
  {==}

# What a Bytes holds
# ==================

law view_size_t:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  {List.length(&2, U32, D.view(C.BT(len, t))) == D.size(C.BT(len, t)) : Nat}

def view_size_t(len, t, d, h):
  +U = D.unpack(C.WL(t))
  Q.take_length(U, U32.to_nat(len),
    AB.subst(Nat, x => {Nat.is_le(U32.to_nat(len), x) == True{} : Bool}, Nat.mul(4n, Nat.pow(2n, d)), List.length(&2, U32, U),
      Equal.sym(Nat, List.length(&2, U32, U), Nat.mul(4n, Nat.pow(2n, d)), ulen(t, d, C.ok_full(len, t, d, h))),
      C.ok_len(len, t, d, h)))

law view_bytes_t:
  for +len: U32
  for +t: P.Tree<U32>
  {D.all_bytes(D.view(C.BT(len, t))) == True{} : Bool}

def view_bytes_t(len, t):
  Q.all_bytes_take(D.unpack(C.WL(t)), U32.to_nat(len), Q.all_bytes_unpack(C.WL(t)))

law cap_ok_t:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  {D.cap(C.BT(len, t)) == Nat.mul(4n, Nat.pow(2n, d)) : Nat}

def cap_ok_t(len, t, d, h):
  %Equal.sym(Nat, List.length(&2, U32, C.WL(t)), Nat.pow(2n, d), P.view_length(U32, d, t, C.ok_full(len, t, d, h))) :
    {Nat.mul(4n, _) == Nat.mul(4n, Nat.pow(2n, d)) : Nat}
  {==}

# Writing
# =======

law set_eq_t:
  for +len: U32
  for +t: P.Tree<U32>
  for +i: U32
  for +v: U32
  {B.set(C.BT(len, t), i, v) == C.BT(len, I.set_tree(U32, t, (i >> 2n : U32), W.put_byte(C.WD(t, (i >> 2n : U32)), U32.to_nat((i .&. 3 : U32)), v))) : D.Bytes}

def set_eq_t(len, t, i, v):
  +k = (i >> 2n : U32)
  +pb = W.put_byte(C.WD(t, k), U32.to_nat((i .&. 3 : U32)), v)
  %Equal.sym(Array<U32> & U32, Array.get(U32, P.fromT(U32, t), k), (P.fromT(U32, t), C.WD(t, k)), P.get_pair_t(U32, t, k)) :
    {B.set.fin(len, i, v, _) == C.BT(len, I.set_tree(U32, t, k, pb)) : D.Bytes}
  %Equal.sym(Array<U32>, Array.set(U32, P.fromT(U32, t), k, pb), P.fromT(U32, I.set_tree(U32, t, k, pb)), I.set_tree_eq(U32, t, k, pb)) :
    {D.Bytes{len, _} == C.BT(len, I.set_tree(U32, t, k, pb)) : D.Bytes}
  {==}

law set_view_t:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +i: U32
  for +v: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hi: {Nat.is_lt(U32.to_nat(i), D.size(C.BT(len, t))) == True{} : Bool}
  for +hv: {U32.is_lt(v, 256) == True{} : Bool}
  {D.view(B.set(C.BT(len, t), i, v)) == List.set(&2, U32, D.view(C.BT(len, t)), U32.to_nat(i), v) : List<&2, U32>}

def set_view_t(len, t, d, i, v, h, hi, hv):
  +k = (i >> 2n : U32)
  +w = C.WD(t, k)
  +pb = W.put_byte(w, U32.to_nat((i .&. 3 : U32)), v)
  +hf = C.ok_full(len, t, d, h)
  +hd = C.ok_d(len, t, d, h)
  +hk = C.word_lt(i, d, N.lt_le_trans(U32.to_nat(i), U32.to_nat(len), Nat.mul(4n, Nat.pow(2n, d)), hi, C.ok_len(len, t, d, h)))
  +RHS = List.set(&2, U32, D.view(C.BT(len, t)), U32.to_nat(i), v)
  %Equal.sym(D.Bytes, B.set(C.BT(len, t), i, v), C.BT(len, I.set_tree(U32, t, k, pb)), set_eq_t(len, t, i, v)) :
    {D.view(_) == RHS : List<&2, U32>}
  %Equal.sym(List<&2, U32>, C.WL(I.set_tree(U32, t, k, pb)), List.set(&2, U32, C.WL(t), U32.to_nat(k), pb), C.wl_set(t, d, k, pb, hf, hd, hk)) :
    {List.take(&2, U32, D.unpack(_), U32.to_nat(len)) == RHS : List<&2, U32>}
  %Equal.sym(List<&2, U32>, D.unpack(List.set(&2, U32, C.WL(t), U32.to_nat(k), pb)), List.set(&2, U32, D.unpack(C.WL(t)), U32.to_nat(i), v),
    C.unpack_set_i(C.WL(t), i, w, v, hv, C.wd_get(t, d, k, hf, hd, hk))) :
    {List.take(&2, U32, _, U32.to_nat(len)) == RHS : List<&2, U32>}
  Q.take_set(D.unpack(C.WL(t)), U32.to_nat(len), U32.to_nat(i), v)

law set_ok_t:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +i: U32
  for +v: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  {D.ok(B.set(C.BT(len, t), i, v), d) == True{} : Bool}

def set_ok_t(len, t, d, i, v, h):
  +k = (i >> 2n : U32)
  +pb = W.put_byte(C.WD(t, k), U32.to_nat((i .&. 3 : U32)), v)
  %Equal.sym(D.Bytes, B.set(C.BT(len, t), i, v), C.BT(len, I.set_tree(U32, t, k, pb)), set_eq_t(len, t, i, v)) :
    {D.ok(_, d) == True{} : Bool}
  C.ok_mk(len, I.set_tree(U32, t, k, pb), d, C.full_set(t, d, k, pb, C.ok_full(len, t, d, h)), C.ok_d(len, t, d, h), C.ok_len(len, t, d, h))

law push_eq_t:
  for +len: U32
  for +t: P.Tree<U32>
  for +v: U32
  {B.push(C.BT(len, t), v) == C.BT((len + 1 : U32), I.set_tree(U32, t, (len >> 2n : U32), W.put_byte(C.WD(t, (len >> 2n : U32)), U32.to_nat((len .&. 3 : U32)), v))) : D.Bytes}

def push_eq_t(len, t, v):
  +k = (len >> 2n : U32)
  +pb = W.put_byte(C.WD(t, k), U32.to_nat((len .&. 3 : U32)), v)
  %Equal.sym(Array<U32> & U32, Array.get(U32, P.fromT(U32, t), k), (P.fromT(U32, t), C.WD(t, k)), P.get_pair_t(U32, t, k)) :
    {B.push.fin(len, v, _) == C.BT((len + 1 : U32), I.set_tree(U32, t, k, pb)) : D.Bytes}
  %Equal.sym(Array<U32>, Array.set(U32, P.fromT(U32, t), k, pb), P.fromT(U32, I.set_tree(U32, t, k, pb)), I.set_tree_eq(U32, t, k, pb)) :
    {D.Bytes{(len + 1 : U32), _} == C.BT((len + 1 : U32), I.set_tree(U32, t, k, pb)) : D.Bytes}
  {==}

# The room test of push, as numbers.
law push_room:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hc: {Nat.is_lt(D.size(C.BT(len, t)), D.cap(C.BT(len, t))) == True{} : Bool}
  {Nat.is_lt(U32.to_nat(len), Nat.mul(4n, Nat.pow(2n, d))) == True{} : Bool}

def push_room(len, t, d, h, hc):
  AB.subst(Nat, x => {Nat.is_lt(U32.to_nat(len), x) == True{} : Bool}, D.cap(C.BT(len, t)), Nat.mul(4n, Nat.pow(2n, d)),
    cap_ok_t(len, t, d, h), hc)

law push_view_t:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +v: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hc: {Nat.is_lt(D.size(C.BT(len, t)), D.cap(C.BT(len, t))) == True{} : Bool}
  for +hv: {U32.is_lt(v, 256) == True{} : Bool}
  {D.view(B.push(C.BT(len, t), v)) == List.append(&2, U32, D.view(C.BT(len, t)), [v]) : List<&2, U32>}

def push_view_t(len, t, d, v, h, hc, hv):
  +k = (len >> 2n : U32)
  +w = C.WD(t, k)
  +pb = W.put_byte(w, U32.to_nat((len .&. 3 : U32)), v)
  +hf = C.ok_full(len, t, d, h)
  +hd = C.ok_d(len, t, d, h)
  +hr = push_room(len, t, d, h, hc)
  +hk = C.word_lt(len, d, hr)
  +U = D.unpack(C.WL(t))
  +RHS = List.append(&2, U32, D.view(C.BT(len, t)), [v])
  %Equal.sym(D.Bytes, B.push(C.BT(len, t), v), C.BT((len + 1 : U32), I.set_tree(U32, t, k, pb)), push_eq_t(len, t, v)) :
    {D.view(_) == RHS : List<&2, U32>}
  %Equal.sym(List<&2, U32>, C.WL(I.set_tree(U32, t, k, pb)), List.set(&2, U32, C.WL(t), U32.to_nat(k), pb), C.wl_set(t, d, k, pb, hf, hd, hk)) :
    {List.take(&2, U32, D.unpack(_), U32.to_nat((len + 1 : U32))) == RHS : List<&2, U32>}
  %Equal.sym(List<&2, U32>, D.unpack(List.set(&2, U32, C.WL(t), U32.to_nat(k), pb)), List.set(&2, U32, U, U32.to_nat(len), v),
    C.unpack_set_i(C.WL(t), len, w, v, hv, C.wd_get(t, d, k, hf, hd, hk))) :
    {List.take(&2, U32, _, U32.to_nat((len + 1 : U32))) == RHS : List<&2, U32>}
  %Equal.sym(Nat, U32.to_nat((len + 1 : U32)), Nat.add(U32.to_nat(len), 1n), C.inc_fits(len, d, hd, hr)) :
    {List.take(&2, U32, List.set(&2, U32, U, U32.to_nat(len), v), _) == RHS : List<&2, U32>}
  Q.take_set_succ(U, U32.to_nat(len), v,
    AB.subst(Nat, x => {Nat.is_lt(U32.to_nat(len), x) == True{} : Bool}, Nat.mul(4n, Nat.pow(2n, d)), List.length(&2, U32, U),
      Equal.sym(Nat, List.length(&2, U32, U), Nat.mul(4n, Nat.pow(2n, d)), ulen(t, d, hf)), hr))

law push_ok_t:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +v: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hc: {Nat.is_lt(D.size(C.BT(len, t)), D.cap(C.BT(len, t))) == True{} : Bool}
  {D.ok(B.push(C.BT(len, t), v), d) == True{} : Bool}

def push_ok_t(len, t, d, v, h, hc):
  +k = (len >> 2n : U32)
  +pb = W.put_byte(C.WD(t, k), U32.to_nat((len .&. 3 : U32)), v)
  +hd = C.ok_d(len, t, d, h)
  +hr = push_room(len, t, d, h, hc)
  +M = Nat.mul(4n, Nat.pow(2n, d))
  %Equal.sym(D.Bytes, B.push(C.BT(len, t), v), C.BT((len + 1 : U32), I.set_tree(U32, t, k, pb)), push_eq_t(len, t, v)) :
    {D.ok(_, d) == True{} : Bool}
  C.ok_mk((len + 1 : U32), I.set_tree(U32, t, k, pb), d, C.full_set(t, d, k, pb, C.ok_full(len, t, d, h)), hd,
    AB.subst(Nat, x => {Nat.is_le(x, M) == True{} : Bool}, Nat.add(U32.to_nat(len), 1n), U32.to_nat((len + 1 : U32)),
      Equal.sym(Nat, U32.to_nat((len + 1 : U32)), Nat.add(U32.to_nat(len), 1n), C.inc_fits(len, d, hd, hr)),
      C.succ_le(U32.to_nat(len), M, hr)))

# Length, capacity, trimming
# ==========================

law capacity_pair_t:
  for +len: U32
  for +t: P.Tree<U32>
  {B.capacity(C.BT(len, t)) == (C.BT(len, t), Pair.snd(D.Bytes, U32, B.capacity(C.BT(len, t)))) : D.Bytes & U32}

def capacity_pair_t(len, t):
  %Equal.sym(Array<U32> & U32, Array.size(U32, P.fromT(U32, t)), (P.fromT(U32, t), Pair.snd(Array<U32>, U32, Array.size(U32, P.fromT(U32, t)))), P.size_eta(U32, P.fromT(U32, t))) :
    {B.capacity.fin(len, _) == (C.BT(len, t), Pair.snd(D.Bytes, U32, B.capacity.fin(len, _))) : D.Bytes & U32}
  {==}

law capacity_view_t:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  {U32.to_nat(Pair.snd(D.Bytes, U32, B.capacity(C.BT(len, t)))) == D.cap(C.BT(len, t)) : Nat}

def capacity_view_t(len, t, d, h):
  +hf = C.ok_full(len, t, d, h)
  +X = Nat.pow(2n, d)
  %Equal.sym(Array<U32> & U32, Array.size(U32, P.fromT(U32, t)), (P.fromT(U32, t), U32.shln(1, d)), P.size_tree(U32, d, t, hf)) :
    {U32.to_nat(Pair.snd(D.Bytes, U32, B.capacity.fin(len, _))) == D.cap(C.BT(len, t)) : Nat}
  %Equal.sym(Nat, List.length(&2, U32, C.WL(t)), X, P.view_length(U32, d, t, hf)) :
    {U32.to_nat(U32.shln(U32.shln(1, d), 2n)) == Nat.mul(4n, _) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.mul(2n, 2n), X), Nat.mul(2n, Nat.mul(2n, X)), N.mul_assoc(2n, 2n, X)) :
    {U32.to_nat(U32.shln(U32.shln(1, d), 2n)) == _ : Nat}
  I.size_n(Nat.add(2n, d), C.he32(d, C.ok_d(len, t, d, h)))

law truncate_view_t:
  for +len: U32
  for +t: P.Tree<U32>
  for +n: U32
  for +h: {Nat.is_le(U32.to_nat(n), D.size(C.BT(len, t))) == True{} : Bool}
  {D.view(B.truncate(C.BT(len, t), n)) == List.take(&2, U32, D.view(C.BT(len, t)), U32.to_nat(n)) : List<&2, U32>}

def truncate_view_t(len, t, n, h):
  +U = D.unpack(C.WL(t))
  Equal.sym(List<&2, U32>, List.take(&2, U32, List.take(&2, U32, U, U32.to_nat(len)), U32.to_nat(n)), List.take(&2, U32, U, U32.to_nat(n)),
    Q.take_take(U, U32.to_nat(len), U32.to_nat(n), h))

law truncate_ok_t:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +n: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hn: {Nat.is_le(U32.to_nat(n), D.size(C.BT(len, t))) == True{} : Bool}
  {D.ok(B.truncate(C.BT(len, t), n), d) == True{} : Bool}

def truncate_ok_t(len, t, d, n, h, hn):
  C.ok_mk(n, t, d, C.ok_full(len, t, d, h), C.ok_d(len, t, d, h),
    N.le_trans(U32.to_nat(n), U32.to_nat(len), Nat.mul(4n, Nat.pow(2n, d)), hn, C.ok_len(len, t, d, h)))
