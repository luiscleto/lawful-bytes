import Base
import ./defs.bend as D
import ./bytes.bend as B
import ./LAWS.bend as L
import ./proof_core.bend as C
import ./proof_ops.bend as O
import ./proof_append.bend as X
import ./proof_find.bend as F
import ./proof_same.bend as S
import ./proof_grow.bend as G
import ./proof_shift.bend as H
import ./proof_list.bend as Q

# Proofs of the laws: `def L.name` proves `law name` of LAWS.bend. A Bytes can
# be used once, so each law about one goes through its mirror (C.bmirror):
# BT(len, t) with a Tree<U32> t, about which the lemmas may say as much as they
# need. The `.go` def takes the mirror apart, rewrites the goal and transports
# the hypotheses (C.tr).

# Reading
# =======

def at_view.go(-b: D.Bytes, +d: Nat, +i: U32, h: {D.ok(b, d) == True{} : Bool},
  hi: {Nat.is_lt(U32.to_nat(i), D.size(b)) == True{} : Bool}, m: C.BMirror(b)) ->
  {Some{Pair.snd(D.Bytes, U32, B.at(b, i))} == List.get(&2, U32, D.view(b), U32.to_nat(i)) : Maybe<&2, U32>}:
  (+len, m2) = m
  (+t, +e) = m2
  %e : {Some{Pair.snd(D.Bytes, U32, B.at(_, i))} == List.get(&2, U32, D.view(_), U32.to_nat(i)) : Maybe<&2, U32>}
  +h2 = C.tr(x => {D.ok(x, d) == True{} : Bool}, b, len, t, e, h)
  C.at_view_t(len, t, d, i, C.ok_full(len, t, d, h2), C.ok_d(len, t, d, h2), C.ok_len(len, t, d, h2),
    C.tr(x => {Nat.is_lt(U32.to_nat(i), D.size(x)) == True{} : Bool}, b, len, t, e, hi))

def L.at_view(b, d, i, h, hi):
  at_view.go(b, d, i, h, hi, C.bmirror(b))

# Laws about a Bytes
# ==================

# One wrapper per law (written mechanically from LAWS.bend): the mirror lemma
# `name_t` is law `name` with each Bytes b replaced by C.BT(l_b, t_b).

def view_size.go(-b: D.Bytes, +d: Nat, h: {D.ok(b, d) == True{} : Bool}, m_b: C.BMirror(b)) ->
  {List.length(&2, U32, D.view(b)) == D.size(b) : Nat}:
  (+l_b, m2_b) = m_b
  (+t_b, +e_b) = m2_b
  %e_b : {List.length(&2, U32, D.view(_)) == D.size(_) : Nat}
  +h_t = C.tr(x => {D.ok(x, d) == True{} : Bool}, b, l_b, t_b, e_b, h)
  O.view_size_t(l_b, t_b, d, h_t)

def L.view_size(b, d, h):
  view_size.go(b, d, h, C.bmirror(b))

def view_bytes.go(-b: D.Bytes, m_b: C.BMirror(b)) ->
  {D.all_bytes(D.view(b)) == True{} : Bool}:
  (+l_b, m2_b) = m_b
  (+t_b, +e_b) = m2_b
  %e_b : {D.all_bytes(D.view(_)) == True{} : Bool}
  O.view_bytes_t(l_b, t_b)

def L.view_bytes(b):
  view_bytes.go(b, C.bmirror(b))

def cap_ok.go(-b: D.Bytes, +d: Nat, h: {D.ok(b, d) == True{} : Bool}, m_b: C.BMirror(b)) ->
  {D.cap(b) == Nat.mul(4n, Nat.pow(2n, d)) : Nat}:
  (+l_b, m2_b) = m_b
  (+t_b, +e_b) = m2_b
  %e_b : {D.cap(_) == Nat.mul(4n, Nat.pow(2n, d)) : Nat}
  +h_t = C.tr(x => {D.ok(x, d) == True{} : Bool}, b, l_b, t_b, e_b, h)
  O.cap_ok_t(l_b, t_b, d, h_t)

def L.cap_ok(b, d, h):
  cap_ok.go(b, d, h, C.bmirror(b))

def grow_view.go(-b: D.Bytes, +d: Nat, +e: Nat, h: {D.ok(b, d) == True{} : Bool}, he: {Nat.is_le(d, e) == True{} : Bool}, he29: {Nat.is_le(e, 29n) == True{} : Bool}, m_b: C.BMirror(b)) ->
  {D.view(B.grow(b, e)) == D.view(b) : List<&2, U32>}:
  (+l_b, m2_b) = m_b
  (+t_b, +e_b) = m2_b
  %e_b : {D.view(B.grow(_, e)) == D.view(_) : List<&2, U32>}
  +h_t = C.tr(x => {D.ok(x, d) == True{} : Bool}, b, l_b, t_b, e_b, h)
  G.grow_view_t(l_b, t_b, d, e, h_t, he, he29)

def L.grow_view(b, d, e, h, he, he29):
  grow_view.go(b, d, e, h, he, he29, C.bmirror(b))

def grow_ok.go(-b: D.Bytes, +d: Nat, +e: Nat, h: {D.ok(b, d) == True{} : Bool}, he: {Nat.is_le(d, e) == True{} : Bool}, he29: {Nat.is_le(e, 29n) == True{} : Bool}, m_b: C.BMirror(b)) ->
  {D.ok(B.grow(b, e), e) == True{} : Bool}:
  (+l_b, m2_b) = m_b
  (+t_b, +e_b) = m2_b
  %e_b : {D.ok(B.grow(_, e), e) == True{} : Bool}
  +h_t = C.tr(x => {D.ok(x, d) == True{} : Bool}, b, l_b, t_b, e_b, h)
  G.grow_ok_t(l_b, t_b, d, e, h_t, he, he29)

def L.grow_ok(b, d, e, h, he, he29):
  grow_ok.go(b, d, e, h, he, he29, C.bmirror(b))

def at_pair.go(-b: D.Bytes, +i: U32, m_b: C.BMirror(b)) ->
  {B.at(b, i) == (b, Pair.snd(D.Bytes, U32, B.at(b, i))) : D.Bytes & U32}:
  (+l_b, m2_b) = m_b
  (+t_b, +e_b) = m2_b
  %e_b : {B.at(_, i) == (_, Pair.snd(D.Bytes, U32, B.at(_, i))) : D.Bytes & U32}
  C.at_pair_t(l_b, t_b, i)

def L.at_pair(b, i):
  at_pair.go(b, i, C.bmirror(b))

def find_view.go(-b: D.Bytes, +d: Nat, +from: U32, +to: U32, +c: U32, h: {D.ok(b, d) == True{} : Bool}, hft: {U32.is_le(from, to) == True{} : Bool}, ht: {Nat.is_le(U32.to_nat(to), D.size(b)) == True{} : Bool}, hc: {U32.is_lt(c, 256) == True{} : Bool}, m_b: C.BMirror(b)) ->
  {U32.to_nat(Pair.snd(D.Bytes, U32, B.find(b, from, to, c))) == D.first(D.view(b), U32.to_nat(from), U32.to_nat(to), c) : Nat}:
  (+l_b, m2_b) = m_b
  (+t_b, +e_b) = m2_b
  %e_b : {U32.to_nat(Pair.snd(D.Bytes, U32, B.find(_, from, to, c))) == D.first(D.view(_), U32.to_nat(from), U32.to_nat(to), c) : Nat}
  +h_t = C.tr(x => {D.ok(x, d) == True{} : Bool}, b, l_b, t_b, e_b, h)
  +ht_t = C.tr(x => {Nat.is_le(U32.to_nat(to), D.size(x)) == True{} : Bool}, b, l_b, t_b, e_b, ht)
  F.find_view_t(l_b, t_b, d, from, to, c, h_t, hft, ht_t, hc)

def L.find_view(b, d, from, to, c, h, hft, ht, hc):
  find_view.go(b, d, from, to, c, h, hft, ht, hc, C.bmirror(b))

def find_pair.go(-b: D.Bytes, +from: U32, +to: U32, +c: U32, m_b: C.BMirror(b)) ->
  {B.find(b, from, to, c) == (b, Pair.snd(D.Bytes, U32, B.find(b, from, to, c))) : D.Bytes & U32}:
  (+l_b, m2_b) = m_b
  (+t_b, +e_b) = m2_b
  %e_b : {B.find(_, from, to, c) == (_, Pair.snd(D.Bytes, U32, B.find(_, from, to, c))) : D.Bytes & U32}
  F.find_pair_t(l_b, t_b, from, to, c)

def L.find_pair(b, from, to, c):
  find_pair.go(b, from, to, c, C.bmirror(b))

def find2_view.go(-b: D.Bytes, +d: Nat, +from: U32, +to: U32, +c1: U32, +c2: U32, h: {D.ok(b, d) == True{} : Bool}, hft: {U32.is_le(from, to) == True{} : Bool}, ht: {Nat.is_le(U32.to_nat(to), D.size(b)) == True{} : Bool}, hc1: {U32.is_lt(c1, 256) == True{} : Bool}, hc2: {U32.is_lt(c2, 256) == True{} : Bool}, m_b: C.BMirror(b)) ->
  {U32.to_nat(Pair.snd(D.Bytes, U32, B.find2(b, from, to, c1, c2))) == D.first2(D.view(b), U32.to_nat(from), U32.to_nat(to), c1, c2) : Nat}:
  (+l_b, m2_b) = m_b
  (+t_b, +e_b) = m2_b
  %e_b : {U32.to_nat(Pair.snd(D.Bytes, U32, B.find2(_, from, to, c1, c2))) == D.first2(D.view(_), U32.to_nat(from), U32.to_nat(to), c1, c2) : Nat}
  +h_t = C.tr(x => {D.ok(x, d) == True{} : Bool}, b, l_b, t_b, e_b, h)
  +ht_t = C.tr(x => {Nat.is_le(U32.to_nat(to), D.size(x)) == True{} : Bool}, b, l_b, t_b, e_b, ht)
  F.find2_view_t(l_b, t_b, d, from, to, c1, c2, h_t, hft, ht_t, hc1, hc2)

def L.find2_view(b, d, from, to, c1, c2, h, hft, ht, hc1, hc2):
  find2_view.go(b, d, from, to, c1, c2, h, hft, ht, hc1, hc2, C.bmirror(b))

def find2_pair.go(-b: D.Bytes, +from: U32, +to: U32, +c1: U32, +c2: U32, m_b: C.BMirror(b)) ->
  {B.find2(b, from, to, c1, c2) == (b, Pair.snd(D.Bytes, U32, B.find2(b, from, to, c1, c2))) : D.Bytes & U32}:
  (+l_b, m2_b) = m_b
  (+t_b, +e_b) = m2_b
  %e_b : {B.find2(_, from, to, c1, c2) == (_, Pair.snd(D.Bytes, U32, B.find2(_, from, to, c1, c2))) : D.Bytes & U32}
  F.find2_pair_t(l_b, t_b, from, to, c1, c2)

def L.find2_pair(b, from, to, c1, c2):
  find2_pair.go(b, from, to, c1, c2, C.bmirror(b))

def same_view.go(-a: D.Bytes, -b: D.Bytes, +d: Nat, +e: Nat, +i: U32, +j: U32, +n: U32, ha: {D.ok(a, d) == True{} : Bool}, hb: {D.ok(b, e) == True{} : Bool}, hi: {Nat.is_le(Nat.add(U32.to_nat(i), U32.to_nat(n)), D.size(a)) == True{} : Bool}, hj: {Nat.is_le(Nat.add(U32.to_nat(j), U32.to_nat(n)), D.size(b)) == True{} : Bool}, m_a: C.BMirror(a), m_b: C.BMirror(b)) ->
  {Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, B.same(a, i, b, j, n))) == D.list_eq(D.slice(D.view(a), U32.to_nat(i), U32.to_nat(n)), D.slice(D.view(b), U32.to_nat(j), U32.to_nat(n))) : Bool}:
  (+l_a, m2_a) = m_a
  (+t_a, +e_a) = m2_a
  (+l_b, m2_b) = m_b
  (+t_b, +e_b) = m2_b
  %e_a : {Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, B.same(_, i, b, j, n))) == D.list_eq(D.slice(D.view(_), U32.to_nat(i), U32.to_nat(n)), D.slice(D.view(b), U32.to_nat(j), U32.to_nat(n))) : Bool}
  %e_b : {Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, B.same(C.BT(l_a, t_a), i, _, j, n))) == D.list_eq(D.slice(D.view(C.BT(l_a, t_a)), U32.to_nat(i), U32.to_nat(n)), D.slice(D.view(_), U32.to_nat(j), U32.to_nat(n))) : Bool}
  +ha_t = C.tr(x => {D.ok(x, d) == True{} : Bool}, a, l_a, t_a, e_a, ha)
  +hb_t = C.tr(x => {D.ok(x, e) == True{} : Bool}, b, l_b, t_b, e_b, hb)
  +hi_t = C.tr(x => {Nat.is_le(Nat.add(U32.to_nat(i), U32.to_nat(n)), D.size(x)) == True{} : Bool}, a, l_a, t_a, e_a, hi)
  +hj_t = C.tr(x => {Nat.is_le(Nat.add(U32.to_nat(j), U32.to_nat(n)), D.size(x)) == True{} : Bool}, b, l_b, t_b, e_b, hj)
  S.same_view_t(l_a, t_a, l_b, t_b, d, e, i, j, n, ha_t, hb_t, hi_t, hj_t)

def L.same_view(a, b, d, e, i, j, n, ha, hb, hi, hj):
  same_view.go(a, b, d, e, i, j, n, ha, hb, hi, hj, C.bmirror(a), C.bmirror(b))

def same_pair.go(-a: D.Bytes, -b: D.Bytes, +i: U32, +j: U32, +n: U32, m_a: C.BMirror(a), m_b: C.BMirror(b)) ->
  {B.same(a, i, b, j, n) == (a, (b, Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, B.same(a, i, b, j, n))))) : D.Bytes & (D.Bytes & Bool)}:
  (+l_a, m2_a) = m_a
  (+t_a, +e_a) = m2_a
  (+l_b, m2_b) = m_b
  (+t_b, +e_b) = m2_b
  %e_a : {B.same(_, i, b, j, n) == (_, (b, Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, B.same(_, i, b, j, n))))) : D.Bytes & (D.Bytes & Bool)}
  %e_b : {B.same(C.BT(l_a, t_a), i, _, j, n) == (C.BT(l_a, t_a), (_, Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, B.same(C.BT(l_a, t_a), i, _, j, n))))) : D.Bytes & (D.Bytes & Bool)}
  S.same_pair_t(l_a, t_a, l_b, t_b, i, j, n)

def L.same_pair(a, b, i, j, n):
  same_pair.go(a, b, i, j, n, C.bmirror(a), C.bmirror(b))

def set_view.go(-b: D.Bytes, +d: Nat, +i: U32, +v: U32, h: {D.ok(b, d) == True{} : Bool}, hi: {Nat.is_lt(U32.to_nat(i), D.size(b)) == True{} : Bool}, hv: {U32.is_lt(v, 256) == True{} : Bool}, m_b: C.BMirror(b)) ->
  {D.view(B.set(b, i, v)) == List.set(&2, U32, D.view(b), U32.to_nat(i), v) : List<&2, U32>}:
  (+l_b, m2_b) = m_b
  (+t_b, +e_b) = m2_b
  %e_b : {D.view(B.set(_, i, v)) == List.set(&2, U32, D.view(_), U32.to_nat(i), v) : List<&2, U32>}
  +h_t = C.tr(x => {D.ok(x, d) == True{} : Bool}, b, l_b, t_b, e_b, h)
  +hi_t = C.tr(x => {Nat.is_lt(U32.to_nat(i), D.size(x)) == True{} : Bool}, b, l_b, t_b, e_b, hi)
  O.set_view_t(l_b, t_b, d, i, v, h_t, hi_t, hv)

def L.set_view(b, d, i, v, h, hi, hv):
  set_view.go(b, d, i, v, h, hi, hv, C.bmirror(b))

def set_ok.go(-b: D.Bytes, +d: Nat, +i: U32, +v: U32, h: {D.ok(b, d) == True{} : Bool}, m_b: C.BMirror(b)) ->
  {D.ok(B.set(b, i, v), d) == True{} : Bool}:
  (+l_b, m2_b) = m_b
  (+t_b, +e_b) = m2_b
  %e_b : {D.ok(B.set(_, i, v), d) == True{} : Bool}
  +h_t = C.tr(x => {D.ok(x, d) == True{} : Bool}, b, l_b, t_b, e_b, h)
  O.set_ok_t(l_b, t_b, d, i, v, h_t)

def L.set_ok(b, d, i, v, h):
  set_ok.go(b, d, i, v, h, C.bmirror(b))

def push_view.go(-b: D.Bytes, +d: Nat, +v: U32, h: {D.ok(b, d) == True{} : Bool}, hc: {Nat.is_lt(D.size(b), D.cap(b)) == True{} : Bool}, hv: {U32.is_lt(v, 256) == True{} : Bool}, m_b: C.BMirror(b)) ->
  {D.view(B.push(b, v)) == List.append(&2, U32, D.view(b), [v]) : List<&2, U32>}:
  (+l_b, m2_b) = m_b
  (+t_b, +e_b) = m2_b
  %e_b : {D.view(B.push(_, v)) == List.append(&2, U32, D.view(_), [v]) : List<&2, U32>}
  +h_t = C.tr(x => {D.ok(x, d) == True{} : Bool}, b, l_b, t_b, e_b, h)
  +hc_t = C.tr(x => {Nat.is_lt(D.size(x), D.cap(x)) == True{} : Bool}, b, l_b, t_b, e_b, hc)
  O.push_view_t(l_b, t_b, d, v, h_t, hc_t, hv)

def L.push_view(b, d, v, h, hc, hv):
  push_view.go(b, d, v, h, hc, hv, C.bmirror(b))

def push_ok.go(-b: D.Bytes, +d: Nat, +v: U32, h: {D.ok(b, d) == True{} : Bool}, hc: {Nat.is_lt(D.size(b), D.cap(b)) == True{} : Bool}, m_b: C.BMirror(b)) ->
  {D.ok(B.push(b, v), d) == True{} : Bool}:
  (+l_b, m2_b) = m_b
  (+t_b, +e_b) = m2_b
  %e_b : {D.ok(B.push(_, v), d) == True{} : Bool}
  +h_t = C.tr(x => {D.ok(x, d) == True{} : Bool}, b, l_b, t_b, e_b, h)
  +hc_t = C.tr(x => {Nat.is_lt(D.size(x), D.cap(x)) == True{} : Bool}, b, l_b, t_b, e_b, hc)
  O.push_ok_t(l_b, t_b, d, v, h_t, hc_t)

def L.push_ok(b, d, v, h, hc):
  push_ok.go(b, d, v, h, hc, C.bmirror(b))

def append_view.go(-dst: D.Bytes, -src: D.Bytes, +d: Nat, +e: Nat, +s: U32, +n: U32, hd: {D.ok(dst, d) == True{} : Bool}, he: {D.ok(src, e) == True{} : Bool}, hs: {Nat.is_le(Nat.add(U32.to_nat(s), U32.to_nat(n)), D.size(src)) == True{} : Bool}, hc: {Nat.is_le(Nat.add(D.size(dst), U32.to_nat(n)), D.cap(dst)) == True{} : Bool}, m_dst: C.BMirror(dst), m_src: C.BMirror(src)) ->
  {D.view(Pair.fst(D.Bytes, D.Bytes, B.append(dst, src, s, n))) == List.append(&2, U32, D.view(dst), D.slice(D.view(src), U32.to_nat(s), U32.to_nat(n))) : List<&2, U32>}:
  (+l_dst, m2_dst) = m_dst
  (+t_dst, +e_dst) = m2_dst
  (+l_src, m2_src) = m_src
  (+t_src, +e_src) = m2_src
  %e_dst : {D.view(Pair.fst(D.Bytes, D.Bytes, B.append(_, src, s, n))) == List.append(&2, U32, D.view(_), D.slice(D.view(src), U32.to_nat(s), U32.to_nat(n))) : List<&2, U32>}
  %e_src : {D.view(Pair.fst(D.Bytes, D.Bytes, B.append(C.BT(l_dst, t_dst), _, s, n))) == List.append(&2, U32, D.view(C.BT(l_dst, t_dst)), D.slice(D.view(_), U32.to_nat(s), U32.to_nat(n))) : List<&2, U32>}
  +hd_t = C.tr(x => {D.ok(x, d) == True{} : Bool}, dst, l_dst, t_dst, e_dst, hd)
  +he_t = C.tr(x => {D.ok(x, e) == True{} : Bool}, src, l_src, t_src, e_src, he)
  +hs_t = C.tr(x => {Nat.is_le(Nat.add(U32.to_nat(s), U32.to_nat(n)), D.size(x)) == True{} : Bool}, src, l_src, t_src, e_src, hs)
  +hc_t = C.tr(x => {Nat.is_le(Nat.add(D.size(x), U32.to_nat(n)), D.cap(x)) == True{} : Bool}, dst, l_dst, t_dst, e_dst, hc)
  X.append_view_t(l_dst, t_dst, l_src, t_src, d, e, s, n, hd_t, he_t, hs_t, hc_t)

def L.append_view(dst, src, d, e, s, n, hd, he, hs, hc):
  append_view.go(dst, src, d, e, s, n, hd, he, hs, hc, C.bmirror(dst), C.bmirror(src))

def append_ok.go(-dst: D.Bytes, -src: D.Bytes, +d: Nat, +s: U32, +n: U32, hd: {D.ok(dst, d) == True{} : Bool}, hc: {Nat.is_le(Nat.add(D.size(dst), U32.to_nat(n)), D.cap(dst)) == True{} : Bool}, m_dst: C.BMirror(dst), m_src: C.BMirror(src)) ->
  {D.ok(Pair.fst(D.Bytes, D.Bytes, B.append(dst, src, s, n)), d) == True{} : Bool}:
  (+l_dst, m2_dst) = m_dst
  (+t_dst, +e_dst) = m2_dst
  (+l_src, m2_src) = m_src
  (+t_src, +e_src) = m2_src
  %e_dst : {D.ok(Pair.fst(D.Bytes, D.Bytes, B.append(_, src, s, n)), d) == True{} : Bool}
  %e_src : {D.ok(Pair.fst(D.Bytes, D.Bytes, B.append(C.BT(l_dst, t_dst), _, s, n)), d) == True{} : Bool}
  +hd_t = C.tr(x => {D.ok(x, d) == True{} : Bool}, dst, l_dst, t_dst, e_dst, hd)
  +hc_t = C.tr(x => {Nat.is_le(Nat.add(D.size(x), U32.to_nat(n)), D.cap(x)) == True{} : Bool}, dst, l_dst, t_dst, e_dst, hc)
  X.append_ok_t(l_dst, t_dst, l_src, t_src, d, s, n, hd_t, hc_t)

def L.append_ok(dst, src, d, s, n, hd, hc):
  append_ok.go(dst, src, d, s, n, hd, hc, C.bmirror(dst), C.bmirror(src))

def append_pair.go(-dst: D.Bytes, -src: D.Bytes, +s: U32, +n: U32, m_dst: C.BMirror(dst), m_src: C.BMirror(src)) ->
  {B.append(dst, src, s, n) == (Pair.fst(D.Bytes, D.Bytes, B.append(dst, src, s, n)), src) : D.Bytes & D.Bytes}:
  (+l_dst, m2_dst) = m_dst
  (+t_dst, +e_dst) = m2_dst
  (+l_src, m2_src) = m_src
  (+t_src, +e_src) = m2_src
  %e_dst : {B.append(_, src, s, n) == (Pair.fst(D.Bytes, D.Bytes, B.append(_, src, s, n)), src) : D.Bytes & D.Bytes}
  %e_src : {B.append(C.BT(l_dst, t_dst), _, s, n) == (Pair.fst(D.Bytes, D.Bytes, B.append(C.BT(l_dst, t_dst), _, s, n)), _) : D.Bytes & D.Bytes}
  X.append_pair_t(l_dst, t_dst, l_src, t_src, s, n)

def L.append_pair(dst, src, s, n):
  append_pair.go(dst, src, s, n, C.bmirror(dst), C.bmirror(src))

def len_view.go(-b: D.Bytes, m_b: C.BMirror(b)) ->
  {U32.to_nat(Pair.snd(D.Bytes, U32, B.len(b))) == D.size(b) : Nat}:
  (+l_b, m2_b) = m_b
  (+t_b, +e_b) = m2_b
  %e_b : {U32.to_nat(Pair.snd(D.Bytes, U32, B.len(_))) == D.size(_) : Nat}
  {==}

def L.len_view(b):
  len_view.go(b, C.bmirror(b))

def len_pair.go(-b: D.Bytes, m_b: C.BMirror(b)) ->
  {B.len(b) == (b, Pair.snd(D.Bytes, U32, B.len(b))) : D.Bytes & U32}:
  (+l_b, m2_b) = m_b
  (+t_b, +e_b) = m2_b
  %e_b : {B.len(_) == (_, Pair.snd(D.Bytes, U32, B.len(_))) : D.Bytes & U32}
  {==}

def L.len_pair(b):
  len_pair.go(b, C.bmirror(b))

def capacity_view.go(-b: D.Bytes, +d: Nat, h: {D.ok(b, d) == True{} : Bool}, m_b: C.BMirror(b)) ->
  {U32.to_nat(Pair.snd(D.Bytes, U32, B.capacity(b))) == D.cap(b) : Nat}:
  (+l_b, m2_b) = m_b
  (+t_b, +e_b) = m2_b
  %e_b : {U32.to_nat(Pair.snd(D.Bytes, U32, B.capacity(_))) == D.cap(_) : Nat}
  +h_t = C.tr(x => {D.ok(x, d) == True{} : Bool}, b, l_b, t_b, e_b, h)
  O.capacity_view_t(l_b, t_b, d, h_t)

def L.capacity_view(b, d, h):
  capacity_view.go(b, d, h, C.bmirror(b))

def capacity_pair.go(-b: D.Bytes, m_b: C.BMirror(b)) ->
  {B.capacity(b) == (b, Pair.snd(D.Bytes, U32, B.capacity(b))) : D.Bytes & U32}:
  (+l_b, m2_b) = m_b
  (+t_b, +e_b) = m2_b
  %e_b : {B.capacity(_) == (_, Pair.snd(D.Bytes, U32, B.capacity(_))) : D.Bytes & U32}
  O.capacity_pair_t(l_b, t_b)

def L.capacity_pair(b):
  capacity_pair.go(b, C.bmirror(b))

def truncate_view.go(-b: D.Bytes, +n: U32, h: {Nat.is_le(U32.to_nat(n), D.size(b)) == True{} : Bool}, m_b: C.BMirror(b)) ->
  {D.view(B.truncate(b, n)) == List.take(&2, U32, D.view(b), U32.to_nat(n)) : List<&2, U32>}:
  (+l_b, m2_b) = m_b
  (+t_b, +e_b) = m2_b
  %e_b : {D.view(B.truncate(_, n)) == List.take(&2, U32, D.view(_), U32.to_nat(n)) : List<&2, U32>}
  +h_t = C.tr(x => {Nat.is_le(U32.to_nat(n), D.size(x)) == True{} : Bool}, b, l_b, t_b, e_b, h)
  O.truncate_view_t(l_b, t_b, n, h_t)

def L.truncate_view(b, n, h):
  truncate_view.go(b, n, h, C.bmirror(b))

def truncate_ok.go(-b: D.Bytes, +d: Nat, +n: U32, h: {D.ok(b, d) == True{} : Bool}, hn: {Nat.is_le(U32.to_nat(n), D.size(b)) == True{} : Bool}, m_b: C.BMirror(b)) ->
  {D.ok(B.truncate(b, n), d) == True{} : Bool}:
  (+l_b, m2_b) = m_b
  (+t_b, +e_b) = m2_b
  %e_b : {D.ok(B.truncate(_, n), d) == True{} : Bool}
  +h_t = C.tr(x => {D.ok(x, d) == True{} : Bool}, b, l_b, t_b, e_b, h)
  +hn_t = C.tr(x => {Nat.is_le(U32.to_nat(n), D.size(x)) == True{} : Bool}, b, l_b, t_b, e_b, hn)
  O.truncate_ok_t(l_b, t_b, d, n, h_t, hn_t)

def L.truncate_ok(b, d, n, h, hn):
  truncate_ok.go(b, d, n, h, hn, C.bmirror(b))

def shift_view.go(-b: D.Bytes, +d: Nat, +k: U32, h: {D.ok(b, d) == True{} : Bool}, hk: {Nat.is_le(U32.to_nat(k), D.size(b)) == True{} : Bool}, m_b: C.BMirror(b)) ->
  {D.view(B.shift(b, k)) == List.drop(&2, U32, D.view(b), U32.to_nat(k)) : List<&2, U32>}:
  (+l_b, m2_b) = m_b
  (+t_b, +e_b) = m2_b
  %e_b : {D.view(B.shift(_, k)) == List.drop(&2, U32, D.view(_), U32.to_nat(k)) : List<&2, U32>}
  +h_t = C.tr(x => {D.ok(x, d) == True{} : Bool}, b, l_b, t_b, e_b, h)
  +hk_t = C.tr(x => {Nat.is_le(U32.to_nat(k), D.size(x)) == True{} : Bool}, b, l_b, t_b, e_b, hk)
  H.shift_view_t(l_b, t_b, d, k, h_t, hk_t)

def L.shift_view(b, d, k, h, hk):
  shift_view.go(b, d, k, h, hk, C.bmirror(b))

def shift_ok.go(-b: D.Bytes, +d: Nat, +k: U32, h: {D.ok(b, d) == True{} : Bool}, hk: {Nat.is_le(U32.to_nat(k), D.size(b)) == True{} : Bool}, m_b: C.BMirror(b)) ->
  {D.ok(B.shift(b, k), d) == True{} : Bool}:
  (+l_b, m2_b) = m_b
  (+t_b, +e_b) = m2_b
  %e_b : {D.ok(B.shift(_, k), d) == True{} : Bool}
  +h_t = C.tr(x => {D.ok(x, d) == True{} : Bool}, b, l_b, t_b, e_b, h)
  +hk_t = C.tr(x => {Nat.is_le(U32.to_nat(k), D.size(x)) == True{} : Bool}, b, l_b, t_b, e_b, hk)
  H.shift_ok_t(l_b, t_b, d, k, h_t, hk_t)

def L.shift_ok(b, d, k, h, hk):
  shift_ok.go(b, d, k, h, hk, C.bmirror(b))

def to_list_view.go(-b: D.Bytes, +d: Nat, +s: U32, +n: U32, h: {D.ok(b, d) == True{} : Bool}, hs: {Nat.is_le(Nat.add(U32.to_nat(s), U32.to_nat(n)), D.size(b)) == True{} : Bool}, m_b: C.BMirror(b)) ->
  {Pair.snd(D.Bytes, List<&2, U32>, B.to_list(b, s, n)) == D.slice(D.view(b), U32.to_nat(s), U32.to_nat(n)) : List<&2, U32>}:
  (+l_b, m2_b) = m_b
  (+t_b, +e_b) = m2_b
  %e_b : {Pair.snd(D.Bytes, List<&2, U32>, B.to_list(_, s, n)) == D.slice(D.view(_), U32.to_nat(s), U32.to_nat(n)) : List<&2, U32>}
  +h_t = C.tr(x => {D.ok(x, d) == True{} : Bool}, b, l_b, t_b, e_b, h)
  +hs_t = C.tr(x => {Nat.is_le(Nat.add(U32.to_nat(s), U32.to_nat(n)), D.size(x)) == True{} : Bool}, b, l_b, t_b, e_b, hs)
  S.to_list_view_t(l_b, t_b, d, s, n, h_t, hs_t)

def L.to_list_view(b, d, s, n, h, hs):
  to_list_view.go(b, d, s, n, h, hs, C.bmirror(b))

def to_list_pair.go(-b: D.Bytes, +s: U32, +n: U32, m_b: C.BMirror(b)) ->
  {B.to_list(b, s, n) == (b, Pair.snd(D.Bytes, List<&2, U32>, B.to_list(b, s, n))) : D.Bytes & List<&2, U32>}:
  (+l_b, m2_b) = m_b
  (+t_b, +e_b) = m2_b
  %e_b : {B.to_list(_, s, n) == (_, Pair.snd(D.Bytes, List<&2, U32>, B.to_list(_, s, n))) : D.Bytes & List<&2, U32>}
  S.to_list_pair_t(l_b, t_b, s, n)

def L.to_list_pair(b, s, n):
  to_list_pair.go(b, s, n, C.bmirror(b))

def same1_view.go(-b: D.Bytes, +d: Nat, +i: U32, +j: U32, +n: U32, h: {D.ok(b, d) == True{} : Bool}, hi: {Nat.is_le(Nat.add(U32.to_nat(i), U32.to_nat(n)), D.size(b)) == True{} : Bool}, hj: {Nat.is_le(Nat.add(U32.to_nat(j), U32.to_nat(n)), D.size(b)) == True{} : Bool}, m_b: C.BMirror(b)) ->
  {Pair.snd(D.Bytes, Bool, B.same1(b, i, j, n)) == D.list_eq(D.slice(D.view(b), U32.to_nat(i), U32.to_nat(n)), D.slice(D.view(b), U32.to_nat(j), U32.to_nat(n))) : Bool}:
  (+l_b, m2_b) = m_b
  (+t_b, +e_b) = m2_b
  %e_b : {Pair.snd(D.Bytes, Bool, B.same1(_, i, j, n)) == D.list_eq(D.slice(D.view(_), U32.to_nat(i), U32.to_nat(n)), D.slice(D.view(_), U32.to_nat(j), U32.to_nat(n))) : Bool}
  +h_t = C.tr(x => {D.ok(x, d) == True{} : Bool}, b, l_b, t_b, e_b, h)
  +hi_t = C.tr(x => {Nat.is_le(Nat.add(U32.to_nat(i), U32.to_nat(n)), D.size(x)) == True{} : Bool}, b, l_b, t_b, e_b, hi)
  +hj_t = C.tr(x => {Nat.is_le(Nat.add(U32.to_nat(j), U32.to_nat(n)), D.size(x)) == True{} : Bool}, b, l_b, t_b, e_b, hj)
  S.same1_view_t(l_b, t_b, d, i, j, n, h_t, hi_t, hj_t)

def L.same1_view(b, d, i, j, n, h, hi, hj):
  same1_view.go(b, d, i, j, n, h, hi, hj, C.bmirror(b))

def same1_pair.go(-b: D.Bytes, +i: U32, +j: U32, +n: U32, m_b: C.BMirror(b)) ->
  {B.same1(b, i, j, n) == (b, Pair.snd(D.Bytes, Bool, B.same1(b, i, j, n))) : D.Bytes & Bool}:
  (+l_b, m2_b) = m_b
  (+t_b, +e_b) = m2_b
  %e_b : {B.same1(_, i, j, n) == (_, Pair.snd(D.Bytes, Bool, B.same1(_, i, j, n))) : D.Bytes & Bool}
  S.same1_pair_t(l_b, t_b, i, j, n)

def L.same1_pair(b, i, j, n):
  same1_pair.go(b, i, j, n, C.bmirror(b))


# Making and lists (no Bytes parameter)
# =====================================

def L.empty_view(d):
  G.empty_view(d)

def L.empty_ok(d, hd):
  G.empty_ok(d, hd)

def L.of_list_view(d, xs, hd, hn, hb):
  G.of_list_view(d, xs, hd, hn, hb)

def L.of_list_ok(d, xs, hd, hn):
  G.of_list_ok(d, xs, hd, hn)

# Facts about the search and comparison definitions
# =================================================

def L.first_range(xs, from, to, c, hft, ht):
  Q.first_range(xs, from, to, c, hft, ht)

def L.first_hit(xs, from, to, c, hft, ht, hlt):
  Q.first_hit(xs, from, to, c, hft, ht, hlt)

def L.first_miss(xs, from, to, c, k, hk1, hk2):
  Q.first_miss(xs, from, to, c, k, hk1, hk2)

def L.first2_range(xs, from, to, c1, c2, hft, ht):
  Q.first2_range(xs, from, to, c1, c2, hft, ht)

def L.first2_hit(xs, from, to, c1, c2, hft, ht, hlt):
  Q.first2_hit(xs, from, to, c1, c2, hft, ht, hlt)

def L.first2_miss(xs, from, to, c1, c2, k, hk1, hk2):
  Q.first2_miss(xs, from, to, c1, c2, k, hk1, hk2)

def L.list_eq_true(xs, ys, h):
  Q.list_eq_true(xs, ys, h)

def L.list_eq_refl(xs):
  Q.list_eq_refl(xs)
