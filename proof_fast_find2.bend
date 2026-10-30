import Base
import ./defs.bend as D
import ./bytes.bend as B
import ./fast.bend as FA
import ./proof_seq.bend as Q
import ./proof_core.bend as C
import ./proof_find.bend as F
import ./proof_append.bend as X
import ./proof_shift.bend as H
import ./proof_fast_word.bend as FW
import ./proof_fast_find.bend as FF
import lawful-words@0.1.0.0/defs.bend as W
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-arrays@0.1.0.0/proof_tree.bend as P
import lawful-arrays@0.1.0.0/defs.bend as A

# fast.bend's find2 on the mirror, the same way as find (proof_fast_find.bend,
# whose word and list lemmas are reused): the mask is the or of two flag
# words, its place the min of their places, and the spec run_len2/first2.

# Whether the head of a list is c1 or c2.
def hd2(xs: List<&2, U32>, +c1: U32, +c2: U32) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{+x, t}:
      U32.is_eq(x, c1) || U32.is_eq(x, c2)

def FG2(n: Nat, z: Bool, +wi: U32, +m: U32, +r1: U32, +r2: U32, +t: P.Tree<U32>) -> U32:
  match n z:
    case 0n _:
      4294967295
    case 1n+k True{}:
      +m2 = (FA.zb((C.WD(t, (wi + 1 : U32)) .^. r1 : U32)) .|. FA.zb((C.WD(t, (wi + 1 : U32)) .^. r2 : U32)) : U32)
      FG2(k, U32.is_zero(m2), (wi + 1 : U32), m2, r1, r2, t)
    case 1n+k False{}:
      ((wi << 2n : U32) + FA.bidx(m) : U32)

law fg2_eq:
  for +n: Nat
  for +z: Bool
  for +wi: U32
  for +m: U32
  for +r1: U32
  for +r2: U32
  for +t: P.Tree<U32>
  {FA.find2.go(n, z, Array.get(U32, P.fromT(U32, t), (wi + 1 : U32)), wi, m, r1, r2) == (P.fromT(U32, t), FG2(n, z, wi, m, r1, r2, t)) : Array<U32> & U32}

def fg2_eq(n, z, wi, m, r1, r2, t):
  match n z:
    case 0n _:
      %Equal.sym(Array<U32> & U32, Array.get(U32, P.fromT(U32, t), (wi + 1 : U32)), (P.fromT(U32, t), C.WD(t, (wi + 1 : U32))), P.get_pair_t(U32, t, (wi + 1 : U32))) :
        {FA.find2.go(0n, z, _, wi, m, r1, r2) == (P.fromT(U32, t), FG2(0n, z, wi, m, r1, r2, t)) : Array<U32> & U32}
      {==}
    case 1n+k True{}:
      +m2 = (FA.zb((C.WD(t, (wi + 1 : U32)) .^. r1 : U32)) .|. FA.zb((C.WD(t, (wi + 1 : U32)) .^. r2 : U32)) : U32)
      %Equal.sym(Array<U32> & U32, Array.get(U32, P.fromT(U32, t), (wi + 1 : U32)), (P.fromT(U32, t), C.WD(t, (wi + 1 : U32))), P.get_pair_t(U32, t, (wi + 1 : U32))) :
        {FA.find2.go(1n+k, True{}, _, wi, m, r1, r2) == (P.fromT(U32, t), FG2(1n+k, True{}, wi, m, r1, r2, t)) : Array<U32> & U32}
      %F.add11(wi) :
        {FA.find2.go(k, U32.is_zero(m2), Array.get(U32, P.fromT(U32, t), _), (wi + 1 : U32), m2, r1, r2) == (P.fromT(U32, t), FG2(k, U32.is_zero(m2), (wi + 1 : U32), m2, r1, r2, t)) : Array<U32> & U32}
      fg2_eq(k, U32.is_zero(m2), (wi + 1 : U32), m2, r1, r2, t)
    case 1n+k False{}:
      %Equal.sym(Array<U32> & U32, Array.get(U32, P.fromT(U32, t), (wi + 1 : U32)), (P.fromT(U32, t), C.WD(t, (wi + 1 : U32))), P.get_pair_t(U32, t, (wi + 1 : U32))) :
        {FA.find2.go(1n+k, False{}, _, wi, m, r1, r2) == (P.fromT(U32, t), FG2(1n+k, False{}, wi, m, r1, r2, t)) : Array<U32> & U32}
      {==}

def M02(+t: P.Tree<U32>, +from: U32, +r1: U32, +r2: U32) -> U32:
  (FA.zb(((C.WD(t, (from >> 2n : U32)) .^. r1 : U32) .|. U32.not(FA.low(from)) : U32)) .|. FA.zb(((C.WD(t, (from >> 2n : U32)) .^. r2 : U32) .|. U32.not(FA.low(from)) : U32)) : U32)

law fast2_eq:
  for +len: U32
  for +t: P.Tree<U32>
  for +from: U32
  for +to: U32
  for +c1: U32
  for +c2: U32
  {FA.find2(C.BT(len, t), from, to, c1, c2) == (C.BT(len, t), U32.min(FG2(FA.words(from, to), U32.is_zero(M02(t, from, FA.rep(c1), FA.rep(c2))), (from >> 2n : U32), M02(t, from, FA.rep(c1), FA.rep(c2)), FA.rep(c1), FA.rep(c2), t), to)) : D.Bytes & U32}

def fast2_eq(len, t, from, to, c1, c2):
  +k = (from >> 2n : U32)
  +r1 = FA.rep(c1)
  +r2 = FA.rep(c2)
  +n = FA.words(from, to)
  %Equal.sym(Array<U32> & U32, Array.get(U32, P.fromT(U32, t), k), (P.fromT(U32, t), C.WD(t, k)), P.get_pair_t(U32, t, k)) :
    {FA.find.k(len, FA.find.fin(to, FA.find2.start(n, _, from, r1, r2))) == (C.BT(len, t), U32.min(FG2(n, U32.is_zero(M02(t, from, r1, r2)), k, M02(t, from, r1, r2), r1, r2, t), to)) : D.Bytes & U32}
  %Equal.sym(Array<U32> & U32, FA.find2.go(n, U32.is_zero(M02(t, from, r1, r2)), Array.get(U32, P.fromT(U32, t), (k + 1 : U32)), k, M02(t, from, r1, r2), r1, r2),
    (P.fromT(U32, t), FG2(n, U32.is_zero(M02(t, from, r1, r2)), k, M02(t, from, r1, r2), r1, r2, t)), fg2_eq(n, U32.is_zero(M02(t, from, r1, r2)), k, M02(t, from, r1, r2), r1, r2, t)) :
    {FA.find.k(len, FA.find.fin(to, _)) == (C.BT(len, t), U32.min(FG2(n, U32.is_zero(M02(t, from, r1, r2)), k, M02(t, from, r1, r2), r1, r2, t), to)) : D.Bytes & U32}
  {==}

# Two runs and their min
# ======================

law min_le_l:
  for +a: Nat
  for +b: Nat
  {Nat.is_le(Nat.min(a, b), a) == True{} : Bool}

def min_le_l(a, b):
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      min_le_l(p, q)

law min_le4:
  for +v1: U32
  for +v2: U32
  {Nat.is_le(Nat.min(FW.P0(v1), FW.P0(v2)), 4n) == True{} : Bool}

def min_le4(v1, v2):
  N.le_trans(Nat.min(FW.P0(v1), FW.P0(v2)), FW.P0(v1), 4n, min_le_l(FW.P0(v1), FW.P0(v2)), FF.run_le(C.L4(v1), 0, FF.hd_eq(C.L4(v1), 0), {==}))

law min_add:
  for +o: Nat
  for +a: Nat
  for +b: Nat
  {Nat.min(Nat.add(o, a), Nat.add(o, b)) == Nat.add(o, Nat.min(a, b)) : Nat}

def min_add(o, a, b):
  match o:
    case 0n:
      {==}
    case 1n+p:
      %min_add(p, a, b) : {1n+Nat.min(Nat.add(p, a), Nat.add(p, b)) == 1n+_ : Nat}
      {==}

# The first c1 or c2 is the earlier of the first c1 and the first c2.
law min_run:
  for +xs: List<&2, U32>
  for +c1: U32
  for +c2: U32
  for +b1: Bool
  for +b2: Bool
  for +hb1: {FF.hd_eq(xs, c1) == b1 : Bool}
  for +hb2: {FF.hd_eq(xs, c2) == b2 : Bool}
  {Nat.min(D.run_len(xs, c1), D.run_len(xs, c2)) == D.run_len2(xs, c1, c2) : Nat}

def min_run(xs, c1, c2, b1, b2, hb1, hb2):
  match xs b1 b2:
    case Nil{} _ _:
      {==}
    case Con{x, t} True{} _:
      %Equal.sym(Bool, FF.hd_eq(x <> t, c1), True{}, hb1) :
        {Nat.min(Bool.pick(Nat, _, 0n, Nat.add(1n, D.run_len(t, c1))), Bool.pick(Nat, U32.is_eq(x, c2), 0n, Nat.add(1n, D.run_len(t, c2)))) == Bool.pick(Nat, Bool.or(_, U32.is_eq(x, c2)), 0n, Nat.add(1n, D.run_len2(t, c1, c2))) : Nat}
      {==}
    case Con{x, t} False{} True{}:
      %Equal.sym(Bool, FF.hd_eq(x <> t, c1), False{}, hb1) :
        {Nat.min(Bool.pick(Nat, _, 0n, Nat.add(1n, D.run_len(t, c1))), Bool.pick(Nat, U32.is_eq(x, c2), 0n, Nat.add(1n, D.run_len(t, c2)))) == Bool.pick(Nat, Bool.or(_, U32.is_eq(x, c2)), 0n, Nat.add(1n, D.run_len2(t, c1, c2))) : Nat}
      %Equal.sym(Bool, FF.hd_eq(x <> t, c2), True{}, hb2) :
        {Nat.min(1n+D.run_len(t, c1), Bool.pick(Nat, _, 0n, Nat.add(1n, D.run_len(t, c2)))) == Bool.pick(Nat, Bool.or(False{}, _), 0n, Nat.add(1n, D.run_len2(t, c1, c2))) : Nat}
      {==}
    case Con{x, t} False{} False{}:
      %Equal.sym(Bool, FF.hd_eq(x <> t, c1), False{}, hb1) :
        {Nat.min(Bool.pick(Nat, _, 0n, Nat.add(1n, D.run_len(t, c1))), Bool.pick(Nat, U32.is_eq(x, c2), 0n, Nat.add(1n, D.run_len(t, c2)))) == Bool.pick(Nat, Bool.or(_, U32.is_eq(x, c2)), 0n, Nat.add(1n, D.run_len2(t, c1, c2))) : Nat}
      %Equal.sym(Bool, FF.hd_eq(x <> t, c2), False{}, hb2) :
        {Nat.min(1n+D.run_len(t, c1), Bool.pick(Nat, _, 0n, Nat.add(1n, D.run_len(t, c2)))) == Bool.pick(Nat, Bool.or(False{}, _), 0n, Nat.add(1n, D.run_len2(t, c1, c2))) : Nat}
      %min_run(t, c1, c2, FF.hd_eq(t, c1), FF.hd_eq(t, c2), {==}, {==}) : {1n+Nat.min(D.run_len(t, c1), D.run_len(t, c2)) == 1n+_ : Nat}
      {==}

# The first word of a search, for two values.
law p0_low2:
  for +w: U32
  for +c1: U32
  for +c2: U32
  for +i: U32
  for +hc1: {U32.is_lt(c1, 256) == True{} : Bool}
  for +hc2: {U32.is_lt(c2, 256) == True{} : Bool}
  {Nat.min(FW.P0(U32.or(U32.xor(w, FA.rep(c1)), U32.not(FA.low(i)))), FW.P0(U32.or(U32.xor(w, FA.rep(c2)), U32.not(FA.low(i))))) == Nat.add(U32.to_nat((i .&. 3 : U32)), D.run_len2(List.drop(&2, U32, C.L4(w), U32.to_nat((i .&. 3 : U32))), c1, c2)) : Nat}

def p0_low2(w, c1, c2, i, hc1, hc2):
  +o = U32.to_nat((i .&. 3 : U32))
  +ys = List.drop(&2, U32, C.L4(w), o)
  %Equal.sym(Nat, FW.P0(U32.or(U32.xor(w, FA.rep(c1)), U32.not(FA.low(i)))), Nat.add(o, D.run_len(ys, c1)), FW.p0_low(w, c1, i, hc1)) :
    {Nat.min(_, FW.P0(U32.or(U32.xor(w, FA.rep(c2)), U32.not(FA.low(i))))) == Nat.add(o, D.run_len2(ys, c1, c2)) : Nat}
  %Equal.sym(Nat, FW.P0(U32.or(U32.xor(w, FA.rep(c2)), U32.not(FA.low(i)))), Nat.add(o, D.run_len(ys, c2)), FW.p0_low(w, c2, i, hc2)) :
    {Nat.min(Nat.add(o, D.run_len(ys, c1)), _) == Nat.add(o, D.run_len2(ys, c1, c2)) : Nat}
  %Equal.sym(Nat, Nat.min(Nat.add(o, D.run_len(ys, c1)), Nat.add(o, D.run_len(ys, c2))), Nat.add(o, Nat.min(D.run_len(ys, c1), D.run_len(ys, c2))), min_add(o, D.run_len(ys, c1), D.run_len(ys, c2))) :
    {_ == Nat.add(o, D.run_len2(ys, c1, c2)) : Nat}
  %Equal.sym(Nat, Nat.min(D.run_len(ys, c1), D.run_len(ys, c2)), D.run_len2(ys, c1, c2), min_run(ys, c1, c2, FF.hd_eq(ys, c1), FF.hd_eq(ys, c2), {==}, {==})) :
    {Nat.add(o, _) == Nat.add(o, D.run_len2(ys, c1, c2)) : Nat}
  {==}

# The next word starts a fresh search.
law hv02:
  for +t: P.Tree<U32>
  for +wi: U32
  for +c1: U32
  for +c2: U32
  for +hc1: {U32.is_lt(c1, 256) == True{} : Bool}
  for +hc2: {U32.is_lt(c2, 256) == True{} : Bool}
  {Nat.min(FW.P0(U32.xor(C.WD(t, wi), FA.rep(c1))), FW.P0(U32.xor(C.WD(t, wi), FA.rep(c2)))) == Nat.add(0n, D.run_len2(FF.AW(t, wi, 0n), c1, c2)) : Nat}

def hv02(t, wi, c1, c2, hc1, hc2):
  +ws = C.L4(C.WD(t, wi))
  %Equal.sym(List<&2, U32>, List.drop(&2, U32, ws, 0n), ws, X.drop_zero(ws)) :
    {Nat.min(FW.P0(U32.xor(C.WD(t, wi), FA.rep(c1))), FW.P0(U32.xor(C.WD(t, wi), FA.rep(c2)))) == Nat.add(0n, D.run_len2(_, c1, c2)) : Nat}
  %Equal.sym(Nat, FW.P0(U32.xor(C.WD(t, wi), FA.rep(c1))), D.run_len(ws, c1), FW.p0_xor(C.WD(t, wi), c1, hc1)) :
    {Nat.min(_, FW.P0(U32.xor(C.WD(t, wi), FA.rep(c2)))) == D.run_len2(ws, c1, c2) : Nat}
  %Equal.sym(Nat, FW.P0(U32.xor(C.WD(t, wi), FA.rep(c2))), D.run_len(ws, c2), FW.p0_xor(C.WD(t, wi), c2, hc2)) :
    {Nat.min(D.run_len(ws, c1), _) == D.run_len2(ws, c1, c2) : Nat}
  min_run(ws, c1, c2, FF.hd_eq(ws, c1), FF.hd_eq(ws, c2), {==}, {==})

# The word loop (from proof_fast_find.bend, for two values)
# =========================================================

law run_hit2:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +n: Nat
  for +c1: U32
  for +c2: U32
  for +b: Bool
  for +hb: {hd2(xs, c1, c2) == b : Bool}
  for +h: {Nat.is_lt(D.run_len2(xs, c1, c2), List.length(&2, U32, xs)) == True{} : Bool}
  {D.run_len2(List.take(&2, U32, List.append(&2, U32, xs, ys), n), c1, c2) == Nat.min(D.run_len2(xs, c1, c2), n) : Nat}

def run_hit2(xs, ys, n, c1, c2, b, hb, h):
  match xs n b:
    case Nil{} _ _:
      Empty.absurd({D.run_len2(List.take(&2, U32, ys, n), c1, c2) == Nat.min(0n, n) : Nat}, AB.lt_zero_absurd(0n, h))
    case Con{x, t} 0n True{}:
      %Equal.sym(Bool, hd2(x <> t, c1, c2), True{}, hb) : {0n == Nat.min(Bool.pick(Nat, _, 0n, Nat.add(1n, D.run_len2(t, c1, c2))), 0n) : Nat}
      {==}
    case Con{x, t} 0n False{}:
      %Equal.sym(Bool, hd2(x <> t, c1, c2), False{}, hb) : {0n == Nat.min(Bool.pick(Nat, _, 0n, Nat.add(1n, D.run_len2(t, c1, c2))), 0n) : Nat}
      {==}
    case Con{x, t} 1n+p True{}:
      %Equal.sym(Bool, hd2(x <> t, c1, c2), True{}, hb) :
        {Bool.pick(Nat, _, 0n, Nat.add(1n, D.run_len2(List.take(&2, U32, List.append(&2, U32, t, ys), p), c1, c2))) == Nat.min(Bool.pick(Nat, _, 0n, Nat.add(1n, D.run_len2(t, c1, c2))), 1n+p) : Nat}
      {==}
    case Con{x, t} 1n+p False{}:
      %Equal.sym(Bool, hd2(x <> t, c1, c2), False{}, hb) :
        {Bool.pick(Nat, _, 0n, Nat.add(1n, D.run_len2(List.take(&2, U32, List.append(&2, U32, t, ys), p), c1, c2))) == Nat.min(Bool.pick(Nat, _, 0n, Nat.add(1n, D.run_len2(t, c1, c2))), 1n+p) : Nat}
      +h2 = AB.subst(Bool, y => {Nat.is_lt(Bool.pick(Nat, y, 0n, Nat.add(1n, D.run_len2(t, c1, c2))), 1n+List.length(&2, U32, t)) == True{} : Bool},
        hd2(x <> t, c1, c2), False{}, hb, h)
      %run_hit2(t, ys, p, c1, c2, hd2(t, c1, c2), {==}, h2) :
        {1n+D.run_len2(List.take(&2, U32, List.append(&2, U32, t, ys), p), c1, c2) == 1n+_ : Nat}
      {==}

law run_skip2:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +n: Nat
  for +c1: U32
  for +c2: U32
  for +b: Bool
  for +hb: {hd2(xs, c1, c2) == b : Bool}
  for +h: {D.run_len2(xs, c1, c2) == List.length(&2, U32, xs) : Nat}
  for +hn: {Nat.is_le(List.length(&2, U32, xs), n) == True{} : Bool}
  {D.run_len2(List.take(&2, U32, List.append(&2, U32, xs, ys), n), c1, c2) == Nat.add(List.length(&2, U32, xs), D.run_len2(List.take(&2, U32, ys, Nat.sub(n, List.length(&2, U32, xs))), c1, c2)) : Nat}

def run_skip2(xs, ys, n, c1, c2, b, hb, h, hn):
  match xs n b:
    case Nil{} _ _:
      %Equal.sym(Nat, Nat.sub(n, 0n), n, N.sub_zero(n)) :
        {D.run_len2(List.take(&2, U32, ys, n), c1, c2) == D.run_len2(List.take(&2, U32, ys, _), c1, c2) : Nat}
      {==}
    case Con{x, t} _ True{}:
      Empty.absurd({D.run_len2(List.take(&2, U32, List.append(&2, U32, x <> t, ys), n), c1, c2) == Nat.add(1n+List.length(&2, U32, t), D.run_len2(List.take(&2, U32, ys, Nat.sub(n, 1n+List.length(&2, U32, t))), c1, c2)) : Nat},
        N.zero_ne_succ(List.length(&2, U32, t), AB.subst(Bool, y => {Bool.pick(Nat, y, 0n, Nat.add(1n, D.run_len2(t, c1, c2))) == 1n+List.length(&2, U32, t) : Nat},
          hd2(x <> t, c1, c2), True{}, hb, h)))
    case Con{x, t} 0n False{}:
      Empty.absurd({0n == Nat.add(1n+List.length(&2, U32, t), D.run_len2(List.take(&2, U32, ys, Nat.sub(0n, 1n+List.length(&2, U32, t))), c1, c2)) : Nat},
        AB.false_ne_true(hn))
    case Con{x, t} 1n+p False{}:
      %Equal.sym(Bool, hd2(x <> t, c1, c2), False{}, hb) :
        {Bool.pick(Nat, _, 0n, Nat.add(1n, D.run_len2(List.take(&2, U32, List.append(&2, U32, t, ys), p), c1, c2))) == 1n+Nat.add(List.length(&2, U32, t), D.run_len2(List.take(&2, U32, ys, Nat.sub(p, List.length(&2, U32, t))), c1, c2)) : Nat}
      +h2 = N.succ_inj(D.run_len2(t, c1, c2), List.length(&2, U32, t),
        AB.subst(Bool, y => {Bool.pick(Nat, y, 0n, Nat.add(1n, D.run_len2(t, c1, c2))) == 1n+List.length(&2, U32, t) : Nat}, hd2(x <> t, c1, c2), False{}, hb, h))
      %run_skip2(t, ys, p, c1, c2, hd2(t, c1, c2), {==}, h2, hn) :
        {1n+D.run_len2(List.take(&2, U32, List.append(&2, U32, t, ys), p), c1, c2) == 1n+_ : Nat}
      {==}

law run_none2:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +n: Nat
  for +c1: U32
  for +c2: U32
  for +b: Bool
  for +hb: {hd2(xs, c1, c2) == b : Bool}
  for +h: {D.run_len2(xs, c1, c2) == List.length(&2, U32, xs) : Nat}
  for +hn: {Nat.is_le(n, List.length(&2, U32, xs)) == True{} : Bool}
  {D.run_len2(List.take(&2, U32, List.append(&2, U32, xs, ys), n), c1, c2) == n : Nat}

def run_none2(xs, ys, n, c1, c2, b, hb, h, hn):
  match xs n b:
    case Nil{} 0n _:
      %Equal.sym(List<&2, U32>, List.take(&2, U32, ys, 0n), Nil{}, Q.take_zero(ys)) : {D.run_len2(_, c1, c2) == 0n : Nat}
      {==}
    case Nil{} 1n+p _:
      Empty.absurd({D.run_len2(List.take(&2, U32, ys, 1n+p), c1, c2) == 1n+p : Nat}, AB.false_ne_true(hn))
    case Con{x, t} 0n _:
      {==}
    case Con{x, t} 1n+p True{}:
      Empty.absurd({D.run_len2(List.take(&2, U32, List.append(&2, U32, x <> t, ys), 1n+p), c1, c2) == 1n+p : Nat},
        N.zero_ne_succ(List.length(&2, U32, t), AB.subst(Bool, y => {Bool.pick(Nat, y, 0n, Nat.add(1n, D.run_len2(t, c1, c2))) == 1n+List.length(&2, U32, t) : Nat},
          hd2(x <> t, c1, c2), True{}, hb, h)))
    case Con{x, t} 1n+p False{}:
      %Equal.sym(Bool, hd2(x <> t, c1, c2), False{}, hb) :
        {Bool.pick(Nat, _, 0n, Nat.add(1n, D.run_len2(List.take(&2, U32, List.append(&2, U32, t, ys), p), c1, c2))) == 1n+p : Nat}
      +h2 = N.succ_inj(D.run_len2(t, c1, c2), List.length(&2, U32, t),
        AB.subst(Bool, y => {Bool.pick(Nat, y, 0n, Nat.add(1n, D.run_len2(t, c1, c2))) == 1n+List.length(&2, U32, t) : Nat}, hd2(x <> t, c1, c2), False{}, hb, h))
      %run_none2(t, ys, p, c1, c2, hd2(t, c1, c2), {==}, h2, hn) : {1n+D.run_len2(List.take(&2, U32, List.append(&2, U32, t, ys), p), c1, c2) == 1n+_ : Nat}
      {==}

law fhit2:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +to: U32
  for +c1: U32
  for +c2: U32
  for +wi: U32
  for +o: Nat
  for +v1: U32
  for +v2: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +ht: {Nat.is_le(U32.to_nat(to), U32.to_nat(len)) == True{} : Bool}
  for +ho: {Nat.is_lt(o, 4n) == True{} : Bool}
  for +hs: {Nat.is_le(FF.SS(wi, o), U32.to_nat(to)) == True{} : Bool}
  for +hk: {Nat.is_lt(U32.to_nat(wi), Nat.pow(2n, d)) == True{} : Bool}
  for +hv: {Nat.min(FW.P0(v1), FW.P0(v2)) == Nat.add(o, D.run_len2(FF.AW(t, wi, o), c1, c2)) : Nat}
  for +hz: {U32.is_zero(U32.or(FA.zb(v1), FA.zb(v2))) == False{} : Bool}
  {U32.to_nat(U32.min(((wi << 2n : U32) + FA.bidx(U32.or(FA.zb(v1), FA.zb(v2))) : U32), to)) == D.first2(FF.UB(t), FF.SS(wi, o), U32.to_nat(to), c1, c2) : Nat}

def fhit2(len, t, d, to, c1, c2, wi, o, v1, v2, h, ht, ho, hs, hk, hv, hz):
  +W = U32.to_nat(wi)
  +T = U32.to_nat(to)
  +r = D.run_len2(FF.AW(t, wi, o), c1, c2)
  +M4 = Nat.mul(4n, Nat.pow(2n, d))
  +hd = C.ok_d(len, t, d, h)
  +hf = C.ok_full(len, t, d, h)
  +hp4 = min_le4(v1, v2)
  +hne = Equal.trans(Bool, Nat.is_eq(Nat.min(FW.P0(v1), FW.P0(v2)), 4n), U32.is_zero(U32.or(FA.zb(v1), FA.zb(v2))), False{}, Equal.sym(Bool, U32.is_zero(U32.or(FA.zb(v1), FA.zb(v2))), Nat.is_eq(Nat.min(FW.P0(v1), FW.P0(v2)), 4n), FW.zb2_none(v1, v2)), hz)
  +hlt = Equal.trans(Bool, Nat.is_lt(Nat.min(FW.P0(v1), FW.P0(v2)), 4n), Nat.is_le(1n+Nat.min(FW.P0(v1), FW.P0(v2)), 4n), True{}, Equal.sym(Bool, Nat.is_le(1n+Nat.min(FW.P0(v1), FW.P0(v2)), 4n), Nat.is_lt(Nat.min(FW.P0(v1), FW.P0(v2)), 4n), N.le_succ_lt(Nat.min(FW.P0(v1), FW.P0(v2)), 4n)),
    N.le_ne(Nat.min(FW.P0(v1), FW.P0(v2)), 4n, hp4, hne))
  +hlt2 = AB.subst(Nat, y => {Nat.is_lt(y, 4n) == True{} : Bool}, Nat.min(FW.P0(v1), FW.P0(v2)), Nat.add(o, r), hv, hlt)
  +eo = N.le_sub_add(o, 4n, N.lt_to_le(o, 4n, ho))
  +hrl0 = FF.lt_cancel(o, r, Nat.sub(4n, o), AB.subst(Nat, y => {Nat.is_lt(Nat.add(o, r), y) == True{} : Bool}, 4n, Nat.add(o, Nat.sub(4n, o)), Equal.sym(Nat, Nat.add(o, Nat.sub(4n, o)), 4n, eo), hlt2))
  +hrl = AB.subst(Nat, y => {Nat.is_lt(r, y) == True{} : Bool}, Nat.sub(4n, o), List.length(&2, U32, FF.AW(t, wi, o)), Equal.sym(Nat, List.length(&2, U32, FF.AW(t, wi, o)), Nat.sub(4n, o), FF.awl(t, wi, o)), hrl0)
  +eb = Equal.trans(Nat, U32.to_nat(FA.bidx(U32.or(FA.zb(v1), FA.zb(v2)))), Nat.min(FW.P0(v1), FW.P0(v2)), Nat.add(o, r), FW.zb2_bidx(v1, v2, hlt), hv)
  +hw4 = FF.wb4(W, Nat.pow(2n, d), hk)
  +esh = FF.shl2(wi, d, hd, N.le_trans(Nat.mul(W, 4n), Nat.add(Nat.mul(W, 4n), 4n), M4, N.le_add_r(Nat.mul(W, 4n), 4n), hw4))
  +b1 = N.le_trans(Nat.add(Nat.mul(W, 4n), Nat.add(o, r)), Nat.add(Nat.mul(W, 4n), 4n), M4,
    N.le_add_mono_l(Nat.mul(W, 4n), Nat.add(o, r), 4n, N.lt_to_le(Nat.add(o, r), 4n, hlt2)), hw4)
  +b2 = AB.subst(Nat, y => {Nat.is_le(Nat.add(y, Nat.add(o, r)), M4) == True{} : Bool}, Nat.mul(W, 4n), U32.to_nat((wi << 2n : U32)), Equal.sym(Nat, U32.to_nat((wi << 2n : U32)), Nat.mul(W, 4n), esh), b1)
  +b3 = AB.subst(Nat, y => {Nat.is_le(Nat.add(U32.to_nat((wi << 2n : U32)), y), M4) == True{} : Bool}, Nat.add(o, r), U32.to_nat(FA.bidx(U32.or(FA.zb(v1), FA.zb(v2)))),
    Equal.sym(Nat, U32.to_nat(FA.bidx(U32.or(FA.zb(v1), FA.zb(v2)))), Nat.add(o, r), eb), b2)
  +ej = C.add_fits((wi << 2n : U32), FA.bidx(U32.or(FA.zb(v1), FA.zb(v2))), d, hd, b3)
  +RHS = D.first2(FF.UB(t), FF.SS(wi, o), T, c1, c2)
  %Equal.sym(Nat, U32.to_nat(U32.min(((wi << 2n : U32) + FA.bidx(U32.or(FA.zb(v1), FA.zb(v2))) : U32), to)), Nat.min(U32.to_nat(((wi << 2n : U32) + FA.bidx(U32.or(FA.zb(v1), FA.zb(v2))) : U32)), T),
    U.to_nat_min(((wi << 2n : U32) + FA.bidx(U32.or(FA.zb(v1), FA.zb(v2))) : U32), to)) :
    {_ == RHS : Nat}
  %Equal.sym(Nat, U32.to_nat(((wi << 2n : U32) + FA.bidx(U32.or(FA.zb(v1), FA.zb(v2))) : U32)), Nat.add(U32.to_nat((wi << 2n : U32)), U32.to_nat(FA.bidx(U32.or(FA.zb(v1), FA.zb(v2))))), ej) :
    {Nat.min(_, T) == RHS : Nat}
  %Equal.sym(Nat, U32.to_nat(FA.bidx(U32.or(FA.zb(v1), FA.zb(v2)))), Nat.add(o, r), eb) :
    {Nat.min(Nat.add(U32.to_nat((wi << 2n : U32)), _), T) == RHS : Nat}
  %Equal.sym(Nat, U32.to_nat((wi << 2n : U32)), Nat.mul(W, 4n), esh) :
    {Nat.min(Nat.add(_, Nat.add(o, r)), T) == RHS : Nat}
  %N.add_assoc(Nat.mul(W, 4n), o, r) :
    {Nat.min(_, T) == RHS : Nat}
  %Equal.sym(Nat, Nat.min(Nat.add(FF.SS(wi, o), r), T), Nat.add(FF.SS(wi, o), Nat.min(r, Nat.sub(T, FF.SS(wi, o)))), FF.min_shift(FF.SS(wi, o), r, T, hs)) :
    {_ == RHS : Nat}
  %Equal.sym(List<&2, U32>, List.drop(&2, U32, FF.UB(t), FF.SS(wi, o)), List.append(&2, U32, FF.AW(t, wi, o), FF.BW(t, wi)), FF.dw(t, d, wi, o, hf, hd, hk, N.lt_to_le(o, 4n, ho))) :
    {Nat.add(FF.SS(wi, o), Nat.min(r, Nat.sub(T, FF.SS(wi, o)))) == Nat.add(FF.SS(wi, o), D.run_len2(List.take(&2, U32, _, Nat.sub(T, FF.SS(wi, o))), c1, c2)) : Nat}
  %Equal.sym(Nat, D.run_len2(List.take(&2, U32, List.append(&2, U32, FF.AW(t, wi, o), FF.BW(t, wi)), Nat.sub(T, FF.SS(wi, o))), c1, c2), Nat.min(r, Nat.sub(T, FF.SS(wi, o))),
    run_hit2(FF.AW(t, wi, o), FF.BW(t, wi), Nat.sub(T, FF.SS(wi, o)), c1, c2, hd2(FF.AW(t, wi, o), c1, c2), {==}, hrl)) :
    {Nat.add(FF.SS(wi, o), Nat.min(r, Nat.sub(T, FF.SS(wi, o)))) == Nat.add(FF.SS(wi, o), _) : Nat}
  {==}

law nohit2:
  for +t: P.Tree<U32>
  for +wi: U32
  for +o: Nat
  for +v1: U32
  for +v2: U32
  for +c1: U32
  for +c2: U32
  for +hv: {Nat.min(FW.P0(v1), FW.P0(v2)) == Nat.add(o, D.run_len2(FF.AW(t, wi, o), c1, c2)) : Nat}
  for +hz: {U32.is_zero(U32.or(FA.zb(v1), FA.zb(v2))) == True{} : Bool}
  {D.run_len2(FF.AW(t, wi, o), c1, c2) == List.length(&2, U32, FF.AW(t, wi, o)) : Nat}

def nohit2(t, wi, o, v1, v2, c1, c2, hv, hz):
  +r = D.run_len2(FF.AW(t, wi, o), c1, c2)
  +e4 = N.eq_sound(Nat.min(FW.P0(v1), FW.P0(v2)), 4n, Equal.trans(Bool, Nat.is_eq(Nat.min(FW.P0(v1), FW.P0(v2)), 4n), U32.is_zero(U32.or(FA.zb(v1), FA.zb(v2))), True{},
    Equal.sym(Bool, U32.is_zero(U32.or(FA.zb(v1), FA.zb(v2))), Nat.is_eq(Nat.min(FW.P0(v1), FW.P0(v2)), 4n), FW.zb2_none(v1, v2)), hz))
  +e5 = Equal.trans(Nat, Nat.add(o, r), Nat.min(FW.P0(v1), FW.P0(v2)), 4n, Equal.sym(Nat, Nat.min(FW.P0(v1), FW.P0(v2)), Nat.add(o, r), hv), e4)
  %Equal.sym(Nat, List.length(&2, U32, FF.AW(t, wi, o)), Nat.sub(4n, o), FF.awl(t, wi, o)) : {r == _ : Nat}
  %e5 : {r == Nat.sub(_, o) : Nat}
  Equal.sym(Nat, Nat.sub(Nat.add(o, r), o), r, N.sub_add_l(o, r))

law fnone2:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +to: U32
  for +c1: U32
  for +c2: U32
  for +wi: U32
  for +o: Nat
  for +v1: U32
  for +v2: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +ht: {Nat.is_le(U32.to_nat(to), U32.to_nat(len)) == True{} : Bool}
  for +ho: {Nat.is_lt(o, 4n) == True{} : Bool}
  for +hs: {Nat.is_le(FF.SS(wi, o), U32.to_nat(to)) == True{} : Bool}
  for +hk: {Nat.is_lt(U32.to_nat(wi), Nat.pow(2n, d)) == True{} : Bool}
  for +hv: {Nat.min(FW.P0(v1), FW.P0(v2)) == Nat.add(o, D.run_len2(FF.AW(t, wi, o), c1, c2)) : Nat}
  for +hz: {U32.is_zero(U32.or(FA.zb(v1), FA.zb(v2))) == True{} : Bool}
  for +he: {Nat.is_le(U32.to_nat(to), Nat.mul(Nat.add(U32.to_nat(wi), 1n), 4n)) == True{} : Bool}
  {U32.to_nat(U32.min(4294967295, to)) == D.first2(FF.UB(t), FF.SS(wi, o), U32.to_nat(to), c1, c2) : Nat}

def fnone2(len, t, d, to, c1, c2, wi, o, v1, v2, h, ht, ho, hs, hk, hv, hz, he):
  +W = U32.to_nat(wi)
  +T = U32.to_nat(to)
  +X = Nat.sub(T, FF.SS(wi, o))
  +hd = C.ok_d(len, t, d, h)
  +hf = C.ok_full(len, t, d, h)
  +a1 = AB.subst(Nat, y => {Nat.is_le(T, y) == True{} : Bool}, Nat.mul(Nat.add(W, 1n), 4n), Nat.add(Nat.mul(W, 4n), 4n), FF.mul4s(W), he)
  +a2 = AB.subst(Nat, y => {Nat.is_le(y, Nat.add(Nat.mul(W, 4n), 4n)) == True{} : Bool}, T, Nat.add(FF.SS(wi, o), X),
    Equal.sym(Nat, Nat.add(FF.SS(wi, o), X), T, N.le_sub_add(FF.SS(wi, o), T, hs)), a1)
  +a3 = AB.subst(Nat, y => {Nat.is_le(y, Nat.add(Nat.mul(W, 4n), 4n)) == True{} : Bool}, Nat.add(Nat.add(Nat.mul(W, 4n), o), X), Nat.add(Nat.mul(W, 4n), Nat.add(o, X)),
    N.add_assoc(Nat.mul(W, 4n), o, X), a2)
  +a4 = N.le_sub_r(o, X, 4n, FF.le_cancel(Nat.mul(W, 4n), Nat.add(o, X), 4n, a3))
  +hn = AB.subst(Nat, y => {Nat.is_le(X, y) == True{} : Bool}, Nat.sub(4n, o), List.length(&2, U32, FF.AW(t, wi, o)),
    Equal.sym(Nat, List.length(&2, U32, FF.AW(t, wi, o)), Nat.sub(4n, o), FF.awl(t, wi, o)), a4)
  +RHS = D.first2(FF.UB(t), FF.SS(wi, o), T, c1, c2)
  %Equal.sym(U32, U32.min(4294967295, to), to, FF.min_top(to, d, hd, N.le_trans(T, U32.to_nat(len), Nat.mul(4n, Nat.pow(2n, d)), ht, C.ok_len(len, t, d, h)))) :
    {U32.to_nat(_) == RHS : Nat}
  %Equal.sym(List<&2, U32>, List.drop(&2, U32, FF.UB(t), FF.SS(wi, o)), List.append(&2, U32, FF.AW(t, wi, o), FF.BW(t, wi)), FF.dw(t, d, wi, o, hf, hd, hk, N.lt_to_le(o, 4n, ho))) :
    {T == Nat.add(FF.SS(wi, o), D.run_len2(List.take(&2, U32, _, X), c1, c2)) : Nat}
  %Equal.sym(Nat, D.run_len2(List.take(&2, U32, List.append(&2, U32, FF.AW(t, wi, o), FF.BW(t, wi)), X), c1, c2), X,
    run_none2(FF.AW(t, wi, o), FF.BW(t, wi), X, c1, c2, hd2(FF.AW(t, wi, o), c1, c2), {==}, nohit2(t, wi, o, v1, v2, c1, c2, hv, hz), hn)) :
    {T == Nat.add(FF.SS(wi, o), _) : Nat}
  Equal.sym(Nat, Nat.add(FF.SS(wi, o), X), T, N.le_sub_add(FF.SS(wi, o), T, hs))

law fskip2:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +to: U32
  for +c1: U32
  for +c2: U32
  for +wi: U32
  for +o: Nat
  for +v1: U32
  for +v2: U32
  for +k: Nat
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +ho: {Nat.is_lt(o, 4n) == True{} : Bool}
  for +hs: {Nat.is_le(FF.SS(wi, o), U32.to_nat(to)) == True{} : Bool}
  for +hk: {Nat.is_lt(U32.to_nat(wi), Nat.pow(2n, d)) == True{} : Bool}
  for +hv: {Nat.min(FW.P0(v1), FW.P0(v2)) == Nat.add(o, D.run_len2(FF.AW(t, wi, o), c1, c2)) : Nat}
  for +hz: {U32.is_zero(U32.or(FA.zb(v1), FA.zb(v2))) == True{} : Bool}
  for +hs1: {Nat.is_le(Nat.mul(Nat.add(U32.to_nat(wi), 1n), 4n), U32.to_nat(to)) == True{} : Bool}
  {D.first2(FF.UB(t), FF.SS(wi, o), U32.to_nat(to), c1, c2) == D.first2(FF.UB(t), Nat.mul(Nat.add(U32.to_nat(wi), 1n), 4n), U32.to_nat(to), c1, c2) : Nat}

def fskip2(len, t, d, to, c1, c2, wi, o, v1, v2, k, h, ho, hs, hk, hv, hz, hs1):
  +W = U32.to_nat(wi)
  +T = U32.to_nat(to)
  +S = FF.SS(wi, o)
  +S1 = Nat.mul(Nat.add(W, 1n), 4n)
  +L = Nat.sub(4n, o)
  +hd = C.ok_d(len, t, d, h)
  +hf = C.ok_full(len, t, d, h)
  +eS = Equal.trans(Nat, Nat.add(S, L), Nat.add(Nat.mul(W, 4n), Nat.add(o, L)), S1, N.add_assoc(Nat.mul(W, 4n), o, L),
    Equal.trans(Nat, Nat.add(Nat.mul(W, 4n), Nat.add(o, L)), Nat.add(Nat.mul(W, 4n), 4n), S1,
      Equal.cong(Nat, Nat, y => Nat.add(Nat.mul(W, 4n), y), Nat.add(o, L), 4n, N.le_sub_add(o, 4n, N.lt_to_le(o, 4n, ho))),
      Equal.sym(Nat, S1, Nat.add(Nat.mul(W, 4n), 4n), FF.mul4s(W))))
  +hl0 = N.le_sub_r(S, L, T, AB.subst(Nat, y => {Nat.is_le(y, T) == True{} : Bool}, S1, Nat.add(S, L), Equal.sym(Nat, Nat.add(S, L), S1, eS), hs1))
  +hn = AB.subst(Nat, y => {Nat.is_le(y, Nat.sub(T, S)) == True{} : Bool}, L, List.length(&2, U32, FF.AW(t, wi, o)),
    Equal.sym(Nat, List.length(&2, U32, FF.AW(t, wi, o)), L, FF.awl(t, wi, o)), hl0)
  +RHS = D.first2(FF.UB(t), S1, T, c1, c2)
  %Equal.sym(List<&2, U32>, List.drop(&2, U32, FF.UB(t), S), List.append(&2, U32, FF.AW(t, wi, o), FF.BW(t, wi)), FF.dw(t, d, wi, o, hf, hd, hk, N.lt_to_le(o, 4n, ho))) :
    {Nat.add(S, D.run_len2(List.take(&2, U32, _, Nat.sub(T, S)), c1, c2)) == RHS : Nat}
  %Equal.sym(Nat, D.run_len2(List.take(&2, U32, List.append(&2, U32, FF.AW(t, wi, o), FF.BW(t, wi)), Nat.sub(T, S)), c1, c2),
    Nat.add(List.length(&2, U32, FF.AW(t, wi, o)), D.run_len2(List.take(&2, U32, FF.BW(t, wi), Nat.sub(Nat.sub(T, S), List.length(&2, U32, FF.AW(t, wi, o)))), c1, c2)),
    run_skip2(FF.AW(t, wi, o), FF.BW(t, wi), Nat.sub(T, S), c1, c2, hd2(FF.AW(t, wi, o), c1, c2), {==}, nohit2(t, wi, o, v1, v2, c1, c2, hv, hz), hn)) :
    {Nat.add(S, _) == RHS : Nat}
  %Equal.sym(Nat, List.length(&2, U32, FF.AW(t, wi, o)), L, FF.awl(t, wi, o)) :
    {Nat.add(S, Nat.add(_, D.run_len2(List.take(&2, U32, FF.BW(t, wi), Nat.sub(Nat.sub(T, S), _)), c1, c2))) == RHS : Nat}
  %Equal.sym(Nat, Nat.sub(Nat.sub(T, S), L), Nat.sub(T, Nat.add(S, L)), FF.sub_sub(T, S, L)) :
    {Nat.add(S, Nat.add(L, D.run_len2(List.take(&2, U32, FF.BW(t, wi), _), c1, c2))) == RHS : Nat}
  %N.add_assoc(S, L, D.run_len2(List.take(&2, U32, FF.BW(t, wi), Nat.sub(T, Nat.add(S, L))), c1, c2)) :
    {_ == RHS : Nat}
  %Equal.sym(Nat, Nat.add(S, L), S1, eS) :
    {Nat.add(_, D.run_len2(List.take(&2, U32, FF.BW(t, wi), Nat.sub(T, _)), c1, c2)) == RHS : Nat}
  {==}

law fi2:
  for +k: Nat
  for +z: Bool
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +to: U32
  for +c1: U32
  for +c2: U32
  for +wi: U32
  for +o: Nat
  for +v1: U32
  for +v2: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +ht: {Nat.is_le(U32.to_nat(to), U32.to_nat(len)) == True{} : Bool}
  for +hc1: {U32.is_lt(c1, 256) == True{} : Bool}
  for +hc2: {U32.is_lt(c2, 256) == True{} : Bool}
  for +ho: {Nat.is_lt(o, 4n) == True{} : Bool}
  for +hs: {Nat.is_le(FF.SS(wi, o), U32.to_nat(to)) == True{} : Bool}
  for +he1: {Nat.is_le(U32.to_nat(to), Nat.mul(Nat.add(U32.to_nat(wi), 1n+k), 4n)) == True{} : Bool}
  for +he2: {Nat.is_lt(Nat.mul(Nat.add(U32.to_nat(wi), k), 4n), U32.to_nat(to)) == True{} : Bool}
  for +hv: {Nat.min(FW.P0(v1), FW.P0(v2)) == Nat.add(o, D.run_len2(FF.AW(t, wi, o), c1, c2)) : Nat}
  for +hz: {U32.is_zero(U32.or(FA.zb(v1), FA.zb(v2))) == z : Bool}
  {U32.to_nat(U32.min(FG2(1n+k, z, wi, U32.or(FA.zb(v1), FA.zb(v2)), FA.rep(c1), FA.rep(c2), t), to)) == D.first2(FF.UB(t), FF.SS(wi, o), U32.to_nat(to), c1, c2) : Nat}

def fi2(k, z, len, t, d, to, c1, c2, wi, o, v1, v2, h, ht, hc1, hc2, ho, hs, he1, he2, hv, hz):
  match k z:
    case 0n False{}:
      fhit2(len, t, d, to, c1, c2, wi, o, v1, v2, h, ht, ho, hs,
        FF.wlt(U32.to_nat(wi), 0n, U32.to_nat(to), U32.to_nat(len), Nat.pow(2n, d), he2, ht, C.ok_len(len, t, d, h)), hv, hz)
    case 1n+q False{}:
      fhit2(len, t, d, to, c1, c2, wi, o, v1, v2, h, ht, ho, hs,
        FF.wlt(U32.to_nat(wi), 1n+q, U32.to_nat(to), U32.to_nat(len), Nat.pow(2n, d), he2, ht, C.ok_len(len, t, d, h)), hv, hz)
    case 0n True{}:
      fnone2(len, t, d, to, c1, c2, wi, o, v1, v2, h, ht, ho, hs,
        FF.wlt(U32.to_nat(wi), 0n, U32.to_nat(to), U32.to_nat(len), Nat.pow(2n, d), he2, ht, C.ok_len(len, t, d, h)), hv, hz, he1)
    case 1n+q True{}:
      +W = U32.to_nat(wi)
      +T = U32.to_nat(to)
      +j1 = (wi + 1 : U32)
      +n1 = U32.xor(C.WD(t, j1), FA.rep(c1))
      +n2 = U32.xor(C.WD(t, j1), FA.rep(c2))
      +S1 = Nat.mul(Nat.add(W, 1n), 4n)
      +hk = FF.wlt(W, 1n+q, T, U32.to_nat(len), Nat.pow(2n, d), he2, ht, C.ok_len(len, t, d, h))
      +ej1 = C.inc_fits(wi, d, C.ok_d(len, t, d, h), N.lt_le_trans(W, Nat.pow(2n, d), Nat.mul(4n, Nat.pow(2n, d)), hk, FF.pow_le4(Nat.pow(2n, d))))
      +hs1 = N.lt_to_le(S1, T, N.le_lt_trans(S1, Nat.mul(Nat.add(W, 1n+q), 4n), T,
        N.le_mul_r(Nat.add(W, 1n), Nat.add(W, 1n+q), 4n, N.le_add_mono_l(W, 1n, 1n+q, N.le_zero_l(q))), he2))
      +ea = Equal.trans(Nat, Nat.add(Nat.mul(U32.to_nat(j1), 4n), 0n), Nat.mul(U32.to_nat(j1), 4n), S1, N.add_zero(Nat.mul(U32.to_nat(j1), 4n)),
        Equal.cong(Nat, Nat, y => Nat.mul(y, 4n), U32.to_nat(j1), Nat.add(W, 1n), ej1))
      +hsi = AB.subst(Nat, y => {Nat.is_le(y, T) == True{} : Bool}, S1, FF.SS(j1, 0n), Equal.sym(Nat, FF.SS(j1, 0n), S1, ea), hs1)
      +e1 = Equal.trans(Nat, Nat.add(U32.to_nat(j1), 1n+q), Nat.add(Nat.add(W, 1n), 1n+q), Nat.add(W, 1n+(1n+q)),
        Equal.cong(Nat, Nat, y => Nat.add(y, 1n+q), U32.to_nat(j1), Nat.add(W, 1n), ej1), N.add_assoc(W, 1n, 1n+q))
      +he1i = AB.subst(Nat, y => {Nat.is_le(T, Nat.mul(y, 4n)) == True{} : Bool}, Nat.add(W, 1n+(1n+q)), Nat.add(U32.to_nat(j1), 1n+q),
        Equal.sym(Nat, Nat.add(U32.to_nat(j1), 1n+q), Nat.add(W, 1n+(1n+q)), e1), he1)
      +e2 = Equal.trans(Nat, Nat.add(U32.to_nat(j1), q), Nat.add(Nat.add(W, 1n), q), Nat.add(W, 1n+q),
        Equal.cong(Nat, Nat, y => Nat.add(y, q), U32.to_nat(j1), Nat.add(W, 1n), ej1), N.add_assoc(W, 1n, q))
      +he2i = AB.subst(Nat, y => {Nat.is_lt(Nat.mul(y, 4n), T) == True{} : Bool}, Nat.add(W, 1n+q), Nat.add(U32.to_nat(j1), q),
        Equal.sym(Nat, Nat.add(U32.to_nat(j1), q), Nat.add(W, 1n+q), e2), he2)
      +ih = fi2(q, U32.is_zero(U32.or(FA.zb(n1), FA.zb(n2))), len, t, d, to, c1, c2, j1, 0n, n1, n2, h, ht, hc1, hc2, {==}, hsi, he1i, he2i, hv02(t, j1, c1, c2, hc1, hc2), {==})
      +sk = fskip2(len, t, d, to, c1, c2, wi, o, v1, v2, q, h, ho, hs, hk, hv, hz, hs1)
      Equal.trans(Nat, U32.to_nat(U32.min(FG2(1n+q, U32.is_zero(U32.or(FA.zb(n1), FA.zb(n2))), j1, U32.or(FA.zb(n1), FA.zb(n2)), FA.rep(c1), FA.rep(c2), t), to)), D.first2(FF.UB(t), FF.SS(j1, 0n), T, c1, c2), D.first2(FF.UB(t), FF.SS(wi, o), T, c1, c2),
        ih, Equal.sym(Nat, D.first2(FF.UB(t), FF.SS(wi, o), T, c1, c2), D.first2(FF.UB(t), FF.SS(j1, 0n), T, c1, c2),
          Equal.trans(Nat, D.first2(FF.UB(t), FF.SS(wi, o), T, c1, c2), D.first2(FF.UB(t), S1, T, c1, c2), D.first2(FF.UB(t), FF.SS(j1, 0n), T, c1, c2), sk,
            Equal.cong(Nat, Nat, y => D.first2(FF.UB(t), y, T, c1, c2), S1, FF.SS(j1, 0n), Equal.sym(Nat, FF.SS(j1, 0n), S1, ea)))))

law fview2_lt:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +from: U32
  for +to: U32
  for +c1: U32
  for +c2: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +ht: {Nat.is_le(U32.to_nat(to), U32.to_nat(len)) == True{} : Bool}
  for +hc1: {U32.is_lt(c1, 256) == True{} : Bool}
  for +hc2: {U32.is_lt(c2, 256) == True{} : Bool}
  for +hlt: {Nat.is_lt(U32.to_nat(from), U32.to_nat(to)) == True{} : Bool}
  {U32.to_nat(U32.min(FG2(U32.to_nat(((((to - 1 : U32) >> 2n : U32) - (from >> 2n : U32) : U32) + 1 : U32)), U32.is_zero(M02(t, from, FA.rep(c1), FA.rep(c2))), (from >> 2n : U32), M02(t, from, FA.rep(c1), FA.rep(c2)), FA.rep(c1), FA.rep(c2), t), to)) == D.first2(D.view(C.BT(len, t)), U32.to_nat(from), U32.to_nat(to), c1, c2) : Nat}

def fview2_lt(len, t, d, from, to, c1, c2, h, ht, hc1, hc2, hlt):
  +F = U32.to_nat(from)
  +T = U32.to_nat(to)
  +wi0 = (from >> 2n : U32)
  +W0 = U32.to_nat(wi0)
  +o0 = U32.to_nat((from .&. 3 : U32))
  +ee = ((to - 1 : U32) >> 2n : U32)
  +E = U32.to_nat(ee)
  +rc1 = FA.rep(c1)
  +rc2 = FA.rep(c2)
  +hd = C.ok_d(len, t, d, h)
  +M4 = Nat.mul(4n, Nat.pow(2n, d))
  +hTM = N.le_trans(T, U32.to_nat(len), M4, ht, C.ok_len(len, t, d, h))
  +h0T = N.le_lt_trans(0n, F, T, N.le_zero_l(F), hlt)
  +eW0 = U.to_nat_shrn(from, 2n)
  +eo = U.to_nat_and_mask(from, 3, 2n, {==})
  +et1 = U.to_nat_sub_le(to, 1, Equal.trans(Bool, U32.is_le(1, to), Nat.is_le(U32.to_nat(1), T), True{}, U.is_le_to_nat(1, to),
    Equal.trans(Bool, Nat.is_le(1n, T), Nat.is_lt(0n, T), True{}, N.le_succ_lt(0n, T), h0T)))
  +eE = Equal.trans(Nat, E, Nat.div(U32.to_nat((to - 1 : U32)), 4n), Nat.div(Nat.sub(T, 1n), 4n), U.to_nat_shrn((to - 1 : U32), 2n),
    Equal.cong(Nat, Nat, y => Nat.div(y, 4n), U32.to_nat((to - 1 : U32)), Nat.sub(T, 1n), et1))
  +hWE = AB.subst(Nat, y => {Nat.is_le(W0, y) == True{} : Bool}, Nat.div(Nat.sub(T, 1n), 4n), E, Equal.sym(Nat, E, Nat.div(Nat.sub(T, 1n), 4n), eE),
    AB.subst(Nat, y => {Nat.is_le(y, Nat.div(Nat.sub(T, 1n), 4n)) == True{} : Bool}, Nat.div(F, 4n), W0, Equal.sym(Nat, W0, Nat.div(F, 4n), eW0),
      FF.div_le4(F, Nat.sub(T, 1n), FF.lt_sub1(F, T, hlt))))
  +k0 = Nat.sub(E, W0)
  +esub = U.to_nat_sub_le(ee, wi0, Equal.trans(Bool, U32.is_le(wi0, ee), Nat.is_le(W0, E), True{}, U.is_le_to_nat(wi0, ee), hWE))
  +hET = N.le_lt_trans(E, Nat.sub(T, 1n), T,
    AB.subst(Nat, y => {Nat.is_le(y, Nat.sub(T, 1n)) == True{} : Bool}, Nat.div(Nat.sub(T, 1n), 4n), E, Equal.sym(Nat, E, Nat.div(Nat.sub(T, 1n), 4n), eE), FF.div_self_le(Nat.sub(T, 1n))),
    FF.sub1_lt(T, h0T))
  +ek = C.inc_fits((ee - wi0 : U32), d, hd,
    AB.subst(Nat, y => {Nat.is_lt(y, M4) == True{} : Bool}, k0, U32.to_nat((ee - wi0 : U32)), Equal.sym(Nat, U32.to_nat((ee - wi0 : U32)), k0, esub),
      N.le_lt_trans(k0, E, M4, H.sub_le(E, W0), N.lt_le_trans(E, T, M4, hET, hTM))))
  +en = Equal.trans(Nat, U32.to_nat(((ee - wi0 : U32) + 1 : U32)), Nat.add(U32.to_nat((ee - wi0 : U32)), 1n), 1n+k0, ek,
    Equal.trans(Nat, Nat.add(U32.to_nat((ee - wi0 : U32)), 1n), Nat.add(k0, 1n), 1n+k0, Equal.cong(Nat, Nat, y => Nat.add(y, 1n), U32.to_nat((ee - wi0 : U32)), k0, esub), N.add_one(k0)))
  +eSF = Equal.trans(Nat, FF.SS(wi0, o0), Nat.add(Nat.mul(Nat.div(F, 4n), 4n), Nat.mod(F, 4n)), F,
    Equal.trans(Nat, Nat.add(Nat.mul(W0, 4n), o0), Nat.add(Nat.mul(Nat.div(F, 4n), 4n), o0), Nat.add(Nat.mul(Nat.div(F, 4n), 4n), Nat.mod(F, 4n)),
      Equal.cong(Nat, Nat, y => Nat.add(Nat.mul(y, 4n), o0), W0, Nat.div(F, 4n), eW0),
      Equal.cong(Nat, Nat, y => Nat.add(Nat.mul(Nat.div(F, 4n), 4n), y), o0, Nat.mod(F, 4n), eo)),
    N.div_mod(F, 4n))
  +ho0 = AB.subst(Nat, y => {Nat.is_lt(y, 4n) == True{} : Bool}, Nat.mod(F, 4n), o0, Equal.sym(Nat, o0, Nat.mod(F, 4n), eo), N.mod_lt(F, 4n, {==}))
  +hs0 = AB.subst(Nat, y => {Nat.is_le(y, T) == True{} : Bool}, F, FF.SS(wi0, o0), Equal.sym(Nat, FF.SS(wi0, o0), F, eSF), N.lt_to_le(F, T, hlt))
  +eWk = N.le_sub_add(W0, E, hWE)
  +eA = Equal.trans(Nat, Nat.add(W0, 1n+k0), 1n+Nat.add(W0, k0), Nat.add(Nat.div(Nat.sub(T, 1n), 4n), 1n), N.add_succ(W0, k0),
    Equal.trans(Nat, 1n+Nat.add(W0, k0), 1n+E, Nat.add(Nat.div(Nat.sub(T, 1n), 4n), 1n), Equal.cong(Nat, Nat, y => 1n+y, Nat.add(W0, k0), E, eWk),
      Equal.trans(Nat, 1n+E, Nat.add(E, 1n), Nat.add(Nat.div(Nat.sub(T, 1n), 4n), 1n), Equal.sym(Nat, Nat.add(E, 1n), 1n+E, N.add_one(E)),
        Equal.cong(Nat, Nat, y => Nat.add(y, 1n), E, Nat.div(Nat.sub(T, 1n), 4n), eE))))
  +he1 = AB.subst(Nat, y => {Nat.is_le(T, Nat.mul(y, 4n)) == True{} : Bool}, Nat.add(Nat.div(Nat.sub(T, 1n), 4n), 1n), Nat.add(W0, 1n+k0),
    Equal.sym(Nat, Nat.add(W0, 1n+k0), Nat.add(Nat.div(Nat.sub(T, 1n), 4n), 1n), eA), FF.last_le(T, h0T))
  +eB = Equal.trans(Nat, Nat.add(W0, k0), E, Nat.div(Nat.sub(T, 1n), 4n), eWk, eE)
  +he2 = AB.subst(Nat, y => {Nat.is_lt(Nat.mul(y, 4n), T) == True{} : Bool}, Nat.div(Nat.sub(T, 1n), 4n), Nat.add(W0, k0),
    Equal.sym(Nat, Nat.add(W0, k0), Nat.div(Nat.sub(T, 1n), 4n), eB), FF.last_lt(T, h0T))
  +fiv = fi2(k0, U32.is_zero(M02(t, from, rc1, rc2)), len, t, d, to, c1, c2, wi0, o0, U32.or(U32.xor(C.WD(t, wi0), rc1), U32.not(FA.low(from))), U32.or(U32.xor(C.WD(t, wi0), rc2), U32.not(FA.low(from))),
    h, ht, hc1, hc2, ho0, hs0, he1, he2, p0_low2(C.WD(t, wi0), c1, c2, from, hc1, hc2), {==})
  +hh = AB.subst(Nat, y => {Nat.is_le(y, U32.to_nat(len)) == True{} : Bool}, T, Nat.add(F, Nat.sub(T, F)),
    Equal.sym(Nat, Nat.add(F, Nat.sub(T, F)), T, N.le_sub_add(F, T, N.lt_to_le(F, T, hlt))), ht)
  +E2 = Equal.trans(Nat, D.first2(FF.UB(t), FF.SS(wi0, o0), T, c1, c2), D.first2(FF.UB(t), F, T, c1, c2), D.first2(D.view(C.BT(len, t)), F, T, c1, c2),
    Equal.cong(Nat, Nat, y => D.first2(FF.UB(t), y, T, c1, c2), FF.SS(wi0, o0), F, eSF),
    Equal.sym(Nat, D.first2(D.view(C.BT(len, t)), F, T, c1, c2), D.first2(FF.UB(t), F, T, c1, c2),
      Equal.cong(List<&2, U32>, Nat, y => Nat.add(F, D.run_len2(y, c1, c2)), D.slice(List.take(&2, U32, FF.UB(t), U32.to_nat(len)), F, Nat.sub(T, F)), D.slice(FF.UB(t), F, Nat.sub(T, F)),
        FF.slice_take(FF.UB(t), U32.to_nat(len), F, Nat.sub(T, F), hh))))
  %Equal.sym(Nat, U32.to_nat(((ee - wi0 : U32) + 1 : U32)), 1n+k0, en) :
    {U32.to_nat(U32.min(FG2(_, U32.is_zero(M02(t, from, rc1, rc2)), wi0, M02(t, from, rc1, rc2), rc1, rc2, t), to)) == D.first2(D.view(C.BT(len, t)), F, T, c1, c2) : Nat}
  Equal.trans(Nat, U32.to_nat(U32.min(FG2(1n+k0, U32.is_zero(M02(t, from, rc1, rc2)), wi0, M02(t, from, rc1, rc2), rc1, rc2, t), to)), D.first2(FF.UB(t), FF.SS(wi0, o0), T, c1, c2),
    D.first2(D.view(C.BT(len, t)), F, T, c1, c2), fiv, E2)

law fview2_go:
  for +b: Bool
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +from: U32
  for +to: U32
  for +c1: U32
  for +c2: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hft: {U32.is_le(from, to) == True{} : Bool}
  for +ht: {Nat.is_le(U32.to_nat(to), U32.to_nat(len)) == True{} : Bool}
  for +hc1: {U32.is_lt(c1, 256) == True{} : Bool}
  for +hc2: {U32.is_lt(c2, 256) == True{} : Bool}
  for +hb: {U32.is_le(to, from) == b : Bool}
  {U32.to_nat(U32.min(FG2(Bool.pick(Nat, b, 0n, U32.to_nat(((((to - 1 : U32) >> 2n : U32) - (from >> 2n : U32) : U32) + 1 : U32))), U32.is_zero(M02(t, from, FA.rep(c1), FA.rep(c2))), (from >> 2n : U32), M02(t, from, FA.rep(c1), FA.rep(c2)), FA.rep(c1), FA.rep(c2), t), to)) == D.first2(D.view(C.BT(len, t)), U32.to_nat(from), U32.to_nat(to), c1, c2) : Nat}

def fview2_go(b, len, t, d, from, to, c1, c2, h, hft, ht, hc1, hc2, hb):
  match b:
    case True{}:
      +F = U32.to_nat(from)
      +T = U32.to_nat(to)
      +xs = D.view(C.BT(len, t))
      +hd = C.ok_d(len, t, d, h)
      +eTF = FF.le_antisym(T, F, Equal.trans(Bool, Nat.is_le(T, F), U32.is_le(to, from), True{}, Equal.sym(Bool, U32.is_le(to, from), Nat.is_le(T, F), U.is_le_to_nat(to, from)), hb),
        Equal.trans(Bool, Nat.is_le(F, T), U32.is_le(from, to), True{}, Equal.sym(Bool, U32.is_le(from, to), Nat.is_le(F, T), U.is_le_to_nat(from, to)), hft))
      %Equal.sym(U32, U32.min(4294967295, to), to, FF.min_top(to, d, hd, N.le_trans(T, U32.to_nat(len), Nat.mul(4n, Nat.pow(2n, d)), ht, C.ok_len(len, t, d, h)))) :
        {U32.to_nat(_) == D.first2(xs, F, T, c1, c2) : Nat}
      %Equal.sym(Nat, T, F, eTF) : {_ == D.first2(xs, F, _, c1, c2) : Nat}
      %Equal.sym(Nat, Nat.sub(F, F), 0n, H.sub_self(F)) : {F == Nat.add(F, D.run_len2(D.slice(xs, F, _), c1, c2)) : Nat}
      %Equal.sym(List<&2, U32>, D.slice(xs, F, 0n), Nil{}, X.slice_zero(xs, F)) : {F == Nat.add(F, D.run_len2(_, c1, c2)) : Nat}
      Equal.sym(Nat, Nat.add(F, 0n), F, N.add_zero(F))
    case False{}:
      fview2_lt(len, t, d, from, to, c1, c2, h, ht, hc1, hc2,
        N.not_le_lt(U32.to_nat(to), U32.to_nat(from), Equal.trans(Bool, Nat.is_le(U32.to_nat(to), U32.to_nat(from)), U32.is_le(to, from), False{},
          Equal.sym(Bool, U32.is_le(to, from), Nat.is_le(U32.to_nat(to), U32.to_nat(from)), U.is_le_to_nat(to, from)), hb)))

law fast_find2_t:
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
  {FA.find2(C.BT(len, t), from, to, c1, c2) == B.find2(C.BT(len, t), from, to, c1, c2) : D.Bytes & U32}

def fast_find2_t(len, t, d, from, to, c1, c2, h, hft, ht, hc1, hc2):
  +rc1 = FA.rep(c1)
  +rc2 = FA.rep(c2)
  +MN = U32.min(FG2(FA.words(from, to), U32.is_zero(M02(t, from, rc1, rc2)), (from >> 2n : U32), M02(t, from, rc1, rc2), rc1, rc2, t), to)
  +SN = Pair.snd(D.Bytes, U32, B.find2(C.BT(len, t), from, to, c1, c2))
  %Equal.sym(D.Bytes & U32, FA.find2(C.BT(len, t), from, to, c1, c2), (C.BT(len, t), MN), fast2_eq(len, t, from, to, c1, c2)) :
    {_ == B.find2(C.BT(len, t), from, to, c1, c2) : D.Bytes & U32}
  %Equal.sym(D.Bytes & U32, B.find2(C.BT(len, t), from, to, c1, c2), (C.BT(len, t), SN), F.find2_pair_t(len, t, from, to, c1, c2)) :
    {(C.BT(len, t), MN) == _ : D.Bytes & U32}
  Equal.cong(U32, D.Bytes & U32, y => (C.BT(len, t), y), MN, SN,
    U.to_nat_inj(MN, SN, Equal.trans(Nat, U32.to_nat(MN), D.first2(D.view(C.BT(len, t)), U32.to_nat(from), U32.to_nat(to), c1, c2), U32.to_nat(SN),
      fview2_go(U32.is_le(to, from), len, t, d, from, to, c1, c2, h, hft, ht, hc1, hc2, {==}),
      Equal.sym(Nat, U32.to_nat(SN), D.first2(D.view(C.BT(len, t)), U32.to_nat(from), U32.to_nat(to), c1, c2), F.find2_view_t(len, t, d, from, to, c1, c2, h, hft, ht, hc1, hc2)))))