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
import lawful-words@0.1.0.0/defs.bend as W
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-arrays@0.1.0.0/proof_tree.bend as P
import lawful-arrays@0.1.0.0/defs.bend as A

# fast.bend's find on the mirror C.BT(len, t). FG is find.go as a function of
# the tree (fg_eq): the word loop answers the offset of the first flagged byte,
# or 4294967295; find.fin takes the min with to. The word facts (what the
# flags and bidx say) are in proof_fast_word.bend.

def FG(n: Nat, z: Bool, +wi: U32, +m: U32, +rc: U32, +t: P.Tree<U32>) -> U32:
  match n z:
    case 0n _:
      4294967295
    case 1n+k True{}:
      +m2 = FA.zb((C.WD(t, (wi + 1 : U32)) .^. rc : U32))
      FG(k, U32.is_zero(m2), (wi + 1 : U32), m2, rc, t)
    case 1n+k False{}:
      ((wi << 2n : U32) + FA.bidx(m) : U32)

law fg_eq:
  for +n: Nat
  for +z: Bool
  for +wi: U32
  for +m: U32
  for +rc: U32
  for +t: P.Tree<U32>
  {FA.find.go(n, z, Array.get(U32, P.fromT(U32, t), (wi + 1 : U32)), wi, m, rc) == (P.fromT(U32, t), FG(n, z, wi, m, rc, t)) : Array<U32> & U32}

def fg_eq(n, z, wi, m, rc, t):
  match n z:
    case 0n _:
      %Equal.sym(Array<U32> & U32, Array.get(U32, P.fromT(U32, t), (wi + 1 : U32)), (P.fromT(U32, t), C.WD(t, (wi + 1 : U32))), P.get_pair_t(U32, t, (wi + 1 : U32))) :
        {FA.find.go(0n, z, _, wi, m, rc) == (P.fromT(U32, t), FG(0n, z, wi, m, rc, t)) : Array<U32> & U32}
      {==}
    case 1n+k True{}:
      +m2 = FA.zb((C.WD(t, (wi + 1 : U32)) .^. rc : U32))
      %Equal.sym(Array<U32> & U32, Array.get(U32, P.fromT(U32, t), (wi + 1 : U32)), (P.fromT(U32, t), C.WD(t, (wi + 1 : U32))), P.get_pair_t(U32, t, (wi + 1 : U32))) :
        {FA.find.go(1n+k, True{}, _, wi, m, rc) == (P.fromT(U32, t), FG(1n+k, True{}, wi, m, rc, t)) : Array<U32> & U32}
      %F.add11(wi) :
        {FA.find.go(k, U32.is_zero(m2), Array.get(U32, P.fromT(U32, t), _), (wi + 1 : U32), m2, rc) == (P.fromT(U32, t), FG(k, U32.is_zero(m2), (wi + 1 : U32), m2, rc, t)) : Array<U32> & U32}
      fg_eq(k, U32.is_zero(m2), (wi + 1 : U32), m2, rc, t)
    case 1n+k False{}:
      %Equal.sym(Array<U32> & U32, Array.get(U32, P.fromT(U32, t), (wi + 1 : U32)), (P.fromT(U32, t), C.WD(t, (wi + 1 : U32))), P.get_pair_t(U32, t, (wi + 1 : U32))) :
        {FA.find.go(1n+k, False{}, _, wi, m, rc) == (P.fromT(U32, t), FG(1n+k, False{}, wi, m, rc, t)) : Array<U32> & U32}
      {==}

# The mask of the first word.
def M0(+t: P.Tree<U32>, +from: U32, +rc: U32) -> U32:
  FA.zb(((C.WD(t, (from >> 2n : U32)) .^. rc : U32) .|. U32.not(FA.low(from)) : U32))

# fast find on the mirror: the same Bytes, and the min of the loop's answer with to.
law fast_eq:
  for +len: U32
  for +t: P.Tree<U32>
  for +from: U32
  for +to: U32
  for +c: U32
  {FA.find(C.BT(len, t), from, to, c) == (C.BT(len, t), U32.min(FG(FA.words(from, to), U32.is_zero(M0(t, from, FA.rep(c))), (from >> 2n : U32), M0(t, from, FA.rep(c)), FA.rep(c), t), to)) : D.Bytes & U32}

def fast_eq(len, t, from, to, c):
  +k = (from >> 2n : U32)
  +rc = FA.rep(c)
  +n = FA.words(from, to)
  %Equal.sym(Array<U32> & U32, Array.get(U32, P.fromT(U32, t), k), (P.fromT(U32, t), C.WD(t, k)), P.get_pair_t(U32, t, k)) :
    {FA.find.k(len, FA.find.fin(to, FA.find.start(n, _, from, rc))) == (C.BT(len, t), U32.min(FG(n, U32.is_zero(M0(t, from, rc)), k, M0(t, from, rc), rc, t), to)) : D.Bytes & U32}
  %Equal.sym(Array<U32> & U32, FA.find.go(n, U32.is_zero(M0(t, from, rc)), Array.get(U32, P.fromT(U32, t), (k + 1 : U32)), k, M0(t, from, rc), rc),
    (P.fromT(U32, t), FG(n, U32.is_zero(M0(t, from, rc)), k, M0(t, from, rc), rc, t)), fg_eq(n, U32.is_zero(M0(t, from, rc)), k, M0(t, from, rc), rc, t)) :
    {FA.find.k(len, FA.find.fin(to, _)) == (C.BT(len, t), U32.min(FG(n, U32.is_zero(M0(t, from, rc)), k, M0(t, from, rc), rc, t), to)) : D.Bytes & U32}
  {==}

# Lists
# =====

law drop_append_l:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +o: Nat
  for +h: {Nat.is_le(o, List.length(&2, U32, xs)) == True{} : Bool}
  {List.drop(&2, U32, List.append(&2, U32, xs, ys), o) == List.append(&2, U32, List.drop(&2, U32, xs, o), ys) : List<&2, U32>}

def drop_append_l(xs, ys, o, h):
  match xs o:
    case Nil{} 0n:
      X.drop_zero(ys)
    case Nil{} 1n+p:
      Empty.absurd({List.drop(&2, U32, ys, 1n+p) == ys : List<&2, U32>}, AB.false_ne_true(h))
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+p:
      drop_append_l(t, ys, p, h)

law drop_unpack:
  for +ws: List<&2, U32>
  for +q: Nat
  {List.drop(&2, U32, D.unpack(ws), Nat.mul(q, 4n)) == D.unpack(List.drop(&2, U32, ws, q)) : List<&2, U32>}

def drop_unpack(ws, q):
  match ws q:
    case Nil{} _:
      {==}
    case Con{x, t} 0n:
      X.drop_zero(D.unpack(Con{x, t}))
    case Con{x, t} 1n+p:
      drop_unpack(t, p)

# Byte 4q + o onwards: the rest of word q, then the words after it.
law drop_word:
  for +ws: List<&2, U32>
  for +q: Nat
  for +o: Nat
  for +w: U32
  for +hw: {List.get(&2, U32, ws, q) == Some{w} : Maybe<&2, U32>}
  for +ho: {Nat.is_le(o, 4n) == True{} : Bool}
  {List.drop(&2, U32, D.unpack(ws), Nat.add(Nat.mul(q, 4n), o)) == List.append(&2, U32, List.drop(&2, U32, C.L4(w), o), D.unpack(List.drop(&2, U32, ws, Nat.add(q, 1n)))) : List<&2, U32>}

def drop_word(ws, q, o, w, hw, ho):
  match ws q:
    case Nil{} _:
      Empty.absurd({List.drop(&2, U32, D.unpack(Nil{}), Nat.add(Nat.mul(q, 4n), o)) == List.append(&2, U32, List.drop(&2, U32, C.L4(w), o), D.unpack(List.drop(&2, U32, Nil{}, Nat.add(q, 1n)))) : List<&2, U32>},
        X.none_some(w, hw))
    case Con{+x, t} 0n:
      %X.some_inj(x, w, hw) :
        {List.drop(&2, U32, List.append(&2, U32, C.L4(x), D.unpack(t)), o) == List.append(&2, U32, List.drop(&2, U32, C.L4(_), o), D.unpack(List.drop(&2, U32, t, 0n))) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, List.drop(&2, U32, t, 0n), t, X.drop_zero(t)) :
        {List.drop(&2, U32, List.append(&2, U32, C.L4(x), D.unpack(t)), o) == List.append(&2, U32, List.drop(&2, U32, C.L4(x), o), D.unpack(_)) : List<&2, U32>}
      drop_append_l(C.L4(x), D.unpack(t), o, ho)
    case Con{x, t} 1n+p:
      drop_word(t, p, o, w, hw, ho)

# Whether the head of a list is c.
def hd_eq(xs: List<&2, U32>, +c: U32) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, t}:
      U32.is_eq(x, c)

# A hit inside xs: the first c of take(xs ++ ys, n) is at min(run, n).
law run_hit:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +n: Nat
  for +c: U32
  for +b: Bool
  for +hb: {hd_eq(xs, c) == b : Bool}
  for +h: {Nat.is_lt(D.run_len(xs, c), List.length(&2, U32, xs)) == True{} : Bool}
  {D.run_len(List.take(&2, U32, List.append(&2, U32, xs, ys), n), c) == Nat.min(D.run_len(xs, c), n) : Nat}

def run_hit(xs, ys, n, c, b, hb, h):
  match xs n b:
    case Nil{} _ _:
      Empty.absurd({D.run_len(List.take(&2, U32, ys, n), c) == Nat.min(0n, n) : Nat}, AB.lt_zero_absurd(0n, h))
    case Con{x, t} 0n True{}:
      %Equal.sym(Bool, hd_eq(x <> t, c), True{}, hb) : {0n == Nat.min(Bool.pick(Nat, _, 0n, Nat.add(1n, D.run_len(t, c))), 0n) : Nat}
      {==}
    case Con{x, t} 0n False{}:
      %Equal.sym(Bool, hd_eq(x <> t, c), False{}, hb) : {0n == Nat.min(Bool.pick(Nat, _, 0n, Nat.add(1n, D.run_len(t, c))), 0n) : Nat}
      {==}
    case Con{x, t} 1n+p True{}:
      %Equal.sym(Bool, hd_eq(x <> t, c), True{}, hb) :
        {Bool.pick(Nat, _, 0n, Nat.add(1n, D.run_len(List.take(&2, U32, List.append(&2, U32, t, ys), p), c))) == Nat.min(Bool.pick(Nat, _, 0n, Nat.add(1n, D.run_len(t, c))), 1n+p) : Nat}
      {==}
    case Con{x, t} 1n+p False{}:
      %Equal.sym(Bool, hd_eq(x <> t, c), False{}, hb) :
        {Bool.pick(Nat, _, 0n, Nat.add(1n, D.run_len(List.take(&2, U32, List.append(&2, U32, t, ys), p), c))) == Nat.min(Bool.pick(Nat, _, 0n, Nat.add(1n, D.run_len(t, c))), 1n+p) : Nat}
      +h2 = AB.subst(Bool, y => {Nat.is_lt(Bool.pick(Nat, y, 0n, Nat.add(1n, D.run_len(t, c))), 1n+List.length(&2, U32, t)) == True{} : Bool},
        hd_eq(x <> t, c), False{}, hb, h)
      %run_hit(t, ys, p, c, hd_eq(t, c), {==}, h2) :
        {1n+D.run_len(List.take(&2, U32, List.append(&2, U32, t, ys), p), c) == 1n+_ : Nat}
      {==}

# No c in xs, and n reaches past it: the search goes on in ys.
law run_skip:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +n: Nat
  for +c: U32
  for +b: Bool
  for +hb: {hd_eq(xs, c) == b : Bool}
  for +h: {D.run_len(xs, c) == List.length(&2, U32, xs) : Nat}
  for +hn: {Nat.is_le(List.length(&2, U32, xs), n) == True{} : Bool}
  {D.run_len(List.take(&2, U32, List.append(&2, U32, xs, ys), n), c) == Nat.add(List.length(&2, U32, xs), D.run_len(List.take(&2, U32, ys, Nat.sub(n, List.length(&2, U32, xs))), c)) : Nat}

def run_skip(xs, ys, n, c, b, hb, h, hn):
  match xs n b:
    case Nil{} _ _:
      %Equal.sym(Nat, Nat.sub(n, 0n), n, N.sub_zero(n)) :
        {D.run_len(List.take(&2, U32, ys, n), c) == D.run_len(List.take(&2, U32, ys, _), c) : Nat}
      {==}
    case Con{x, t} _ True{}:
      Empty.absurd({D.run_len(List.take(&2, U32, List.append(&2, U32, x <> t, ys), n), c) == Nat.add(1n+List.length(&2, U32, t), D.run_len(List.take(&2, U32, ys, Nat.sub(n, 1n+List.length(&2, U32, t))), c)) : Nat},
        N.zero_ne_succ(List.length(&2, U32, t), AB.subst(Bool, y => {Bool.pick(Nat, y, 0n, Nat.add(1n, D.run_len(t, c))) == 1n+List.length(&2, U32, t) : Nat},
          hd_eq(x <> t, c), True{}, hb, h)))
    case Con{x, t} 0n False{}:
      Empty.absurd({0n == Nat.add(1n+List.length(&2, U32, t), D.run_len(List.take(&2, U32, ys, Nat.sub(0n, 1n+List.length(&2, U32, t))), c)) : Nat},
        AB.false_ne_true(hn))
    case Con{x, t} 1n+p False{}:
      %Equal.sym(Bool, hd_eq(x <> t, c), False{}, hb) :
        {Bool.pick(Nat, _, 0n, Nat.add(1n, D.run_len(List.take(&2, U32, List.append(&2, U32, t, ys), p), c))) == 1n+Nat.add(List.length(&2, U32, t), D.run_len(List.take(&2, U32, ys, Nat.sub(p, List.length(&2, U32, t))), c)) : Nat}
      +h2 = N.succ_inj(D.run_len(t, c), List.length(&2, U32, t),
        AB.subst(Bool, y => {Bool.pick(Nat, y, 0n, Nat.add(1n, D.run_len(t, c))) == 1n+List.length(&2, U32, t) : Nat}, hd_eq(x <> t, c), False{}, hb, h))
      %run_skip(t, ys, p, c, hd_eq(t, c), {==}, h2, hn) :
        {1n+D.run_len(List.take(&2, U32, List.append(&2, U32, t, ys), p), c) == 1n+_ : Nat}
      {==}

# No c in xs, and n stays within it.
law run_none:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +n: Nat
  for +c: U32
  for +b: Bool
  for +hb: {hd_eq(xs, c) == b : Bool}
  for +h: {D.run_len(xs, c) == List.length(&2, U32, xs) : Nat}
  for +hn: {Nat.is_le(n, List.length(&2, U32, xs)) == True{} : Bool}
  {D.run_len(List.take(&2, U32, List.append(&2, U32, xs, ys), n), c) == n : Nat}

def run_none(xs, ys, n, c, b, hb, h, hn):
  match xs n b:
    case Nil{} 0n _:
      %Equal.sym(List<&2, U32>, List.take(&2, U32, ys, 0n), Nil{}, Q.take_zero(ys)) : {D.run_len(_, c) == 0n : Nat}
      {==}
    case Nil{} 1n+p _:
      Empty.absurd({D.run_len(List.take(&2, U32, ys, 1n+p), c) == 1n+p : Nat}, AB.false_ne_true(hn))
    case Con{x, t} 0n _:
      {==}
    case Con{x, t} 1n+p True{}:
      Empty.absurd({D.run_len(List.take(&2, U32, List.append(&2, U32, x <> t, ys), 1n+p), c) == 1n+p : Nat},
        N.zero_ne_succ(List.length(&2, U32, t), AB.subst(Bool, y => {Bool.pick(Nat, y, 0n, Nat.add(1n, D.run_len(t, c))) == 1n+List.length(&2, U32, t) : Nat},
          hd_eq(x <> t, c), True{}, hb, h)))
    case Con{x, t} 1n+p False{}:
      %Equal.sym(Bool, hd_eq(x <> t, c), False{}, hb) :
        {Bool.pick(Nat, _, 0n, Nat.add(1n, D.run_len(List.take(&2, U32, List.append(&2, U32, t, ys), p), c))) == 1n+p : Nat}
      +h2 = N.succ_inj(D.run_len(t, c), List.length(&2, U32, t),
        AB.subst(Bool, y => {Bool.pick(Nat, y, 0n, Nat.add(1n, D.run_len(t, c))) == 1n+List.length(&2, U32, t) : Nat}, hd_eq(x <> t, c), False{}, hb, h))
      %run_none(t, ys, p, c, hd_eq(t, c), {==}, h2, hn) : {1n+D.run_len(List.take(&2, U32, List.append(&2, U32, t, ys), p), c) == 1n+_ : Nat}
      {==}

law run_le:
  for +xs: List<&2, U32>
  for +c: U32
  for +b: Bool
  for +hb: {hd_eq(xs, c) == b : Bool}
  {Nat.is_le(D.run_len(xs, c), List.length(&2, U32, xs)) == True{} : Bool}

def run_le(xs, c, b, hb):
  match xs b:
    case Nil{} _:
      {==}
    case Con{x, t} True{}:
      %Equal.sym(Bool, hd_eq(x <> t, c), True{}, hb) :
        {Nat.is_le(Bool.pick(Nat, _, 0n, Nat.add(1n, D.run_len(t, c))), 1n+List.length(&2, U32, t)) == True{} : Bool}
      {==}
    case Con{x, t} False{}:
      %Equal.sym(Bool, hd_eq(x <> t, c), False{}, hb) :
        {Nat.is_le(Bool.pick(Nat, _, 0n, Nat.add(1n, D.run_len(t, c))), 1n+List.length(&2, U32, t)) == True{} : Bool}
      run_le(t, c, hd_eq(t, c), {==})

# Nat
# ===

law min_shift:
  for +s: Nat
  for +r: Nat
  for +tt: Nat
  for +h: {Nat.is_le(s, tt) == True{} : Bool}
  {Nat.min(Nat.add(s, r), tt) == Nat.add(s, Nat.min(r, Nat.sub(tt, s))) : Nat}

def min_shift(s, r, tt, h):
  match s tt:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.min(1n+Nat.add(p, r), 0n) == 1n+Nat.add(p, Nat.min(r, 0n)) : Nat}, AB.false_ne_true(h))
    case 1n+p 1n+q:
      %min_shift(p, r, q, h) : {1n+Nat.min(Nat.add(p, r), q) == 1n+_ : Nat}
      {==}

law le_cancel:
  for +a: Nat
  for +x: Nat
  for +y: Nat
  for +h: {Nat.is_le(Nat.add(a, x), Nat.add(a, y)) == True{} : Bool}
  {Nat.is_le(x, y) == True{} : Bool}

def le_cancel(a, x, y, h):
  match a:
    case 0n:
      h
    case 1n+p:
      le_cancel(p, x, y, h)

law lt_cancel:
  for +a: Nat
  for +x: Nat
  for +y: Nat
  for +h: {Nat.is_lt(Nat.add(a, x), Nat.add(a, y)) == True{} : Bool}
  {Nat.is_lt(x, y) == True{} : Bool}

def lt_cancel(a, x, y, h):
  match a:
    case 0n:
      h
    case 1n+p:
      lt_cancel(p, x, y, h)

law sub_sub:
  for +tt: Nat
  for +s: Nat
  for +l: Nat
  {Nat.sub(Nat.sub(tt, s), l) == Nat.sub(tt, Nat.add(s, l)) : Nat}

def sub_sub(tt, s, l):
  match tt s:
    case 0n _:
      match l:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      sub_sub(p, q, l)

law mul4s:
  for +w: Nat
  {Nat.mul(Nat.add(w, 1n), 4n) == Nat.add(Nat.mul(w, 4n), 4n) : Nat}

def mul4s(w):
  match w:
    case 0n:
      {==}
    case 1n+p:
      %mul4s(p) : {Nat.add(4n, Nat.mul(Nat.add(p, 1n), 4n)) == Nat.add(4n, _) : Nat}
      {==}

# Word index bounds: the words searched lie inside the block.
law wlt:
  for +w: Nat
  for +k: Nat
  for +tt: Nat
  for +ll: Nat
  for +pp: Nat
  for +h1: {Nat.is_lt(Nat.mul(Nat.add(w, k), 4n), tt) == True{} : Bool}
  for +h2: {Nat.is_le(tt, ll) == True{} : Bool}
  for +h3: {Nat.is_le(ll, Nat.mul(4n, pp)) == True{} : Bool}
  {Nat.is_lt(w, pp) == True{} : Bool}

def wlt(w, k, tt, ll, pp, h1, h2, h3):
  +a = N.le_lt_trans(Nat.mul(w, 4n), Nat.mul(Nat.add(w, k), 4n), Nat.mul(4n, pp), N.le_mul_r(w, Nat.add(w, k), 4n, N.le_add_r(w, k)),
    N.lt_le_trans(Nat.mul(Nat.add(w, k), 4n), tt, Nat.mul(4n, pp), h1, N.le_trans(tt, ll, Nat.mul(4n, pp), h2, h3)))
  N.lt_mul_cancel(4n, w, pp, AB.subst(Nat, y => {Nat.is_lt(y, Nat.mul(4n, pp)) == True{} : Bool}, Nat.mul(w, 4n), Nat.mul(4n, w), N.mul_comm(w, 4n), a))

law wb4:
  for +w: Nat
  for +pp: Nat
  for +h: {Nat.is_lt(w, pp) == True{} : Bool}
  {Nat.is_le(Nat.add(Nat.mul(w, 4n), 4n), Nat.mul(4n, pp)) == True{} : Bool}

def wb4(w, pp, h):
  +a = N.le_mul_r(1n+w, pp, 4n, Equal.trans(Bool, Nat.is_le(1n+w, pp), Nat.is_lt(w, pp), True{}, N.le_succ_lt(w, pp), h))
  %Equal.sym(Nat, Nat.add(Nat.mul(w, 4n), 4n), Nat.add(4n, Nat.mul(w, 4n)), N.add_comm(Nat.mul(w, 4n), 4n)) : {Nat.is_le(_, Nat.mul(4n, pp)) == True{} : Bool}
  %Equal.sym(Nat, Nat.mul(4n, pp), Nat.mul(pp, 4n), N.mul_comm(4n, pp)) : {Nat.is_le(Nat.add(4n, Nat.mul(w, 4n)), _) == True{} : Bool}
  a

# The loop's "no hit" answer 4294967295 is above every length.
law not0:
  {U32.not(0) == 4294967295 : U32}

def not0():
  {==}

law min_r:
  for +a: U32
  for +b: U32
  for +h: {U32.is_lt(a, b) == False{} : Bool}
  {U32.min(a, b) == b : U32}

def min_r(a, b, h):
  match a b:
    case U32{x} U32{y}:
      %Equal.sym(Bool, U32.is_lt(U32{x}, U32{y}), False{}, h) : {Bool.pick(U32, _, U32{x}, U32{y}) == U32{y} : U32}
      {==}

def gtop.go(+tt: Nat, +m: Nat, +ht: {Nat.is_lt(tt, m) == True{} : Bool}) -> {Nat.is_lt(Nat.sub(Nat.sub(m, 1n), 0n), tt) == False{} : Bool}:
  match m:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, tt) == False{} : Bool}, AB.lt_zero_absurd(tt, ht))
    case 1n+p:
      %Equal.sym(Nat, Nat.sub(Nat.sub(p, 0n), 0n), Nat.sub(p, 0n), N.sub_zero(Nat.sub(p, 0n))) : {Nat.is_lt(_, tt) == False{} : Bool}
      %Equal.sym(Nat, Nat.sub(p, 0n), p, N.sub_zero(p)) : {Nat.is_lt(_, tt) == False{} : Bool}
      N.le_not_lt(tt, p, Equal.trans(Bool, Nat.is_le(tt, p), Nat.is_lt(tt, 1n+p), True{}, Equal.sym(Bool, Nat.is_lt(tt, 1n+p), Nat.is_le(tt, p), N.lt_succ_iff(tt, p)), ht))

# With the bound m abstract (m stands for 2^32).
law gtop:
  for +x: Nat
  for +tt: Nat
  for +m: Nat
  for +hx: {x == Nat.sub(Nat.sub(m, 1n), U32.to_nat(0)) : Nat}
  for +ht: {Nat.is_lt(tt, m) == True{} : Bool}
  {Nat.is_lt(x, tt) == False{} : Bool}

def gtop(x, tt, m, hx, ht):
  %Equal.sym(Nat, x, Nat.sub(Nat.sub(m, 1n), U32.to_nat(0)), hx) : {Nat.is_lt(_, tt) == False{} : Bool}
  gtop.go(tt, m, ht)


law top_nat:
  {U32.to_nat(4294967295) == Nat.sub(Nat.sub(Nat.pow(2n, 32n), 1n), U32.to_nat(0)) : Nat}

def top_nat():
  %not0() : {U32.to_nat(_) == Nat.sub(Nat.sub(Nat.pow(2n, 32n), 1n), U32.to_nat(0)) : Nat}
  U.to_nat_not_p(0)

law is_lt_top:
  for +to: U32
  for +d: Nat
  for +hd: {Nat.is_le(d, 29n) == True{} : Bool}
  for +ht: {Nat.is_le(U32.to_nat(to), Nat.mul(4n, Nat.pow(2n, d))) == True{} : Bool}
  {U32.is_lt(4294967295, to) == False{} : Bool}

def is_lt_top(to, d, hd, ht):
  %Equal.sym(Bool, U32.is_lt(4294967295, to), Nat.is_lt(U32.to_nat(4294967295), U32.to_nat(to)), U.is_lt_to_nat(4294967295, to)) :
    {_ == False{} : Bool}
  gtop(U32.to_nat(4294967295), U32.to_nat(to), Nat.pow(2n, 32n), top_nat(), C.fits_e(U32.to_nat(to), d, 32n, C.he32(d, hd), ht))

law min_top:
  for +to: U32
  for +d: Nat
  for +hd: {Nat.is_le(d, 29n) == True{} : Bool}
  for +ht: {Nat.is_le(U32.to_nat(to), Nat.mul(4n, Nat.pow(2n, d))) == True{} : Bool}
  {U32.min(4294967295, to) == to : U32}

def min_top(to, d, hd, ht):
  min_r(4294967295, to, is_lt_top(to, d, hd, ht))

# The word loop
# =============

# All the block's bytes, the start of a search inside word wi (o bytes in),
# the rest of that word, and the bytes from the next word on.
def UB(+t: P.Tree<U32>) -> List<&2, U32>:
  D.unpack(C.WL(t))

def SS(+wi: U32, +o: Nat) -> Nat:
  Nat.add(Nat.mul(U32.to_nat(wi), 4n), o)

def AW(+t: P.Tree<U32>, +wi: U32, +o: Nat) -> List<&2, U32>:
  List.drop(&2, U32, C.L4(C.WD(t, wi)), o)

def BW(+t: P.Tree<U32>, +wi: U32) -> List<&2, U32>:
  List.drop(&2, U32, UB(t), Nat.mul(Nat.add(U32.to_nat(wi), 1n), 4n))

law shl2:
  for +wi: U32
  for +d: Nat
  for +hd: {Nat.is_le(d, 29n) == True{} : Bool}
  for +hx: {Nat.is_le(Nat.mul(U32.to_nat(wi), 4n), Nat.mul(4n, Nat.pow(2n, d))) == True{} : Bool}
  {U32.to_nat((wi << 2n : U32)) == Nat.mul(U32.to_nat(wi), 4n) : Nat}

def shl2(wi, d, hd, hx):
  U.to_nat_shln_fits_p(wi, 2n, C.fits_e(Nat.mul(U32.to_nat(wi), Nat.pow(2n, 2n)), d, 32n, C.he32(d, hd), hx))

law dw:
  for +t: P.Tree<U32>
  for +d: Nat
  for +wi: U32
  for +o: Nat
  for +hf: {A.full(U32, P.fromT(U32, t), d) == True{} : Bool}
  for +hd: {Nat.is_le(d, 29n) == True{} : Bool}
  for +hk: {Nat.is_lt(U32.to_nat(wi), Nat.pow(2n, d)) == True{} : Bool}
  for +ho: {Nat.is_le(o, 4n) == True{} : Bool}
  {List.drop(&2, U32, UB(t), SS(wi, o)) == List.append(&2, U32, AW(t, wi, o), BW(t, wi)) : List<&2, U32>}

def dw(t, d, wi, o, hf, hd, hk, ho):
  %Equal.sym(List<&2, U32>, List.drop(&2, U32, UB(t), Nat.mul(Nat.add(U32.to_nat(wi), 1n), 4n)), D.unpack(List.drop(&2, U32, C.WL(t), Nat.add(U32.to_nat(wi), 1n))),
    drop_unpack(C.WL(t), Nat.add(U32.to_nat(wi), 1n))) :
    {List.drop(&2, U32, UB(t), SS(wi, o)) == List.append(&2, U32, AW(t, wi, o), _) : List<&2, U32>}
  drop_word(C.WL(t), U32.to_nat(wi), o, C.WD(t, wi), C.wd_get(t, d, wi, hf, hd, hk), ho)

law awl:
  for +t: P.Tree<U32>
  for +wi: U32
  for +o: Nat
  {List.length(&2, U32, AW(t, wi, o)) == Nat.sub(4n, o) : Nat}

def awl(t, wi, o):
  H.drop_length(C.L4(C.WD(t, wi)), o)

# The flagged word: the answer is the first c from the start, or to.
law fhit:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +to: U32
  for +c: U32
  for +wi: U32
  for +o: Nat
  for +v: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +ht: {Nat.is_le(U32.to_nat(to), U32.to_nat(len)) == True{} : Bool}
  for +ho: {Nat.is_lt(o, 4n) == True{} : Bool}
  for +hs: {Nat.is_le(SS(wi, o), U32.to_nat(to)) == True{} : Bool}
  for +hk: {Nat.is_lt(U32.to_nat(wi), Nat.pow(2n, d)) == True{} : Bool}
  for +hv: {FW.P0(v) == Nat.add(o, D.run_len(AW(t, wi, o), c)) : Nat}
  for +hz: {U32.is_zero(FA.zb(v)) == False{} : Bool}
  {U32.to_nat(U32.min(((wi << 2n : U32) + FA.bidx(FA.zb(v)) : U32), to)) == D.first(UB(t), SS(wi, o), U32.to_nat(to), c) : Nat}

def fhit(len, t, d, to, c, wi, o, v, h, ht, ho, hs, hk, hv, hz):
  +W = U32.to_nat(wi)
  +T = U32.to_nat(to)
  +r = D.run_len(AW(t, wi, o), c)
  +M4 = Nat.mul(4n, Nat.pow(2n, d))
  +hd = C.ok_d(len, t, d, h)
  +hf = C.ok_full(len, t, d, h)
  +hp4 = run_le(C.L4(v), 0, hd_eq(C.L4(v), 0), {==})
  +hne = Equal.trans(Bool, Nat.is_eq(FW.P0(v), 4n), U32.is_zero(FA.zb(v)), False{}, Equal.sym(Bool, U32.is_zero(FA.zb(v)), Nat.is_eq(FW.P0(v), 4n), FW.zb_none(v)), hz)
  +hlt = Equal.trans(Bool, Nat.is_lt(FW.P0(v), 4n), Nat.is_le(1n+FW.P0(v), 4n), True{}, Equal.sym(Bool, Nat.is_le(1n+FW.P0(v), 4n), Nat.is_lt(FW.P0(v), 4n), N.le_succ_lt(FW.P0(v), 4n)),
    N.le_ne(FW.P0(v), 4n, hp4, hne))
  +hlt2 = AB.subst(Nat, y => {Nat.is_lt(y, 4n) == True{} : Bool}, FW.P0(v), Nat.add(o, r), hv, hlt)
  +eo = N.le_sub_add(o, 4n, N.lt_to_le(o, 4n, ho))
  +hrl0 = lt_cancel(o, r, Nat.sub(4n, o), AB.subst(Nat, y => {Nat.is_lt(Nat.add(o, r), y) == True{} : Bool}, 4n, Nat.add(o, Nat.sub(4n, o)), Equal.sym(Nat, Nat.add(o, Nat.sub(4n, o)), 4n, eo), hlt2))
  +hrl = AB.subst(Nat, y => {Nat.is_lt(r, y) == True{} : Bool}, Nat.sub(4n, o), List.length(&2, U32, AW(t, wi, o)), Equal.sym(Nat, List.length(&2, U32, AW(t, wi, o)), Nat.sub(4n, o), awl(t, wi, o)), hrl0)
  +eb = Equal.trans(Nat, U32.to_nat(FA.bidx(FA.zb(v))), FW.P0(v), Nat.add(o, r), FW.zb_bidx(v, hlt), hv)
  +hw4 = wb4(W, Nat.pow(2n, d), hk)
  +esh = shl2(wi, d, hd, N.le_trans(Nat.mul(W, 4n), Nat.add(Nat.mul(W, 4n), 4n), M4, N.le_add_r(Nat.mul(W, 4n), 4n), hw4))
  +b1 = N.le_trans(Nat.add(Nat.mul(W, 4n), Nat.add(o, r)), Nat.add(Nat.mul(W, 4n), 4n), M4,
    N.le_add_mono_l(Nat.mul(W, 4n), Nat.add(o, r), 4n, N.lt_to_le(Nat.add(o, r), 4n, hlt2)), hw4)
  +b2 = AB.subst(Nat, y => {Nat.is_le(Nat.add(y, Nat.add(o, r)), M4) == True{} : Bool}, Nat.mul(W, 4n), U32.to_nat((wi << 2n : U32)), Equal.sym(Nat, U32.to_nat((wi << 2n : U32)), Nat.mul(W, 4n), esh), b1)
  +b3 = AB.subst(Nat, y => {Nat.is_le(Nat.add(U32.to_nat((wi << 2n : U32)), y), M4) == True{} : Bool}, Nat.add(o, r), U32.to_nat(FA.bidx(FA.zb(v))),
    Equal.sym(Nat, U32.to_nat(FA.bidx(FA.zb(v))), Nat.add(o, r), eb), b2)
  +ej = C.add_fits((wi << 2n : U32), FA.bidx(FA.zb(v)), d, hd, b3)
  +RHS = D.first(UB(t), SS(wi, o), T, c)
  %Equal.sym(Nat, U32.to_nat(U32.min(((wi << 2n : U32) + FA.bidx(FA.zb(v)) : U32), to)), Nat.min(U32.to_nat(((wi << 2n : U32) + FA.bidx(FA.zb(v)) : U32)), T),
    U.to_nat_min(((wi << 2n : U32) + FA.bidx(FA.zb(v)) : U32), to)) :
    {_ == RHS : Nat}
  %Equal.sym(Nat, U32.to_nat(((wi << 2n : U32) + FA.bidx(FA.zb(v)) : U32)), Nat.add(U32.to_nat((wi << 2n : U32)), U32.to_nat(FA.bidx(FA.zb(v)))), ej) :
    {Nat.min(_, T) == RHS : Nat}
  %Equal.sym(Nat, U32.to_nat(FA.bidx(FA.zb(v))), Nat.add(o, r), eb) :
    {Nat.min(Nat.add(U32.to_nat((wi << 2n : U32)), _), T) == RHS : Nat}
  %Equal.sym(Nat, U32.to_nat((wi << 2n : U32)), Nat.mul(W, 4n), esh) :
    {Nat.min(Nat.add(_, Nat.add(o, r)), T) == RHS : Nat}
  %N.add_assoc(Nat.mul(W, 4n), o, r) :
    {Nat.min(_, T) == RHS : Nat}
  %Equal.sym(Nat, Nat.min(Nat.add(SS(wi, o), r), T), Nat.add(SS(wi, o), Nat.min(r, Nat.sub(T, SS(wi, o)))), min_shift(SS(wi, o), r, T, hs)) :
    {_ == RHS : Nat}
  %Equal.sym(List<&2, U32>, List.drop(&2, U32, UB(t), SS(wi, o)), List.append(&2, U32, AW(t, wi, o), BW(t, wi)), dw(t, d, wi, o, hf, hd, hk, N.lt_to_le(o, 4n, ho))) :
    {Nat.add(SS(wi, o), Nat.min(r, Nat.sub(T, SS(wi, o)))) == Nat.add(SS(wi, o), D.run_len(List.take(&2, U32, _, Nat.sub(T, SS(wi, o))), c)) : Nat}
  %Equal.sym(Nat, D.run_len(List.take(&2, U32, List.append(&2, U32, AW(t, wi, o), BW(t, wi)), Nat.sub(T, SS(wi, o))), c), Nat.min(r, Nat.sub(T, SS(wi, o))),
    run_hit(AW(t, wi, o), BW(t, wi), Nat.sub(T, SS(wi, o)), c, hd_eq(AW(t, wi, o), c), {==}, hrl)) :
    {Nat.add(SS(wi, o), Nat.min(r, Nat.sub(T, SS(wi, o)))) == Nat.add(SS(wi, o), _) : Nat}
  {==}

# An unflagged word has no c from the start on.
law nohit_run:
  for +t: P.Tree<U32>
  for +wi: U32
  for +o: Nat
  for +v: U32
  for +c: U32
  for +hv: {FW.P0(v) == Nat.add(o, D.run_len(AW(t, wi, o), c)) : Nat}
  for +hz: {U32.is_zero(FA.zb(v)) == True{} : Bool}
  {D.run_len(AW(t, wi, o), c) == List.length(&2, U32, AW(t, wi, o)) : Nat}

def nohit_run(t, wi, o, v, c, hv, hz):
  +r = D.run_len(AW(t, wi, o), c)
  +e4 = N.eq_sound(FW.P0(v), 4n, Equal.trans(Bool, Nat.is_eq(FW.P0(v), 4n), U32.is_zero(FA.zb(v)), True{},
    Equal.sym(Bool, U32.is_zero(FA.zb(v)), Nat.is_eq(FW.P0(v), 4n), FW.zb_none(v)), hz))
  +e5 = Equal.trans(Nat, Nat.add(o, r), FW.P0(v), 4n, Equal.sym(Nat, FW.P0(v), Nat.add(o, r), hv), e4)
  %Equal.sym(Nat, List.length(&2, U32, AW(t, wi, o)), Nat.sub(4n, o), awl(t, wi, o)) : {r == _ : Nat}
  %e5 : {r == Nat.sub(_, o) : Nat}
  Equal.sym(Nat, Nat.sub(Nat.add(o, r), o), r, N.sub_add_l(o, r))

law pow_le4:
  for +p: Nat
  {Nat.is_le(p, Nat.mul(4n, p)) == True{} : Bool}

def pow_le4(p):
  N.le_add_r(p, Nat.mul(3n, p))

# The last word, unflagged: the answer is to.
law fnone0:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +to: U32
  for +c: U32
  for +wi: U32
  for +o: Nat
  for +v: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +ht: {Nat.is_le(U32.to_nat(to), U32.to_nat(len)) == True{} : Bool}
  for +ho: {Nat.is_lt(o, 4n) == True{} : Bool}
  for +hs: {Nat.is_le(SS(wi, o), U32.to_nat(to)) == True{} : Bool}
  for +hk: {Nat.is_lt(U32.to_nat(wi), Nat.pow(2n, d)) == True{} : Bool}
  for +hv: {FW.P0(v) == Nat.add(o, D.run_len(AW(t, wi, o), c)) : Nat}
  for +hz: {U32.is_zero(FA.zb(v)) == True{} : Bool}
  for +he: {Nat.is_le(U32.to_nat(to), Nat.mul(Nat.add(U32.to_nat(wi), 1n), 4n)) == True{} : Bool}
  {U32.to_nat(U32.min(4294967295, to)) == D.first(UB(t), SS(wi, o), U32.to_nat(to), c) : Nat}

def fnone0(len, t, d, to, c, wi, o, v, h, ht, ho, hs, hk, hv, hz, he):
  +W = U32.to_nat(wi)
  +T = U32.to_nat(to)
  +X = Nat.sub(T, SS(wi, o))
  +hd = C.ok_d(len, t, d, h)
  +hf = C.ok_full(len, t, d, h)
  +a1 = AB.subst(Nat, y => {Nat.is_le(T, y) == True{} : Bool}, Nat.mul(Nat.add(W, 1n), 4n), Nat.add(Nat.mul(W, 4n), 4n), mul4s(W), he)
  +a2 = AB.subst(Nat, y => {Nat.is_le(y, Nat.add(Nat.mul(W, 4n), 4n)) == True{} : Bool}, T, Nat.add(SS(wi, o), X),
    Equal.sym(Nat, Nat.add(SS(wi, o), X), T, N.le_sub_add(SS(wi, o), T, hs)), a1)
  +a3 = AB.subst(Nat, y => {Nat.is_le(y, Nat.add(Nat.mul(W, 4n), 4n)) == True{} : Bool}, Nat.add(Nat.add(Nat.mul(W, 4n), o), X), Nat.add(Nat.mul(W, 4n), Nat.add(o, X)),
    N.add_assoc(Nat.mul(W, 4n), o, X), a2)
  +a4 = N.le_sub_r(o, X, 4n, le_cancel(Nat.mul(W, 4n), Nat.add(o, X), 4n, a3))
  +hn = AB.subst(Nat, y => {Nat.is_le(X, y) == True{} : Bool}, Nat.sub(4n, o), List.length(&2, U32, AW(t, wi, o)),
    Equal.sym(Nat, List.length(&2, U32, AW(t, wi, o)), Nat.sub(4n, o), awl(t, wi, o)), a4)
  +RHS = D.first(UB(t), SS(wi, o), T, c)
  %Equal.sym(U32, U32.min(4294967295, to), to, min_top(to, d, hd, N.le_trans(T, U32.to_nat(len), Nat.mul(4n, Nat.pow(2n, d)), ht, C.ok_len(len, t, d, h)))) :
    {U32.to_nat(_) == RHS : Nat}
  %Equal.sym(List<&2, U32>, List.drop(&2, U32, UB(t), SS(wi, o)), List.append(&2, U32, AW(t, wi, o), BW(t, wi)), dw(t, d, wi, o, hf, hd, hk, N.lt_to_le(o, 4n, ho))) :
    {T == Nat.add(SS(wi, o), D.run_len(List.take(&2, U32, _, X), c)) : Nat}
  %Equal.sym(Nat, D.run_len(List.take(&2, U32, List.append(&2, U32, AW(t, wi, o), BW(t, wi)), X), c), X,
    run_none(AW(t, wi, o), BW(t, wi), X, c, hd_eq(AW(t, wi, o), c), {==}, nohit_run(t, wi, o, v, c, hv, hz), hn)) :
    {T == Nat.add(SS(wi, o), _) : Nat}
  Equal.sym(Nat, Nat.add(SS(wi, o), X), T, N.le_sub_add(SS(wi, o), T, hs))

# An unflagged word that is not the last: the search goes on at the next word.
law fskip:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +to: U32
  for +c: U32
  for +wi: U32
  for +o: Nat
  for +v: U32
  for +k: Nat
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +ho: {Nat.is_lt(o, 4n) == True{} : Bool}
  for +hs: {Nat.is_le(SS(wi, o), U32.to_nat(to)) == True{} : Bool}
  for +hk: {Nat.is_lt(U32.to_nat(wi), Nat.pow(2n, d)) == True{} : Bool}
  for +hv: {FW.P0(v) == Nat.add(o, D.run_len(AW(t, wi, o), c)) : Nat}
  for +hz: {U32.is_zero(FA.zb(v)) == True{} : Bool}
  for +hs1: {Nat.is_le(Nat.mul(Nat.add(U32.to_nat(wi), 1n), 4n), U32.to_nat(to)) == True{} : Bool}
  {D.first(UB(t), SS(wi, o), U32.to_nat(to), c) == D.first(UB(t), Nat.mul(Nat.add(U32.to_nat(wi), 1n), 4n), U32.to_nat(to), c) : Nat}

def fskip(len, t, d, to, c, wi, o, v, k, h, ho, hs, hk, hv, hz, hs1):
  +W = U32.to_nat(wi)
  +T = U32.to_nat(to)
  +S = SS(wi, o)
  +S1 = Nat.mul(Nat.add(W, 1n), 4n)
  +L = Nat.sub(4n, o)
  +hd = C.ok_d(len, t, d, h)
  +hf = C.ok_full(len, t, d, h)
  +eS = Equal.trans(Nat, Nat.add(S, L), Nat.add(Nat.mul(W, 4n), Nat.add(o, L)), S1, N.add_assoc(Nat.mul(W, 4n), o, L),
    Equal.trans(Nat, Nat.add(Nat.mul(W, 4n), Nat.add(o, L)), Nat.add(Nat.mul(W, 4n), 4n), S1,
      Equal.cong(Nat, Nat, y => Nat.add(Nat.mul(W, 4n), y), Nat.add(o, L), 4n, N.le_sub_add(o, 4n, N.lt_to_le(o, 4n, ho))),
      Equal.sym(Nat, S1, Nat.add(Nat.mul(W, 4n), 4n), mul4s(W))))
  +hl0 = N.le_sub_r(S, L, T, AB.subst(Nat, y => {Nat.is_le(y, T) == True{} : Bool}, S1, Nat.add(S, L), Equal.sym(Nat, Nat.add(S, L), S1, eS), hs1))
  +hn = AB.subst(Nat, y => {Nat.is_le(y, Nat.sub(T, S)) == True{} : Bool}, L, List.length(&2, U32, AW(t, wi, o)),
    Equal.sym(Nat, List.length(&2, U32, AW(t, wi, o)), L, awl(t, wi, o)), hl0)
  +RHS = D.first(UB(t), S1, T, c)
  %Equal.sym(List<&2, U32>, List.drop(&2, U32, UB(t), S), List.append(&2, U32, AW(t, wi, o), BW(t, wi)), dw(t, d, wi, o, hf, hd, hk, N.lt_to_le(o, 4n, ho))) :
    {Nat.add(S, D.run_len(List.take(&2, U32, _, Nat.sub(T, S)), c)) == RHS : Nat}
  %Equal.sym(Nat, D.run_len(List.take(&2, U32, List.append(&2, U32, AW(t, wi, o), BW(t, wi)), Nat.sub(T, S)), c),
    Nat.add(List.length(&2, U32, AW(t, wi, o)), D.run_len(List.take(&2, U32, BW(t, wi), Nat.sub(Nat.sub(T, S), List.length(&2, U32, AW(t, wi, o)))), c)),
    run_skip(AW(t, wi, o), BW(t, wi), Nat.sub(T, S), c, hd_eq(AW(t, wi, o), c), {==}, nohit_run(t, wi, o, v, c, hv, hz), hn)) :
    {Nat.add(S, _) == RHS : Nat}
  %Equal.sym(Nat, List.length(&2, U32, AW(t, wi, o)), L, awl(t, wi, o)) :
    {Nat.add(S, Nat.add(_, D.run_len(List.take(&2, U32, BW(t, wi), Nat.sub(Nat.sub(T, S), _)), c))) == RHS : Nat}
  %Equal.sym(Nat, Nat.sub(Nat.sub(T, S), L), Nat.sub(T, Nat.add(S, L)), sub_sub(T, S, L)) :
    {Nat.add(S, Nat.add(L, D.run_len(List.take(&2, U32, BW(t, wi), _), c))) == RHS : Nat}
  %N.add_assoc(S, L, D.run_len(List.take(&2, U32, BW(t, wi), Nat.sub(T, Nat.add(S, L))), c)) :
    {_ == RHS : Nat}
  %Equal.sym(Nat, Nat.add(S, L), S1, eS) :
    {Nat.add(_, D.run_len(List.take(&2, U32, BW(t, wi), Nat.sub(T, _)), c)) == RHS : Nat}
  {==}

# The first byte of the next word starts a fresh search.
law hv0:
  for +t: P.Tree<U32>
  for +wi: U32
  for +c: U32
  for +hc: {U32.is_lt(c, 256) == True{} : Bool}
  {FW.P0(U32.xor(C.WD(t, wi), FA.rep(c))) == Nat.add(0n, D.run_len(AW(t, wi, 0n), c)) : Nat}

def hv0(t, wi, c, hc):
  %Equal.sym(List<&2, U32>, List.drop(&2, U32, C.L4(C.WD(t, wi)), 0n), C.L4(C.WD(t, wi)), X.drop_zero(C.L4(C.WD(t, wi)))) :
    {FW.P0(U32.xor(C.WD(t, wi), FA.rep(c))) == Nat.add(0n, D.run_len(_, c)) : Nat}
  FW.p0_xor(C.WD(t, wi), c, hc)

# The loop invariant, for 1 + k words left (wi's included): the answer, capped
# at to, is the first c from the start o bytes into word wi.
law fi:
  for +k: Nat
  for +z: Bool
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +to: U32
  for +c: U32
  for +wi: U32
  for +o: Nat
  for +v: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +ht: {Nat.is_le(U32.to_nat(to), U32.to_nat(len)) == True{} : Bool}
  for +hc: {U32.is_lt(c, 256) == True{} : Bool}
  for +ho: {Nat.is_lt(o, 4n) == True{} : Bool}
  for +hs: {Nat.is_le(SS(wi, o), U32.to_nat(to)) == True{} : Bool}
  for +he1: {Nat.is_le(U32.to_nat(to), Nat.mul(Nat.add(U32.to_nat(wi), 1n+k), 4n)) == True{} : Bool}
  for +he2: {Nat.is_lt(Nat.mul(Nat.add(U32.to_nat(wi), k), 4n), U32.to_nat(to)) == True{} : Bool}
  for +hv: {FW.P0(v) == Nat.add(o, D.run_len(AW(t, wi, o), c)) : Nat}
  for +hz: {U32.is_zero(FA.zb(v)) == z : Bool}
  {U32.to_nat(U32.min(FG(1n+k, z, wi, FA.zb(v), FA.rep(c), t), to)) == D.first(UB(t), SS(wi, o), U32.to_nat(to), c) : Nat}

def fi(k, z, len, t, d, to, c, wi, o, v, h, ht, hc, ho, hs, he1, he2, hv, hz):
  match k z:
    case 0n False{}:
      fhit(len, t, d, to, c, wi, o, v, h, ht, ho, hs,
        wlt(U32.to_nat(wi), 0n, U32.to_nat(to), U32.to_nat(len), Nat.pow(2n, d), he2, ht, C.ok_len(len, t, d, h)), hv, hz)
    case 1n+q False{}:
      fhit(len, t, d, to, c, wi, o, v, h, ht, ho, hs,
        wlt(U32.to_nat(wi), 1n+q, U32.to_nat(to), U32.to_nat(len), Nat.pow(2n, d), he2, ht, C.ok_len(len, t, d, h)), hv, hz)
    case 0n True{}:
      fnone0(len, t, d, to, c, wi, o, v, h, ht, ho, hs,
        wlt(U32.to_nat(wi), 0n, U32.to_nat(to), U32.to_nat(len), Nat.pow(2n, d), he2, ht, C.ok_len(len, t, d, h)), hv, hz, he1)
    case 1n+q True{}:
      +W = U32.to_nat(wi)
      +T = U32.to_nat(to)
      +j1 = (wi + 1 : U32)
      +v1 = U32.xor(C.WD(t, j1), FA.rep(c))
      +S1 = Nat.mul(Nat.add(W, 1n), 4n)
      +hk = wlt(W, 1n+q, T, U32.to_nat(len), Nat.pow(2n, d), he2, ht, C.ok_len(len, t, d, h))
      +ej1 = C.inc_fits(wi, d, C.ok_d(len, t, d, h), N.lt_le_trans(W, Nat.pow(2n, d), Nat.mul(4n, Nat.pow(2n, d)), hk, pow_le4(Nat.pow(2n, d))))
      +hs1 = N.lt_to_le(S1, T, N.le_lt_trans(S1, Nat.mul(Nat.add(W, 1n+q), 4n), T,
        N.le_mul_r(Nat.add(W, 1n), Nat.add(W, 1n+q), 4n, N.le_add_mono_l(W, 1n, 1n+q, N.le_zero_l(q))), he2))
      +ea = Equal.trans(Nat, Nat.add(Nat.mul(U32.to_nat(j1), 4n), 0n), Nat.mul(U32.to_nat(j1), 4n), S1, N.add_zero(Nat.mul(U32.to_nat(j1), 4n)),
        Equal.cong(Nat, Nat, y => Nat.mul(y, 4n), U32.to_nat(j1), Nat.add(W, 1n), ej1))
      +hsi = AB.subst(Nat, y => {Nat.is_le(y, T) == True{} : Bool}, S1, SS(j1, 0n), Equal.sym(Nat, SS(j1, 0n), S1, ea), hs1)
      +e1 = Equal.trans(Nat, Nat.add(U32.to_nat(j1), 1n+q), Nat.add(Nat.add(W, 1n), 1n+q), Nat.add(W, 1n+(1n+q)),
        Equal.cong(Nat, Nat, y => Nat.add(y, 1n+q), U32.to_nat(j1), Nat.add(W, 1n), ej1), N.add_assoc(W, 1n, 1n+q))
      +he1i = AB.subst(Nat, y => {Nat.is_le(T, Nat.mul(y, 4n)) == True{} : Bool}, Nat.add(W, 1n+(1n+q)), Nat.add(U32.to_nat(j1), 1n+q),
        Equal.sym(Nat, Nat.add(U32.to_nat(j1), 1n+q), Nat.add(W, 1n+(1n+q)), e1), he1)
      +e2 = Equal.trans(Nat, Nat.add(U32.to_nat(j1), q), Nat.add(Nat.add(W, 1n), q), Nat.add(W, 1n+q),
        Equal.cong(Nat, Nat, y => Nat.add(y, q), U32.to_nat(j1), Nat.add(W, 1n), ej1), N.add_assoc(W, 1n, q))
      +he2i = AB.subst(Nat, y => {Nat.is_lt(Nat.mul(y, 4n), T) == True{} : Bool}, Nat.add(W, 1n+q), Nat.add(U32.to_nat(j1), q),
        Equal.sym(Nat, Nat.add(U32.to_nat(j1), q), Nat.add(W, 1n+q), e2), he2)
      +ih = fi(q, U32.is_zero(FA.zb(v1)), len, t, d, to, c, j1, 0n, v1, h, ht, hc, {==}, hsi, he1i, he2i, hv0(t, j1, c, hc), {==})
      +sk = fskip(len, t, d, to, c, wi, o, v, q, h, ho, hs, hk, hv, hz, hs1)
      Equal.trans(Nat, U32.to_nat(U32.min(FG(1n+q, U32.is_zero(FA.zb(v1)), j1, FA.zb(v1), FA.rep(c), t), to)), D.first(UB(t), SS(j1, 0n), T, c), D.first(UB(t), SS(wi, o), T, c),
        ih, Equal.sym(Nat, D.first(UB(t), SS(wi, o), T, c), D.first(UB(t), SS(j1, 0n), T, c),
          Equal.trans(Nat, D.first(UB(t), SS(wi, o), T, c), D.first(UB(t), S1, T, c), D.first(UB(t), SS(j1, 0n), T, c), sk,
            Equal.cong(Nat, Nat, y => D.first(UB(t), y, T, c), S1, SS(j1, 0n), Equal.sym(Nat, SS(j1, 0n), S1, ea)))))

# The top level
# =============

law slice_take:
  for +xs: List<&2, U32>
  for +l: Nat
  for +f: Nat
  for +n: Nat
  for +h: {Nat.is_le(Nat.add(f, n), l) == True{} : Bool}
  {D.slice(List.take(&2, U32, xs, l), f, n) == D.slice(xs, f, n) : List<&2, U32>}

def slice_take(xs, l, f, n, h):
  match xs l f:
    case Nil{} _ _:
      {==}
    case Con{x, t} 0n 0n:
      match n:
        case 0n:
          {==}
        case 1n+q:
          Empty.absurd({D.slice(Nil{}, 0n, 1n+q) == D.slice(x <> t, 0n, 1n+q) : List<&2, U32>}, AB.false_ne_true(h))
    case Con{x, t} 0n 1n+g:
      Empty.absurd({D.slice(Nil{}, 1n+g, n) == D.slice(x <> t, 1n+g, n) : List<&2, U32>}, AB.false_ne_true(h))
    case Con{+x, t} 1n+p 0n:
      match n:
        case 0n:
          {==}
        case 1n+q:
          Equal.cong(List<&2, U32>, List<&2, U32>, y => x <> y, List.take(&2, U32, List.take(&2, U32, t, p), q), List.take(&2, U32, t, q), Q.take_take(t, p, q, h))
    case Con{x, t} 1n+p 1n+g:
      slice_take(t, p, g, n, h)

law le_antisym:
  for +a: Nat
  for +b: Nat
  for +h1: {Nat.is_le(a, b) == True{} : Bool}
  for +h2: {Nat.is_le(b, a) == True{} : Bool}
  {a == b : Nat}

def le_antisym(a, b, h1, h2):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, AB.false_ne_true(h2))
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, AB.false_ne_true(h1))
    case 1n+p 1n+q:
      %le_antisym(p, q, h1, h2) : {1n+p == 1n+_ : Nat}
      {==}

law lt_add_l:
  for +c: Nat
  for +a: Nat
  for +b: Nat
  for +h: {Nat.is_lt(a, b) == True{} : Bool}
  {Nat.is_lt(Nat.add(c, a), Nat.add(c, b)) == True{} : Bool}

def lt_add_l(c, a, b, h):
  match c:
    case 0n:
      h
    case 1n+p:
      lt_add_l(p, a, b, h)

law div_le4:
  for +a: Nat
  for +b: Nat
  for +h: {Nat.is_le(a, b) == True{} : Bool}
  {Nat.is_le(Nat.div(a, 4n), Nat.div(b, 4n)) == True{} : Bool}

def div_le4(a, b, h):
  +qb = Nat.div(b, 4n)
  +rb = Nat.mod(b, 4n)
  +hb = AB.subst(Nat, y => {Nat.is_le(a, y) == True{} : Bool}, b, Nat.add(Nat.mul(qb, 4n), rb), Equal.sym(Nat, Nat.add(Nat.mul(qb, 4n), rb), b, N.div_mod(b, 4n)), h)
  +h1 = N.le_lt_trans(a, Nat.add(Nat.mul(qb, 4n), rb), Nat.add(Nat.mul(qb, 4n), 4n), hb, lt_add_l(Nat.mul(qb, 4n), rb, 4n, N.mod_lt(b, 4n, {==})))
  +h2 = AB.subst(Nat, y => {Nat.is_lt(a, y) == True{} : Bool}, Nat.add(Nat.mul(qb, 4n), 4n), Nat.mul(4n, 1n+qb),
    Equal.trans(Nat, Nat.add(Nat.mul(qb, 4n), 4n), Nat.mul(1n+qb, 4n), Nat.mul(4n, 1n+qb),
      Equal.trans(Nat, Nat.add(Nat.mul(qb, 4n), 4n), Nat.add(4n, Nat.mul(qb, 4n)), Nat.mul(1n+qb, 4n), N.add_comm(Nat.mul(qb, 4n), 4n), {==}),
      N.mul_comm(1n+qb, 4n)), h1)
  Equal.trans(Bool, Nat.is_le(Nat.div(a, 4n), qb), Nat.is_lt(Nat.div(a, 4n), 1n+qb), True{},
    Equal.sym(Bool, Nat.is_lt(Nat.div(a, 4n), 1n+qb), Nat.is_le(Nat.div(a, 4n), qb), N.lt_succ_iff(Nat.div(a, 4n), qb)),
    N.div_lt(a, 4n, 1n+qb, {==}, h2))

# The last word holds byte to - 1: 4E < to <= 4E + 4 for E = (to - 1) / 4.
law last_lt:
  for +tt: Nat
  for +h: {Nat.is_lt(0n, tt) == True{} : Bool}
  {Nat.is_lt(Nat.mul(Nat.div(Nat.sub(tt, 1n), 4n), 4n), tt) == True{} : Bool}

def last_lt(tt, h):
  match tt:
    case 0n:
      Empty.absurd({Nat.is_lt(Nat.mul(Nat.div(Nat.sub(0n, 1n), 4n), 4n), 0n) == True{} : Bool}, AB.false_ne_true(h))
    case 1n+p:
      %Equal.sym(Nat, Nat.sub(p, 0n), p, N.sub_zero(p)) : {Nat.is_lt(Nat.mul(Nat.div(_, 4n), 4n), 1n+p) == True{} : Bool}
      Equal.trans(Bool, Nat.is_lt(Nat.mul(Nat.div(p, 4n), 4n), 1n+p), Nat.is_le(Nat.mul(Nat.div(p, 4n), 4n), p), True{},
        N.lt_succ_iff(Nat.mul(Nat.div(p, 4n), 4n), p),
        AB.subst(Nat, y => {Nat.is_le(Nat.mul(Nat.div(p, 4n), 4n), y) == True{} : Bool}, Nat.add(Nat.mul(Nat.div(p, 4n), 4n), Nat.mod(p, 4n)), p, N.div_mod(p, 4n),
          N.le_add_r(Nat.mul(Nat.div(p, 4n), 4n), Nat.mod(p, 4n))))

law last_le:
  for +tt: Nat
  for +h: {Nat.is_lt(0n, tt) == True{} : Bool}
  {Nat.is_le(tt, Nat.mul(Nat.add(Nat.div(Nat.sub(tt, 1n), 4n), 1n), 4n)) == True{} : Bool}

def last_le(tt, h):
  match tt:
    case 0n:
      Empty.absurd({Nat.is_le(0n, Nat.mul(Nat.add(Nat.div(Nat.sub(0n, 1n), 4n), 1n), 4n)) == True{} : Bool}, AB.false_ne_true(h))
    case 1n+p:
      +q = Nat.div(p, 4n)
      %Equal.sym(Nat, Nat.sub(p, 0n), p, N.sub_zero(p)) : {Nat.is_le(1n+p, Nat.mul(Nat.add(Nat.div(_, 4n), 1n), 4n)) == True{} : Bool}
      %Equal.sym(Nat, Nat.mul(Nat.add(q, 1n), 4n), Nat.add(Nat.mul(q, 4n), 4n), mul4s(q)) : {Nat.is_le(1n+p, _) == True{} : Bool}
      %N.div_mod(p, 4n) : {Nat.is_le(1n+_, Nat.add(Nat.mul(q, 4n), 4n)) == True{} : Bool}
      %N.add_succ(Nat.mul(q, 4n), Nat.mod(p, 4n)) : {Nat.is_le(_, Nat.add(Nat.mul(q, 4n), 4n)) == True{} : Bool}
      N.le_add_mono_l(Nat.mul(q, 4n), 1n+Nat.mod(p, 4n), 4n,
        Equal.trans(Bool, Nat.is_le(1n+Nat.mod(p, 4n), 4n), Nat.is_lt(Nat.mod(p, 4n), 4n), True{}, N.le_succ_lt(Nat.mod(p, 4n), 4n), N.mod_lt(p, 4n, {==})))

law lt_sub1:
  for +f: Nat
  for +tt: Nat
  for +h: {Nat.is_lt(f, tt) == True{} : Bool}
  {Nat.is_le(f, Nat.sub(tt, 1n)) == True{} : Bool}

def lt_sub1(f, tt, h):
  match tt:
    case 0n:
      Empty.absurd({Nat.is_le(f, 0n) == True{} : Bool}, AB.lt_zero_absurd(f, h))
    case 1n+p:
      %Equal.sym(Nat, Nat.sub(p, 0n), p, N.sub_zero(p)) : {Nat.is_le(f, _) == True{} : Bool}
      Equal.trans(Bool, Nat.is_le(f, p), Nat.is_lt(f, 1n+p), True{}, Equal.sym(Bool, Nat.is_lt(f, 1n+p), Nat.is_le(f, p), N.lt_succ_iff(f, p)), h)

law div_self_le:
  for +a: Nat
  {Nat.is_le(Nat.div(a, 4n), a) == True{} : Bool}

def div_self_le(a):
  +h = Equal.trans(Bool, Nat.is_lt(a, 1n+Nat.add(a, Nat.mul(3n, 1n+a))), Nat.is_le(a, Nat.add(a, Nat.mul(3n, 1n+a))), True{},
    N.lt_succ_iff(a, Nat.add(a, Nat.mul(3n, 1n+a))), N.le_add_r(a, Nat.mul(3n, 1n+a)))
  Equal.trans(Bool, Nat.is_le(Nat.div(a, 4n), a), Nat.is_lt(Nat.div(a, 4n), 1n+a), True{},
    Equal.sym(Bool, Nat.is_lt(Nat.div(a, 4n), 1n+a), Nat.is_le(Nat.div(a, 4n), a), N.lt_succ_iff(Nat.div(a, 4n), a)),
    N.div_lt(a, 4n, 1n+a, {==}, h))

law sub1_lt:
  for +tt: Nat
  for +h: {Nat.is_lt(0n, tt) == True{} : Bool}
  {Nat.is_lt(Nat.sub(tt, 1n), tt) == True{} : Bool}

def sub1_lt(tt, h):
  match tt:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, AB.false_ne_true(h))
    case 1n+p:
      %Equal.sym(Nat, Nat.sub(p, 0n), p, N.sub_zero(p)) : {Nat.is_lt(_, 1n+p) == True{} : Bool}
      Equal.trans(Bool, Nat.is_lt(p, 1n+p), Nat.is_le(p, p), True{}, N.lt_succ_iff(p, p), N.le_refl(p))

# from < to: the loop runs 1 + k0 words, from word from >> 2 to word (to - 1) >> 2.
law fview_lt:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +from: U32
  for +to: U32
  for +c: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +ht: {Nat.is_le(U32.to_nat(to), U32.to_nat(len)) == True{} : Bool}
  for +hc: {U32.is_lt(c, 256) == True{} : Bool}
  for +hlt: {Nat.is_lt(U32.to_nat(from), U32.to_nat(to)) == True{} : Bool}
  {U32.to_nat(U32.min(FG(U32.to_nat(((((to - 1 : U32) >> 2n : U32) - (from >> 2n : U32) : U32) + 1 : U32)), U32.is_zero(M0(t, from, FA.rep(c))), (from >> 2n : U32), M0(t, from, FA.rep(c)), FA.rep(c), t), to)) == D.first(D.view(C.BT(len, t)), U32.to_nat(from), U32.to_nat(to), c) : Nat}

def fview_lt(len, t, d, from, to, c, h, ht, hc, hlt):
  +F = U32.to_nat(from)
  +T = U32.to_nat(to)
  +wi0 = (from >> 2n : U32)
  +W0 = U32.to_nat(wi0)
  +o0 = U32.to_nat((from .&. 3 : U32))
  +ee = ((to - 1 : U32) >> 2n : U32)
  +E = U32.to_nat(ee)
  +rc = FA.rep(c)
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
      div_le4(F, Nat.sub(T, 1n), lt_sub1(F, T, hlt))))
  +k0 = Nat.sub(E, W0)
  +esub = U.to_nat_sub_le(ee, wi0, Equal.trans(Bool, U32.is_le(wi0, ee), Nat.is_le(W0, E), True{}, U.is_le_to_nat(wi0, ee), hWE))
  +hET = N.le_lt_trans(E, Nat.sub(T, 1n), T,
    AB.subst(Nat, y => {Nat.is_le(y, Nat.sub(T, 1n)) == True{} : Bool}, Nat.div(Nat.sub(T, 1n), 4n), E, Equal.sym(Nat, E, Nat.div(Nat.sub(T, 1n), 4n), eE), div_self_le(Nat.sub(T, 1n))),
    sub1_lt(T, h0T))
  +ek = C.inc_fits((ee - wi0 : U32), d, hd,
    AB.subst(Nat, y => {Nat.is_lt(y, M4) == True{} : Bool}, k0, U32.to_nat((ee - wi0 : U32)), Equal.sym(Nat, U32.to_nat((ee - wi0 : U32)), k0, esub),
      N.le_lt_trans(k0, E, M4, H.sub_le(E, W0), N.lt_le_trans(E, T, M4, hET, hTM))))
  +en = Equal.trans(Nat, U32.to_nat(((ee - wi0 : U32) + 1 : U32)), Nat.add(U32.to_nat((ee - wi0 : U32)), 1n), 1n+k0, ek,
    Equal.trans(Nat, Nat.add(U32.to_nat((ee - wi0 : U32)), 1n), Nat.add(k0, 1n), 1n+k0, Equal.cong(Nat, Nat, y => Nat.add(y, 1n), U32.to_nat((ee - wi0 : U32)), k0, esub), N.add_one(k0)))
  +eSF = Equal.trans(Nat, SS(wi0, o0), Nat.add(Nat.mul(Nat.div(F, 4n), 4n), Nat.mod(F, 4n)), F,
    Equal.trans(Nat, Nat.add(Nat.mul(W0, 4n), o0), Nat.add(Nat.mul(Nat.div(F, 4n), 4n), o0), Nat.add(Nat.mul(Nat.div(F, 4n), 4n), Nat.mod(F, 4n)),
      Equal.cong(Nat, Nat, y => Nat.add(Nat.mul(y, 4n), o0), W0, Nat.div(F, 4n), eW0),
      Equal.cong(Nat, Nat, y => Nat.add(Nat.mul(Nat.div(F, 4n), 4n), y), o0, Nat.mod(F, 4n), eo)),
    N.div_mod(F, 4n))
  +ho0 = AB.subst(Nat, y => {Nat.is_lt(y, 4n) == True{} : Bool}, Nat.mod(F, 4n), o0, Equal.sym(Nat, o0, Nat.mod(F, 4n), eo), N.mod_lt(F, 4n, {==}))
  +hs0 = AB.subst(Nat, y => {Nat.is_le(y, T) == True{} : Bool}, F, SS(wi0, o0), Equal.sym(Nat, SS(wi0, o0), F, eSF), N.lt_to_le(F, T, hlt))
  +eWk = N.le_sub_add(W0, E, hWE)
  +eA = Equal.trans(Nat, Nat.add(W0, 1n+k0), 1n+Nat.add(W0, k0), Nat.add(Nat.div(Nat.sub(T, 1n), 4n), 1n), N.add_succ(W0, k0),
    Equal.trans(Nat, 1n+Nat.add(W0, k0), 1n+E, Nat.add(Nat.div(Nat.sub(T, 1n), 4n), 1n), Equal.cong(Nat, Nat, y => 1n+y, Nat.add(W0, k0), E, eWk),
      Equal.trans(Nat, 1n+E, Nat.add(E, 1n), Nat.add(Nat.div(Nat.sub(T, 1n), 4n), 1n), Equal.sym(Nat, Nat.add(E, 1n), 1n+E, N.add_one(E)),
        Equal.cong(Nat, Nat, y => Nat.add(y, 1n), E, Nat.div(Nat.sub(T, 1n), 4n), eE))))
  +he1 = AB.subst(Nat, y => {Nat.is_le(T, Nat.mul(y, 4n)) == True{} : Bool}, Nat.add(Nat.div(Nat.sub(T, 1n), 4n), 1n), Nat.add(W0, 1n+k0),
    Equal.sym(Nat, Nat.add(W0, 1n+k0), Nat.add(Nat.div(Nat.sub(T, 1n), 4n), 1n), eA), last_le(T, h0T))
  +eB = Equal.trans(Nat, Nat.add(W0, k0), E, Nat.div(Nat.sub(T, 1n), 4n), eWk, eE)
  +he2 = AB.subst(Nat, y => {Nat.is_lt(Nat.mul(y, 4n), T) == True{} : Bool}, Nat.div(Nat.sub(T, 1n), 4n), Nat.add(W0, k0),
    Equal.sym(Nat, Nat.add(W0, k0), Nat.div(Nat.sub(T, 1n), 4n), eB), last_lt(T, h0T))
  +fiv = fi(k0, U32.is_zero(M0(t, from, rc)), len, t, d, to, c, wi0, o0, U32.or(U32.xor(C.WD(t, wi0), rc), U32.not(FA.low(from))),
    h, ht, hc, ho0, hs0, he1, he2, FW.p0_low(C.WD(t, wi0), c, from, hc), {==})
  +hh = AB.subst(Nat, y => {Nat.is_le(y, U32.to_nat(len)) == True{} : Bool}, T, Nat.add(F, Nat.sub(T, F)),
    Equal.sym(Nat, Nat.add(F, Nat.sub(T, F)), T, N.le_sub_add(F, T, N.lt_to_le(F, T, hlt))), ht)
  +E2 = Equal.trans(Nat, D.first(UB(t), SS(wi0, o0), T, c), D.first(UB(t), F, T, c), D.first(D.view(C.BT(len, t)), F, T, c),
    Equal.cong(Nat, Nat, y => D.first(UB(t), y, T, c), SS(wi0, o0), F, eSF),
    Equal.sym(Nat, D.first(D.view(C.BT(len, t)), F, T, c), D.first(UB(t), F, T, c),
      Equal.cong(List<&2, U32>, Nat, y => Nat.add(F, D.run_len(y, c)), D.slice(List.take(&2, U32, UB(t), U32.to_nat(len)), F, Nat.sub(T, F)), D.slice(UB(t), F, Nat.sub(T, F)),
        slice_take(UB(t), U32.to_nat(len), F, Nat.sub(T, F), hh))))
  %Equal.sym(Nat, U32.to_nat(((ee - wi0 : U32) + 1 : U32)), 1n+k0, en) :
    {U32.to_nat(U32.min(FG(_, U32.is_zero(M0(t, from, rc)), wi0, M0(t, from, rc), rc, t), to)) == D.first(D.view(C.BT(len, t)), F, T, c) : Nat}
  Equal.trans(Nat, U32.to_nat(U32.min(FG(1n+k0, U32.is_zero(M0(t, from, rc)), wi0, M0(t, from, rc), rc, t), to)), D.first(UB(t), SS(wi0, o0), T, c),
    D.first(D.view(C.BT(len, t)), F, T, c), fiv, E2)

# The answer as a number, split on to <= from (no words: the answer is to = from).
law fview_go:
  for +b: Bool
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +from: U32
  for +to: U32
  for +c: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hft: {U32.is_le(from, to) == True{} : Bool}
  for +ht: {Nat.is_le(U32.to_nat(to), U32.to_nat(len)) == True{} : Bool}
  for +hc: {U32.is_lt(c, 256) == True{} : Bool}
  for +hb: {U32.is_le(to, from) == b : Bool}
  {U32.to_nat(U32.min(FG(Bool.pick(Nat, b, 0n, U32.to_nat(((((to - 1 : U32) >> 2n : U32) - (from >> 2n : U32) : U32) + 1 : U32))), U32.is_zero(M0(t, from, FA.rep(c))), (from >> 2n : U32), M0(t, from, FA.rep(c)), FA.rep(c), t), to)) == D.first(D.view(C.BT(len, t)), U32.to_nat(from), U32.to_nat(to), c) : Nat}

def fview_go(b, len, t, d, from, to, c, h, hft, ht, hc, hb):
  match b:
    case True{}:
      +F = U32.to_nat(from)
      +T = U32.to_nat(to)
      +xs = D.view(C.BT(len, t))
      +hd = C.ok_d(len, t, d, h)
      +eTF = le_antisym(T, F, Equal.trans(Bool, Nat.is_le(T, F), U32.is_le(to, from), True{}, Equal.sym(Bool, U32.is_le(to, from), Nat.is_le(T, F), U.is_le_to_nat(to, from)), hb),
        Equal.trans(Bool, Nat.is_le(F, T), U32.is_le(from, to), True{}, Equal.sym(Bool, U32.is_le(from, to), Nat.is_le(F, T), U.is_le_to_nat(from, to)), hft))
      %Equal.sym(U32, U32.min(4294967295, to), to, min_top(to, d, hd, N.le_trans(T, U32.to_nat(len), Nat.mul(4n, Nat.pow(2n, d)), ht, C.ok_len(len, t, d, h)))) :
        {U32.to_nat(_) == D.first(xs, F, T, c) : Nat}
      %Equal.sym(Nat, T, F, eTF) : {_ == D.first(xs, F, _, c) : Nat}
      %Equal.sym(Nat, Nat.sub(F, F), 0n, H.sub_self(F)) : {F == Nat.add(F, D.run_len(D.slice(xs, F, _), c)) : Nat}
      %Equal.sym(List<&2, U32>, D.slice(xs, F, 0n), Nil{}, X.slice_zero(xs, F)) : {F == Nat.add(F, D.run_len(_, c)) : Nat}
      Equal.sym(Nat, Nat.add(F, 0n), F, N.add_zero(F))
    case False{}:
      fview_lt(len, t, d, from, to, c, h, ht, hc,
        N.not_le_lt(U32.to_nat(to), U32.to_nat(from), Equal.trans(Bool, Nat.is_le(U32.to_nat(to), U32.to_nat(from)), U32.is_le(to, from), False{},
          Equal.sym(Bool, U32.is_le(to, from), Nat.is_le(U32.to_nat(to), U32.to_nat(from)), U.is_le_to_nat(to, from)), hb)))

# fast find equals the reference find, Bytes included.
law fast_find_t:
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
  {FA.find(C.BT(len, t), from, to, c) == B.find(C.BT(len, t), from, to, c) : D.Bytes & U32}

def fast_find_t(len, t, d, from, to, c, h, hft, ht, hc):
  +rc = FA.rep(c)
  +MN = U32.min(FG(FA.words(from, to), U32.is_zero(M0(t, from, rc)), (from >> 2n : U32), M0(t, from, rc), rc, t), to)
  +SN = Pair.snd(D.Bytes, U32, B.find(C.BT(len, t), from, to, c))
  %Equal.sym(D.Bytes & U32, FA.find(C.BT(len, t), from, to, c), (C.BT(len, t), MN), fast_eq(len, t, from, to, c)) :
    {_ == B.find(C.BT(len, t), from, to, c) : D.Bytes & U32}
  %Equal.sym(D.Bytes & U32, B.find(C.BT(len, t), from, to, c), (C.BT(len, t), SN), F.find_pair_t(len, t, from, to, c)) :
    {(C.BT(len, t), MN) == _ : D.Bytes & U32}
  Equal.cong(U32, D.Bytes & U32, y => (C.BT(len, t), y), MN, SN,
    U.to_nat_inj(MN, SN, Equal.trans(Nat, U32.to_nat(MN), D.first(D.view(C.BT(len, t)), U32.to_nat(from), U32.to_nat(to), c), U32.to_nat(SN),
      fview_go(U32.is_le(to, from), len, t, d, from, to, c, h, hft, ht, hc, {==}),
      Equal.sym(Nat, U32.to_nat(SN), D.first(D.view(C.BT(len, t)), U32.to_nat(from), U32.to_nat(to), c), F.find_view_t(len, t, d, from, to, c, h, hft, ht, hc)))))
