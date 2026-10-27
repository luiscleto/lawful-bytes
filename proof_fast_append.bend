import Base
import ./defs.bend as D
import ./bytes.bend as B
import ./fast.bend as FA
import ./proof_seq.bend as Q
import ./proof_core.bend as C
import ./proof_ops.bend as O
import ./proof_append.bend as X
import ./proof_shift.bend as H
import ../lawful-words/defs.bend as W
import ../lawful-words/proof_nat.bend as N
import ../lawful-words/proof_u32.bend as U
import ../lawful-words/proof_bytes.bend as Y
import ../lawful-arrays/defs.bend as A
import ../lawful-arrays/proof_base.bend as AB
import ../lawful-arrays/proof_tree.bend as P
import ../lawful-arrays/proof_index.bend as I

# fast.bend's append on the mirror. The first bytes go through bytes.bend's
# append (X.append_*_t), up to dst's next word boundary; then append.words
# writes whole words, each the merge of two src words. AWT computes the tree
# append.words leaves (aw_eq), and the view invariant (av) says that after the
# words written so far the bytes in use are the target's. Up to 3 bytes past
# the new length come from src bytes past s + n: they are outside the view.

# Lists
# =====

law drop_drop:
  for +xs: List<&2, U32>
  for +a: Nat
  for +b: Nat
  {List.drop(&2, U32, List.drop(&2, U32, xs, a), b) == List.drop(&2, U32, xs, Nat.add(a, b)) : List<&2, U32>}

def drop_drop(xs, a, b):
  match xs a:
    case Nil{} _:
      {==}
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+p:
      drop_drop(t, p, b)

# A list whose first element is b.
law tcons:
  for +ys: List<&2, U32>
  for +b: U32
  for +m: Nat
  for +rest: List<&2, U32>
  for +h: {List.get(&2, U32, ys, 0n) == Some{b} : Maybe<&2, U32>}
  for +ht: {List.take(&2, U32, List.drop(&2, U32, ys, 1n), m) == rest : List<&2, U32>}
  {List.take(&2, U32, ys, 1n+m) == b <> rest : List<&2, U32>}

def tcons(ys, b, m, rest, h, ht):
  match ys:
    case Nil{}:
      Empty.absurd({List.take(&2, U32, Nil{}, 1n+m) == b <> rest : List<&2, U32>}, X.none_some(b, h))
    case Con{+y, t}:
      %Equal.sym(U32, y, b, X.some_inj(y, b, h)) : {_ <> List.take(&2, U32, t, m) == b <> rest : List<&2, U32>}
      %Equal.sym(List<&2, U32>, List.take(&2, U32, t, m), rest,
        AB.subst(List<&2, U32>, z => {List.take(&2, U32, z, m) == rest : List<&2, U32>}, List.drop(&2, U32, t, 0n), t, X.drop_zero(t), ht)) :
        {b <> _ == b <> rest : List<&2, U32>}
      {==}

# The first m (<= 4) elements of ys are b0 .. b3, given each one asked for.
law tg1:
  for +ys: List<&2, U32>
  for +m: Nat
  for +b0: U32
  for +hm: {Nat.is_le(m, 1n) == True{} : Bool}
  for g0: {Nat.is_lt(0n, m) == True{} : Bool} -> {List.get(&2, U32, ys, 0n) == Some{b0} : Maybe<&2, U32>}
  {List.take(&2, U32, ys, m) == List.take(&2, U32, [b0], m) : List<&2, U32>}

def tg1(ys, m, b0, hm, g0):
  match m:
    case 0n:
      Q.take_zero(ys)
    case 1n+m1:
      match m1:
        case 0n:
          tcons(ys, b0, 0n, Nil{}, g0({==}), Q.take_zero(List.drop(&2, U32, ys, 1n)))
        case 1n+m2:
          Empty.absurd({List.take(&2, U32, ys, 2n+m2) == List.take(&2, U32, [b0], 2n+m2) : List<&2, U32>}, AB.false_ne_true(hm))

law tg2:
  for +ys: List<&2, U32>
  for +m: Nat
  for +b0: U32
  for +b1: U32
  for +hm: {Nat.is_le(m, 2n) == True{} : Bool}
  for g0: {Nat.is_lt(0n, m) == True{} : Bool} -> {List.get(&2, U32, ys, 0n) == Some{b0} : Maybe<&2, U32>}
  for g1: {Nat.is_lt(1n, m) == True{} : Bool} -> {List.get(&2, U32, ys, 1n) == Some{b1} : Maybe<&2, U32>}
  {List.take(&2, U32, ys, m) == List.take(&2, U32, [b0, b1], m) : List<&2, U32>}

def tg2(ys, m, b0, b1, hm, g0, g1):
  match m:
    case 0n:
      Q.take_zero(ys)
    case 1n+m1:
      tcons(ys, b0, m1, List.take(&2, U32, [b1], m1), g0({==}),
        tg1(List.drop(&2, U32, ys, 1n), m1, b1, hm,
          h => Equal.trans(Maybe<&2, U32>, List.get(&2, U32, List.drop(&2, U32, ys, 1n), 0n), List.get(&2, U32, ys, 1n), Some{b1},
            H.get_drop(ys, 1n, 0n), g1(h))))

law tg3:
  for +ys: List<&2, U32>
  for +m: Nat
  for +b0: U32
  for +b1: U32
  for +b2: U32
  for +hm: {Nat.is_le(m, 3n) == True{} : Bool}
  for g0: {Nat.is_lt(0n, m) == True{} : Bool} -> {List.get(&2, U32, ys, 0n) == Some{b0} : Maybe<&2, U32>}
  for g1: {Nat.is_lt(1n, m) == True{} : Bool} -> {List.get(&2, U32, ys, 1n) == Some{b1} : Maybe<&2, U32>}
  for g2: {Nat.is_lt(2n, m) == True{} : Bool} -> {List.get(&2, U32, ys, 2n) == Some{b2} : Maybe<&2, U32>}
  {List.take(&2, U32, ys, m) == List.take(&2, U32, [b0, b1, b2], m) : List<&2, U32>}

def tg3(ys, m, b0, b1, b2, hm, g0, g1, g2):
  match m:
    case 0n:
      Q.take_zero(ys)
    case 1n+m1:
      tcons(ys, b0, m1, List.take(&2, U32, [b1, b2], m1), g0({==}),
        tg2(List.drop(&2, U32, ys, 1n), m1, b1, b2, hm,
          h => Equal.trans(Maybe<&2, U32>, List.get(&2, U32, List.drop(&2, U32, ys, 1n), 0n), List.get(&2, U32, ys, 1n), Some{b1},
            H.get_drop(ys, 1n, 0n), g1(h)),
          h => Equal.trans(Maybe<&2, U32>, List.get(&2, U32, List.drop(&2, U32, ys, 1n), 1n), List.get(&2, U32, ys, 2n), Some{b2},
            H.get_drop(ys, 1n, 1n), g2(h))))

law tg4:
  for +ys: List<&2, U32>
  for +m: Nat
  for +b0: U32
  for +b1: U32
  for +b2: U32
  for +b3: U32
  for +hm: {Nat.is_le(m, 4n) == True{} : Bool}
  for g0: {Nat.is_lt(0n, m) == True{} : Bool} -> {List.get(&2, U32, ys, 0n) == Some{b0} : Maybe<&2, U32>}
  for g1: {Nat.is_lt(1n, m) == True{} : Bool} -> {List.get(&2, U32, ys, 1n) == Some{b1} : Maybe<&2, U32>}
  for g2: {Nat.is_lt(2n, m) == True{} : Bool} -> {List.get(&2, U32, ys, 2n) == Some{b2} : Maybe<&2, U32>}
  for g3: {Nat.is_lt(3n, m) == True{} : Bool} -> {List.get(&2, U32, ys, 3n) == Some{b3} : Maybe<&2, U32>}
  {List.take(&2, U32, ys, m) == List.take(&2, U32, [b0, b1, b2, b3], m) : List<&2, U32>}

def tg4(ys, m, b0, b1, b2, b3, hm, g0, g1, g2, g3):
  match m:
    case 0n:
      Q.take_zero(ys)
    case 1n+m1:
      tcons(ys, b0, m1, List.take(&2, U32, [b1, b2, b3], m1), g0({==}),
        tg3(List.drop(&2, U32, ys, 1n), m1, b1, b2, b3, hm,
          h => Equal.trans(Maybe<&2, U32>, List.get(&2, U32, List.drop(&2, U32, ys, 1n), 0n), List.get(&2, U32, ys, 1n), Some{b1},
            H.get_drop(ys, 1n, 0n), g1(h)),
          h => Equal.trans(Maybe<&2, U32>, List.get(&2, U32, List.drop(&2, U32, ys, 1n), 1n), List.get(&2, U32, ys, 2n), Some{b2},
            H.get_drop(ys, 1n, 1n), g2(h)),
          h => Equal.trans(Maybe<&2, U32>, List.get(&2, U32, List.drop(&2, U32, ys, 1n), 2n), List.get(&2, U32, ys, 3n), Some{b3},
            H.get_drop(ys, 1n, 2n), g3(h))))

# Writing word q replaces bytes 4q .. 4q+3 of the unpacked list.
law us1:
  for +ws: List<&2, U32>
  for +q: Nat
  for +x: U32
  for +m: Nat
  for +hq: {Nat.is_lt(q, List.length(&2, U32, ws)) == True{} : Bool}
  for +hm: {Nat.is_le(m, 4n) == True{} : Bool}
  {List.take(&2, U32, D.unpack(List.set(&2, U32, ws, q, x)), Nat.add(Nat.mul(q, 4n), m)) == List.append(&2, U32, List.take(&2, U32, D.unpack(ws), Nat.mul(q, 4n)), List.take(&2, U32, C.L4(x), m)) : List<&2, U32>}

def us1(ws, q, x, m, hq, hm):
  match ws q:
    case Nil{} _:
      Empty.absurd({List.take(&2, U32, Nil{}, Nat.add(Nat.mul(q, 4n), m)) == List.append(&2, U32, List.take(&2, U32, Nil{}, Nat.mul(q, 4n)), List.take(&2, U32, C.L4(x), m)) : List<&2, U32>},
        AB.lt_zero_absurd(q, hq))
    case Con{w0, t} 0n:
      Q.take_append_l(C.L4(x), D.unpack(t), m, hm)
    case Con{+w0, t} 1n+p:
      %us1(t, p, x, m, hq, hm) :
        {W.byte(w0, 0n) <> W.byte(w0, 1n) <> W.byte(w0, 2n) <> W.byte(w0, 3n) <> List.take(&2, U32, D.unpack(List.set(&2, U32, t, p, x)), Nat.add(Nat.mul(p, 4n), m))
          == W.byte(w0, 0n) <> W.byte(w0, 1n) <> W.byte(w0, 2n) <> W.byte(w0, 3n) <> _ : List<&2, U32>}
      {==}

law take_split:
  for +ys: List<&2, U32>
  for +a: Nat
  for +m: Nat
  {List.append(&2, U32, List.take(&2, U32, ys, a), List.take(&2, U32, List.drop(&2, U32, ys, a), m)) == List.take(&2, U32, ys, Nat.add(a, m)) : List<&2, U32>}

def take_split(ys, a, m):
  match ys a:
    case Nil{} _:
      {==}
    case Con{y, t} 0n:
      {==}
    case Con{+y, t} 1n+p:
      %take_split(t, p, m) :
        {y <> List.append(&2, U32, List.take(&2, U32, t, p), List.take(&2, U32, List.drop(&2, U32, t, p), m)) == y <> _ : List<&2, U32>}
      {==}

law slice_split:
  for +xs: List<&2, U32>
  for +s: Nat
  for +a: Nat
  for +b: Nat
  {List.append(&2, U32, D.slice(xs, s, a), D.slice(xs, Nat.add(s, a), b)) == D.slice(xs, s, Nat.add(a, b)) : List<&2, U32>}

def slice_split(xs, s, a, b):
  %drop_drop(xs, s, a) :
    {List.append(&2, U32, D.slice(xs, s, a), List.take(&2, U32, _, b)) == D.slice(xs, s, Nat.add(a, b)) : List<&2, U32>}
  take_split(List.drop(&2, U32, xs, s), a, b)

# A slice of the first l elements, inside them.
law slice_take:
  for +xs: List<&2, U32>
  for +l: Nat
  for +q: Nat
  for +n: Nat
  for +h: {Nat.is_le(Nat.add(q, n), l) == True{} : Bool}
  {D.slice(List.take(&2, U32, xs, l), q, n) == List.take(&2, U32, List.drop(&2, U32, xs, q), n) : List<&2, U32>}

def slice_take(xs, l, q, n, h):
  match xs l q n:
    case Nil{} _ _ _:
      {==}
    case Con{x, t} 0n 0n 0n:
      {==}
    case Con{x, t} 0n 0n 1n+n1:
      Empty.absurd({List.take(&2, U32, Nil{}, 1n+n1) == x <> List.take(&2, U32, t, n1) : List<&2, U32>}, AB.false_ne_true(h))
    case Con{x, t} 0n 1n+q1 _:
      Empty.absurd({List.take(&2, U32, List.drop(&2, U32, Nil{}, 1n+q1), n) == List.take(&2, U32, List.drop(&2, U32, t, q1), n) : List<&2, U32>},
        AB.false_ne_true(h))
    case Con{x, t} 1n+l1 0n _:
      Q.take_take(x <> t, 1n+l1, n, h)
    case Con{x, t} 1n+l1 1n+q1 _:
      slice_take(t, l1, q1, n, h)

law slice_length:
  for +xs: List<&2, U32>
  for +s: Nat
  for +a: Nat
  for +h: {Nat.is_le(Nat.add(s, a), List.length(&2, U32, xs)) == True{} : Bool}
  {List.length(&2, U32, D.slice(xs, s, a)) == a : Nat}

def slice_length(xs, s, a, h):
  Q.take_length(List.drop(&2, U32, xs, s), a,
    AB.subst(Nat, y => {Nat.is_le(a, y) == True{} : Bool}, Nat.sub(List.length(&2, U32, xs), s), List.length(&2, U32, List.drop(&2, U32, xs, s)),
      Equal.sym(Nat, List.length(&2, U32, List.drop(&2, U32, xs, s)), Nat.sub(List.length(&2, U32, xs), s), H.drop_length(xs, s)),
      N.le_sub_r(s, a, List.length(&2, U32, xs), h)))

# Nat
# ===

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

law min_l:
  for +a: Nat
  for +b: Nat
  for +h: {Nat.is_lt(a, b) == True{} : Bool}
  {Nat.min(a, b) == a : Nat}

def min_l(a, b, h):
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      Empty.absurd({0n == 1n+p : Nat}, AB.false_ne_true(h))
    case 1n+p 1n+q:
      %min_l(p, q, h) : {1n+Nat.min(p, q) == 1n+_ : Nat}
      {==}

law min_r:
  for +a: Nat
  for +b: Nat
  for +h: {Nat.is_lt(a, b) == False{} : Bool}
  {Nat.min(a, b) == b : Nat}

def min_r(a, b, h):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, AB.true_ne_false(h))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      %min_r(p, q, h) : {1n+Nat.min(p, q) == 1n+_ : Nat}
      {==}

law min_le:
  for +a: Nat
  for +b: Nat
  {Nat.is_le(Nat.min(a, b), b) == True{} : Bool}

def min_le(a, b):
  match a b:
    case 0n _:
      N.le_zero_l(b)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      min_le(p, q)

law lt_w:
  for +w: Nat
  for +x: Nat
  for +pp: Nat
  for +h: {Nat.is_lt(Nat.add(Nat.mul(w, 4n), x), Nat.mul(4n, pp)) == True{} : Bool}
  {Nat.is_lt(w, pp) == True{} : Bool}

def lt_w(w, x, pp, h):
  N.lt_mul_cancel(4n, w, pp,
    AB.subst(Nat, y => {Nat.is_lt(y, Nat.mul(4n, pp)) == True{} : Bool}, Nat.mul(w, 4n), Nat.mul(4n, w), N.mul_comm(w, 4n),
      N.le_lt_trans(Nat.mul(w, 4n), Nat.add(Nat.mul(w, 4n), x), Nat.mul(4n, pp), N.le_add_r(Nat.mul(w, 4n), x), h)))

law lt8:
  for +r: Nat
  for +j: Nat
  for +hr: {Nat.is_lt(r, 4n) == True{} : Bool}
  for +hj: {Nat.is_lt(j, 4n) == True{} : Bool}
  {Nat.is_lt(Nat.add(r, j), 8n) == True{} : Bool}

def lt8(r, j, hr, hj):
  match r:
    case 0n:
      N.lt_trans(j, 4n, 8n, hj, {==})
    case 1n+r1:
      match r1:
        case 0n:
          N.lt_trans(j, 4n, 7n, hj, {==})
        case 1n+r2:
          match r2:
            case 0n:
              N.lt_trans(j, 4n, 6n, hj, {==})
            case 1n+r3:
              match r3:
                case 0n:
                  N.lt_trans(j, 4n, 5n, hj, {==})
                case 1n+r4:
                  Empty.absurd({Nat.is_lt(Nat.add(4n+r4, j), 8n) == True{} : Bool}, AB.lt_zero_absurd(r4, hr))

law sub4_lt:
  for +x: Nat
  for +h: {Nat.is_lt(x, 8n) == True{} : Bool}
  {Nat.is_lt(Nat.sub(x, 4n), 4n) == True{} : Bool}

def sub4_lt(x, h):
  match x:
    case 0n:
      {==}
    case 1n+x1:
      match x1:
        case 0n:
          {==}
        case 1n+x2:
          match x2:
            case 0n:
              {==}
            case 1n+x3:
              match x3:
                case 0n:
                  {==}
                case 1n+x4:
                  %Equal.sym(Nat, Nat.sub(x4, 0n), x4, N.sub_zero(x4)) : {Nat.is_lt(_, 4n) == True{} : Bool}
                  h

# Index 4w + x for x >= 4 is index 4(w + 1) + (x - 4).
law idx_up:
  for +w: Nat
  for +x: Nat
  for +h: {Nat.is_le(4n, x) == True{} : Bool}
  {Nat.add(Nat.mul(w, 4n), x) == Nat.add(Nat.mul(1n+w, 4n), Nat.sub(x, 4n)) : Nat}

def idx_up(w, x, h):
  %Equal.sym(Nat, x, Nat.add(4n, Nat.sub(x, 4n)), Equal.sym(Nat, Nat.add(4n, Nat.sub(x, 4n)), x, N.le_sub_add(4n, x, h))) :
    {Nat.add(Nat.mul(w, 4n), _) == Nat.add(Nat.mul(1n+w, 4n), Nat.sub(x, 4n)) : Nat}
  N.add_left_comm(Nat.mul(w, 4n), 4n, Nat.sub(x, 4n))

# Words and shifts
# ================

# The tree append.words leaves: p is the word read next (hi), lo the word
# before it, td the dst block, di the dst word written, sh the shift in bits.
def AWT(n: Nat, +ts: P.Tree<U32>, +p: U32, +lo: U32, +td: P.Tree<U32>, +si: U32, +di: U32, +sh: Nat) -> P.Tree<U32>:
  match n:
    case 0n:
      td
    case 1n+k:
      +hi = C.WD(ts, p)
      AWT(k, ts, (si + 2 : U32), hi, I.set_tree(U32, td, di, U32.or(U32.shrn(lo, sh), U32.shln(hi, Nat.sub(32n, sh)))), (si + 1 : U32), (di + 1 : U32), sh)

law aw_eq:
  for +n: Nat
  for +ts: P.Tree<U32>
  for +p: U32
  for +lo: U32
  for +td: P.Tree<U32>
  for +si: U32
  for +di: U32
  for +sh: Nat
  {FA.append.words(n, Array.get(U32, P.fromT(U32, ts), p), lo, P.fromT(U32, td), si, di, sh) == (P.fromT(U32, AWT(n, ts, p, lo, td, si, di, sh)), P.fromT(U32, ts)) : Array<U32> & Array<U32>}

def aw_eq(n, ts, p, lo, td, si, di, sh):
  match n:
    case 0n:
      %Equal.sym(Array<U32> & U32, Array.get(U32, P.fromT(U32, ts), p), (P.fromT(U32, ts), C.WD(ts, p)), P.get_pair_t(U32, ts, p)) :
        {FA.append.words(0n, _, lo, P.fromT(U32, td), si, di, sh) == (P.fromT(U32, td), P.fromT(U32, ts)) : Array<U32> & Array<U32>}
      {==}
    case 1n+k:
      +hi = C.WD(ts, p)
      +mw = U32.or(U32.shrn(lo, sh), U32.shln(hi, Nat.sub(32n, sh)))
      %Equal.sym(Array<U32> & U32, Array.get(U32, P.fromT(U32, ts), p), (P.fromT(U32, ts), hi), P.get_pair_t(U32, ts, p)) :
        {FA.append.words(1n+k, _, lo, P.fromT(U32, td), si, di, sh) == (P.fromT(U32, AWT(1n+k, ts, p, lo, td, si, di, sh)), P.fromT(U32, ts)) : Array<U32> & Array<U32>}
      %Equal.sym(Array<U32>, Array.set(U32, P.fromT(U32, td), di, mw), P.fromT(U32, I.set_tree(U32, td, di, mw)), I.set_tree_eq(U32, td, di, mw)) :
        {FA.append.words(k, Array.get(U32, P.fromT(U32, ts), (si + 2 : U32)), hi, _, (si + 1 : U32), (di + 1 : U32), sh) == (P.fromT(U32, AWT(k, ts, (si + 2 : U32), hi, I.set_tree(U32, td, di, mw), (si + 1 : U32), (di + 1 : U32), sh)), P.fromT(U32, ts)) : Array<U32> & Array<U32>}
      aw_eq(k, ts, (si + 2 : U32), hi, I.set_tree(U32, td, di, mw), (si + 1 : U32), (di + 1 : U32), sh)

# The code's shifted pair is lawful-words' merge.
law mrg2:
  for +lo: U32
  for +hi: U32
  for +r: Nat
  for +hr: {Nat.is_lt(r, 4n) == True{} : Bool}
  {U32.or(U32.shrn(lo, Nat.mul(8n, r)), U32.shln(hi, Nat.sub(32n, Nat.mul(8n, r)))) == W.merge(lo, hi, r) : U32}

def mrg2(lo, hi, r, hr):
  match r:
    case 0n:
      {==}
    case 1n+r1:
      match r1:
        case 0n:
          {==}
        case 1n+r2:
          match r2:
            case 0n:
              {==}
            case 1n+r3:
              match r3:
                case 0n:
                  {==}
                case 1n+r4:
                  Empty.absurd({U32.or(U32.shrn(lo, Nat.mul(8n, 4n+r4)), U32.shln(hi, Nat.sub(32n, Nat.mul(8n, 4n+r4)))) == W.merge(lo, hi, 4n+r4) : U32},
                    AB.lt_zero_absurd(r4, hr))

law mrg:
  for +lo: U32
  for +hi: U32
  for +sh: Nat
  for +r: Nat
  for +hsh: {sh == Nat.mul(8n, r) : Nat}
  for +hr: {Nat.is_lt(r, 4n) == True{} : Bool}
  {U32.or(U32.shrn(lo, sh), U32.shln(hi, Nat.sub(32n, sh))) == W.merge(lo, hi, r) : U32}

def mrg(lo, hi, sh, r, hsh, hr):
  %Equal.sym(Nat, sh, Nat.mul(8n, r), hsh) : {U32.or(U32.shrn(lo, _), U32.shln(hi, Nat.sub(32n, _))) == W.merge(lo, hi, r) : U32}
  mrg2(lo, hi, r, hr)

law and3_lt:
  for +q: U32
  {Nat.is_lt(U32.to_nat((q .&. 3 : U32)), 4n) == True{} : Bool}

def and3_lt(q):
  AB.subst(Nat, y => {Nat.is_lt(y, 4n) == True{} : Bool}, Nat.mod(U32.to_nat(q), 4n), U32.to_nat((q .&. 3 : U32)),
    Equal.sym(Nat, U32.to_nat((q .&. 3 : U32)), Nat.mod(U32.to_nat(q), 4n), U.to_nat_and_mask(q, 3, 2n, {==})),
    N.mod_lt(U32.to_nat(q), 4n, {==}))

law shq2:
  for +x: U32
  for +r: Nat
  for +e: {U32.to_nat(x) == r : Nat}
  for +hr: {Nat.is_lt(r, 4n) == True{} : Bool}
  {U32.to_nat((x << 3n : U32)) == Nat.mul(8n, U32.to_nat(x)) : Nat}

def shq2(x, r, e, hr):
  match r:
    case 0n:
      %Equal.sym(U32, x, 0, U.to_nat_inj(x, 0, e)) : {U32.to_nat((_ << 3n : U32)) == Nat.mul(8n, U32.to_nat(_)) : Nat}
      {==}
    case 1n+r1:
      match r1:
        case 0n:
          %Equal.sym(U32, x, 1, U.to_nat_inj(x, 1, e)) : {U32.to_nat((_ << 3n : U32)) == Nat.mul(8n, U32.to_nat(_)) : Nat}
          {==}
        case 1n+r2:
          match r2:
            case 0n:
              %Equal.sym(U32, x, 2, U.to_nat_inj(x, 2, e)) : {U32.to_nat((_ << 3n : U32)) == Nat.mul(8n, U32.to_nat(_)) : Nat}
              {==}
            case 1n+r3:
              match r3:
                case 0n:
                  %Equal.sym(U32, x, 3, U.to_nat_inj(x, 3, e)) : {U32.to_nat((_ << 3n : U32)) == Nat.mul(8n, U32.to_nat(_)) : Nat}
                  {==}
                case 1n+r4:
                  Empty.absurd({U32.to_nat((x << 3n : U32)) == Nat.mul(8n, U32.to_nat(x)) : Nat}, AB.lt_zero_absurd(r4, hr))

# The shift of append.w is 8 * (q & 3).
law shq:
  for +q: U32
  {U32.to_nat(((q .&. 3 : U32) << 3n : U32)) == Nat.mul(8n, U32.to_nat((q .&. 3 : U32))) : Nat}

def shq(q):
  shq2((q .&. 3 : U32), U32.to_nat((q .&. 3 : U32)), {==}, and3_lt(q))

# Bytes of a merged word
# ======================

def US(+ts: P.Tree<U32>) -> List<&2, U32>:
  D.unpack(C.WL(ts))

law mb_lo:
  for +ts: P.Tree<U32>
  for +e: Nat
  for +si: U32
  for +p: U32
  for +lo: U32
  for +r: Nat
  for +j: Nat
  for +hf: {A.full(U32, P.fromT(U32, ts), e) == True{} : Bool}
  for +he: {Nat.is_le(e, 29n) == True{} : Bool}
  for +hlo: {lo == C.WD(ts, si) : U32}
  for +hb: {Nat.is_lt(Nat.add(Nat.mul(U32.to_nat(si), 4n), Nat.add(r, j)), Nat.mul(4n, Nat.pow(2n, e))) == True{} : Bool}
  for +hq: {Nat.is_lt(Nat.add(r, j), 4n) == True{} : Bool}
  {List.get(&2, U32, US(ts), Nat.add(Nat.mul(U32.to_nat(si), 4n), Nat.add(r, j))) == Some{W.byte(W.merge(lo, C.WD(ts, p), r), j)} : Maybe<&2, U32>}

def mb_lo(ts, e, si, p, lo, r, j, hf, he, hlo, hb, hq):
  +w = U32.to_nat(si)
  +hi = C.WD(ts, p)
  +RHS = {Some{W.byte(W.merge(lo, hi, r), j)} : Maybe<&2, U32>}
  %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, US(ts), Nat.add(Nat.mul(w, 4n), Nat.add(r, j))), C.mb(List.get(&2, U32, C.WL(ts), w), Nat.add(r, j)),
    C.unpack_get(C.WL(ts), w, Nat.add(r, j), hq)) :
    {_ == RHS : Maybe<&2, U32>}
  %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, C.WL(ts), w), Some{C.WD(ts, si)}, C.wd_get(ts, e, si, hf, he, lt_w(w, Nat.add(r, j), Nat.pow(2n, e), hb))) :
    {C.mb(_, Nat.add(r, j)) == RHS : Maybe<&2, U32>}
  %Equal.sym(U32, W.byte(W.merge(lo, hi, r), j), W.byte(lo, Nat.add(j, r)),
    Y.byte_merge_lo(lo, hi, r, j, AB.subst(Nat, y => {Nat.is_lt(y, 4n) == True{} : Bool}, Nat.add(r, j), Nat.add(j, r), N.add_comm(r, j), hq))) :
    {Some{W.byte(C.WD(ts, si), Nat.add(r, j))} == Some{_} : Maybe<&2, U32>}
  %Equal.sym(U32, lo, C.WD(ts, si), hlo) : {Some{W.byte(C.WD(ts, si), Nat.add(r, j))} == Some{W.byte(_, Nat.add(j, r))} : Maybe<&2, U32>}
  %N.add_comm(r, j) : {Some{W.byte(C.WD(ts, si), Nat.add(r, j))} == Some{W.byte(C.WD(ts, si), _)} : Maybe<&2, U32>}
  {==}

law mb_hi:
  for +ts: P.Tree<U32>
  for +e: Nat
  for +si: U32
  for +p: U32
  for +lo: U32
  for +r: Nat
  for +j: Nat
  for +hf: {A.full(U32, P.fromT(U32, ts), e) == True{} : Bool}
  for +he: {Nat.is_le(e, 29n) == True{} : Bool}
  for +hp: {U32.to_nat(p) == Nat.add(U32.to_nat(si), 1n) : Nat}
  for +hr: {Nat.is_lt(r, 4n) == True{} : Bool}
  for +hj: {Nat.is_lt(j, 4n) == True{} : Bool}
  for +hb: {Nat.is_lt(Nat.add(Nat.mul(U32.to_nat(si), 4n), Nat.add(r, j)), Nat.mul(4n, Nat.pow(2n, e))) == True{} : Bool}
  for +hq: {Nat.is_lt(Nat.add(r, j), 4n) == False{} : Bool}
  {List.get(&2, U32, US(ts), Nat.add(Nat.mul(U32.to_nat(si), 4n), Nat.add(r, j))) == Some{W.byte(W.merge(lo, C.WD(ts, p), r), j)} : Maybe<&2, U32>}

def mb_hi(ts, e, si, p, lo, r, j, hf, he, hp, hr, hj, hb, hq):
  +w = U32.to_nat(si)
  +hi = C.WD(ts, p)
  +x = Nat.add(r, j)
  +z = Nat.sub(x, 4n)
  +RHS = {Some{W.byte(W.merge(lo, hi, r), j)} : Maybe<&2, U32>}
  +h4 = N.not_lt_le(x, 4n, hq)
  +eu = idx_up(w, x, h4)
  +hz = sub4_lt(x, lt8(r, j, hr, hj))
  +ep = Equal.trans(Nat, U32.to_nat(p), Nat.add(w, 1n), 1n+w, hp, N.add_one(w))
  +hb2 = AB.subst(Nat, y => {Nat.is_lt(y, Nat.mul(4n, Nat.pow(2n, e))) == True{} : Bool}, Nat.add(Nat.mul(w, 4n), x), Nat.add(Nat.mul(1n+w, 4n), z), eu, hb)
  +hpl = AB.subst(Nat, y => {Nat.is_lt(y, Nat.pow(2n, e)) == True{} : Bool}, 1n+w, U32.to_nat(p), Equal.sym(Nat, U32.to_nat(p), 1n+w, ep),
    lt_w(1n+w, z, Nat.pow(2n, e), hb2))
  +gp = AB.subst(Nat, y => {List.get(&2, U32, C.WL(ts), y) == Some{hi} : Maybe<&2, U32>}, U32.to_nat(p), 1n+w, ep, C.wd_get(ts, e, p, hf, he, hpl))
  %Equal.sym(Nat, Nat.add(Nat.mul(w, 4n), x), Nat.add(Nat.mul(1n+w, 4n), z), eu) : {List.get(&2, U32, US(ts), _) == RHS : Maybe<&2, U32>}
  %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, US(ts), Nat.add(Nat.mul(1n+w, 4n), z)), C.mb(List.get(&2, U32, C.WL(ts), 1n+w), z),
    C.unpack_get(C.WL(ts), 1n+w, z, hz)) :
    {_ == RHS : Maybe<&2, U32>}
  %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, C.WL(ts), 1n+w), Some{hi}, gp) : {C.mb(_, z) == RHS : Maybe<&2, U32>}
  %Equal.sym(U32, W.byte(W.merge(lo, hi, r), j), W.byte(hi, Nat.sub(Nat.add(j, r), 4n)),
    Y.byte_merge_hi(lo, hi, r, j, N.lt_to_le(r, 4n, hr), hj,
      AB.subst(Nat, y => {Nat.is_le(4n, y) == True{} : Bool}, x, Nat.add(j, r), N.add_comm(r, j), h4))) :
    {Some{W.byte(hi, z)} == Some{_} : Maybe<&2, U32>}
  %N.add_comm(r, j) : {Some{W.byte(hi, z)} == Some{W.byte(hi, Nat.sub(_, 4n))} : Maybe<&2, U32>}
  {==}

law gsel:
  for +ts: P.Tree<U32>
  for +e: Nat
  for +si: U32
  for +p: U32
  for +lo: U32
  for +r: Nat
  for +j: Nat
  for +b: Bool
  for +hf: {A.full(U32, P.fromT(U32, ts), e) == True{} : Bool}
  for +he: {Nat.is_le(e, 29n) == True{} : Bool}
  for +hlo: {lo == C.WD(ts, si) : U32}
  for +hp: {U32.to_nat(p) == Nat.add(U32.to_nat(si), 1n) : Nat}
  for +hr: {Nat.is_lt(r, 4n) == True{} : Bool}
  for +hj: {Nat.is_lt(j, 4n) == True{} : Bool}
  for +hb: {Nat.is_lt(Nat.add(Nat.mul(U32.to_nat(si), 4n), Nat.add(r, j)), Nat.mul(4n, Nat.pow(2n, e))) == True{} : Bool}
  for +hq: {Nat.is_lt(Nat.add(r, j), 4n) == b : Bool}
  {List.get(&2, U32, US(ts), Nat.add(Nat.mul(U32.to_nat(si), 4n), Nat.add(r, j))) == Some{W.byte(W.merge(lo, C.WD(ts, p), r), j)} : Maybe<&2, U32>}

def gsel(ts, e, si, p, lo, r, j, b, hf, he, hlo, hp, hr, hj, hb, hq):
  match b:
    case True{}:
      mb_lo(ts, e, si, p, lo, r, j, hf, he, hlo, hb, hq)
    case False{}:
      mb_hi(ts, e, si, p, lo, r, j, hf, he, hp, hr, hj, hb, hq)

# Byte j of the window at 4 si + r, for j below m.
law gj:
  for +ts: P.Tree<U32>
  for +e: Nat
  for +si: U32
  for +p: U32
  for +lo: U32
  for +r: Nat
  for +m: Nat
  for +j: Nat
  for +hf: {A.full(U32, P.fromT(U32, ts), e) == True{} : Bool}
  for +he: {Nat.is_le(e, 29n) == True{} : Bool}
  for +hlo: {lo == C.WD(ts, si) : U32}
  for +hp: {U32.to_nat(p) == Nat.add(U32.to_nat(si), 1n) : Nat}
  for +hr: {Nat.is_lt(r, 4n) == True{} : Bool}
  for +hm: {Nat.is_le(m, 4n) == True{} : Bool}
  for +hb: {Nat.is_le(Nat.add(Nat.add(Nat.mul(U32.to_nat(si), 4n), r), m), Nat.mul(4n, Nat.pow(2n, e))) == True{} : Bool}
  for +hjm: {Nat.is_lt(j, m) == True{} : Bool}
  {List.get(&2, U32, List.drop(&2, U32, US(ts), Nat.add(Nat.mul(U32.to_nat(si), 4n), r)), j) == Some{W.byte(W.merge(lo, C.WD(ts, p), r), j)} : Maybe<&2, U32>}

def gj(ts, e, si, p, lo, r, m, j, hf, he, hlo, hp, hr, hm, hb, hjm):
  +X = Nat.mul(U32.to_nat(si), 4n)
  +ea = N.add_assoc(X, r, j)
  +hbj = AB.subst(Nat, y => {Nat.is_lt(y, Nat.mul(4n, Nat.pow(2n, e))) == True{} : Bool}, Nat.add(Nat.add(X, r), j), Nat.add(X, Nat.add(r, j)), ea,
    N.lt_le_trans(Nat.add(Nat.add(X, r), j), Nat.add(Nat.add(X, r), m), Nat.mul(4n, Nat.pow(2n, e)), N.lt_add_l(Nat.add(X, r), j, m, hjm), hb))
  %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, List.drop(&2, U32, US(ts), Nat.add(X, r)), j), List.get(&2, U32, US(ts), Nat.add(Nat.add(X, r), j)), H.get_drop(US(ts), Nat.add(X, r), j)) :
    {_ == Some{W.byte(W.merge(lo, C.WD(ts, p), r), j)} : Maybe<&2, U32>}
  %Equal.sym(Nat, Nat.add(Nat.add(X, r), j), Nat.add(X, Nat.add(r, j)), ea) : {List.get(&2, U32, US(ts), _) == Some{W.byte(W.merge(lo, C.WD(ts, p), r), j)} : Maybe<&2, U32>}
  gsel(ts, e, si, p, lo, r, j, Nat.is_lt(Nat.add(r, j), 4n), hf, he, hlo, hp, hr, N.lt_le_trans(j, m, 4n, hjm, hm), hbj, {==})

# The first m bytes of a merged word are the m src bytes from 4 si + r.
law win:
  for +ts: P.Tree<U32>
  for +e: Nat
  for +si: U32
  for +p: U32
  for +lo: U32
  for +r: Nat
  for +m: Nat
  for +hf: {A.full(U32, P.fromT(U32, ts), e) == True{} : Bool}
  for +he: {Nat.is_le(e, 29n) == True{} : Bool}
  for +hlo: {lo == C.WD(ts, si) : U32}
  for +hp: {U32.to_nat(p) == Nat.add(U32.to_nat(si), 1n) : Nat}
  for +hr: {Nat.is_lt(r, 4n) == True{} : Bool}
  for +hm: {Nat.is_le(m, 4n) == True{} : Bool}
  for +hb: {Nat.is_le(Nat.add(Nat.add(Nat.mul(U32.to_nat(si), 4n), r), m), Nat.mul(4n, Nat.pow(2n, e))) == True{} : Bool}
  {List.take(&2, U32, C.L4(W.merge(lo, C.WD(ts, p), r)), m) == List.take(&2, U32, List.drop(&2, U32, US(ts), Nat.add(Nat.mul(U32.to_nat(si), 4n), r)), m) : List<&2, U32>}

def win(ts, e, si, p, lo, r, m, hf, he, hlo, hp, hr, hm, hb):
  +mw = W.merge(lo, C.WD(ts, p), r)
  +ys = List.drop(&2, U32, US(ts), Nat.add(Nat.mul(U32.to_nat(si), 4n), r))
  Equal.sym(List<&2, U32>, List.take(&2, U32, ys, m), List.take(&2, U32, C.L4(mw), m),
    tg4(ys, m, W.byte(mw, 0n), W.byte(mw, 1n), W.byte(mw, 2n), W.byte(mw, 3n), hm,
      h => gj(ts, e, si, p, lo, r, m, 0n, hf, he, hlo, hp, hr, hm, hb, h),
      h => gj(ts, e, si, p, lo, r, m, 1n, hf, he, hlo, hp, hr, hm, hb, h),
      h => gj(ts, e, si, p, lo, r, m, 2n, hf, he, hlo, hp, hr, hm, hb, h),
      h => gj(ts, e, si, p, lo, r, m, 3n, hf, he, hlo, hp, hr, hm, hb, h)))

# Nat facts for the word loop
# ===========================

law lt_w0:
  for +w: Nat
  for +pp: Nat
  for +h: {Nat.is_lt(Nat.mul(w, 4n), Nat.mul(4n, pp)) == True{} : Bool}
  {Nat.is_lt(w, pp) == True{} : Bool}

def lt_w0(w, pp, h):
  N.lt_mul_cancel(4n, w, pp, AB.subst(Nat, y => {Nat.is_lt(y, Nat.mul(4n, pp)) == True{} : Bool}, Nat.mul(w, 4n), Nat.mul(4n, w), N.mul_comm(w, 4n), h))

law le_x4:
  for +w: Nat
  {Nat.is_le(w, Nat.mul(w, 4n)) == True{} : Bool}

def le_x4(w):
  AB.subst(Nat, y => {Nat.is_le(w, y) == True{} : Bool}, Nat.mul(4n, w), Nat.mul(w, 4n), N.mul_comm(4n, w), N.le_add_r(w, Nat.mul(3n, w)))

law four_alg:
  for +a: Nat
  for +b: Nat
  {Nat.add(4n, Nat.add(a, b)) == Nat.add(a, Nat.add(b, 4n)) : Nat}

def four_alg(a, b):
  %N.add_comm(4n, b) : {Nat.add(4n, Nat.add(a, b)) == Nat.add(a, _) : Nat}
  Equal.sym(Nat, Nat.add(a, Nat.add(4n, b)), Nat.add(4n, Nat.add(a, b)), N.add_left_comm(a, 4n, b))

law c4:
  for +o: Nat
  for +y: Nat
  for +np: Nat
  for +h: {Nat.is_lt(Nat.add(o, Nat.add(4n, y)), Nat.add(np, 4n)) == True{} : Bool}
  {Nat.is_lt(Nat.add(o, y), np) == True{} : Bool}

def c4(o, y, np, h):
  +h2 = AB.subst(Nat, z => {Nat.is_lt(z, Nat.add(np, 4n)) == True{} : Bool}, Nat.add(o, Nat.add(4n, y)), Nat.add(4n, Nat.add(o, y)), N.add_left_comm(o, 4n, y), h)
  AB.subst(Nat, z => {Nat.is_lt(Nat.add(4n, Nat.add(o, y)), z) == True{} : Bool}, Nat.add(np, 4n), Nat.add(4n, np), N.add_comm(np, 4n), h2)

law w2_bound:
  for +w: Nat
  for +pp: Nat
  for +hp: {Nat.is_lt(0n, pp) == True{} : Bool}
  for +h: {Nat.is_lt(w, pp) == True{} : Bool}
  {Nat.is_le(Nat.add(w, 2n), Nat.mul(4n, pp)) == True{} : Bool}

def w2_bound(w, pp, hp, h):
  +R = Nat.add(pp, Nat.add(pp, Nat.add(pp, 0n)))
  +h1 = AB.subst(Nat, y => {Nat.is_le(y, Nat.add(pp, 1n)) == True{} : Bool}, Nat.add(Nat.add(w, 1n), 1n), Nat.add(w, 2n), N.add_assoc(w, 1n, 1n),
    N.le_add_mono_r(1n, Nat.add(w, 1n), pp, C.succ_le(w, pp, h)))
  N.le_trans(Nat.add(w, 2n), Nat.add(pp, 1n), Nat.mul(4n, pp), h1,
    N.le_add_mono_l(pp, 1n, R, Equal.trans(Bool, Nat.is_le(1n, R), Nat.is_lt(0n, R), True{}, N.le_succ_lt(0n, R), N.pos_add_l(pp, Nat.add(pp, Nat.add(pp, 0n)), hp))))

law sub_le_of:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +h: {Nat.is_le(a, Nat.add(b, c)) == True{} : Bool}
  {Nat.is_le(Nat.sub(a, b), c) == True{} : Bool}

def sub_le_of(a, b, c, h):
  match a b:
    case 0n _:
      N.le_zero_l(c)
    case 1n+p 0n:
      h
    case 1n+p 1n+q:
      sub_le_of(p, q, c, h)

# One word written
# ================

law step:
  for +ts: P.Tree<U32>
  for +e: Nat
  for +td: P.Tree<U32>
  for +d: Nat
  for +p: U32
  for +lo: U32
  for +si: U32
  for +di: U32
  for +sh: Nat
  for +l1: Nat
  for +qn: Nat
  for +r: Nat
  for +o: Nat
  for +np: Nat
  for +v1: List<&2, U32>
  for +m: Nat
  for +hfs: {A.full(U32, P.fromT(U32, ts), e) == True{} : Bool}
  for +hes: {Nat.is_le(e, 29n) == True{} : Bool}
  for +hfd: {A.full(U32, P.fromT(U32, td), d) == True{} : Bool}
  for +hdd: {Nat.is_le(d, 29n) == True{} : Bool}
  for +hdi: {Nat.mul(U32.to_nat(di), 4n) == Nat.add(l1, o) : Nat}
  for +hsi: {Nat.add(Nat.mul(U32.to_nat(si), 4n), r) == Nat.add(qn, o) : Nat}
  for +hp: {U32.to_nat(p) == Nat.add(U32.to_nat(si), 1n) : Nat}
  for +hlo: {lo == C.WD(ts, si) : U32}
  for +hsh: {sh == Nat.mul(8n, r) : Nat}
  for +hr: {Nat.is_lt(r, 4n) == True{} : Bool}
  for +hq: {Nat.is_le(Nat.add(qn, np), Nat.mul(4n, Nat.pow(2n, e))) == True{} : Bool}
  for +hl: {Nat.is_le(Nat.add(l1, np), Nat.mul(4n, Nat.pow(2n, d))) == True{} : Bool}
  for +ho: {Nat.is_lt(o, np) == True{} : Bool}
  for +hm: {Nat.is_le(m, 4n) == True{} : Bool}
  for +hmv: {Nat.is_le(Nat.add(o, m), np) == True{} : Bool}
  for +hinv: {List.take(&2, U32, US(td), Nat.add(l1, o)) == List.append(&2, U32, v1, List.take(&2, U32, List.drop(&2, U32, US(ts), qn), o)) : List<&2, U32>}
  {List.take(&2, U32, US(I.set_tree(U32, td, di, U32.or(U32.shrn(lo, sh), U32.shln(C.WD(ts, p), Nat.sub(32n, sh))))), Nat.add(l1, Nat.add(o, m))) == List.append(&2, U32, v1, List.take(&2, U32, List.drop(&2, U32, US(ts), qn), Nat.add(o, m))) : List<&2, U32>}

def step(ts, e, td, d, p, lo, si, di, sh, l1, qn, r, o, np, v1, m, hfs, hes, hfd, hdd, hdi, hsi, hp, hlo, hsh, hr, hq, hl, ho, hm, hmv, hinv):
  +hi = C.WD(ts, p)
  +mw = U32.or(U32.shrn(lo, sh), U32.shln(hi, Nat.sub(32n, sh)))
  +dd = U32.to_nat(di)
  +w = U32.to_nat(si)
  +ys = List.drop(&2, U32, US(ts), qn)
  +RHS = List.append(&2, U32, v1, List.take(&2, U32, ys, Nat.add(o, m)))
  +hdl = AB.subst(Nat, y => {Nat.is_lt(y, Nat.mul(4n, Nat.pow(2n, d))) == True{} : Bool}, Nat.add(l1, o), Nat.mul(dd, 4n), Equal.sym(Nat, Nat.mul(dd, 4n), Nat.add(l1, o), hdi),
    N.lt_le_trans(Nat.add(l1, o), Nat.add(l1, np), Nat.mul(4n, Nat.pow(2n, d)), N.lt_add_l(l1, o, np, ho), hl))
  +hD = lt_w0(dd, Nat.pow(2n, d), hdl)
  +hDl = AB.subst(Nat, y => {Nat.is_lt(dd, y) == True{} : Bool}, Nat.pow(2n, d), List.length(&2, U32, C.WL(td)),
    Equal.sym(Nat, List.length(&2, U32, C.WL(td)), Nat.pow(2n, d), P.view_length(U32, d, td, hfd)), hD)
  +eidx = Equal.trans(Nat, Nat.add(Nat.mul(dd, 4n), m), Nat.add(Nat.add(l1, o), m), Nat.add(l1, Nat.add(o, m)),
    Equal.cong(Nat, Nat, z => Nat.add(z, m), Nat.mul(dd, 4n), Nat.add(l1, o), hdi), N.add_assoc(l1, o, m))
  +hb = AB.subst(Nat, y => {Nat.is_le(Nat.add(y, m), Nat.mul(4n, Nat.pow(2n, e))) == True{} : Bool}, Nat.add(qn, o), Nat.add(Nat.mul(w, 4n), r),
    Equal.sym(Nat, Nat.add(Nat.mul(w, 4n), r), Nat.add(qn, o), hsi),
    AB.subst(Nat, y => {Nat.is_le(y, Nat.mul(4n, Nat.pow(2n, e))) == True{} : Bool}, Nat.add(qn, Nat.add(o, m)), Nat.add(Nat.add(qn, o), m),
      Equal.sym(Nat, Nat.add(Nat.add(qn, o), m), Nat.add(qn, Nat.add(o, m)), N.add_assoc(qn, o, m)),
      N.le_trans(Nat.add(qn, Nat.add(o, m)), Nat.add(qn, np), Nat.mul(4n, Nat.pow(2n, e)), N.le_add_mono_l(qn, Nat.add(o, m), np, hmv), hq)))
  +ew = Equal.trans(List<&2, U32>, List.take(&2, U32, C.L4(mw), m), List.take(&2, U32, C.L4(W.merge(lo, hi, r)), m), List.take(&2, U32, List.drop(&2, U32, US(ts), Nat.add(qn, o)), m),
    Equal.cong(U32, List<&2, U32>, z => List.take(&2, U32, C.L4(z), m), mw, W.merge(lo, hi, r), mrg(lo, hi, sh, r, hsh, hr)),
    Equal.trans(List<&2, U32>, List.take(&2, U32, C.L4(W.merge(lo, hi, r)), m), List.take(&2, U32, List.drop(&2, U32, US(ts), Nat.add(Nat.mul(w, 4n), r)), m),
      List.take(&2, U32, List.drop(&2, U32, US(ts), Nat.add(qn, o)), m),
      win(ts, e, si, p, lo, r, m, hfs, hes, hlo, hp, hr, hm, hb),
      Equal.cong(Nat, List<&2, U32>, z => List.take(&2, U32, List.drop(&2, U32, US(ts), z), m), Nat.add(Nat.mul(w, 4n), r), Nat.add(qn, o), hsi)))
  +ew2 = AB.subst(List<&2, U32>, z => {List.take(&2, U32, C.L4(mw), m) == List.take(&2, U32, z, m) : List<&2, U32>},
    List.drop(&2, U32, US(ts), Nat.add(qn, o)), List.drop(&2, U32, ys, o),
    Equal.sym(List<&2, U32>, List.drop(&2, U32, ys, o), List.drop(&2, U32, US(ts), Nat.add(qn, o)), drop_drop(US(ts), qn, o)), ew)
  %Equal.sym(List<&2, U32>, C.WL(I.set_tree(U32, td, di, mw)), List.set(&2, U32, C.WL(td), dd, mw), C.wl_set(td, d, di, mw, hfd, hdd, hD)) :
    {List.take(&2, U32, D.unpack(_), Nat.add(l1, Nat.add(o, m))) == RHS : List<&2, U32>}
  %eidx : {List.take(&2, U32, D.unpack(List.set(&2, U32, C.WL(td), dd, mw)), _) == RHS : List<&2, U32>}
  %Equal.sym(List<&2, U32>, List.take(&2, U32, D.unpack(List.set(&2, U32, C.WL(td), dd, mw)), Nat.add(Nat.mul(dd, 4n), m)),
    List.append(&2, U32, List.take(&2, U32, D.unpack(C.WL(td)), Nat.mul(dd, 4n)), List.take(&2, U32, C.L4(mw), m)),
    us1(C.WL(td), dd, mw, m, hDl, hm)) :
    {_ == RHS : List<&2, U32>}
  %Equal.sym(Nat, Nat.mul(dd, 4n), Nat.add(l1, o), hdi) :
    {List.append(&2, U32, List.take(&2, U32, D.unpack(C.WL(td)), _), List.take(&2, U32, C.L4(mw), m)) == RHS : List<&2, U32>}
  %Equal.sym(List<&2, U32>, List.take(&2, U32, US(td), Nat.add(l1, o)), List.append(&2, U32, v1, List.take(&2, U32, ys, o)), hinv) :
    {List.append(&2, U32, _, List.take(&2, U32, C.L4(mw), m)) == RHS : List<&2, U32>}
  %Equal.sym(List<&2, U32>, List.take(&2, U32, C.L4(mw), m), List.take(&2, U32, List.drop(&2, U32, ys, o), m), ew2) :
    {List.append(&2, U32, List.append(&2, U32, v1, List.take(&2, U32, ys, o)), _) == RHS : List<&2, U32>}
  Equal.trans(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, v1, List.take(&2, U32, ys, o)), List.take(&2, U32, List.drop(&2, U32, ys, o), m)),
    List.append(&2, U32, v1, List.append(&2, U32, List.take(&2, U32, ys, o), List.take(&2, U32, List.drop(&2, U32, ys, o), m))), RHS,
    X.append_assoc(v1, List.take(&2, U32, ys, o), List.take(&2, U32, List.drop(&2, U32, ys, o), m)),
    Equal.cong(List<&2, U32>, List<&2, U32>, z => List.append(&2, U32, v1, z),
      List.append(&2, U32, List.take(&2, U32, ys, o), List.take(&2, U32, List.drop(&2, U32, ys, o), m)), List.take(&2, U32, ys, Nat.add(o, m)), take_split(ys, o, m)))

# The last word, when fewer than 4 bytes are left.
law avf:
  for +k1: Nat
  for +ts: P.Tree<U32>
  for +e: Nat
  for +td: P.Tree<U32>
  for +d: Nat
  for +p: U32
  for +lo: U32
  for +si: U32
  for +di: U32
  for +sh: Nat
  for +l1: Nat
  for +qn: Nat
  for +r: Nat
  for +o: Nat
  for +np: Nat
  for +v1: List<&2, U32>
  for +hbq: {Nat.is_le(Nat.add(o, 4n), np) == False{} : Bool}
  for +hfs: {A.full(U32, P.fromT(U32, ts), e) == True{} : Bool}
  for +hes: {Nat.is_le(e, 29n) == True{} : Bool}
  for +hfd: {A.full(U32, P.fromT(U32, td), d) == True{} : Bool}
  for +hdd: {Nat.is_le(d, 29n) == True{} : Bool}
  for +hdi: {Nat.mul(U32.to_nat(di), 4n) == Nat.add(l1, o) : Nat}
  for +hsi: {Nat.add(Nat.mul(U32.to_nat(si), 4n), r) == Nat.add(qn, o) : Nat}
  for +hp: {U32.to_nat(p) == Nat.add(U32.to_nat(si), 1n) : Nat}
  for +hlo: {lo == C.WD(ts, si) : U32}
  for +hsh: {sh == Nat.mul(8n, r) : Nat}
  for +hr: {Nat.is_lt(r, 4n) == True{} : Bool}
  for +hq: {Nat.is_le(Nat.add(qn, np), Nat.mul(4n, Nat.pow(2n, e))) == True{} : Bool}
  for +hl: {Nat.is_le(Nat.add(l1, np), Nat.mul(4n, Nat.pow(2n, d))) == True{} : Bool}
  for +hon: {Nat.is_le(o, np) == True{} : Bool}
  for +hc1: {Nat.is_le(np, Nat.add(o, Nat.mul(1n+k1, 4n))) == True{} : Bool}
  for +hc2: {Nat.is_lt(Nat.add(o, Nat.mul(1n+k1, 4n)), Nat.add(np, 4n)) == True{} : Bool}
  for +hinv: {List.take(&2, U32, US(td), Nat.add(l1, o)) == List.append(&2, U32, v1, List.take(&2, U32, List.drop(&2, U32, US(ts), qn), o)) : List<&2, U32>}
  {List.take(&2, U32, US(AWT(1n+k1, ts, p, lo, td, si, di, sh)), Nat.add(l1, np)) == List.append(&2, U32, v1, List.take(&2, U32, List.drop(&2, U32, US(ts), qn), np)) : List<&2, U32>}

def avf(k1, ts, e, td, d, p, lo, si, di, sh, l1, qn, r, o, np, v1, hbq, hfs, hes, hfd, hdd, hdi, hsi, hp, hlo, hsh, hr, hq, hl, hon, hc1, hc2, hinv):
  match k1:
    case 0n:
      +hi = C.WD(ts, p)
      +mw = U32.or(U32.shrn(lo, sh), U32.shln(hi, Nat.sub(32n, sh)))
      +ho = N.le_lt_trans(o, Nat.add(o, 0n), np, N.le_add_r(o, 0n), c4(o, 0n, np, hc2))
      +eo = N.le_sub_add(o, np, N.lt_to_le(o, np, ho))
      +hm = sub_le_of(np, o, 4n, N.lt_to_le(np, Nat.add(o, 4n), N.not_le_lt(Nat.add(o, 4n), np, hbq)))
      +hmv = AB.subst(Nat, y => {Nat.is_le(y, np) == True{} : Bool}, np, Nat.add(o, Nat.sub(np, o)), Equal.sym(Nat, Nat.add(o, Nat.sub(np, o)), np, eo), N.le_refl(np))
      AB.subst(Nat, y => {List.take(&2, U32, US(I.set_tree(U32, td, di, mw)), Nat.add(l1, y)) == List.append(&2, U32, v1, List.take(&2, U32, List.drop(&2, U32, US(ts), qn), y)) : List<&2, U32>},
        Nat.add(o, Nat.sub(np, o)), np, eo,
        step(ts, e, td, d, p, lo, si, di, sh, l1, qn, r, o, np, v1, Nat.sub(np, o), hfs, hes, hfd, hdd, hdi, hsi, hp, hlo, hsh, hr, hq, hl, ho, hm, hmv, hinv))
    case 1n+k2:
      +X2 = Nat.mul(k2, 4n)
      +h1 = c4(o, Nat.add(4n, X2), np, hc2)
      +h2 = N.le_lt_trans(Nat.add(o, 4n), Nat.add(o, Nat.add(4n, X2)), np, N.le_add_mono_l(o, 4n, Nat.add(4n, X2), N.le_add_r(4n, X2)), h1)
      Empty.absurd({List.take(&2, U32, US(AWT(2n+k2, ts, p, lo, td, si, di, sh)), Nat.add(l1, np)) == List.append(&2, U32, v1, List.take(&2, U32, List.drop(&2, U32, US(ts), qn), np)) : List<&2, U32>},
        AB.false_ne_true(Equal.trans(Bool, False{}, Nat.is_le(Nat.add(o, 4n), np), True{}, Equal.sym(Bool, Nat.is_le(Nat.add(o, 4n), np), False{}, hbq),
          N.lt_to_le(Nat.add(o, 4n), np, h2))))

# The word loop
# =============

# After the words written so far (o bytes, o <= np), the bytes in use agree
# with v1 then src from qn; the k words left finish the np bytes.
law av:
  for +k: Nat
  for +b: Bool
  for +ts: P.Tree<U32>
  for +e: Nat
  for +td: P.Tree<U32>
  for +d: Nat
  for +p: U32
  for +lo: U32
  for +si: U32
  for +di: U32
  for +sh: Nat
  for +l1: Nat
  for +qn: Nat
  for +r: Nat
  for +o: Nat
  for +np: Nat
  for +v1: List<&2, U32>
  for +hbq: {Nat.is_le(Nat.add(o, 4n), np) == b : Bool}
  for +hfs: {A.full(U32, P.fromT(U32, ts), e) == True{} : Bool}
  for +hes: {Nat.is_le(e, 29n) == True{} : Bool}
  for +hfd: {A.full(U32, P.fromT(U32, td), d) == True{} : Bool}
  for +hdd: {Nat.is_le(d, 29n) == True{} : Bool}
  for +hdi: {Nat.mul(U32.to_nat(di), 4n) == Nat.add(l1, o) : Nat}
  for +hsi: {Nat.add(Nat.mul(U32.to_nat(si), 4n), r) == Nat.add(qn, o) : Nat}
  for +hp: {U32.to_nat(p) == Nat.add(U32.to_nat(si), 1n) : Nat}
  for +hlo: {lo == C.WD(ts, si) : U32}
  for +hsh: {sh == Nat.mul(8n, r) : Nat}
  for +hr: {Nat.is_lt(r, 4n) == True{} : Bool}
  for +hq: {Nat.is_le(Nat.add(qn, np), Nat.mul(4n, Nat.pow(2n, e))) == True{} : Bool}
  for +hl: {Nat.is_le(Nat.add(l1, np), Nat.mul(4n, Nat.pow(2n, d))) == True{} : Bool}
  for +hon: {Nat.is_le(o, np) == True{} : Bool}
  for +hc1: {Nat.is_le(np, Nat.add(o, Nat.mul(k, 4n))) == True{} : Bool}
  for +hc2: {Nat.is_lt(Nat.add(o, Nat.mul(k, 4n)), Nat.add(np, 4n)) == True{} : Bool}
  for +hinv: {List.take(&2, U32, US(td), Nat.add(l1, o)) == List.append(&2, U32, v1, List.take(&2, U32, List.drop(&2, U32, US(ts), qn), o)) : List<&2, U32>}
  {List.take(&2, U32, US(AWT(k, ts, p, lo, td, si, di, sh)), Nat.add(l1, np)) == List.append(&2, U32, v1, List.take(&2, U32, List.drop(&2, U32, US(ts), qn), np)) : List<&2, U32>}

def av(k, b, ts, e, td, d, p, lo, si, di, sh, l1, qn, r, o, np, v1, hbq, hfs, hes, hfd, hdd, hdi, hsi, hp, hlo, hsh, hr, hq, hl, hon, hc1, hc2, hinv):
  match k b:
    case 0n _:
      +eo = le_antisym(o, np, hon, AB.subst(Nat, y => {Nat.is_le(np, y) == True{} : Bool}, Nat.add(o, 0n), o, N.add_zero(o), hc1))
      %eo : {List.take(&2, U32, US(td), Nat.add(l1, _)) == List.append(&2, U32, v1, List.take(&2, U32, List.drop(&2, U32, US(ts), qn), _)) : List<&2, U32>}
      hinv
    case 1n+k1 True{}:
      +w = U32.to_nat(si)
      +dd = U32.to_nat(di)
      +hi = C.WD(ts, p)
      +mw = U32.or(U32.shrn(lo, sh), U32.shln(hi, Nat.sub(32n, sh)))
      +MD = Nat.mul(4n, Nat.pow(2n, d))
      +ME = Nat.mul(4n, Nat.pow(2n, e))
      +X = Nat.mul(k1, 4n)
      +ho = N.le_lt_trans(o, Nat.add(o, X), np, N.le_add_r(o, X), c4(o, X, np, hc2))
      +hinv2 = step(ts, e, td, d, p, lo, si, di, sh, l1, qn, r, o, np, v1, 4n, hfs, hes, hfd, hdd, hdi, hsi, hp, hlo, hsh, hr, hq, hl, ho, {==}, hbq, hinv)
      +hdl = AB.subst(Nat, y => {Nat.is_lt(y, MD) == True{} : Bool}, Nat.add(l1, o), Nat.mul(dd, 4n), Equal.sym(Nat, Nat.mul(dd, 4n), Nat.add(l1, o), hdi),
        N.lt_le_trans(Nat.add(l1, o), Nat.add(l1, np), MD, N.lt_add_l(l1, o, np, ho), hl))
      +e1 = C.inc_fits(di, d, hdd, N.le_lt_trans(dd, Nat.mul(dd, 4n), MD, le_x4(dd), hdl))
      +hwl = AB.subst(Nat, y => {Nat.is_lt(y, ME) == True{} : Bool}, Nat.add(qn, o), Nat.add(Nat.mul(w, 4n), r), Equal.sym(Nat, Nat.add(Nat.mul(w, 4n), r), Nat.add(qn, o), hsi),
        N.lt_le_trans(Nat.add(qn, o), Nat.add(qn, np), ME, N.lt_add_l(qn, o, np, ho), hq))
      +hw4 = N.le_lt_trans(Nat.mul(w, 4n), Nat.add(Nat.mul(w, 4n), r), ME, N.le_add_r(Nat.mul(w, 4n), r), hwl)
      +e2 = C.inc_fits(si, e, hes, N.le_lt_trans(w, Nat.mul(w, 4n), ME, le_x4(w), hw4))
      +e3 = C.add_fits(si, 2, e, hes, w2_bound(w, Nat.pow(2n, e), AB.pow_pos(e), lt_w0(w, Nat.pow(2n, e), hw4)))
      +hdi2 = Equal.trans(Nat, Nat.mul(U32.to_nat((di + 1 : U32)), 4n), Nat.mul(1n+dd, 4n), Nat.add(l1, Nat.add(o, 4n)),
        Equal.cong(Nat, Nat, z => Nat.mul(z, 4n), U32.to_nat((di + 1 : U32)), 1n+dd, Equal.trans(Nat, U32.to_nat((di + 1 : U32)), Nat.add(dd, 1n), 1n+dd, e1, N.add_one(dd))),
        Equal.trans(Nat, Nat.add(4n, Nat.mul(dd, 4n)), Nat.add(4n, Nat.add(l1, o)), Nat.add(l1, Nat.add(o, 4n)),
          Equal.cong(Nat, Nat, z => Nat.add(4n, z), Nat.mul(dd, 4n), Nat.add(l1, o), hdi), four_alg(l1, o)))
      +hsi2 = Equal.trans(Nat, Nat.add(Nat.mul(U32.to_nat((si + 1 : U32)), 4n), r), Nat.add(Nat.mul(1n+w, 4n), r), Nat.add(qn, Nat.add(o, 4n)),
        Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(z, 4n), r), U32.to_nat((si + 1 : U32)), 1n+w, Equal.trans(Nat, U32.to_nat((si + 1 : U32)), Nat.add(w, 1n), 1n+w, e2, N.add_one(w))),
        Equal.trans(Nat, Nat.add(4n, Nat.add(Nat.mul(w, 4n), r)), Nat.add(4n, Nat.add(qn, o)), Nat.add(qn, Nat.add(o, 4n)),
          Equal.cong(Nat, Nat, z => Nat.add(4n, z), Nat.add(Nat.mul(w, 4n), r), Nat.add(qn, o), hsi), four_alg(qn, o)))
      +hp2 = Equal.trans(Nat, U32.to_nat((si + 2 : U32)), Nat.add(w, 2n), Nat.add(U32.to_nat((si + 1 : U32)), 1n), e3,
        Equal.sym(Nat, Nat.add(U32.to_nat((si + 1 : U32)), 1n), Nat.add(w, 2n),
          Equal.trans(Nat, Nat.add(U32.to_nat((si + 1 : U32)), 1n), Nat.add(Nat.add(w, 1n), 1n), Nat.add(w, 2n),
            Equal.cong(Nat, Nat, z => Nat.add(z, 1n), U32.to_nat((si + 1 : U32)), Nat.add(w, 1n), e2), N.add_assoc(w, 1n, 1n))))
      +hlo2 = Equal.cong(U32, U32, z => C.WD(ts, z), p, (si + 1 : U32),
        U.to_nat_inj(p, (si + 1 : U32), Equal.trans(Nat, U32.to_nat(p), Nat.add(w, 1n), U32.to_nat((si + 1 : U32)), hp, Equal.sym(Nat, U32.to_nat((si + 1 : U32)), Nat.add(w, 1n), e2))))
      +ea = Equal.sym(Nat, Nat.add(Nat.add(o, 4n), X), Nat.add(o, Nat.add(4n, X)), N.add_assoc(o, 4n, X))
      +hc12 = AB.subst(Nat, y => {Nat.is_le(np, y) == True{} : Bool}, Nat.add(o, Nat.add(4n, X)), Nat.add(Nat.add(o, 4n), X), ea, hc1)
      +hc22 = AB.subst(Nat, y => {Nat.is_lt(y, Nat.add(np, 4n)) == True{} : Bool}, Nat.add(o, Nat.add(4n, X)), Nat.add(Nat.add(o, 4n), X), ea, hc2)
      av(k1, Nat.is_le(Nat.add(Nat.add(o, 4n), 4n), np), ts, e, I.set_tree(U32, td, di, mw), d, (si + 2 : U32), hi, (si + 1 : U32), (di + 1 : U32), sh, l1, qn, r, Nat.add(o, 4n), np, v1,
        {==}, hfs, hes, C.full_set(td, d, di, mw, hfd), hdd, hdi2, hsi2, hp2, hlo2, hsh, hr, hq, hl, hbq, hc12, hc22, hinv2)
    case 1n+k1 False{}:
      avf(k1, ts, e, td, d, p, lo, si, di, sh, l1, qn, r, o, np, v1, hbq, hfs, hes, hfd, hdd, hdi, hsi, hp, hlo, hsh, hr, hq, hl, hon, hc1, hc2, hinv)

# Facts for the top level
# =======================

# The length after the reference append's pushes.
law ag_size:
  for +n: Nat
  for +ld: U32
  for +td: P.Tree<U32>
  for +ls: U32
  for +ts: P.Tree<U32>
  for +d: Nat
  for +s: U32
  for +hd: {D.ok(C.BT(ld, td), d) == True{} : Bool}
  for +hc: {Nat.is_le(Nat.add(U32.to_nat(ld), n), D.cap(C.BT(ld, td))) == True{} : Bool}
  {D.size(Pair.fst(D.Bytes, D.Bytes, B.append.go(n, C.BT(ld, td), B.at(C.BT(ls, ts), s), s))) == Nat.add(U32.to_nat(ld), n) : Nat}

def ag_size(n, ld, td, ls, ts, d, s, hd, hc):
  match n:
    case 0n:
      %Equal.sym(D.Bytes & U32, B.at(C.BT(ls, ts), s), (C.BT(ls, ts), C.AT(ls, ts, s)), C.at_pair_t(ls, ts, s)) :
        {D.size(Pair.fst(D.Bytes, D.Bytes, B.append.go(0n, C.BT(ld, td), _, s))) == Nat.add(U32.to_nat(ld), 0n) : Nat}
      Equal.sym(Nat, Nat.add(U32.to_nat(ld), 0n), U32.to_nat(ld), N.add_zero(U32.to_nat(ld)))
    case 1n+k:
      +x = C.AT(ls, ts, s)
      %Equal.sym(D.Bytes & U32, B.at(C.BT(ls, ts), s), (C.BT(ls, ts), x), C.at_pair_t(ls, ts, s)) :
        {D.size(Pair.fst(D.Bytes, D.Bytes, B.append.go(1n+k, C.BT(ld, td), _, s))) == Nat.add(U32.to_nat(ld), 1n+k) : Nat}
      %Equal.sym(D.Bytes, B.push(C.BT(ld, td), x), C.BT((ld + 1 : U32), X.PT(ld, td, x)), O.push_eq_t(ld, td, x)) :
        {D.size(Pair.fst(D.Bytes, D.Bytes, B.append.go(k, _, B.at(C.BT(ls, ts), (s + 1 : U32)), (s + 1 : U32)))) == Nat.add(U32.to_nat(ld), 1n+k) : Nat}
      Equal.trans(Nat, D.size(Pair.fst(D.Bytes, D.Bytes, B.append.go(k, C.BT((ld + 1 : U32), X.PT(ld, td, x)), B.at(C.BT(ls, ts), (s + 1 : U32)), (s + 1 : U32)))),
        Nat.add(U32.to_nat((ld + 1 : U32)), k), Nat.add(U32.to_nat(ld), 1n+k),
        ag_size(k, (ld + 1 : U32), X.PT(ld, td, x), ls, ts, d, (s + 1 : U32), X.step_ok(ld, td, d, x, k, hd, hc), X.step_cap(ld, td, d, x, k, hd, hc)),
        Equal.trans(Nat, Nat.add(U32.to_nat((ld + 1 : U32)), k), Nat.add(Nat.add(U32.to_nat(ld), 1n), k), Nat.add(U32.to_nat(ld), 1n+k),
          Equal.cong(Nat, Nat, z => Nat.add(z, k), U32.to_nat((ld + 1 : U32)), Nat.add(U32.to_nat(ld), 1n),
            C.inc_fits(ld, d, C.ok_d(ld, td, d, hd), X.step_room(ld, td, d, k, hd, hc))),
          N.add_assoc(U32.to_nat(ld), 1n, k)))

law aw_full:
  for +n: Nat
  for +ts: P.Tree<U32>
  for +p: U32
  for +lo: U32
  for +td: P.Tree<U32>
  for +si: U32
  for +di: U32
  for +sh: Nat
  for +d: Nat
  for +hfd: {A.full(U32, P.fromT(U32, td), d) == True{} : Bool}
  {A.full(U32, P.fromT(U32, AWT(n, ts, p, lo, td, si, di, sh)), d) == True{} : Bool}

def aw_full(n, ts, p, lo, td, si, di, sh, d, hfd):
  match n:
    case 0n:
      hfd
    case 1n+k:
      +mw = U32.or(U32.shrn(lo, sh), U32.shln(C.WD(ts, p), Nat.sub(32n, sh)))
      aw_full(k, ts, (si + 2 : U32), C.WD(ts, p), I.set_tree(U32, td, di, mw), (si + 1 : U32), (di + 1 : U32), sh, d, C.full_set(td, d, di, mw, hfd))

law mul4div:
  for +z: Nat
  for +y: Nat
  for +e: {z == Nat.mul(y, 4n) : Nat}
  {Nat.mul(Nat.div(z, 4n), 4n) == z : Nat}

def mul4div(z, y, e):
  %Equal.sym(Nat, z, Nat.mul(y, 4n), e) : {Nat.mul(Nat.div(_, 4n), 4n) == _ : Nat}
  Equal.cong(Nat, Nat, w => Nat.mul(w, 4n), Nat.div(Nat.mul(y, 4n), 4n), y,
    AB.subst(Nat, w => {Nat.div(w, 4n) == y : Nat}, Nat.add(Nat.mul(y, 4n), 0n), Nat.mul(y, 4n), N.add_zero(Nat.mul(y, 4n)), N.div_mul_add(y, 4n, 0n, {==})))

# x = 4a + k with k + h = 4 gives x + h = 4(a + 1).
law al_k:
  for +x: Nat
  for +a: Nat
  for +k: Nat
  for +h: Nat
  for +ex: {x == Nat.add(Nat.mul(a, 4n), k) : Nat}
  for +ek: {Nat.add(k, h) == 4n : Nat}
  {Nat.add(x, h) == Nat.mul(1n+a, 4n) : Nat}

def al_k(x, a, k, h, ex, ek):
  %Equal.sym(Nat, x, Nat.add(Nat.mul(a, 4n), k), ex) : {Nat.add(_, h) == Nat.mul(1n+a, 4n) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(a, 4n), k), h), Nat.add(Nat.mul(a, 4n), Nat.add(k, h)), N.add_assoc(Nat.mul(a, 4n), k, h)) : {_ == Nat.mul(1n+a, 4n) : Nat}
  %Equal.sym(Nat, Nat.add(k, h), 4n, ek) : {Nat.add(Nat.mul(a, 4n), _) == Nat.mul(1n+a, 4n) : Nat}
  N.add_comm(Nat.mul(a, 4n), 4n)

def H0(+ld: U32) -> U32:
  U32.and(U32.sub(4, U32.and(ld, 3)), 3)

law exk:
  for +ld: U32
  for +k: Nat
  for +ek: {U32.to_nat((ld .&. 3 : U32)) == k : Nat}
  {U32.to_nat(ld) == Nat.add(Nat.mul(Nat.div(U32.to_nat(ld), 4n), 4n), k) : Nat}

def exk(ld, k, ek):
  +x = U32.to_nat(ld)
  +a = Nat.div(x, 4n)
  +ex0 = Equal.sym(Nat, Nat.add(Nat.mul(a, 4n), U32.to_nat((ld .&. 3 : U32))), x,
    AB.subst(Nat, z => {Nat.add(Nat.mul(a, 4n), z) == x : Nat}, Nat.mod(x, 4n), U32.to_nat((ld .&. 3 : U32)),
      Equal.sym(Nat, U32.to_nat((ld .&. 3 : U32)), Nat.mod(x, 4n), U.to_nat_and_mask(ld, 3, 2n, {==})), N.div_mod(x, 4n)))
  AB.subst(Nat, z => {x == Nat.add(Nat.mul(a, 4n), z) : Nat}, U32.to_nat((ld .&. 3 : U32)), k, ek, ex0)

law align2:
  for +ld: U32
  for +k: Nat
  for +ek: {U32.to_nat((ld .&. 3 : U32)) == k : Nat}
  for +hk: {Nat.is_lt(k, 4n) == True{} : Bool}
  {Nat.mul(Nat.div(Nat.add(U32.to_nat(ld), U32.to_nat(H0(ld))), 4n), 4n) == Nat.add(U32.to_nat(ld), U32.to_nat(H0(ld))) : Nat}

def align2(ld, k, ek, hk):
  match k:
    case 0n:
      +x = U32.to_nat(ld)
      +a = Nat.div(x, 4n)
      +ex = exk(ld, 0n, ek)
      +eh = Equal.cong(U32, Nat, z => U32.to_nat(U32.and(U32.sub(4, z), 3)), (ld .&. 3 : U32), 0, U.to_nat_inj((ld .&. 3 : U32), 0, ek))
      mul4div(Nat.add(x, U32.to_nat(H0(ld))), a,
        Equal.trans(Nat, Nat.add(x, U32.to_nat(H0(ld))), Nat.add(x, 0n), Nat.mul(a, 4n), Equal.cong(Nat, Nat, z => Nat.add(x, z), U32.to_nat(H0(ld)), 0n, eh),
          Equal.trans(Nat, Nat.add(x, 0n), x, Nat.mul(a, 4n), N.add_zero(x),
            Equal.trans(Nat, x, Nat.add(Nat.mul(a, 4n), 0n), Nat.mul(a, 4n), ex, N.add_zero(Nat.mul(a, 4n))))))
    case 1n+k1:
      match k1:
        case 0n:
          +x = U32.to_nat(ld)
          +a = Nat.div(x, 4n)
          +ex = exk(ld, 1n, ek)
          +eh = Equal.cong(U32, Nat, z => U32.to_nat(U32.and(U32.sub(4, z), 3)), (ld .&. 3 : U32), 1, U.to_nat_inj((ld .&. 3 : U32), 1, ek))
          mul4div(Nat.add(x, U32.to_nat(H0(ld))), 1n+a,
            Equal.trans(Nat, Nat.add(x, U32.to_nat(H0(ld))), Nat.add(x, 3n), Nat.mul(1n+a, 4n), Equal.cong(Nat, Nat, z => Nat.add(x, z), U32.to_nat(H0(ld)), 3n, eh),
              al_k(x, a, 1n, 3n, ex, {==})))
        case 1n+k2:
          match k2:
            case 0n:
              +x = U32.to_nat(ld)
              +a = Nat.div(x, 4n)
              +ex = exk(ld, 2n, ek)
              +eh = Equal.cong(U32, Nat, z => U32.to_nat(U32.and(U32.sub(4, z), 3)), (ld .&. 3 : U32), 2, U.to_nat_inj((ld .&. 3 : U32), 2, ek))
              mul4div(Nat.add(x, U32.to_nat(H0(ld))), 1n+a,
                Equal.trans(Nat, Nat.add(x, U32.to_nat(H0(ld))), Nat.add(x, 2n), Nat.mul(1n+a, 4n), Equal.cong(Nat, Nat, z => Nat.add(x, z), U32.to_nat(H0(ld)), 2n, eh),
                  al_k(x, a, 2n, 2n, ex, {==})))
            case 1n+k3:
              match k3:
                case 0n:
                  +x = U32.to_nat(ld)
                  +a = Nat.div(x, 4n)
                  +ex = exk(ld, 3n, ek)
                  +eh = Equal.cong(U32, Nat, z => U32.to_nat(U32.and(U32.sub(4, z), 3)), (ld .&. 3 : U32), 3, U.to_nat_inj((ld .&. 3 : U32), 3, ek))
                  mul4div(Nat.add(x, U32.to_nat(H0(ld))), 1n+a,
                    Equal.trans(Nat, Nat.add(x, U32.to_nat(H0(ld))), Nat.add(x, 1n), Nat.mul(1n+a, 4n), Equal.cong(Nat, Nat, z => Nat.add(x, z), U32.to_nat(H0(ld)), 1n, eh),
                      al_k(x, a, 3n, 1n, ex, {==})))
                case 1n+k4:
                  Empty.absurd({Nat.mul(Nat.div(Nat.add(U32.to_nat(ld), U32.to_nat(H0(ld))), 4n), 4n) == Nat.add(U32.to_nat(ld), U32.to_nat(H0(ld))) : Nat}, AB.lt_zero_absurd(k4, hk))

# dst's length after the first h0 bytes is a multiple of 4.
law align:
  for +ld: U32
  {Nat.mul(Nat.div(Nat.add(U32.to_nat(ld), U32.to_nat(H0(ld))), 4n), 4n) == Nat.add(U32.to_nat(ld), U32.to_nat(H0(ld))) : Nat}

def align(ld):
  align2(ld, U32.to_nat((ld .&. 3 : U32)), {==}, and3_lt(ld))

# x + y < 2^e for x <= 4 * 2^d and y <= 3, when d + 2 < e (e a variable:
# the callers put 32n only in the final type).
law x3_lt_e:
  for +x: Nat
  for +y: Nat
  for +d: Nat
  for +e: Nat
  for +hy: {Nat.is_le(y, 3n) == True{} : Bool}
  for +hx: {Nat.is_le(x, Nat.mul(4n, Nat.pow(2n, d))) == True{} : Bool}
  for +he: {Nat.is_lt(Nat.add(2n, d), e) == True{} : Bool}
  {Nat.is_lt(Nat.add(x, y), Nat.pow(2n, e)) == True{} : Bool}

def x3_lt_e(x, y, d, e, hy, hx, he):
  +pp = Nat.pow(2n, d)
  +q = Nat.pow(2n, Nat.add(2n, d))
  +eq = N.mul_assoc(2n, 2n, pp)
  +hxq = AB.subst(Nat, z => {Nat.is_le(x, z) == True{} : Bool}, Nat.mul(Nat.mul(2n, 2n), pp), Nat.mul(2n, Nat.mul(2n, pp)), eq, hx)
  +h1 = N.le_trans(Nat.add(x, y), Nat.add(q, y), Nat.add(q, 3n), N.le_add_mono_r(y, x, q, hxq), N.le_add_mono_l(q, y, 3n, hy))
  +h41 = N.le_mul_l(4n, 1n, pp, Equal.trans(Bool, Nat.is_le(1n, pp), Nat.is_lt(0n, pp), True{}, N.le_succ_lt(0n, pp), AB.pow_pos(d)))
  +h4q = AB.subst(Nat, z => {Nat.is_le(4n, z) == True{} : Bool}, Nat.mul(Nat.mul(2n, 2n), pp), Nat.mul(2n, Nat.mul(2n, pp)), eq, h41)
  +h4 = Equal.trans(Bool, Nat.is_lt(3n, q), Nat.is_le(4n, q), True{}, Equal.sym(Bool, Nat.is_le(4n, q), Nat.is_lt(3n, q), N.le_succ_lt(3n, q)), h4q)
  +h2 = AB.subst(Nat, z => {Nat.is_lt(Nat.add(q, 3n), z) == True{} : Bool}, Nat.add(q, q), Nat.add(q, Nat.add(q, 0n)),
    Equal.cong(Nat, Nat, z => Nat.add(q, z), q, Nat.add(q, 0n), Equal.sym(Nat, Nat.add(q, 0n), q, N.add_zero(q))), N.lt_add_l(q, 3n, q, h4))
  +h3 = N.pow_le(Nat.add(3n, d), e, Equal.trans(Bool, Nat.is_le(Nat.add(3n, d), e), Nat.is_lt(Nat.add(2n, d), e), True{}, N.le_succ_lt(Nat.add(2n, d), e), he))
  N.le_lt_trans(Nat.add(x, y), Nat.add(q, 3n), Nat.pow(2n, e), h1, N.lt_le_trans(Nat.add(q, 3n), Nat.pow(2n, Nat.add(3n, d)), Nat.pow(2n, e), h2, h3))

# The word count (np + 3) >> 2 covers np bytes with less than one word left.
law cnt1:
  for +np: Nat
  {Nat.is_le(np, Nat.mul(Nat.div(Nat.add(np, 3n), 4n), 4n)) == True{} : Bool}

def cnt1(np):
  +xx = Nat.add(np, 3n)
  +q = Nat.div(xx, 4n)
  +rm = Nat.mod(xx, 4n)
  +h1 = AB.subst(Nat, z => {Nat.is_le(z, Nat.add(Nat.mul(q, 4n), 3n)) == True{} : Bool}, Nat.add(Nat.mul(q, 4n), rm), xx, N.div_mod(xx, 4n),
    N.le_add_mono_l(Nat.mul(q, 4n), rm, 3n, Equal.trans(Bool, Nat.is_le(rm, 3n), Nat.is_lt(rm, 4n), True{}, Equal.sym(Bool, Nat.is_lt(rm, 4n), Nat.is_le(rm, 3n), N.lt_succ_iff(rm, 3n)), N.mod_lt(xx, 4n, {==}))))
  +h2 = AB.subst(Nat, z => {Nat.is_le(z, Nat.add(Nat.mul(q, 4n), 3n)) == True{} : Bool}, xx, Nat.add(3n, np), N.add_comm(np, 3n), h1)
  AB.subst(Nat, z => {Nat.is_le(Nat.add(3n, np), z) == True{} : Bool}, Nat.add(Nat.mul(q, 4n), 3n), Nat.add(3n, Nat.mul(q, 4n)), N.add_comm(Nat.mul(q, 4n), 3n), h2)

law cnt2:
  for +np: Nat
  {Nat.is_lt(Nat.mul(Nat.div(Nat.add(np, 3n), 4n), 4n), Nat.add(np, 4n)) == True{} : Bool}

def cnt2(np):
  +xx = Nat.add(np, 3n)
  +q = Nat.div(xx, 4n)
  +rm = Nat.mod(xx, 4n)
  N.le_lt_trans(Nat.mul(q, 4n), xx, Nat.add(np, 4n),
    AB.subst(Nat, z => {Nat.is_le(Nat.mul(q, 4n), z) == True{} : Bool}, Nat.add(Nat.mul(q, 4n), rm), xx, N.div_mod(xx, 4n), N.le_add_r(Nat.mul(q, 4n), rm)),
    N.lt_add_l(np, 3n, 4n, {==}))

# The fast append on mirrors
# ==========================

# The bytes done one at a time, the bytes left, and where they start.
def HH(+ld: U32, +n: U32) -> U32:
  U32.min(H0(ld), n)

def NPw(+ld: U32, +n: U32) -> U32:
  U32.sub(n, HH(ld, n))

def QQ(+ld: U32, +s: U32, +n: U32) -> U32:
  U32.add(s, HH(ld, n))

def NW(+ld: U32, +n: U32) -> Nat:
  U32.to_nat(U32.shrn(U32.add(NPw(ld, n), 3), 2n))

def SH(+q: U32) -> Nat:
  U32.to_nat(U32.shln(U32.and(q, 3), 3n))

def TF(+ld: U32, +ts: P.Tree<U32>, +s: U32, +n: U32, +l1: U32, +t1: P.Tree<U32>) -> P.Tree<U32>:
  AWT(NW(ld, n), ts, U32.add(U32.shrn(QQ(ld, s, n), 2n), 1), C.WD(ts, U32.shrn(QQ(ld, s, n), 2n)), t1, U32.shrn(QQ(ld, s, n), 2n), U32.shrn(l1, 2n), SH(QQ(ld, s, n)))

# With BT(l1, t1) the result of the first bytes, fast append is these mirrors.
law fa_eq:
  for +ld: U32
  for +td: P.Tree<U32>
  for +ls: U32
  for +ts: P.Tree<U32>
  for +s: U32
  for +n: U32
  for +l1: U32
  for +t1: P.Tree<U32>
  for +e1: {C.BT(l1, t1) == Pair.fst(D.Bytes, D.Bytes, B.append(C.BT(ld, td), C.BT(ls, ts), s, HH(ld, n))) : D.Bytes}
  {FA.append(C.BT(ld, td), C.BT(ls, ts), s, n) == (C.BT(U32.add(l1, NPw(ld, n)), TF(ld, ts, s, n, l1, t1)), C.BT(ls, ts)) : D.Bytes & D.Bytes}

def fa_eq(ld, td, ls, ts, s, n, l1, t1, e1):
  +h = HH(ld, n)
  +q = QQ(ld, s, n)
  +qw = U32.shrn(q, 2n)
  %Equal.sym(D.Bytes & D.Bytes, B.append(C.BT(ld, td), C.BT(ls, ts), s, h), (Pair.fst(D.Bytes, D.Bytes, B.append(C.BT(ld, td), C.BT(ls, ts), s, h)), C.BT(ls, ts)),
    X.append_pair_t(ld, td, ls, ts, s, h)) :
    {FA.append.k(NPw(ld, n), q, _) == (C.BT(U32.add(l1, NPw(ld, n)), TF(ld, ts, s, n, l1, t1)), C.BT(ls, ts)) : D.Bytes & D.Bytes}
  %e1 : {FA.append.k(NPw(ld, n), q, (_, C.BT(ls, ts))) == (C.BT(U32.add(l1, NPw(ld, n)), TF(ld, ts, s, n, l1, t1)), C.BT(ls, ts)) : D.Bytes & D.Bytes}
  %Equal.sym(Array<U32> & U32, Array.get(U32, P.fromT(U32, ts), qw), (P.fromT(U32, ts), C.WD(ts, qw)), P.get_pair_t(U32, ts, qw)) :
    {FA.append.w(l1, NPw(ld, n), q, P.fromT(U32, t1), ls, _) == (C.BT(U32.add(l1, NPw(ld, n)), TF(ld, ts, s, n, l1, t1)), C.BT(ls, ts)) : D.Bytes & D.Bytes}
  %Equal.sym(Array<U32> & Array<U32>,
    FA.append.words(NW(ld, n), Array.get(U32, P.fromT(U32, ts), U32.add(qw, 1)), C.WD(ts, qw), P.fromT(U32, t1), qw, U32.shrn(l1, 2n), SH(q)),
    (P.fromT(U32, TF(ld, ts, s, n, l1, t1)), P.fromT(U32, ts)),
    aw_eq(NW(ld, n), ts, U32.add(qw, 1), C.WD(ts, qw), t1, qw, U32.shrn(l1, 2n), SH(q))) :
    {FA.append.fin(U32.add(l1, NPw(ld, n)), ls, _) == (C.BT(U32.add(l1, NPw(ld, n)), TF(ld, ts, s, n, l1, t1)), C.BT(ls, ts)) : D.Bytes & D.Bytes}
  {==}

# The last list step: the bytes of the prefix and of the words make the slice.
law fin_eq:
  for +v1: List<&2, U32>
  for +vd: List<&2, U32>
  for +us: List<&2, U32>
  for +ls: Nat
  for +s: Nat
  for +hh: Nat
  for +qn: Nat
  for +np: Nat
  for +nn: Nat
  for +hv: {v1 == List.append(&2, U32, vd, D.slice(List.take(&2, U32, us, ls), s, hh)) : List<&2, U32>}
  for +hq: {qn == Nat.add(s, hh) : Nat}
  for +hnp: {np == Nat.sub(nn, hh) : Nat}
  for +hhn: {Nat.is_le(hh, nn) == True{} : Bool}
  for +hb: {Nat.is_le(Nat.add(s, nn), ls) == True{} : Bool}
  {List.append(&2, U32, v1, List.take(&2, U32, List.drop(&2, U32, us, qn), np)) == List.append(&2, U32, vd, D.slice(List.take(&2, U32, us, ls), s, nn)) : List<&2, U32>}

def fin_eq(v1, vd, us, ls, s, hh, qn, np, nn, hv, hq, hnp, hhn, hb):
  +xs = List.take(&2, U32, us, ls)
  +rest = Nat.sub(nn, hh)
  +RHS = List.append(&2, U32, vd, D.slice(xs, s, nn))
  +esum = Equal.trans(Nat, Nat.add(Nat.add(s, hh), rest), Nat.add(s, Nat.add(hh, rest)), Nat.add(s, nn), N.add_assoc(s, hh, rest),
    Equal.cong(Nat, Nat, z => Nat.add(s, z), Nat.add(hh, rest), nn, N.le_sub_add(hh, nn, hhn)))
  %Equal.sym(Nat, np, rest, hnp) : {List.append(&2, U32, v1, List.take(&2, U32, List.drop(&2, U32, us, qn), _)) == RHS : List<&2, U32>}
  %Equal.sym(Nat, qn, Nat.add(s, hh), hq) : {List.append(&2, U32, v1, List.take(&2, U32, List.drop(&2, U32, us, _), rest)) == RHS : List<&2, U32>}
  %Equal.sym(List<&2, U32>, v1, List.append(&2, U32, vd, D.slice(xs, s, hh)), hv) :
    {List.append(&2, U32, _, List.take(&2, U32, List.drop(&2, U32, us, Nat.add(s, hh)), rest)) == RHS : List<&2, U32>}
  %slice_take(us, ls, Nat.add(s, hh), rest,
    AB.subst(Nat, z => {Nat.is_le(z, ls) == True{} : Bool}, Nat.add(s, nn), Nat.add(Nat.add(s, hh), rest), Equal.sym(Nat, Nat.add(Nat.add(s, hh), rest), Nat.add(s, nn), esum), hb)) :
    {List.append(&2, U32, List.append(&2, U32, vd, D.slice(xs, s, hh)), _) == RHS : List<&2, U32>}
  Equal.trans(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, vd, D.slice(xs, s, hh)), D.slice(xs, Nat.add(s, hh), rest)),
    List.append(&2, U32, vd, List.append(&2, U32, D.slice(xs, s, hh), D.slice(xs, Nat.add(s, hh), rest))), RHS,
    X.append_assoc(vd, D.slice(xs, s, hh), D.slice(xs, Nat.add(s, hh), rest)),
    Equal.cong(List<&2, U32>, List<&2, U32>, z => List.append(&2, U32, vd, z),
      List.append(&2, U32, D.slice(xs, s, hh), D.slice(xs, Nat.add(s, hh), rest)), D.slice(xs, s, nn),
      Equal.trans(List<&2, U32>, List.append(&2, U32, D.slice(xs, s, hh), D.slice(xs, Nat.add(s, hh), rest)), D.slice(xs, s, Nat.add(hh, rest)), D.slice(xs, s, nn),
        slice_split(xs, s, hh, rest), Equal.cong(Nat, List<&2, U32>, z => D.slice(xs, s, z), Nat.add(hh, rest), nn, N.le_sub_add(hh, nn, hhn)))))

# Facts shared by the three laws
# ==============================

def D1(+ld: U32, +td: P.Tree<U32>, +ls: U32, +ts: P.Tree<U32>, +s: U32, +n: U32) -> D.Bytes:
  Pair.fst(D.Bytes, D.Bytes, B.append(C.BT(ld, td), C.BT(ls, ts), s, HH(ld, n)))

law hh_le:
  for +ld: U32
  for +n: U32
  {Nat.is_le(U32.to_nat(HH(ld, n)), U32.to_nat(n)) == True{} : Bool}

def hh_le(ld, n):
  AB.subst(Nat, y => {Nat.is_le(y, U32.to_nat(n)) == True{} : Bool}, Nat.min(U32.to_nat(H0(ld)), U32.to_nat(n)), U32.to_nat(HH(ld, n)),
    Equal.sym(Nat, U32.to_nat(HH(ld, n)), Nat.min(U32.to_nat(H0(ld)), U32.to_nat(n)), U.to_nat_min(H0(ld), n)),
    min_le(U32.to_nat(H0(ld)), U32.to_nat(n)))

law hc_h:
  for +ld: U32
  for +td: P.Tree<U32>
  for +n: U32
  for +hc: {Nat.is_le(Nat.add(D.size(C.BT(ld, td)), U32.to_nat(n)), D.cap(C.BT(ld, td))) == True{} : Bool}
  {Nat.is_le(Nat.add(U32.to_nat(ld), U32.to_nat(HH(ld, n))), D.cap(C.BT(ld, td))) == True{} : Bool}

def hc_h(ld, td, n, hc):
  N.le_trans(Nat.add(U32.to_nat(ld), U32.to_nat(HH(ld, n))), Nat.add(U32.to_nat(ld), U32.to_nat(n)), D.cap(C.BT(ld, td)),
    N.le_add_mono_l(U32.to_nat(ld), U32.to_nat(HH(ld, n)), U32.to_nat(n), hh_le(ld, n)), hc)

law ok1:
  for +ld: U32
  for +td: P.Tree<U32>
  for +ls: U32
  for +ts: P.Tree<U32>
  for +d: Nat
  for +s: U32
  for +n: U32
  for +l1: U32
  for +t1: P.Tree<U32>
  for +e1: {C.BT(l1, t1) == D1(ld, td, ls, ts, s, n) : D.Bytes}
  for +hd: {D.ok(C.BT(ld, td), d) == True{} : Bool}
  for +hc: {Nat.is_le(Nat.add(D.size(C.BT(ld, td)), U32.to_nat(n)), D.cap(C.BT(ld, td))) == True{} : Bool}
  {D.ok(C.BT(l1, t1), d) == True{} : Bool}

def ok1(ld, td, ls, ts, d, s, n, l1, t1, e1, hd, hc):
  AB.subst(D.Bytes, y => {D.ok(y, d) == True{} : Bool}, D1(ld, td, ls, ts, s, n), C.BT(l1, t1), Equal.sym(D.Bytes, C.BT(l1, t1), D1(ld, td, ls, ts, s, n), e1),
    X.append_ok_t(ld, td, ls, ts, d, s, HH(ld, n), hd, hc_h(ld, td, n, hc)))

law el1:
  for +ld: U32
  for +td: P.Tree<U32>
  for +ls: U32
  for +ts: P.Tree<U32>
  for +d: Nat
  for +s: U32
  for +n: U32
  for +l1: U32
  for +t1: P.Tree<U32>
  for +e1: {C.BT(l1, t1) == D1(ld, td, ls, ts, s, n) : D.Bytes}
  for +hd: {D.ok(C.BT(ld, td), d) == True{} : Bool}
  for +hc: {Nat.is_le(Nat.add(D.size(C.BT(ld, td)), U32.to_nat(n)), D.cap(C.BT(ld, td))) == True{} : Bool}
  {U32.to_nat(l1) == Nat.add(U32.to_nat(ld), U32.to_nat(HH(ld, n))) : Nat}

def el1(ld, td, ls, ts, d, s, n, l1, t1, e1, hd, hc):
  Equal.trans(Nat, U32.to_nat(l1), D.size(D1(ld, td, ls, ts, s, n)), Nat.add(U32.to_nat(ld), U32.to_nat(HH(ld, n))),
    Equal.cong(D.Bytes, Nat, b => D.size(b), C.BT(l1, t1), D1(ld, td, ls, ts, s, n), e1),
    ag_size(U32.to_nat(HH(ld, n)), ld, td, ls, ts, d, s, hd, hc_h(ld, td, n, hc)))

law enp:
  for +ld: U32
  for +n: U32
  {U32.to_nat(NPw(ld, n)) == Nat.sub(U32.to_nat(n), U32.to_nat(HH(ld, n))) : Nat}

def enp(ld, n):
  U.to_nat_sub_le(n, HH(ld, n), Equal.trans(Bool, U32.is_le(HH(ld, n), n), Nat.is_le(U32.to_nat(HH(ld, n)), U32.to_nat(n)), True{}, U.is_le_to_nat(HH(ld, n), n), hh_le(ld, n)))

# l1 + (n - h) = ld + n.
law esum:
  for +ld: U32
  for +l1: U32
  for +n: U32
  for +el: {U32.to_nat(l1) == Nat.add(U32.to_nat(ld), U32.to_nat(HH(ld, n))) : Nat}
  {Nat.add(U32.to_nat(l1), U32.to_nat(NPw(ld, n))) == Nat.add(U32.to_nat(ld), U32.to_nat(n)) : Nat}

def esum(ld, l1, n, el):
  +a = U32.to_nat(ld)
  +h = U32.to_nat(HH(ld, n))
  +nn = U32.to_nat(n)
  %Equal.sym(Nat, U32.to_nat(l1), Nat.add(a, h), el) : {Nat.add(_, U32.to_nat(NPw(ld, n))) == Nat.add(a, nn) : Nat}
  %Equal.sym(Nat, U32.to_nat(NPw(ld, n)), Nat.sub(nn, h), enp(ld, n)) : {Nat.add(Nat.add(a, h), _) == Nat.add(a, nn) : Nat}
  Equal.trans(Nat, Nat.add(Nat.add(a, h), Nat.sub(nn, h)), Nat.add(a, Nat.add(h, Nat.sub(nn, h))), Nat.add(a, nn), N.add_assoc(a, h, Nat.sub(nn, h)),
    Equal.cong(Nat, Nat, z => Nat.add(a, z), Nat.add(h, Nat.sub(nn, h)), nn, N.le_sub_add(h, nn, hh_le(ld, n))))

law hlen0:
  for +ld: U32
  for +td: P.Tree<U32>
  for +l1: U32
  for +d: Nat
  for +n: U32
  for +el: {U32.to_nat(l1) == Nat.add(U32.to_nat(ld), U32.to_nat(HH(ld, n))) : Nat}
  for +hd: {D.ok(C.BT(ld, td), d) == True{} : Bool}
  for +hc: {Nat.is_le(Nat.add(D.size(C.BT(ld, td)), U32.to_nat(n)), D.cap(C.BT(ld, td))) == True{} : Bool}
  {Nat.is_le(Nat.add(U32.to_nat(l1), U32.to_nat(NPw(ld, n))), Nat.mul(4n, Nat.pow(2n, d))) == True{} : Bool}

def hlen0(ld, td, l1, d, n, el, hd, hc):
  AB.subst(Nat, y => {Nat.is_le(y, Nat.mul(4n, Nat.pow(2n, d))) == True{} : Bool}, Nat.add(U32.to_nat(ld), U32.to_nat(n)), Nat.add(U32.to_nat(l1), U32.to_nat(NPw(ld, n))),
    Equal.sym(Nat, Nat.add(U32.to_nat(l1), U32.to_nat(NPw(ld, n))), Nat.add(U32.to_nat(ld), U32.to_nat(n)), esum(ld, l1, n, el)),
    AB.subst(Nat, y => {Nat.is_le(Nat.add(U32.to_nat(ld), U32.to_nat(n)), y) == True{} : Bool}, D.cap(C.BT(ld, td)), Nat.mul(4n, Nat.pow(2n, d)), O.cap_ok_t(ld, td, d, hd), hc))

# The pair law
# ============

def fap.go(+ld: U32, +td: P.Tree<U32>, +ls: U32, +ts: P.Tree<U32>, +s: U32, +n: U32, m: C.BMirror(D1(ld, td, ls, ts, s, n))) ->
  {FA.append(C.BT(ld, td), C.BT(ls, ts), s, n) == (Pair.fst(D.Bytes, D.Bytes, FA.append(C.BT(ld, td), C.BT(ls, ts), s, n)), C.BT(ls, ts)) : D.Bytes & D.Bytes}:
  (+l1, m2) = m
  (+t1, +e1) = m2
  %Equal.sym(D.Bytes & D.Bytes, FA.append(C.BT(ld, td), C.BT(ls, ts), s, n), (C.BT(U32.add(l1, NPw(ld, n)), TF(ld, ts, s, n, l1, t1)), C.BT(ls, ts)),
    fa_eq(ld, td, ls, ts, s, n, l1, t1, e1)) :
    {_ == (Pair.fst(D.Bytes, D.Bytes, _), C.BT(ls, ts)) : D.Bytes & D.Bytes}
  {==}

law fast_append_pair_t:
  for +ld: U32
  for +td: P.Tree<U32>
  for +ls: U32
  for +ts: P.Tree<U32>
  for +s: U32
  for +n: U32
  {FA.append(C.BT(ld, td), C.BT(ls, ts), s, n) == (Pair.fst(D.Bytes, D.Bytes, FA.append(C.BT(ld, td), C.BT(ls, ts), s, n)), C.BT(ls, ts)) : D.Bytes & D.Bytes}

def fast_append_pair_t(ld, td, ls, ts, s, n):
  fap.go(ld, td, ls, ts, s, n, C.bmirror(D1(ld, td, ls, ts, s, n)))

# The ok law
# ==========

def fao.go(+ld: U32, +td: P.Tree<U32>, +ls: U32, +ts: P.Tree<U32>, +d: Nat, +s: U32, +n: U32,
  +hd: {D.ok(C.BT(ld, td), d) == True{} : Bool},
  +hc: {Nat.is_le(Nat.add(D.size(C.BT(ld, td)), U32.to_nat(n)), D.cap(C.BT(ld, td))) == True{} : Bool},
  m: C.BMirror(D1(ld, td, ls, ts, s, n))) ->
  {D.ok(Pair.fst(D.Bytes, D.Bytes, FA.append(C.BT(ld, td), C.BT(ls, ts), s, n)), d) == True{} : Bool}:
  (+l1, m2) = m
  (+t1, +e1) = m2
  +q = QQ(ld, s, n)
  +hk1 = ok1(ld, td, ls, ts, d, s, n, l1, t1, e1, hd, hc)
  +el = el1(ld, td, ls, ts, d, s, n, l1, t1, e1, hd, hc)
  +hdd = C.ok_d(ld, td, d, hd)
  +hl0 = hlen0(ld, td, l1, d, n, el, hd, hc)
  %Equal.sym(D.Bytes & D.Bytes, FA.append(C.BT(ld, td), C.BT(ls, ts), s, n), (C.BT(U32.add(l1, NPw(ld, n)), TF(ld, ts, s, n, l1, t1)), C.BT(ls, ts)),
    fa_eq(ld, td, ls, ts, s, n, l1, t1, e1)) :
    {D.ok(Pair.fst(D.Bytes, D.Bytes, _), d) == True{} : Bool}
  C.ok_mk(U32.add(l1, NPw(ld, n)), TF(ld, ts, s, n, l1, t1), d,
    aw_full(NW(ld, n), ts, U32.add(U32.shrn(q, 2n), 1), C.WD(ts, U32.shrn(q, 2n)), t1, U32.shrn(q, 2n), U32.shrn(l1, 2n), SH(q), d, C.ok_full(l1, t1, d, hk1)),
    hdd,
    AB.subst(Nat, y => {Nat.is_le(y, Nat.mul(4n, Nat.pow(2n, d))) == True{} : Bool}, Nat.add(U32.to_nat(l1), U32.to_nat(NPw(ld, n))), U32.to_nat(U32.add(l1, NPw(ld, n))),
      Equal.sym(Nat, U32.to_nat(U32.add(l1, NPw(ld, n))), Nat.add(U32.to_nat(l1), U32.to_nat(NPw(ld, n))), C.add_fits(l1, NPw(ld, n), d, hdd, hl0)), hl0))

law fast_append_ok_t:
  for +ld: U32
  for +td: P.Tree<U32>
  for +ls: U32
  for +ts: P.Tree<U32>
  for +d: Nat
  for +s: U32
  for +n: U32
  for +hd: {D.ok(C.BT(ld, td), d) == True{} : Bool}
  for +hc: {Nat.is_le(Nat.add(D.size(C.BT(ld, td)), U32.to_nat(n)), D.cap(C.BT(ld, td))) == True{} : Bool}
  {D.ok(Pair.fst(D.Bytes, D.Bytes, FA.append(C.BT(ld, td), C.BT(ls, ts), s, n)), d) == True{} : Bool}

def fast_append_ok_t(ld, td, ls, ts, d, s, n, hd, hc):
  fao.go(ld, td, ls, ts, d, s, n, hd, hc, C.bmirror(D1(ld, td, ls, ts, s, n)))

# The view law
# ============

law esum_n:
  for +a: Nat
  for +h: Nat
  for +nn: Nat
  for +hle: {Nat.is_le(h, nn) == True{} : Bool}
  {Nat.add(Nat.add(a, h), Nat.sub(nn, h)) == Nat.add(a, nn) : Nat}

def esum_n(a, h, nn, hle):
  Equal.trans(Nat, Nat.add(Nat.add(a, h), Nat.sub(nn, h)), Nat.add(a, Nat.add(h, Nat.sub(nn, h))), Nat.add(a, nn), N.add_assoc(a, h, Nat.sub(nn, h)),
    Equal.cong(Nat, Nat, z => Nat.add(a, z), Nat.add(h, Nat.sub(nn, h)), nn, N.le_sub_add(h, nn, hle)))

# What the word loop leaves: the bytes in use after the prefix, then src from q.
law avc:
  for +b0: Bool
  for +ld: U32
  for +td: P.Tree<U32>
  for +ls: U32
  for +ts: P.Tree<U32>
  for +d: Nat
  for +e: Nat
  for +s: U32
  for +n: U32
  for +l1: U32
  for +t1: P.Tree<U32>
  for +hb0: {Nat.is_lt(U32.to_nat(H0(ld)), U32.to_nat(n)) == b0 : Bool}
  for +e1: {C.BT(l1, t1) == D1(ld, td, ls, ts, s, n) : D.Bytes}
  for +hd: {D.ok(C.BT(ld, td), d) == True{} : Bool}
  for +he: {D.ok(C.BT(ls, ts), e) == True{} : Bool}
  for +hs: {Nat.is_le(Nat.add(U32.to_nat(s), U32.to_nat(n)), D.size(C.BT(ls, ts))) == True{} : Bool}
  for +hc: {Nat.is_le(Nat.add(D.size(C.BT(ld, td)), U32.to_nat(n)), D.cap(C.BT(ld, td))) == True{} : Bool}
  {List.take(&2, U32, US(TF(ld, ts, s, n, l1, t1)), Nat.add(U32.to_nat(l1), U32.to_nat(NPw(ld, n)))) == List.append(&2, U32, D.view(C.BT(l1, t1)), List.take(&2, U32, List.drop(&2, U32, US(ts), U32.to_nat(QQ(ld, s, n))), U32.to_nat(NPw(ld, n)))) : List<&2, U32>}

def avc(b0, ld, td, ls, ts, d, e, s, n, l1, t1, hb0, e1, hd, he, hs, hc):
  match b0:
    case True{}:
      +q = QQ(ld, s, n)
      +qw = U32.shrn(q, 2n)
      +L1 = U32.to_nat(l1)
      +NP = U32.to_nat(NPw(ld, n))
      +qn = U32.to_nat(q)
      +sn = U32.to_nat(s)
      +nn = U32.to_nat(n)
      +hhn = U32.to_nat(HH(ld, n))
      +h0n = U32.to_nat(H0(ld))
      +r0 = U32.to_nat((q .&. 3 : U32))
      +ME = Nat.mul(4n, Nat.pow(2n, e))
      +MD = Nat.mul(4n, Nat.pow(2n, d))
      +v1 = D.view(C.BT(l1, t1))
      +hfs = C.ok_full(ls, ts, e, he)
      +hes = C.ok_d(ls, ts, e, he)
      +hdd = C.ok_d(ld, td, d, hd)
      +hk1 = ok1(ld, td, ls, ts, d, s, n, l1, t1, e1, hd, hc)
      +el = el1(ld, td, ls, ts, d, s, n, l1, t1, e1, hd, hc)
      +hl0 = hlen0(ld, td, l1, d, n, el, hd, hc)
      +hsl = N.le_trans(Nat.add(sn, nn), U32.to_nat(ls), ME, hs, C.ok_len(ls, ts, e, he))
      +ehh = Equal.trans(Nat, hhn, Nat.min(h0n, nn), h0n, U.to_nat_min(H0(ld), n), min_l(h0n, nn, hb0))
      +eL = Equal.trans(Nat, L1, Nat.add(U32.to_nat(ld), hhn), Nat.add(U32.to_nat(ld), h0n), el, Equal.cong(Nat, Nat, z => Nat.add(U32.to_nat(ld), z), hhn, h0n, ehh))
      +hdi0 = Equal.trans(Nat, Nat.mul(U32.to_nat(U32.shrn(l1, 2n)), 4n), Nat.mul(Nat.div(L1, 4n), 4n), Nat.add(L1, 0n),
        Equal.cong(Nat, Nat, z => Nat.mul(z, 4n), U32.to_nat(U32.shrn(l1, 2n)), Nat.div(L1, 4n), U.to_nat_shrn(l1, 2n)),
        Equal.trans(Nat, Nat.mul(Nat.div(L1, 4n), 4n), Nat.mul(Nat.div(Nat.add(U32.to_nat(ld), h0n), 4n), 4n), Nat.add(L1, 0n),
          Equal.cong(Nat, Nat, z => Nat.mul(Nat.div(z, 4n), 4n), L1, Nat.add(U32.to_nat(ld), h0n), eL),
          Equal.trans(Nat, Nat.mul(Nat.div(Nat.add(U32.to_nat(ld), h0n), 4n), 4n), Nat.add(U32.to_nat(ld), h0n), Nat.add(L1, 0n), align(ld),
            Equal.trans(Nat, Nat.add(U32.to_nat(ld), h0n), L1, Nat.add(L1, 0n), Equal.sym(Nat, L1, Nat.add(U32.to_nat(ld), h0n), eL),
              Equal.sym(Nat, Nat.add(L1, 0n), L1, N.add_zero(L1))))))
      +hsi0 = Equal.trans(Nat, Nat.add(Nat.mul(U32.to_nat(qw), 4n), r0), Nat.add(Nat.mul(Nat.div(qn, 4n), 4n), r0), Nat.add(qn, 0n),
        Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(z, 4n), r0), U32.to_nat(qw), Nat.div(qn, 4n), U.to_nat_shrn(q, 2n)),
        Equal.trans(Nat, Nat.add(Nat.mul(Nat.div(qn, 4n), 4n), r0), qn, Nat.add(qn, 0n), Equal.sym(Nat, qn, Nat.add(Nat.mul(Nat.div(qn, 4n), 4n), r0), exk(q, r0, {==})),
          Equal.sym(Nat, Nat.add(qn, 0n), qn, N.add_zero(qn))))
      +hbq = N.le_trans(Nat.add(sn, hhn), Nat.add(sn, nn), ME, N.le_add_mono_l(sn, hhn, nn, hh_le(ld, n)), hsl)
      +eq = C.add_fits(s, HH(ld, n), e, hes, hbq)
      +hhl = AB.subst(Nat, z => {Nat.is_lt(z, nn) == True{} : Bool}, h0n, hhn, Equal.sym(Nat, hhn, h0n, ehh), hb0)
      +hq4 = AB.subst(Nat, z => {Nat.is_lt(z, ME) == True{} : Bool}, Nat.add(sn, hhn), qn, Equal.sym(Nat, qn, Nat.add(sn, hhn), eq),
        N.lt_le_trans(Nat.add(sn, hhn), Nat.add(sn, nn), ME, N.lt_add_l(sn, hhn, nn, hhl), hsl))
      +hdq = AB.subst(Nat, z => {Nat.is_lt(z, Nat.pow(2n, e)) == True{} : Bool}, Nat.div(qn, 4n), U32.to_nat(qw), Equal.sym(Nat, U32.to_nat(qw), Nat.div(qn, 4n), U.to_nat_shrn(q, 2n)),
        N.div_lt(qn, 4n, Nat.pow(2n, e), {==}, hq4))
      +hp0 = C.inc_fits(qw, e, hes, N.lt_le_trans(U32.to_nat(qw), Nat.pow(2n, e), ME, hdq, N.le_add_r(Nat.pow(2n, e), Nat.add(Nat.pow(2n, e), Nat.add(Nat.pow(2n, e), Nat.add(Nat.pow(2n, e), 0n))))))
      +eqs = Equal.trans(Nat, Nat.add(qn, NP), Nat.add(Nat.add(sn, hhn), NP), Nat.add(sn, nn), Equal.cong(Nat, Nat, z => Nat.add(z, NP), qn, Nat.add(sn, hhn), eq),
        Equal.trans(Nat, Nat.add(Nat.add(sn, hhn), NP), Nat.add(Nat.add(sn, hhn), Nat.sub(nn, hhn)), Nat.add(sn, nn), Equal.cong(Nat, Nat, z => Nat.add(Nat.add(sn, hhn), z), NP, Nat.sub(nn, hhn), enp(ld, n)),
          esum_n(sn, hhn, nn, hh_le(ld, n))))
      +hq0 = AB.subst(Nat, z => {Nat.is_le(z, ME) == True{} : Bool}, Nat.add(sn, nn), Nat.add(qn, NP), Equal.sym(Nat, Nat.add(qn, NP), Nat.add(sn, nn), eqs), hsl)
      +hnp = N.le_trans(NP, Nat.add(L1, NP), MD, N.le_add_l(NP, L1), hl0)
      +efit = U.to_nat_add_fits_p(NPw(ld, n), 3, x3_lt_e(NP, U32.to_nat(3), d, 32n, {==}, hnp, C.he32(d, hdd)))
      +enw = Equal.trans(Nat, NW(ld, n), Nat.div(U32.to_nat(U32.add(NPw(ld, n), 3)), 4n), Nat.div(Nat.add(NP, 3n), 4n), U.to_nat_shrn(U32.add(NPw(ld, n), 3), 2n),
        Equal.cong(Nat, Nat, z => Nat.div(z, 4n), U32.to_nat(U32.add(NPw(ld, n), 3)), Nat.add(NP, 3n), efit))
      +hc10 = AB.subst(Nat, z => {Nat.is_le(NP, Nat.mul(z, 4n)) == True{} : Bool}, Nat.div(Nat.add(NP, 3n), 4n), NW(ld, n), Equal.sym(Nat, NW(ld, n), Nat.div(Nat.add(NP, 3n), 4n), enw), cnt1(NP))
      +hc20 = AB.subst(Nat, z => {Nat.is_lt(Nat.mul(z, 4n), Nat.add(NP, 4n)) == True{} : Bool}, Nat.div(Nat.add(NP, 3n), 4n), NW(ld, n), Equal.sym(Nat, NW(ld, n), Nat.div(Nat.add(NP, 3n), 4n), enw), cnt2(NP))
      +hinv0 = Equal.trans(List<&2, U32>, List.take(&2, U32, US(t1), Nat.add(L1, 0n)), List.take(&2, U32, US(t1), L1), List.append(&2, U32, v1, List.take(&2, U32, List.drop(&2, U32, US(ts), qn), 0n)),
        Equal.cong(Nat, List<&2, U32>, z => List.take(&2, U32, US(t1), z), Nat.add(L1, 0n), L1, N.add_zero(L1)),
        Equal.sym(List<&2, U32>, List.append(&2, U32, v1, List.take(&2, U32, List.drop(&2, U32, US(ts), qn), 0n)), v1,
          Equal.trans(List<&2, U32>, List.append(&2, U32, v1, List.take(&2, U32, List.drop(&2, U32, US(ts), qn), 0n)), List.append(&2, U32, v1, Nil{}), v1,
            Equal.cong(List<&2, U32>, List<&2, U32>, z => List.append(&2, U32, v1, z), List.take(&2, U32, List.drop(&2, U32, US(ts), qn), 0n), Nil{}, Q.take_zero(List.drop(&2, U32, US(ts), qn))),
            X.append_nil(v1))))
      av(NW(ld, n), Nat.is_le(Nat.add(0n, 4n), NP), ts, e, t1, d, U32.add(qw, 1), C.WD(ts, qw), qw, U32.shrn(l1, 2n), SH(q), L1, qn, r0, 0n, NP, v1,
        {==}, hfs, hes, C.ok_full(l1, t1, d, hk1), hdd, hdi0, hsi0, hp0, {==}, shq(q), and3_lt(q), hq0, hl0, N.le_zero_l(NP), hc10, hc20, hinv0)
    case False{}:
      +q = QQ(ld, s, n)
      +qw = U32.shrn(q, 2n)
      +L1 = U32.to_nat(l1)
      +NP = U32.to_nat(NPw(ld, n))
      +qn = U32.to_nat(q)
      +nn = U32.to_nat(n)
      +hhn = U32.to_nat(HH(ld, n))
      +v1 = D.view(C.BT(l1, t1))
      +ehh = Equal.trans(Nat, hhn, Nat.min(U32.to_nat(H0(ld)), nn), nn, U.to_nat_min(H0(ld), n), min_r(U32.to_nat(H0(ld)), nn, hb0))
      +enp0 = Equal.trans(Nat, NP, Nat.sub(nn, hhn), 0n, enp(ld, n),
        Equal.trans(Nat, Nat.sub(nn, hhn), Nat.sub(nn, nn), 0n, Equal.cong(Nat, Nat, z => Nat.sub(nn, z), hhn, nn, ehh), H.sub_self(nn)))
      +enw0 = Equal.cong(U32, Nat, z => U32.to_nat(U32.shrn(U32.add(z, 3), 2n)), NPw(ld, n), 0, U.to_nat_inj(NPw(ld, n), 0, enp0))
      %Equal.sym(Nat, NW(ld, n), U32.to_nat(U32.shrn(U32.add(0, 3), 2n)), enw0) :
        {List.take(&2, U32, US(AWT(_, ts, U32.add(qw, 1), C.WD(ts, qw), t1, qw, U32.shrn(l1, 2n), SH(q))), Nat.add(L1, NP)) == List.append(&2, U32, v1, List.take(&2, U32, List.drop(&2, U32, US(ts), qn), NP)) : List<&2, U32>}
      %Equal.sym(Nat, NP, 0n, enp0) :
        {List.take(&2, U32, US(t1), Nat.add(L1, _)) == List.append(&2, U32, v1, List.take(&2, U32, List.drop(&2, U32, US(ts), qn), _)) : List<&2, U32>}
      Equal.trans(List<&2, U32>, List.take(&2, U32, US(t1), Nat.add(L1, 0n)), List.take(&2, U32, US(t1), L1), List.append(&2, U32, v1, List.take(&2, U32, List.drop(&2, U32, US(ts), qn), 0n)),
        Equal.cong(Nat, List<&2, U32>, z => List.take(&2, U32, US(t1), z), Nat.add(L1, 0n), L1, N.add_zero(L1)),
        Equal.sym(List<&2, U32>, List.append(&2, U32, v1, List.take(&2, U32, List.drop(&2, U32, US(ts), qn), 0n)), v1,
          Equal.trans(List<&2, U32>, List.append(&2, U32, v1, List.take(&2, U32, List.drop(&2, U32, US(ts), qn), 0n)), List.append(&2, U32, v1, Nil{}), v1,
            Equal.cong(List<&2, U32>, List<&2, U32>, z => List.append(&2, U32, v1, z), List.take(&2, U32, List.drop(&2, U32, US(ts), qn), 0n), Nil{}, Q.take_zero(List.drop(&2, U32, US(ts), qn))),
            X.append_nil(v1))))

def fav.go(+ld: U32, +td: P.Tree<U32>, +ls: U32, +ts: P.Tree<U32>, +d: Nat, +e: Nat, +s: U32, +n: U32,
  +hd: {D.ok(C.BT(ld, td), d) == True{} : Bool},
  +he: {D.ok(C.BT(ls, ts), e) == True{} : Bool},
  +hs: {Nat.is_le(Nat.add(U32.to_nat(s), U32.to_nat(n)), D.size(C.BT(ls, ts))) == True{} : Bool},
  +hc: {Nat.is_le(Nat.add(D.size(C.BT(ld, td)), U32.to_nat(n)), D.cap(C.BT(ld, td))) == True{} : Bool},
  m: C.BMirror(D1(ld, td, ls, ts, s, n))) ->
  {D.view(Pair.fst(D.Bytes, D.Bytes, FA.append(C.BT(ld, td), C.BT(ls, ts), s, n))) == List.append(&2, U32, D.view(C.BT(ld, td)), D.slice(D.view(C.BT(ls, ts)), U32.to_nat(s), U32.to_nat(n))) : List<&2, U32>}:
  (+l1, m2) = m
  (+t1, +e1) = m2
  +sn = U32.to_nat(s)
  +nn = U32.to_nat(n)
  +hhn = U32.to_nat(HH(ld, n))
  +L1 = U32.to_nat(l1)
  +NP = U32.to_nat(NPw(ld, n))
  +RHS = List.append(&2, U32, D.view(C.BT(ld, td)), D.slice(D.view(C.BT(ls, ts)), sn, nn))
  +el = el1(ld, td, ls, ts, d, s, n, l1, t1, e1, hd, hc)
  +hl0 = hlen0(ld, td, l1, d, n, el, hd, hc)
  +hss = N.le_trans(Nat.add(sn, hhn), Nat.add(sn, nn), U32.to_nat(ls), N.le_add_mono_l(sn, hhn, nn, hh_le(ld, n)), hs)
  +vd1 = AB.subst(D.Bytes, y => {D.view(y) == List.append(&2, U32, D.view(C.BT(ld, td)), D.slice(D.view(C.BT(ls, ts)), sn, hhn)) : List<&2, U32>},
    D1(ld, td, ls, ts, s, n), C.BT(l1, t1), Equal.sym(D.Bytes, C.BT(l1, t1), D1(ld, td, ls, ts, s, n), e1),
    X.append_view_t(ld, td, ls, ts, d, e, s, HH(ld, n), hd, he, hss, hc_h(ld, td, n, hc)))
  +eq = C.add_fits(s, HH(ld, n), e, C.ok_d(ls, ts, e, he),
    N.le_trans(Nat.add(sn, hhn), U32.to_nat(ls), Nat.mul(4n, Nat.pow(2n, e)), hss, C.ok_len(ls, ts, e, he)))
  %Equal.sym(D.Bytes & D.Bytes, FA.append(C.BT(ld, td), C.BT(ls, ts), s, n), (C.BT(U32.add(l1, NPw(ld, n)), TF(ld, ts, s, n, l1, t1)), C.BT(ls, ts)),
    fa_eq(ld, td, ls, ts, s, n, l1, t1, e1)) :
    {D.view(Pair.fst(D.Bytes, D.Bytes, _)) == RHS : List<&2, U32>}
  %Equal.sym(Nat, U32.to_nat(U32.add(l1, NPw(ld, n))), Nat.add(L1, NP), C.add_fits(l1, NPw(ld, n), d, C.ok_d(ld, td, d, hd), hl0)) :
    {List.take(&2, U32, US(TF(ld, ts, s, n, l1, t1)), _) == RHS : List<&2, U32>}
  Equal.trans(List<&2, U32>, List.take(&2, U32, US(TF(ld, ts, s, n, l1, t1)), Nat.add(L1, NP)),
    List.append(&2, U32, D.view(C.BT(l1, t1)), List.take(&2, U32, List.drop(&2, U32, US(ts), U32.to_nat(QQ(ld, s, n))), NP)), RHS,
    avc(Nat.is_lt(U32.to_nat(H0(ld)), nn), ld, td, ls, ts, d, e, s, n, l1, t1, {==}, e1, hd, he, hs, hc),
    fin_eq(D.view(C.BT(l1, t1)), D.view(C.BT(ld, td)), US(ts), U32.to_nat(ls), sn, hhn, U32.to_nat(QQ(ld, s, n)), NP, nn, vd1, eq, enp(ld, n), hh_le(ld, n), hs))

law fast_append_view_t:
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
  {D.view(Pair.fst(D.Bytes, D.Bytes, FA.append(C.BT(ld, td), C.BT(ls, ts), s, n))) == List.append(&2, U32, D.view(C.BT(ld, td)), D.slice(D.view(C.BT(ls, ts)), U32.to_nat(s), U32.to_nat(n))) : List<&2, U32>}

def fast_append_view_t(ld, td, ls, ts, d, e, s, n, hd, he, hs, hc):
  fav.go(ld, td, ls, ts, d, e, s, n, hd, he, hs, hc, C.bmirror(D1(ld, td, ls, ts, s, n)))
