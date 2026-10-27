import Base
import ./defs.bend as D
import ./bytes.bend as B
import ../lawful-words/defs.bend as W
import ../lawful-words/proof_nat.bend as N
import ../lawful-words/proof_u32.bend as U
import ../lawful-words/proof_bytes.bend as Y
import ../lawful-arrays/defs.bend as A
import ../lawful-arrays/proof_base.bend as AB
import ../lawful-arrays/proof_tree.bend as P
import ../lawful-arrays/proof_index.bend as I
import ../lawful-arrays/proof_shape.bend as S

# The core of the Bytes proofs. A Bytes is a Type (it holds an Array), so a
# proof may use one only once. Every lemma here is about BT(len, t): a Bytes
# whose block is the mirror P.fromT(t) of a Tree<U32> t (Data), so len and t
# may be used freely. A law first takes its Bytes apart and mirrors the block.

def BT(+len: U32, +t: P.Tree<U32>) -> D.Bytes:
  D.Bytes{len, P.fromT(U32, t)}

# The words of the block.
def WL(+t: P.Tree<U32>) -> List<&2, U32>:
  A.view(U32, P.fromT(U32, t))

# Word k of the block, as Array.get reads it.
def WD(+t: P.Tree<U32>, +k: U32) -> U32:
  Pair.snd(Array<U32>, U32, Array.get(U32, P.fromT(U32, t), k))

# Byte i, as B.at reads it.
def AT(+len: U32, +t: P.Tree<U32>, +i: U32) -> U32:
  Pair.snd(D.Bytes, U32, B.at(BT(len, t), i))

# What a Maybe word gives for byte r.
def mb(m: Maybe<&2, U32>, +r: Nat) -> Maybe<&2, U32>:
  match m:
    case None{}:
      None{}
    case Some{w}:
      Some{W.byte(w, r)}

# Reading a byte
# ==============

law at_pair_t:
  for +len: U32
  for +t: P.Tree<U32>
  for +i: U32
  {B.at(BT(len, t), i) == (BT(len, t), AT(len, t, i)) : D.Bytes & U32}

def at_pair_t(len, t, i):
  +k = (i >> 2n : U32)
  %Equal.sym(Array<U32> & U32, Array.get(U32, P.fromT(U32, t), k), (P.fromT(U32, t), WD(t, k)), P.get_pair_t(U32, t, k)) :
    {B.at.fin(len, i, _) == (BT(len, t), Pair.snd(D.Bytes, U32, B.at.fin(len, i, _))) : D.Bytes & U32}
  {==}

law at_val:
  for +len: U32
  for +t: P.Tree<U32>
  for +i: U32
  {AT(len, t, i) == W.byte(WD(t, (i >> 2n : U32)), U32.to_nat((i .&. 3 : U32))) : U32}

def at_val(len, t, i):
  +k = (i >> 2n : U32)
  %Equal.sym(Array<U32> & U32, Array.get(U32, P.fromT(U32, t), k), (P.fromT(U32, t), WD(t, k)), P.get_pair_t(U32, t, k)) :
    {Pair.snd(D.Bytes, U32, B.at.fin(len, i, _)) == W.byte(WD(t, k), U32.to_nat((i .&. 3 : U32))) : U32}
  {==}

# The bytes of a word list
# ========================

law unpack_get0:
  for +w: U32
  for +t: List<&2, U32>
  for +r: Nat
  for +hr: {Nat.is_lt(r, 4n) == True{} : Bool}
  {List.get(&2, U32, D.unpack(w <> t), r) == Some{W.byte(w, r)} : Maybe<&2, U32>}

def unpack_get0(w, t, r, hr):
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
                  Empty.absurd({List.get(&2, U32, D.unpack(w <> t), 4n+r4) == Some{W.byte(w, 4n+r4)} : Maybe<&2, U32>},
                    AB.lt_zero_absurd(r4, hr))

# Byte r of word q is byte 4q + r.
law unpack_get:
  for +ws: List<&2, U32>
  for +q: Nat
  for +r: Nat
  for +hr: {Nat.is_lt(r, 4n) == True{} : Bool}
  {List.get(&2, U32, D.unpack(ws), Nat.add(Nat.mul(q, 4n), r)) == mb(List.get(&2, U32, ws, q), r) : Maybe<&2, U32>}

def unpack_get(ws, q, r, hr):
  match ws q:
    case Nil{} _:
      {==}
    case Con{w, t} 0n:
      unpack_get0(w, t, r, hr)
    case Con{w, t} 1n+p:
      unpack_get(t, p, r, hr)

# Byte n of the word list: byte n % 4 of word n / 4.
law unpack_get_n:
  for +ws: List<&2, U32>
  for +n: Nat
  {List.get(&2, U32, D.unpack(ws), n) == mb(List.get(&2, U32, ws, Nat.div(n, 4n)), Nat.mod(n, 4n)) : Maybe<&2, U32>}

def unpack_get_n(ws, n):
  %N.div_mod(n, 4n) : {List.get(&2, U32, D.unpack(ws), _) == mb(List.get(&2, U32, ws, Nat.div(n, 4n)), Nat.mod(n, 4n)) : Maybe<&2, U32>}
  unpack_get(ws, Nat.div(n, 4n), Nat.mod(n, 4n), N.mod_lt(n, 4n, {==}))

# The same for a U32 index: word i >> 2, byte i & 3.
law unpack_get_i:
  for +ws: List<&2, U32>
  for +i: U32
  {List.get(&2, U32, D.unpack(ws), U32.to_nat(i)) == mb(List.get(&2, U32, ws, U32.to_nat((i >> 2n : U32))), U32.to_nat((i .&. 3 : U32))) : Maybe<&2, U32>}

def unpack_get_i(ws, i):
  +n = U32.to_nat(i)
  %Equal.sym(Nat, U32.to_nat((i >> 2n : U32)), Nat.div(n, 4n), U.to_nat_shrn(i, 2n)) :
    {List.get(&2, U32, D.unpack(ws), n) == mb(List.get(&2, U32, ws, _), U32.to_nat((i .&. 3 : U32))) : Maybe<&2, U32>}
  %Equal.sym(Nat, U32.to_nat((i .&. 3 : U32)), Nat.mod(n, 4n), U.to_nat_and_mask(i, 3, 2n, {==})) :
    {List.get(&2, U32, D.unpack(ws), n) == mb(List.get(&2, U32, ws, Nat.div(n, 4n)), _) : Maybe<&2, U32>}
  unpack_get_n(ws, n)

# Lists
# =====

law take_get:
  for +xs: List<&2, U32>
  for +n: Nat
  for +i: Nat
  for +h: {Nat.is_lt(i, n) == True{} : Bool}
  {List.get(&2, U32, List.take(&2, U32, xs, n), i) == List.get(&2, U32, xs, i) : Maybe<&2, U32>}

def take_get(xs, n, i, h):
  match xs n i:
    case Nil{} _ _:
      {==}
    case Con{x, t} 0n _:
      Empty.absurd({List.get(&2, U32, Nil{}, i) == List.get(&2, U32, x <> t, i) : Maybe<&2, U32>},
        AB.lt_zero_absurd(i, h))
    case Con{x, t} 1n+p 0n:
      {==}
    case Con{x, t} 1n+p 1n+j:
      take_get(t, p, j, h)

# Index facts
# ===========

law lt32:
  for +d: Nat
  for +hd: {Nat.is_le(d, 29n) == True{} : Bool}
  {Nat.is_lt(d, 32n) == True{} : Bool}

def lt32(d, hd):
  N.le_lt_trans(d, 29n, 32n, hd, {==})

# A byte index below 4 * 2^d has its word index below 2^d.
law word_lt:
  for +i: U32
  for +d: Nat
  for +h: {Nat.is_lt(U32.to_nat(i), Nat.mul(4n, Nat.pow(2n, d))) == True{} : Bool}
  {Nat.is_lt(U32.to_nat((i >> 2n : U32)), Nat.pow(2n, d)) == True{} : Bool}

def word_lt(i, d, h):
  %Equal.sym(Nat, U32.to_nat((i >> 2n : U32)), Nat.div(U32.to_nat(i), 4n), U.to_nat_shrn(i, 2n)) :
    {Nat.is_lt(_, Nat.pow(2n, d)) == True{} : Bool}
  N.div_lt(U32.to_nat(i), 4n, Nat.pow(2n, d), {==}, h)

# Reading a byte
# ==============

law at_view_t:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +i: U32
  for +hf: {A.full(U32, P.fromT(U32, t), d) == True{} : Bool}
  for +hd: {Nat.is_le(d, 29n) == True{} : Bool}
  for +hl: {Nat.is_le(U32.to_nat(len), Nat.mul(4n, Nat.pow(2n, d))) == True{} : Bool}
  for +hi: {Nat.is_lt(U32.to_nat(i), U32.to_nat(len)) == True{} : Bool}
  {Some{AT(len, t, i)} == List.get(&2, U32, D.view(BT(len, t)), U32.to_nat(i)) : Maybe<&2, U32>}

def at_view_t(len, t, d, i, hf, hd, hl, hi):
  +k = (i >> 2n : U32)
  +r = U32.to_nat((i .&. 3 : U32))
  +n = U32.to_nat(i)
  %Equal.sym(U32, AT(len, t, i), W.byte(WD(t, k), r), at_val(len, t, i)) :
    {Some{_} == List.get(&2, U32, D.view(BT(len, t)), n) : Maybe<&2, U32>}
  %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, List.take(&2, U32, D.unpack(WL(t)), U32.to_nat(len)), n),
    List.get(&2, U32, D.unpack(WL(t)), n), take_get(D.unpack(WL(t)), U32.to_nat(len), n, hi)) :
    {Some{W.byte(WD(t, k), r)} == _ : Maybe<&2, U32>}
  %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, D.unpack(WL(t)), n), mb(List.get(&2, U32, WL(t), U32.to_nat(k)), r),
    unpack_get_i(WL(t), i)) :
    {Some{W.byte(WD(t, k), r)} == _ : Maybe<&2, U32>}
  +hk = word_lt(i, d, N.lt_le_trans(n, U32.to_nat(len), Nat.mul(4n, Nat.pow(2n, d)), hi, hl))
  %I.slot_small_t(k, d, hk) : {Some{W.byte(WD(t, k), r)} == mb(List.get(&2, U32, WL(t), _), r) : Maybe<&2, U32>}
  %I.get_view_t(U32, t, d, k, hf, lt32(d, hd)) : {Some{W.byte(WD(t, k), r)} == mb(_, r) : Maybe<&2, U32>}
  {==}

# The mirror of a Bytes
# =====================

# Every Bytes is BT(len, t) for some len and tree t.
def BMirror(-b: D.Bytes) -> Data:
  Sigma<&2, &2, U32, len => Sigma<&2, &2, P.Tree<U32>, t => {BT(len, t) == b : D.Bytes}>>

def bmirror.go(+len: U32, -buf: Array<U32>, m: P.Mirror(U32, buf)) -> BMirror(D.Bytes{len, buf}):
  (t, e) = m
  (len, (t, Equal.cong(Array<U32>, D.Bytes, x => D.Bytes{len, x}, P.fromT(U32, t), buf, e)))

def bmirror(b: D.Bytes) -> BMirror(b):
  match b:
    case D.Bytes{+len, buf}:
      bmirror.go(len, buf, P.mirror(U32, buf))

# Transport of a hypothesis about b to its mirror.
def tr(-H: D.Bytes -> Type, -b: D.Bytes, +len: U32, +t: P.Tree<U32>, e: {BT(len, t) == b : D.Bytes}, h: H(b)) -> H(BT(len, t)):
  AB.subst(D.Bytes, H, b, BT(len, t), Equal.sym(D.Bytes, BT(len, t), b, e), h)

# The three parts of ok.
law ok_full:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +h: {D.ok(BT(len, t), d) == True{} : Bool}
  {A.full(U32, P.fromT(U32, t), d) == True{} : Bool}

def ok_full(len, t, d, h):
  AB.and_true_l(A.full(U32, P.fromT(U32, t), d),
    Nat.is_le(d, 29n) && Nat.is_le(U32.to_nat(len), Nat.mul(4n, Nat.pow(2n, d))), h)

law ok_d:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +h: {D.ok(BT(len, t), d) == True{} : Bool}
  {Nat.is_le(d, 29n) == True{} : Bool}

def ok_d(len, t, d, h):
  AB.and_true_l(Nat.is_le(d, 29n), Nat.is_le(U32.to_nat(len), Nat.mul(4n, Nat.pow(2n, d))),
    AB.and_true_r(A.full(U32, P.fromT(U32, t), d),
      Nat.is_le(d, 29n) && Nat.is_le(U32.to_nat(len), Nat.mul(4n, Nat.pow(2n, d))), h))

law ok_len:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +h: {D.ok(BT(len, t), d) == True{} : Bool}
  {Nat.is_le(U32.to_nat(len), Nat.mul(4n, Nat.pow(2n, d))) == True{} : Bool}

def ok_len(len, t, d, h):
  AB.and_true_r(Nat.is_le(d, 29n), Nat.is_le(U32.to_nat(len), Nat.mul(4n, Nat.pow(2n, d))),
    AB.and_true_r(A.full(U32, P.fromT(U32, t), d),
      Nat.is_le(d, 29n) && Nat.is_le(U32.to_nat(len), Nat.mul(4n, Nat.pow(2n, d))), h))

# ok from its three parts.
law ok_mk:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +hf: {A.full(U32, P.fromT(U32, t), d) == True{} : Bool}
  for +hd: {Nat.is_le(d, 29n) == True{} : Bool}
  for +hl: {Nat.is_le(U32.to_nat(len), Nat.mul(4n, Nat.pow(2n, d))) == True{} : Bool}
  {D.ok(BT(len, t), d) == True{} : Bool}

def ok_mk(len, t, d, hf, hd, hl):
  %Equal.sym(Bool, A.full(U32, P.fromT(U32, t), d), True{}, hf) :
    {Bool.and(_, Nat.is_le(d, 29n) && Nat.is_le(U32.to_nat(len), Nat.mul(4n, Nat.pow(2n, d)))) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_le(d, 29n), True{}, hd) :
    {Bool.and(True{}, Bool.and(_, Nat.is_le(U32.to_nat(len), Nat.mul(4n, Nat.pow(2n, d))))) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_le(U32.to_nat(len), Nat.mul(4n, Nat.pow(2n, d))), True{}, hl) :
    {Bool.and(True{}, Bool.and(True{}, _)) == True{} : Bool}
  {==}

# Writing a byte
# ==============

def L4(+w: U32) -> List<&2, U32>:
  [W.byte(w, 0n), W.byte(w, 1n), W.byte(w, 2n), W.byte(w, 3n)]

# The four bytes of a word with byte k set to v (k a literal).
law wbp0:
  for +w: U32
  for +v: U32
  for +hv: {U32.is_lt(v, 256) == True{} : Bool}
  {L4(W.put_byte(w, 0n, v)) == List.set(&2, U32, L4(w), 0n, v) : List<&2, U32>}

def wbp0(w, v, hv):
  %Equal.sym(U32, W.byte(W.put_byte(w, 0n, v), 0n), v, Y.byte_put_same(w, 0n, v, {==}, hv)) :
    {[_, W.byte(W.put_byte(w, 0n, v), 1n), W.byte(W.put_byte(w, 0n, v), 2n), W.byte(W.put_byte(w, 0n, v), 3n)] == List.set(&2, U32, L4(w), 0n, v) : List<&2, U32>}
  %Equal.sym(U32, W.byte(W.put_byte(w, 0n, v), 1n), W.byte(w, 1n), Y.byte_put_other(w, 1n, 0n, v, hv, {==})) :
    {[v, _, W.byte(W.put_byte(w, 0n, v), 2n), W.byte(W.put_byte(w, 0n, v), 3n)] == List.set(&2, U32, L4(w), 0n, v) : List<&2, U32>}
  %Equal.sym(U32, W.byte(W.put_byte(w, 0n, v), 2n), W.byte(w, 2n), Y.byte_put_other(w, 2n, 0n, v, hv, {==})) :
    {[v, W.byte(w, 1n), _, W.byte(W.put_byte(w, 0n, v), 3n)] == List.set(&2, U32, L4(w), 0n, v) : List<&2, U32>}
  %Equal.sym(U32, W.byte(W.put_byte(w, 0n, v), 3n), W.byte(w, 3n), Y.byte_put_other(w, 3n, 0n, v, hv, {==})) :
    {[v, W.byte(w, 1n), W.byte(w, 2n), _] == List.set(&2, U32, L4(w), 0n, v) : List<&2, U32>}
  {==}

law wbp1:
  for +w: U32
  for +v: U32
  for +hv: {U32.is_lt(v, 256) == True{} : Bool}
  {L4(W.put_byte(w, 1n, v)) == List.set(&2, U32, L4(w), 1n, v) : List<&2, U32>}

def wbp1(w, v, hv):
  %Equal.sym(U32, W.byte(W.put_byte(w, 1n, v), 0n), W.byte(w, 0n), Y.byte_put_other(w, 0n, 1n, v, hv, {==})) :
    {[_, W.byte(W.put_byte(w, 1n, v), 1n), W.byte(W.put_byte(w, 1n, v), 2n), W.byte(W.put_byte(w, 1n, v), 3n)] == List.set(&2, U32, L4(w), 1n, v) : List<&2, U32>}
  %Equal.sym(U32, W.byte(W.put_byte(w, 1n, v), 1n), v, Y.byte_put_same(w, 1n, v, {==}, hv)) :
    {[W.byte(w, 0n), _, W.byte(W.put_byte(w, 1n, v), 2n), W.byte(W.put_byte(w, 1n, v), 3n)] == List.set(&2, U32, L4(w), 1n, v) : List<&2, U32>}
  %Equal.sym(U32, W.byte(W.put_byte(w, 1n, v), 2n), W.byte(w, 2n), Y.byte_put_other(w, 2n, 1n, v, hv, {==})) :
    {[W.byte(w, 0n), v, _, W.byte(W.put_byte(w, 1n, v), 3n)] == List.set(&2, U32, L4(w), 1n, v) : List<&2, U32>}
  %Equal.sym(U32, W.byte(W.put_byte(w, 1n, v), 3n), W.byte(w, 3n), Y.byte_put_other(w, 3n, 1n, v, hv, {==})) :
    {[W.byte(w, 0n), v, W.byte(w, 2n), _] == List.set(&2, U32, L4(w), 1n, v) : List<&2, U32>}
  {==}

law wbp2:
  for +w: U32
  for +v: U32
  for +hv: {U32.is_lt(v, 256) == True{} : Bool}
  {L4(W.put_byte(w, 2n, v)) == List.set(&2, U32, L4(w), 2n, v) : List<&2, U32>}

def wbp2(w, v, hv):
  %Equal.sym(U32, W.byte(W.put_byte(w, 2n, v), 0n), W.byte(w, 0n), Y.byte_put_other(w, 0n, 2n, v, hv, {==})) :
    {[_, W.byte(W.put_byte(w, 2n, v), 1n), W.byte(W.put_byte(w, 2n, v), 2n), W.byte(W.put_byte(w, 2n, v), 3n)] == List.set(&2, U32, L4(w), 2n, v) : List<&2, U32>}
  %Equal.sym(U32, W.byte(W.put_byte(w, 2n, v), 1n), W.byte(w, 1n), Y.byte_put_other(w, 1n, 2n, v, hv, {==})) :
    {[W.byte(w, 0n), _, W.byte(W.put_byte(w, 2n, v), 2n), W.byte(W.put_byte(w, 2n, v), 3n)] == List.set(&2, U32, L4(w), 2n, v) : List<&2, U32>}
  %Equal.sym(U32, W.byte(W.put_byte(w, 2n, v), 2n), v, Y.byte_put_same(w, 2n, v, {==}, hv)) :
    {[W.byte(w, 0n), W.byte(w, 1n), _, W.byte(W.put_byte(w, 2n, v), 3n)] == List.set(&2, U32, L4(w), 2n, v) : List<&2, U32>}
  %Equal.sym(U32, W.byte(W.put_byte(w, 2n, v), 3n), W.byte(w, 3n), Y.byte_put_other(w, 3n, 2n, v, hv, {==})) :
    {[W.byte(w, 0n), W.byte(w, 1n), v, _] == List.set(&2, U32, L4(w), 2n, v) : List<&2, U32>}
  {==}

law wbp3:
  for +w: U32
  for +v: U32
  for +hv: {U32.is_lt(v, 256) == True{} : Bool}
  {L4(W.put_byte(w, 3n, v)) == List.set(&2, U32, L4(w), 3n, v) : List<&2, U32>}

def wbp3(w, v, hv):
  %Equal.sym(U32, W.byte(W.put_byte(w, 3n, v), 0n), W.byte(w, 0n), Y.byte_put_other(w, 0n, 3n, v, hv, {==})) :
    {[_, W.byte(W.put_byte(w, 3n, v), 1n), W.byte(W.put_byte(w, 3n, v), 2n), W.byte(W.put_byte(w, 3n, v), 3n)] == List.set(&2, U32, L4(w), 3n, v) : List<&2, U32>}
  %Equal.sym(U32, W.byte(W.put_byte(w, 3n, v), 1n), W.byte(w, 1n), Y.byte_put_other(w, 1n, 3n, v, hv, {==})) :
    {[W.byte(w, 0n), _, W.byte(W.put_byte(w, 3n, v), 2n), W.byte(W.put_byte(w, 3n, v), 3n)] == List.set(&2, U32, L4(w), 3n, v) : List<&2, U32>}
  %Equal.sym(U32, W.byte(W.put_byte(w, 3n, v), 2n), W.byte(w, 2n), Y.byte_put_other(w, 2n, 3n, v, hv, {==})) :
    {[W.byte(w, 0n), W.byte(w, 1n), _, W.byte(W.put_byte(w, 3n, v), 3n)] == List.set(&2, U32, L4(w), 3n, v) : List<&2, U32>}
  %Equal.sym(U32, W.byte(W.put_byte(w, 3n, v), 3n), v, Y.byte_put_same(w, 3n, v, {==}, hv)) :
    {[W.byte(w, 0n), W.byte(w, 1n), W.byte(w, 2n), _] == List.set(&2, U32, L4(w), 3n, v) : List<&2, U32>}
  {==}

law wbp:
  for +w: U32
  for +r: Nat
  for +v: U32
  for +hr: {Nat.is_lt(r, 4n) == True{} : Bool}
  for +hv: {U32.is_lt(v, 256) == True{} : Bool}
  {L4(W.put_byte(w, r, v)) == List.set(&2, U32, L4(w), r, v) : List<&2, U32>}

def wbp(w, r, v, hr, hv):
  match r:
    case 0n:
      wbp0(w, v, hv)
    case 1n+r1:
      match r1:
        case 0n:
          wbp1(w, v, hv)
        case 1n+r2:
          match r2:
            case 0n:
              wbp2(w, v, hv)
            case 1n+r3:
              match r3:
                case 0n:
                  wbp3(w, v, hv)
                case 1n+r4:
                  Empty.absurd({L4(W.put_byte(w, 4n+r4, v)) == List.set(&2, U32, L4(w), 4n+r4, v) : List<&2, U32>},
                    AB.lt_zero_absurd(r4, hr))

# Byte 4q + r of the word list after word q is written with its byte r set.
law unpack_set:
  for +ws: List<&2, U32>
  for +q: Nat
  for +r: Nat
  for +w: U32
  for +v: U32
  for +hr: {Nat.is_lt(r, 4n) == True{} : Bool}
  for +hv: {U32.is_lt(v, 256) == True{} : Bool}
  for +hw: {List.get(&2, U32, ws, q) == Some{w} : Maybe<&2, U32>}
  {D.unpack(List.set(&2, U32, ws, q, W.put_byte(w, r, v))) == List.set(&2, U32, D.unpack(ws), Nat.add(Nat.mul(q, 4n), r), v) : List<&2, U32>}

def unpack_set(ws, q, r, w, v, hr, hv, hw):
  match ws q:
    case Nil{} _:
      {==}
    case Con{+x, t} 0n:
      +xw = Equal.cong(Maybe<&2, U32>, U32, m => I.unsome(U32, x, m), Some{x}, Some{w}, hw)
      +U = D.unpack(t)
      %Equal.sym(U32, x, w, xw) :
        {List.append(&2, U32, L4(W.put_byte(w, r, v)), U) == List.set(&2, U32, List.append(&2, U32, L4(_), U), r, v) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, List.set(&2, U32, List.append(&2, U32, L4(w), U), r, v),
        List.append(&2, U32, List.set(&2, U32, L4(w), r, v), U), AB.set_append_l(U32, L4(w), U, r, v, hr)) :
        {List.append(&2, U32, L4(W.put_byte(w, r, v)), U) == _ : List<&2, U32>}
      %wbp(w, r, v, hr, hv) : {List.append(&2, U32, L4(W.put_byte(w, r, v)), U) == List.append(&2, U32, _, U) : List<&2, U32>}
      {==}
    case Con{+x, t} 1n+p:
      %unpack_set(t, p, r, w, v, hr, hv, hw) :
        {List.append(&2, U32, L4(x), D.unpack(List.set(&2, U32, t, p, W.put_byte(w, r, v)))) == List.append(&2, U32, L4(x), _) : List<&2, U32>}
      {==}

# The same for a U32 index.
law unpack_set_i:
  for +ws: List<&2, U32>
  for +i: U32
  for +w: U32
  for +v: U32
  for +hv: {U32.is_lt(v, 256) == True{} : Bool}
  for +hw: {List.get(&2, U32, ws, U32.to_nat((i >> 2n : U32))) == Some{w} : Maybe<&2, U32>}
  {D.unpack(List.set(&2, U32, ws, U32.to_nat((i >> 2n : U32)), W.put_byte(w, U32.to_nat((i .&. 3 : U32)), v))) == List.set(&2, U32, D.unpack(ws), U32.to_nat(i), v) : List<&2, U32>}

def unpack_set_i(ws, i, w, v, hv, hw):
  +n = U32.to_nat(i)
  +eq = U.to_nat_shrn(i, 2n)
  %Equal.sym(Nat, U32.to_nat((i >> 2n : U32)), Nat.div(n, 4n), eq) :
    {D.unpack(List.set(&2, U32, ws, _, W.put_byte(w, U32.to_nat((i .&. 3 : U32)), v))) == List.set(&2, U32, D.unpack(ws), n, v) : List<&2, U32>}
  %Equal.sym(Nat, U32.to_nat((i .&. 3 : U32)), Nat.mod(n, 4n), U.to_nat_and_mask(i, 3, 2n, {==})) :
    {D.unpack(List.set(&2, U32, ws, Nat.div(n, 4n), W.put_byte(w, _, v))) == List.set(&2, U32, D.unpack(ws), n, v) : List<&2, U32>}
  %N.div_mod(n, 4n) :
    {D.unpack(List.set(&2, U32, ws, Nat.div(n, 4n), W.put_byte(w, Nat.mod(n, 4n), v))) == List.set(&2, U32, D.unpack(ws), _, v) : List<&2, U32>}
  unpack_set(ws, Nat.div(n, 4n), Nat.mod(n, 4n), w, v, N.mod_lt(n, 4n, {==}), hv,
    AB.subst(Nat, x => {List.get(&2, U32, ws, x) == Some{w} : Maybe<&2, U32>}, U32.to_nat((i >> 2n : U32)), Nat.div(n, 4n), eq, hw))

# Words of the block
# ==================

# Word k (in range) is the k-th of the word list.
law wd_get:
  for +t: P.Tree<U32>
  for +d: Nat
  for +k: U32
  for +hf: {A.full(U32, P.fromT(U32, t), d) == True{} : Bool}
  for +hd: {Nat.is_le(d, 29n) == True{} : Bool}
  for +hk: {Nat.is_lt(U32.to_nat(k), Nat.pow(2n, d)) == True{} : Bool}
  {List.get(&2, U32, WL(t), U32.to_nat(k)) == Some{WD(t, k)} : Maybe<&2, U32>}

def wd_get(t, d, k, hf, hd, hk):
  %I.slot_small_t(k, d, hk) : {List.get(&2, U32, WL(t), _) == Some{WD(t, k)} : Maybe<&2, U32>}
  Equal.sym(Maybe<&2, U32>, Some{WD(t, k)}, List.get(&2, U32, WL(t), A.slot(k, d)), I.get_view_t(U32, t, d, k, hf, lt32(d, hd)))

# Writing word k (in range) sets the k-th of the word list.
law wl_set:
  for +t: P.Tree<U32>
  for +d: Nat
  for +k: U32
  for +w: U32
  for +hf: {A.full(U32, P.fromT(U32, t), d) == True{} : Bool}
  for +hd: {Nat.is_le(d, 29n) == True{} : Bool}
  for +hk: {Nat.is_lt(U32.to_nat(k), Nat.pow(2n, d)) == True{} : Bool}
  {WL(I.set_tree(U32, t, k, w)) == List.set(&2, U32, WL(t), U32.to_nat(k), w) : List<&2, U32>}

def wl_set(t, d, k, w, hf, hd, hk):
  %I.set_tree_eq(U32, t, k, w) : {A.view(U32, _) == List.set(&2, U32, WL(t), U32.to_nat(k), w) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, A.view(U32, Array.set(U32, P.fromT(U32, t), k, w)), List.set(&2, U32, WL(t), A.slot(k, d), w),
    I.set_view_t(U32, t, d, k, w, hf, lt32(d, hd))) :
    {_ == List.set(&2, U32, WL(t), U32.to_nat(k), w) : List<&2, U32>}
  %I.slot_small_t(k, d, hk) : {List.set(&2, U32, WL(t), A.slot(k, d), w) == List.set(&2, U32, WL(t), _, w) : List<&2, U32>}
  {==}

law full_set:
  for +t: P.Tree<U32>
  for +d: Nat
  for +k: U32
  for +w: U32
  for +hf: {A.full(U32, P.fromT(U32, t), d) == True{} : Bool}
  {A.full(U32, P.fromT(U32, I.set_tree(U32, t, k, w)), d) == True{} : Bool}

def full_set(t, d, k, w, hf):
  %I.set_tree_eq(U32, t, k, w) : {A.full(U32, _, d) == True{} : Bool}
  S.set_full(U32, P.fromT(U32, t), d, k, w, hf)

# Bounds: every length is at most 4 * 2^d <= 2^31, so sums of two fit in a U32
# ===========================================================================

# 4 * 2^d < 2^e for d + 2 < e (e stays a variable here: 2^32 must never be
# unfolded, so the callers instantiate e = 32n only in the final type).
law four_lt_e:
  for +d: Nat
  for +e: Nat
  for +he: {Nat.is_lt(Nat.add(2n, d), e) == True{} : Bool}
  {Nat.is_lt(Nat.mul(4n, Nat.pow(2n, d)), Nat.pow(2n, e)) == True{} : Bool}

def four_lt_e(d, e, he):
  +P = Nat.pow(2n, d)
  %Equal.sym(Nat, Nat.mul(Nat.mul(2n, 2n), P), Nat.mul(2n, Nat.mul(2n, P)), N.mul_assoc(2n, 2n, P)) :
    {Nat.is_lt(_, Nat.pow(2n, e)) == True{} : Bool}
  AB.pow_lt(Nat.add(2n, d), e, he)

law fits_e:
  for +x: Nat
  for +d: Nat
  for +e: Nat
  for +he: {Nat.is_lt(Nat.add(2n, d), e) == True{} : Bool}
  for +hx: {Nat.is_le(x, Nat.mul(4n, Nat.pow(2n, d))) == True{} : Bool}
  {Nat.is_lt(x, Nat.pow(2n, e)) == True{} : Bool}

def fits_e(x, d, e, he, hx):
  N.le_lt_trans(x, Nat.mul(4n, Nat.pow(2n, d)), Nat.pow(2n, e), hx, four_lt_e(d, e, he))

law he32:
  for +d: Nat
  for +hd: {Nat.is_le(d, 29n) == True{} : Bool}
  {Nat.is_lt(Nat.add(2n, d), 32n) == True{} : Bool}

def he32(d, hd):
  Equal.trans(Bool, Nat.is_lt(Nat.add(2n, d), 32n), Nat.is_le(d, 29n), True{}, N.lt_succ_iff(d, 29n), hd)

# A sum of two words that stays within 4 * 2^d does not wrap.
law add_fits:
  for +a: U32
  for +b: U32
  for +d: Nat
  for +hd: {Nat.is_le(d, 29n) == True{} : Bool}
  for +h: {Nat.is_le(Nat.add(U32.to_nat(a), U32.to_nat(b)), Nat.mul(4n, Nat.pow(2n, d))) == True{} : Bool}
  {U32.to_nat(U32.add(a, b)) == Nat.add(U32.to_nat(a), U32.to_nat(b)) : Nat}

def add_fits(a, b, d, hd, h):
  U.to_nat_add_fits_p(a, b, fits_e(Nat.add(U32.to_nat(a), U32.to_nat(b)), d, 32n, he32(d, hd), h))

law succ_le:
  for +x: Nat
  for +m: Nat
  for +h: {Nat.is_lt(x, m) == True{} : Bool}
  {Nat.is_le(Nat.add(x, 1n), m) == True{} : Bool}

def succ_le(x, m, h):
  %Equal.sym(Nat, Nat.add(x, 1n), 1n+x, N.add_one(x)) : {Nat.is_le(_, m) == True{} : Bool}
  Equal.trans(Bool, Nat.is_le(1n+x, m), Nat.is_lt(x, m), True{}, N.le_succ_lt(x, m), h)

# An index below 4 * 2^d steps up by one.
law inc_fits:
  for +a: U32
  for +d: Nat
  for +hd: {Nat.is_le(d, 29n) == True{} : Bool}
  for +h: {Nat.is_lt(U32.to_nat(a), Nat.mul(4n, Nat.pow(2n, d))) == True{} : Bool}
  {U32.to_nat((a + 1 : U32)) == Nat.add(U32.to_nat(a), 1n) : Nat}

def inc_fits(a, d, hd, h):
  add_fits(a, 1, d, hd, succ_le(U32.to_nat(a), Nat.mul(4n, Nat.pow(2n, d)), h))
