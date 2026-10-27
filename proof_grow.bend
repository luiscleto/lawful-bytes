import Base
import ./defs.bend as D
import ./bytes.bend as B
import ./proof_seq.bend as Q
import ./proof_core.bend as C
import ./proof_ops.bend as O
import ../lawful-words/defs.bend as W
import ../lawful-words/proof_nat.bend as N
import ../lawful-arrays/defs.bend as A
import ../lawful-arrays/proof_base.bend as AB
import ../lawful-arrays/proof_tree.bend as P
import ../lawful-arrays/proof_index.bend as I

# The laws about making Bytes: empty, of_list (a loop of pushes) and grow (a
# loop copying words into a new block). Blocks made by Array.new are mirrored
# by tnew, so every loop runs on mirrors C.BT(len, t).

# A new block as a tree.
def tnew(+d: Nat, +v: U32) -> P.Tree<U32>:
  match d:
    case 0n:
      P.TLeaf{v}
    case 1n+p:
      P.TNode{tnew(p, v), tnew(p, v)}

law tnew_eq:
  for +d: Nat
  for +v: U32
  {P.fromT(U32, tnew(d, v)) == Array.new(U32, d, v) : Array<U32>}

def tnew_eq(d, v):
  match d:
    case 0n:
      {==}
    case 1n+p:
      P.anode_eq(U32, P.fromT(U32, tnew(p, v)), P.fromT(U32, tnew(p, v)), Array.new(U32, p, v), Array.new(U32, p, v),
        tnew_eq(p, v), tnew_eq(p, v))

law tnew_full:
  for +d: Nat
  for +v: U32
  {A.full(U32, P.fromT(U32, tnew(d, v)), d) == True{} : Bool}

def tnew_full(d, v):
  %Equal.sym(Array<U32>, P.fromT(U32, tnew(d, v)), Array.new(U32, d, v), tnew_eq(d, v)) : {A.full(U32, _, d) == True{} : Bool}
  P.new_full(U32, d, v)

law empty_eq:
  for +d: Nat
  {B.empty(d) == C.BT(0, tnew(d, 0)) : D.Bytes}

def empty_eq(d):
  %tnew_eq(d, 0) : {D.Bytes{0, _} == C.BT(0, tnew(d, 0)) : D.Bytes}
  {==}

# Empty
# =====

law empty_view:
  for +d: Nat
  {D.view(B.empty(d)) == Nil{} : List<&2, U32>}

def empty_view(d):
  Q.take_zero(D.unpack(A.view(U32, Array.new(U32, d, 0))))

law empty_ok:
  for +d: Nat
  for +hd: {Nat.is_le(d, 29n) == True{} : Bool}
  {D.ok(B.empty(d), d) == True{} : Bool}

def empty_ok(d, hd):
  %Equal.sym(D.Bytes, B.empty(d), C.BT(0, tnew(d, 0)), empty_eq(d)) : {D.ok(_, d) == True{} : Bool}
  C.ok_mk(0, tnew(d, 0), d, tnew_full(d, 0), hd, I.le0(Nat.mul(4n, Nat.pow(2n, d))))

# Lists
# =====

law append_nil:
  for +xs: List<&2, U32>
  {List.append(&2, U32, xs, Nil{}) == xs : List<&2, U32>}

def append_nil(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      %append_nil(t) : {x <> List.append(&2, U32, t, Nil{}) == x <> _ : List<&2, U32>}
      {==}

law app_snoc:
  for +xs: List<&2, U32>
  for +x: U32
  for +r: List<&2, U32>
  {List.append(&2, U32, List.append(&2, U32, xs, [x]), r) == List.append(&2, U32, xs, x <> r) : List<&2, U32>}

def app_snoc(xs, x, r):
  match xs:
    case Nil{}:
      {==}
    case Con{y, t}:
      %app_snoc(t, x, r) : {y <> List.append(&2, U32, List.append(&2, U32, t, [x]), r) == y <> _ : List<&2, U32>}
      {==}

# of_list
# =======

# Room for one more byte when the rest of the list still fits.
law ol_room:
  for +len: U32
  for +r: Nat
  for +m: Nat
  for +hn: {Nat.is_le(Nat.add(U32.to_nat(len), 1n+r), m) == True{} : Bool}
  {Nat.is_lt(U32.to_nat(len), m) == True{} : Bool}

def ol_room(len, r, m, hn):
  +L = U32.to_nat(len)
  +h1 = AB.subst(Nat, x => {Nat.is_le(x, m) == True{} : Bool}, Nat.add(L, 1n+r), 1n+Nat.add(L, r), N.add_succ(L, r), hn)
  +h2 = Equal.trans(Bool, Nat.is_lt(Nat.add(L, r), m), Nat.is_le(1n+Nat.add(L, r), m), True{},
    Equal.sym(Bool, Nat.is_le(1n+Nat.add(L, r), m), Nat.is_lt(Nat.add(L, r), m), N.le_succ_lt(Nat.add(L, r), m)), h1)
  N.le_lt_trans(L, Nat.add(L, r), m, N.le_add_r(L, r), h2)

# The rest still fits after the push.
law ol_rest:
  for +len: U32
  for +d: Nat
  for +r: Nat
  for +hd: {Nat.is_le(d, 29n) == True{} : Bool}
  for +hn: {Nat.is_le(Nat.add(U32.to_nat(len), 1n+r), Nat.mul(4n, Nat.pow(2n, d))) == True{} : Bool}
  {Nat.is_le(Nat.add(U32.to_nat((len + 1 : U32)), r), Nat.mul(4n, Nat.pow(2n, d))) == True{} : Bool}

def ol_rest(len, d, r, hd, hn):
  +L = U32.to_nat(len)
  +M = Nat.mul(4n, Nat.pow(2n, d))
  %Equal.sym(Nat, U32.to_nat((len + 1 : U32)), Nat.add(L, 1n), C.inc_fits(len, d, hd, ol_room(len, r, M, hn))) :
    {Nat.is_le(Nat.add(_, r), M) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(Nat.add(L, 1n), r), Nat.add(L, Nat.add(1n, r)), N.add_assoc(L, 1n, r)) : {Nat.is_le(_, M) == True{} : Bool}
  hn

law ol_go_view:
  for +xs: List<&2, U32>
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hb: {D.all_bytes(xs) == True{} : Bool}
  for +hn: {Nat.is_le(Nat.add(U32.to_nat(len), List.length(&2, U32, xs)), Nat.mul(4n, Nat.pow(2n, d))) == True{} : Bool}
  {D.view(B.of_list.go(xs, C.BT(len, t))) == List.append(&2, U32, D.view(C.BT(len, t)), xs) : List<&2, U32>}

def ol_go_view(xs, len, t, d, h, hb, hn):
  match xs:
    case Nil{}:
      Equal.sym(List<&2, U32>, List.append(&2, U32, D.view(C.BT(len, t)), Nil{}), D.view(C.BT(len, t)), append_nil(D.view(C.BT(len, t))))
    case Con{+x, rest}:
      +k = (len >> 2n : U32)
      +t2 = I.set_tree(U32, t, k, W.put_byte(C.WD(t, k), U32.to_nat((len .&. 3 : U32)), x))
      +l2 = (len + 1 : U32)
      +M = Nat.mul(4n, Nat.pow(2n, d))
      +hd = C.ok_d(len, t, d, h)
      +hr = ol_room(len, List.length(&2, U32, rest), M, hn)
      +hc = AB.subst(Nat, y => {Nat.is_lt(U32.to_nat(len), y) == True{} : Bool}, M, D.cap(C.BT(len, t)),
        Equal.sym(Nat, D.cap(C.BT(len, t)), M, O.cap_ok_t(len, t, d, h)), hr)
      +pe = O.push_eq_t(len, t, x)
      +hv = AB.and_true_l(U32.is_lt(x, 256), D.all_bytes(rest), hb)
      +h2 = AB.subst(D.Bytes, y => {D.ok(y, d) == True{} : Bool}, B.push(C.BT(len, t), x), C.BT(l2, t2), pe,
        O.push_ok_t(len, t, d, x, h, hc))
      +pv = AB.subst(D.Bytes, y => {D.view(y) == List.append(&2, U32, D.view(C.BT(len, t)), [x]) : List<&2, U32>},
        B.push(C.BT(len, t), x), C.BT(l2, t2), pe, O.push_view_t(len, t, d, x, h, hc, hv))
      +RHS = List.append(&2, U32, D.view(C.BT(len, t)), x <> rest)
      %Equal.sym(D.Bytes, B.push(C.BT(len, t), x), C.BT(l2, t2), pe) : {D.view(B.of_list.go(rest, _)) == RHS : List<&2, U32>}
      %Equal.sym(List<&2, U32>, D.view(B.of_list.go(rest, C.BT(l2, t2))), List.append(&2, U32, D.view(C.BT(l2, t2)), rest),
        ol_go_view(rest, l2, t2, d, h2, AB.and_true_r(U32.is_lt(x, 256), D.all_bytes(rest), hb),
          ol_rest(len, d, List.length(&2, U32, rest), hd, hn))) :
        {_ == RHS : List<&2, U32>}
      %Equal.sym(List<&2, U32>, D.view(C.BT(l2, t2)), List.append(&2, U32, D.view(C.BT(len, t)), [x]), pv) :
        {List.append(&2, U32, _, rest) == RHS : List<&2, U32>}
      app_snoc(D.view(C.BT(len, t)), x, rest)

law ol_go_ok:
  for +xs: List<&2, U32>
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hn: {Nat.is_le(Nat.add(U32.to_nat(len), List.length(&2, U32, xs)), Nat.mul(4n, Nat.pow(2n, d))) == True{} : Bool}
  {D.ok(B.of_list.go(xs, C.BT(len, t)), d) == True{} : Bool}

def ol_go_ok(xs, len, t, d, h, hn):
  match xs:
    case Nil{}:
      h
    case Con{+x, rest}:
      +k = (len >> 2n : U32)
      +t2 = I.set_tree(U32, t, k, W.put_byte(C.WD(t, k), U32.to_nat((len .&. 3 : U32)), x))
      +l2 = (len + 1 : U32)
      +M = Nat.mul(4n, Nat.pow(2n, d))
      +hd = C.ok_d(len, t, d, h)
      +hr = ol_room(len, List.length(&2, U32, rest), M, hn)
      +hc = AB.subst(Nat, y => {Nat.is_lt(U32.to_nat(len), y) == True{} : Bool}, M, D.cap(C.BT(len, t)),
        Equal.sym(Nat, D.cap(C.BT(len, t)), M, O.cap_ok_t(len, t, d, h)), hr)
      +pe = O.push_eq_t(len, t, x)
      +h2 = AB.subst(D.Bytes, y => {D.ok(y, d) == True{} : Bool}, B.push(C.BT(len, t), x), C.BT(l2, t2), pe,
        O.push_ok_t(len, t, d, x, h, hc))
      %Equal.sym(D.Bytes, B.push(C.BT(len, t), x), C.BT(l2, t2), pe) : {D.ok(B.of_list.go(rest, _), d) == True{} : Bool}
      ol_go_ok(rest, l2, t2, d, h2, ol_rest(len, d, List.length(&2, U32, rest), hd, hn))

law of_list_view:
  for +d: Nat
  for +xs: List<&2, U32>
  for +hd: {Nat.is_le(d, 29n) == True{} : Bool}
  for +hn: {Nat.is_le(List.length(&2, U32, xs), Nat.mul(4n, Nat.pow(2n, d))) == True{} : Bool}
  for +hb: {D.all_bytes(xs) == True{} : Bool}
  {D.view(B.of_list(d, xs)) == xs : List<&2, U32>}

def of_list_view(d, xs, hd, hn, hb):
  +t0 = tnew(d, 0)
  %Equal.sym(D.Bytes, B.empty(d), C.BT(0, t0), empty_eq(d)) : {D.view(B.of_list.go(xs, _)) == xs : List<&2, U32>}
  %Equal.sym(List<&2, U32>, D.view(B.of_list.go(xs, C.BT(0, t0))), List.append(&2, U32, D.view(C.BT(0, t0)), xs),
    ol_go_view(xs, 0, t0, d, C.ok_mk(0, t0, d, tnew_full(d, 0), hd, I.le0(Nat.mul(4n, Nat.pow(2n, d)))), hb, hn)) :
    {_ == xs : List<&2, U32>}
  %Equal.sym(List<&2, U32>, List.take(&2, U32, D.unpack(C.WL(t0)), 0n), Nil{}, Q.take_zero(D.unpack(C.WL(t0)))) :
    {List.append(&2, U32, _, xs) == xs : List<&2, U32>}
  {==}

law of_list_ok:
  for +d: Nat
  for +xs: List<&2, U32>
  for +hd: {Nat.is_le(d, 29n) == True{} : Bool}
  for +hn: {Nat.is_le(List.length(&2, U32, xs), Nat.mul(4n, Nat.pow(2n, d))) == True{} : Bool}
  {D.ok(B.of_list(d, xs), d) == True{} : Bool}

def of_list_ok(d, xs, hd, hn):
  +t0 = tnew(d, 0)
  %Equal.sym(D.Bytes, B.empty(d), C.BT(0, t0), empty_eq(d)) : {D.ok(B.of_list.go(xs, _), d) == True{} : Bool}
  ol_go_ok(xs, 0, t0, d, C.ok_mk(0, t0, d, tnew_full(d, 0), hd, I.le0(Nat.mul(4n, Nat.pow(2n, d)))), hn)

# grow
# ====

# The tree grow.go builds from td: words i .. i+n-1 of t written in.
def gtree(n: Nat, +t: P.Tree<U32>, +td: P.Tree<U32>, +i: U32) -> P.Tree<U32>:
  match n:
    case 0n:
      td
    case 1n+k:
      gtree(k, t, I.set_tree(U32, td, i, C.WD(t, i)), (i + 1 : U32))

law ggo:
  for +n: Nat
  for +t: P.Tree<U32>
  for +td: P.Tree<U32>
  for +i: U32
  {B.grow.go(n, Array.get(U32, P.fromT(U32, t), i), P.fromT(U32, td), i) == P.fromT(U32, gtree(n, t, td, i)) : Array<U32>}

def ggo(n, t, td, i):
  match n:
    case 0n:
      %Equal.sym(Array<U32> & U32, Array.get(U32, P.fromT(U32, t), i), (P.fromT(U32, t), C.WD(t, i)), P.get_pair_t(U32, t, i)) :
        {B.grow.go(0n, _, P.fromT(U32, td), i) == P.fromT(U32, td) : Array<U32>}
      {==}
    case 1n+k:
      +w = C.WD(t, i)
      +i1 = (i + 1 : U32)
      %Equal.sym(Array<U32> & U32, Array.get(U32, P.fromT(U32, t), i), (P.fromT(U32, t), w), P.get_pair_t(U32, t, i)) :
        {B.grow.go(1n+k, _, P.fromT(U32, td), i) == P.fromT(U32, gtree(1n+k, t, td, i)) : Array<U32>}
      %Equal.sym(Array<U32>, Array.set(U32, P.fromT(U32, td), i, w), P.fromT(U32, I.set_tree(U32, td, i, w)), I.set_tree_eq(U32, td, i, w)) :
        {B.grow.go(k, Array.get(U32, P.fromT(U32, t), i1), _, i1) == P.fromT(U32, gtree(k, t, I.set_tree(U32, td, i, w), i1)) : Array<U32>}
      ggo(k, t, I.set_tree(U32, td, i, w), i1)

law grow_eq:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +e: Nat
  for +hf: {A.full(U32, P.fromT(U32, t), d) == True{} : Bool}
  {B.grow(C.BT(len, t), e) == C.BT(len, gtree(U32.to_nat(U32.shln(1, d)), t, tnew(e, 0), 0)) : D.Bytes}

def grow_eq(len, t, d, e, hf):
  +N0 = U32.to_nat(U32.shln(1, d))
  %Equal.sym(Array<U32> & U32, Array.size(U32, P.fromT(U32, t)), (P.fromT(U32, t), U32.shln(1, d)), P.size_tree(U32, d, t, hf)) :
    {B.grow.fin(len, e, _) == C.BT(len, gtree(N0, t, tnew(e, 0), 0)) : D.Bytes}
  %tnew_eq(e, 0) : {D.Bytes{len, B.grow.go(N0, Array.get(U32, P.fromT(U32, t), 0), _, 0)} == C.BT(len, gtree(N0, t, tnew(e, 0), 0)) : D.Bytes}
  %Equal.sym(Array<U32>, B.grow.go(N0, Array.get(U32, P.fromT(U32, t), 0), P.fromT(U32, tnew(e, 0)), 0),
    P.fromT(U32, gtree(N0, t, tnew(e, 0), 0)), ggo(N0, t, tnew(e, 0), 0)) :
    {D.Bytes{len, _} == C.BT(len, gtree(N0, t, tnew(e, 0), 0)) : D.Bytes}
  {==}

law gfull:
  for +n: Nat
  for +t: P.Tree<U32>
  for +td: P.Tree<U32>
  for +i: U32
  for +e: Nat
  for +hf: {A.full(U32, P.fromT(U32, td), e) == True{} : Bool}
  {A.full(U32, P.fromT(U32, gtree(n, t, td, i)), e) == True{} : Bool}

def gfull(n, t, td, i, e, hf):
  match n:
    case 0n:
      hf
    case 1n+k:
      gfull(k, t, I.set_tree(U32, td, i, C.WD(t, i)), (i + 1 : U32), e, C.full_set(td, e, i, C.WD(t, i), hf))

def mtag(m: Maybe<&2, U32>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      True{}

law take_succ_get:
  for +xs: List<&2, U32>
  for +j: Nat
  for +w: U32
  for +hg: {List.get(&2, U32, xs, j) == Some{w} : Maybe<&2, U32>}
  {List.take(&2, U32, xs, Nat.add(j, 1n)) == List.append(&2, U32, List.take(&2, U32, xs, j), [w]) : List<&2, U32>}

def take_succ_get(xs, j, w, hg):
  match xs j:
    case Nil{} _:
      Empty.absurd({List.take(&2, U32, Nil{}, Nat.add(j, 1n)) == List.append(&2, U32, Nil{}, [w]) : List<&2, U32>},
        AB.false_ne_true(Equal.cong(Maybe<&2, U32>, Bool, m => mtag(m), None{}, Some{w}, hg)))
    case Con{+x, r} 0n:
      +xw = Equal.cong(Maybe<&2, U32>, U32, m => I.unsome(U32, x, m), Some{x}, Some{w}, hg)
      %Equal.sym(List<&2, U32>, List.take(&2, U32, r, 0n), Nil{}, Q.take_zero(r)) : {x <> _ == [w] : List<&2, U32>}
      %Equal.sym(U32, x, w, xw) : {_ <> Nil{} == [w] : List<&2, U32>}
      {==}
    case Con{+x, r} 1n+p:
      %take_succ_get(r, p, w, hg) : {x <> List.take(&2, U32, r, Nat.add(p, 1n)) == x <> _ : List<&2, U32>}
      {==}

law take_all:
  for +xs: List<&2, U32>
  {List.take(&2, U32, xs, List.length(&2, U32, xs)) == xs : List<&2, U32>}

def take_all(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{x, r}:
      %take_all(r) : {x <> List.take(&2, U32, r, List.length(&2, U32, r)) == x <> _ : List<&2, U32>}
      {==}

# Only the first q words matter for the first m <= 4q bytes.
law ut:
  for +ws: List<&2, U32>
  for +q: Nat
  for +m: Nat
  for +h: {Nat.is_le(m, Nat.mul(q, 4n)) == True{} : Bool}
  {List.take(&2, U32, D.unpack(ws), m) == List.take(&2, U32, D.unpack(List.take(&2, U32, ws, q)), m) : List<&2, U32>}

def ut(ws, q, m, h):
  match ws q m:
    case Nil{} _ _:
      {==}
    case Con{w, r} 0n 0n:
      {==}
    case Con{w, r} 0n 1n+m1:
      Empty.absurd({List.take(&2, U32, D.unpack(w <> r), 1n+m1) == Nil{} : List<&2, U32>}, AB.false_ne_true(h))
    case Con{+w, r} 1n+p 0n:
      {==}
    case Con{+w, r} 1n+p 1n+m1:
      match m1:
        case 0n:
          {==}
        case 1n+m2:
          match m2:
            case 0n:
              {==}
            case 1n+m3:
              match m3:
                case 0n:
                  {==}
                case 1n+m4:
                  %ut(r, p, m4, h) :
                    {W.byte(w, 0n) <> W.byte(w, 1n) <> W.byte(w, 2n) <> W.byte(w, 3n) <> List.take(&2, U32, D.unpack(r), m4) ==
                      W.byte(w, 0n) <> W.byte(w, 1n) <> W.byte(w, 2n) <> W.byte(w, 3n) <> _ : List<&2, U32>}
                  {==}

# Writing word i keeps the copied prefix and extends it by one word.
law ginv:
  for +t: P.Tree<U32>
  for +td: P.Tree<U32>
  for +i: U32
  for +d: Nat
  for +e: Nat
  for +hft: {A.full(U32, P.fromT(U32, t), d) == True{} : Bool}
  for +hfd: {A.full(U32, P.fromT(U32, td), e) == True{} : Bool}
  for +hd: {Nat.is_le(d, 29n) == True{} : Bool}
  for +he29: {Nat.is_le(e, 29n) == True{} : Bool}
  for +hjd: {Nat.is_lt(U32.to_nat(i), Nat.pow(2n, d)) == True{} : Bool}
  for +hje: {Nat.is_lt(U32.to_nat(i), Nat.pow(2n, e)) == True{} : Bool}
  for +ei1: {U32.to_nat((i + 1 : U32)) == Nat.add(U32.to_nat(i), 1n) : Nat}
  for +hinv: {List.take(&2, U32, C.WL(td), U32.to_nat(i)) == List.take(&2, U32, C.WL(t), U32.to_nat(i)) : List<&2, U32>}
  {List.take(&2, U32, C.WL(I.set_tree(U32, td, i, C.WD(t, i))), U32.to_nat((i + 1 : U32))) == List.take(&2, U32, C.WL(t), U32.to_nat((i + 1 : U32))) : List<&2, U32>}

def ginv(t, td, i, d, e, hft, hfd, hd, he29, hjd, hje, ei1, hinv):
  +j = U32.to_nat(i)
  +w = C.WD(t, i)
  +td2 = I.set_tree(U32, td, i, w)
  %Equal.sym(Nat, U32.to_nat((i + 1 : U32)), Nat.add(j, 1n), ei1) :
    {List.take(&2, U32, C.WL(td2), _) == List.take(&2, U32, C.WL(t), _) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, C.WL(td2), List.set(&2, U32, C.WL(td), j, w), C.wl_set(td, e, i, w, hfd, he29, hje)) :
    {List.take(&2, U32, _, Nat.add(j, 1n)) == List.take(&2, U32, C.WL(t), Nat.add(j, 1n)) : List<&2, U32>}
  +hlen = AB.subst(Nat, x => {Nat.is_lt(j, x) == True{} : Bool}, Nat.pow(2n, e), List.length(&2, U32, C.WL(td)),
    Equal.sym(Nat, List.length(&2, U32, C.WL(td)), Nat.pow(2n, e), P.view_length(U32, e, td, hfd)), hje)
  %Equal.sym(List<&2, U32>, List.take(&2, U32, List.set(&2, U32, C.WL(td), j, w), Nat.add(j, 1n)),
    List.append(&2, U32, List.take(&2, U32, C.WL(td), j), [w]), Q.take_set_succ(C.WL(td), j, w, hlen)) :
    {_ == List.take(&2, U32, C.WL(t), Nat.add(j, 1n)) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, List.take(&2, U32, C.WL(td), j), List.take(&2, U32, C.WL(t), j), hinv) :
    {List.append(&2, U32, _, [w]) == List.take(&2, U32, C.WL(t), Nat.add(j, 1n)) : List<&2, U32>}
  Equal.sym(List<&2, U32>, List.take(&2, U32, C.WL(t), Nat.add(j, 1n)), List.append(&2, U32, List.take(&2, U32, C.WL(t), j), [w]),
    take_succ_get(C.WL(t), j, w, C.wd_get(t, d, i, hft, hd, hjd)))

# The loop copies words i .. i+n-1 of t.
law gtake:
  for +n: Nat
  for +t: P.Tree<U32>
  for +td: P.Tree<U32>
  for +i: U32
  for +d: Nat
  for +e: Nat
  for +hft: {A.full(U32, P.fromT(U32, t), d) == True{} : Bool}
  for +hfd: {A.full(U32, P.fromT(U32, td), e) == True{} : Bool}
  for +hd: {Nat.is_le(d, 29n) == True{} : Bool}
  for +he: {Nat.is_le(d, e) == True{} : Bool}
  for +he29: {Nat.is_le(e, 29n) == True{} : Bool}
  for +hn: {Nat.is_le(Nat.add(U32.to_nat(i), n), Nat.pow(2n, d)) == True{} : Bool}
  for +hinv: {List.take(&2, U32, C.WL(td), U32.to_nat(i)) == List.take(&2, U32, C.WL(t), U32.to_nat(i)) : List<&2, U32>}
  {List.take(&2, U32, C.WL(gtree(n, t, td, i)), Nat.add(U32.to_nat(i), n)) == List.take(&2, U32, C.WL(t), Nat.add(U32.to_nat(i), n)) : List<&2, U32>}

def gtake(n, t, td, i, d, e, hft, hfd, hd, he, he29, hn, hinv):
  match n:
    case 0n:
      +j = U32.to_nat(i)
      %Equal.sym(Nat, Nat.add(j, 0n), j, N.add_zero(j)) :
        {List.take(&2, U32, C.WL(td), _) == List.take(&2, U32, C.WL(t), _) : List<&2, U32>}
      hinv
    case 1n+k:
      +j = U32.to_nat(i)
      +w = C.WD(t, i)
      +i1 = (i + 1 : U32)
      +td2 = I.set_tree(U32, td, i, w)
      +Pd = Nat.pow(2n, d)
      +hjd = ol_room(i, k, Pd, hn)
      +hje = N.lt_le_trans(j, Pd, Nat.pow(2n, e), hjd, N.pow_le(d, e, he))
      +hj4 = N.lt_le_trans(j, Pd, Nat.mul(4n, Pd), hjd, N.le_add_r(Pd, Nat.mul(3n, Pd)))
      +ei1 = C.inc_fits(i, d, hd, hj4)
      +ek = Equal.trans(Nat, Nat.add(U32.to_nat(i1), k), Nat.add(Nat.add(j, 1n), k), Nat.add(j, 1n+k),
        Equal.cong(Nat, Nat, x => Nat.add(x, k), U32.to_nat(i1), Nat.add(j, 1n), ei1), N.add_assoc(j, 1n, k))
      %ek : {List.take(&2, U32, C.WL(gtree(k, t, td2, i1)), _) == List.take(&2, U32, C.WL(t), _) : List<&2, U32>}
      gtake(k, t, td2, i1, d, e, hft, C.full_set(td, e, i, w, hfd), hd, he, he29,
        AB.subst(Nat, x => {Nat.is_le(x, Pd) == True{} : Bool}, Nat.add(j, 1n+k), Nat.add(U32.to_nat(i1), k),
          Equal.sym(Nat, Nat.add(U32.to_nat(i1), k), Nat.add(j, 1n+k), ek), hn),
        ginv(t, td, i, d, e, hft, hfd, hd, he29, hjd, hje, ei1, hinv))

law grow_view_t:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +e: Nat
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +he: {Nat.is_le(d, e) == True{} : Bool}
  for +he29: {Nat.is_le(e, 29n) == True{} : Bool}
  {D.view(B.grow(C.BT(len, t), e)) == D.view(C.BT(len, t)) : List<&2, U32>}

def grow_view_t(len, t, d, e, h, he, he29):
  +hf = C.ok_full(len, t, d, h)
  +hd = C.ok_d(len, t, d, h)
  +L = U32.to_nat(len)
  +N0 = U32.to_nat(U32.shln(1, d))
  +Pd = Nat.pow(2n, d)
  +t0 = tnew(e, 0)
  +GTR = gtree(N0, t, t0, 0)
  +RHS = D.view(C.BT(len, t))
  +hl4 = AB.subst(Nat, x => {Nat.is_le(L, x) == True{} : Bool}, Nat.mul(4n, Pd), Nat.mul(Pd, 4n), N.mul_comm(4n, Pd),
    C.ok_len(len, t, d, h))
  +hn0 = AB.subst(Nat, x => {Nat.is_le(x, Pd) == True{} : Bool}, Pd, N0,
    Equal.sym(Nat, N0, Pd, I.size_n(d, C.lt32(d, hd))), N.le_refl(Pd))
  +hinv0 = Equal.trans(List<&2, U32>, List.take(&2, U32, C.WL(t0), 0n), Nil{}, List.take(&2, U32, C.WL(t), 0n),
    Q.take_zero(C.WL(t0)), Equal.sym(List<&2, U32>, List.take(&2, U32, C.WL(t), 0n), Nil{}, Q.take_zero(C.WL(t))))
  +g1 = AB.subst(Nat, x => {List.take(&2, U32, C.WL(GTR), x) == List.take(&2, U32, C.WL(t), x) : List<&2, U32>}, N0, Pd,
    I.size_n(d, C.lt32(d, hd)), gtake(N0, t, t0, 0, d, e, hf, tnew_full(e, 0), hd, he, he29, hn0, hinv0))
  +tall = AB.subst(Nat, x => {List.take(&2, U32, C.WL(t), x) == C.WL(t) : List<&2, U32>}, List.length(&2, U32, C.WL(t)), Pd,
    P.view_length(U32, d, t, hf), take_all(C.WL(t)))
  +e1 = Equal.trans(List<&2, U32>, List.take(&2, U32, C.WL(GTR), Pd), List.take(&2, U32, C.WL(t), Pd), C.WL(t), g1, tall)
  %Equal.sym(D.Bytes, B.grow(C.BT(len, t), e), C.BT(len, GTR), grow_eq(len, t, d, e, hf)) : {D.view(_) == RHS : List<&2, U32>}
  %Equal.sym(List<&2, U32>, List.take(&2, U32, D.unpack(C.WL(GTR)), L), List.take(&2, U32, D.unpack(List.take(&2, U32, C.WL(GTR), Pd)), L),
    ut(C.WL(GTR), Pd, L, hl4)) :
    {_ == RHS : List<&2, U32>}
  %Equal.sym(List<&2, U32>, List.take(&2, U32, C.WL(GTR), Pd), C.WL(t), e1) :
    {List.take(&2, U32, D.unpack(_), L) == RHS : List<&2, U32>}
  {==}

law grow_ok_t:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +e: Nat
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +he: {Nat.is_le(d, e) == True{} : Bool}
  for +he29: {Nat.is_le(e, 29n) == True{} : Bool}
  {D.ok(B.grow(C.BT(len, t), e), e) == True{} : Bool}

def grow_ok_t(len, t, d, e, h, he, he29):
  +hf = C.ok_full(len, t, d, h)
  +N0 = U32.to_nat(U32.shln(1, d))
  +GTR = gtree(N0, t, tnew(e, 0), 0)
  %Equal.sym(D.Bytes, B.grow(C.BT(len, t), e), C.BT(len, GTR), grow_eq(len, t, d, e, hf)) : {D.ok(_, e) == True{} : Bool}
  C.ok_mk(len, GTR, e, gfull(N0, t, tnew(e, 0), 0, e, tnew_full(e, 0)), he29,
    N.le_trans(U32.to_nat(len), Nat.mul(4n, Nat.pow(2n, d)), Nat.mul(4n, Nat.pow(2n, e)), C.ok_len(len, t, d, h),
      N.le_mul_l(4n, Nat.pow(2n, d), Nat.pow(2n, e), N.pow_le(d, e, he))))
