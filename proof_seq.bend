import Base
import ./defs.bend as D
import lawful-words@0.1.0.0/defs.bend as W
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_bytes.bend as Y
import lawful-arrays@0.1.0.0/proof_base.bend as AB

# List facts the Bytes proofs need (take, set, append, unpack), for lists of
# U32. Every variable is reusable.

law take_zero:
  for +xs: List<&2, U32>
  {List.take(&2, U32, xs, 0n) == Nil{} : List<&2, U32>}

def take_zero(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      {==}

law take_length:
  for +xs: List<&2, U32>
  for +n: Nat
  for +h: {Nat.is_le(n, List.length(&2, U32, xs)) == True{} : Bool}
  {List.length(&2, U32, List.take(&2, U32, xs, n)) == n : Nat}

def take_length(xs, n, h):
  match xs n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      Empty.absurd({0n == 1n+p : Nat}, AB.false_ne_true(h))
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+p:
      %take_length(t, p, h) : {1n+List.length(&2, U32, List.take(&2, U32, t, p)) == 1n+_ : Nat}
      {==}

law take_take:
  for +xs: List<&2, U32>
  for +m: Nat
  for +n: Nat
  for +h: {Nat.is_le(n, m) == True{} : Bool}
  {List.take(&2, U32, List.take(&2, U32, xs, m), n) == List.take(&2, U32, xs, n) : List<&2, U32>}

def take_take(xs, m, n, h):
  match xs m n:
    case Nil{} _ _:
      {==}
    case Con{x, t} 0n 0n:
      {==}
    case Con{x, t} 0n 1n+q:
      Empty.absurd({Nil{} == x <> List.take(&2, U32, t, q) : List<&2, U32>}, AB.false_ne_true(h))
    case Con{x, t} 1n+p 0n:
      {==}
    case Con{x, t} 1n+p 1n+q:
      %take_take(t, p, q, h) : {x <> List.take(&2, U32, List.take(&2, U32, t, p), q) == x <> _ : List<&2, U32>}
      {==}

law take_set:
  for +xs: List<&2, U32>
  for +m: Nat
  for +i: Nat
  for +v: U32
  {List.take(&2, U32, List.set(&2, U32, xs, i, v), m) == List.set(&2, U32, List.take(&2, U32, xs, m), i, v) : List<&2, U32>}

def take_set(xs, m, i, v):
  match xs m i:
    case Nil{} _ _:
      {==}
    case Con{x, t} 0n 0n:
      {==}
    case Con{x, t} 0n 1n+j:
      {==}
    case Con{x, t} 1n+p 0n:
      {==}
    case Con{x, t} 1n+p 1n+j:
      %take_set(t, p, j, v) : {x <> List.take(&2, U32, List.set(&2, U32, t, j, v), p) == x <> _ : List<&2, U32>}
      {==}

# Setting index n and keeping n + 1 elements: the first n, then v.
law take_set_succ:
  for +xs: List<&2, U32>
  for +n: Nat
  for +v: U32
  for +h: {Nat.is_lt(n, List.length(&2, U32, xs)) == True{} : Bool}
  {List.take(&2, U32, List.set(&2, U32, xs, n, v), Nat.add(n, 1n)) == List.append(&2, U32, List.take(&2, U32, xs, n), [v]) : List<&2, U32>}

def take_set_succ(xs, n, v, h):
  match xs n:
    case Nil{} _:
      Empty.absurd({List.take(&2, U32, Nil{}, Nat.add(n, 1n)) == List.append(&2, U32, Nil{}, [v]) : List<&2, U32>},
        AB.lt_zero_absurd(n, h))
    case Con{x, t} 0n:
      %Equal.sym(List<&2, U32>, List.take(&2, U32, t, 0n), Nil{}, take_zero(t)) : {v <> _ == [v] : List<&2, U32>}
      {==}
    case Con{x, t} 1n+p:
      %take_set_succ(t, p, v, h) : {x <> List.take(&2, U32, List.set(&2, U32, t, p, v), Nat.add(p, 1n)) == x <> _ : List<&2, U32>}
      {==}

law take_append_l:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +n: Nat
  for +h: {Nat.is_le(n, List.length(&2, U32, xs)) == True{} : Bool}
  {List.take(&2, U32, List.append(&2, U32, xs, ys), n) == List.take(&2, U32, xs, n) : List<&2, U32>}

def take_append_l(xs, ys, n, h):
  match xs n:
    case Nil{} 0n:
      take_zero(ys)
    case Nil{} 1n+p:
      Empty.absurd({List.take(&2, U32, ys, 1n+p) == Nil{} : List<&2, U32>}, AB.false_ne_true(h))
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+p:
      %take_append_l(t, ys, p, h) : {x <> List.take(&2, U32, List.append(&2, U32, t, ys), p) == x <> _ : List<&2, U32>}
      {==}

# Unpacking
# =========

law unpack_length4:
  for +ws: List<&2, U32>
  {List.length(&2, U32, D.unpack(ws)) == Nat.mul(List.length(&2, U32, ws), 4n) : Nat}

def unpack_length4(ws):
  match ws:
    case Nil{}:
      {==}
    case Con{w, t}:
      %unpack_length4(t) : {4n+List.length(&2, U32, D.unpack(t)) == 4n+_ : Nat}
      {==}

law unpack_length:
  for +ws: List<&2, U32>
  {List.length(&2, U32, D.unpack(ws)) == Nat.mul(4n, List.length(&2, U32, ws)) : Nat}

def unpack_length(ws):
  Equal.trans(Nat, List.length(&2, U32, D.unpack(ws)), Nat.mul(List.length(&2, U32, ws), 4n),
    Nat.mul(4n, List.length(&2, U32, ws)), unpack_length4(ws), N.mul_comm(List.length(&2, U32, ws), 4n))

law unpack_append:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  {D.unpack(List.append(&2, U32, xs, ys)) == List.append(&2, U32, D.unpack(xs), D.unpack(ys)) : List<&2, U32>}

def unpack_append(xs, ys):
  match xs:
    case Nil{}:
      {==}
    case Con{+w, t}:
      %unpack_append(t, ys) :
        {W.byte(w, 0n) <> W.byte(w, 1n) <> W.byte(w, 2n) <> W.byte(w, 3n) <> D.unpack(List.append(&2, U32, t, ys)) ==
          W.byte(w, 0n) <> W.byte(w, 1n) <> W.byte(w, 2n) <> W.byte(w, 3n) <> _ : List<&2, U32>}
      {==}

law all_bytes_unpack:
  for +ws: List<&2, U32>
  {D.all_bytes(D.unpack(ws)) == True{} : Bool}

def all_bytes_unpack(ws):
  match ws:
    case Nil{}:
      {==}
    case Con{+w, t}:
      %Equal.sym(Bool, U32.is_lt(W.byte(w, 0n), 256), True{}, Y.byte_lt(w, 0n)) :
        {Bool.and(_, Bool.and(U32.is_lt(W.byte(w, 1n), 256), Bool.and(U32.is_lt(W.byte(w, 2n), 256),
          Bool.and(U32.is_lt(W.byte(w, 3n), 256), D.all_bytes(D.unpack(t)))))) == True{} : Bool}
      %Equal.sym(Bool, U32.is_lt(W.byte(w, 1n), 256), True{}, Y.byte_lt(w, 1n)) :
        {Bool.and(True{}, Bool.and(_, Bool.and(U32.is_lt(W.byte(w, 2n), 256),
          Bool.and(U32.is_lt(W.byte(w, 3n), 256), D.all_bytes(D.unpack(t)))))) == True{} : Bool}
      %Equal.sym(Bool, U32.is_lt(W.byte(w, 2n), 256), True{}, Y.byte_lt(w, 2n)) :
        {Bool.and(True{}, Bool.and(True{}, Bool.and(_,
          Bool.and(U32.is_lt(W.byte(w, 3n), 256), D.all_bytes(D.unpack(t)))))) == True{} : Bool}
      %Equal.sym(Bool, U32.is_lt(W.byte(w, 3n), 256), True{}, Y.byte_lt(w, 3n)) :
        {Bool.and(True{}, Bool.and(True{}, Bool.and(True{},
          Bool.and(_, D.all_bytes(D.unpack(t)))))) == True{} : Bool}
      %Equal.sym(Bool, D.all_bytes(D.unpack(t)), True{}, all_bytes_unpack(t)) :
        {Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, _)))) == True{} : Bool}
      {==}

law all_bytes_take:
  for +xs: List<&2, U32>
  for +n: Nat
  for +h: {D.all_bytes(xs) == True{} : Bool}
  {D.all_bytes(List.take(&2, U32, xs, n)) == True{} : Bool}

def all_bytes_take(xs, n, h):
  match xs n:
    case Nil{} _:
      {==}
    case Con{x, t} 0n:
      {==}
    case Con{+x, t} 1n+p:
      %Equal.sym(Bool, U32.is_lt(x, 256), True{}, AB.and_true_l(U32.is_lt(x, 256), D.all_bytes(t), h)) :
        {Bool.and(_, D.all_bytes(List.take(&2, U32, t, p))) == True{} : Bool}
      all_bytes_take(t, p, AB.and_true_r(U32.is_lt(x, 256), D.all_bytes(t), h))
