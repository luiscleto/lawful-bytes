import Base
import ./defs.bend as D
import ../lawful-words/proof_nat.bend as WN
import ../lawful-words/proof_u32.bend as WU

# The pure list laws: first/first2 (search answers) and list_eq. Every
# variable is reusable, so PROOF.bend can forward the laws here.
#
# first(xs, from, to, c) is from + run_len(take(drop(xs, from), to - from)).
# For xs = x <> rest, from = 1+f and to = 1+t it computes to
# 1 + first(rest, f, t, c) (and to 1 + first(rest, f, 0n, c) for to = 0n), so
# every law goes by induction on xs and from down to from = 0n, where it is a
# fact about run_len(take(xs, to)) (the pl_r* and pl_r2* lemmas).

# Bool and Nat
# ============

law pl_ft:
  for e: {False{} == True{} : Bool}
  Empty

def pl_ft(e):
  %e : Bool.pick(Type, _, Empty, Unit)
  Unit{}

law pl_tf:
  for e: {True{} == False{} : Bool}
  Empty

def pl_tf(e):
  %e : Bool.pick(Type, _, Unit, Empty)
  Unit{}

# k < 0 is impossible.
law pl_lt0:
  for +k: Nat
  for +e: {Nat.is_lt(k, 0n) == True{} : Bool}
  Empty

def pl_lt0(k, e):
  match k:
    case 0n:
      pl_ft(e)
    case 1n+p:
      pl_ft(e)

law pl_and_l:
  for +a: Bool
  for +b: Bool
  for +e: {Bool.and(a, b) == True{} : Bool}
  {a == True{} : Bool}

def pl_and_l(a, b, e):
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, pl_ft(e))

law pl_and_r:
  for +a: Bool
  for +b: Bool
  for +e: {Bool.and(a, b) == True{} : Bool}
  {b == True{} : Bool}

def pl_and_r(a, b, e):
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({b == True{} : Bool}, pl_ft(e))

# 0 <= n, inside a conjunction.
law pl_le0_and:
  for +n: Nat
  for +b: Bool
  for +e: {b == True{} : Bool}
  {(Nat.is_le(0n, n) && b) == True{} : Bool}

def pl_le0_and(n, b, e):
  match n:
    case 0n:
      e
    case 1n+p:
      e

law pl_u32_eq_refl:
  for +a: U32
  {U32.is_eq(a, a) == True{} : Bool}

def pl_u32_eq_refl(a):
  Equal.trans(Bool, U32.is_eq(a, a), Nat.is_eq(U32.to_nat(a), U32.to_nat(a)), True{},
    WU.is_eq_to_nat(a, a), WN.eq_refl(U32.to_nat(a)))

# run_len over a prefix (from = 0n)
# ================================

law pl_r_step_le:
  for +z: Bool
  for +r: Nat
  for +p: Nat
  for +h: {Nat.is_le(r, p) == True{} : Bool}
  {Nat.is_le(Bool.pick(Nat, z, 0n, 1n+r), 1n+p) == True{} : Bool}

def pl_r_step_le(z, r, p, h):
  match z:
    case True{}:
      {==}
    case False{}:
      h

# The run is no longer than the prefix.
law pl_r_le:
  for +zs: List<&2, U32>
  for +n: Nat
  for +c: U32
  {Nat.is_le(D.run_len(List.take(&2, U32, zs, n), c), n) == True{} : Bool}

def pl_r_le(zs, n, c):
  match zs n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      {==}
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+p:
      pl_r_step_le(U32.is_eq(x, c), D.run_len(List.take(&2, U32, t, p), c), p, pl_r_le(t, p, c))

law pl_r_hit_step:
  for +x: U32
  for +t: List<&2, U32>
  for +c: U32
  for +r: Nat
  for +p: Nat
  for +z: Bool
  for +hz: {U32.is_eq(x, c) == z : Bool}
  for +hlt: {Nat.is_lt(Bool.pick(Nat, z, 0n, 1n+r), 1n+p) == True{} : Bool}
  for ih: {Nat.is_lt(r, p) == True{} : Bool} -> {D.has(t, r, c) == True{} : Bool}
  {D.has(Con{x, t}, Bool.pick(Nat, z, 0n, 1n+r), c) == True{} : Bool}

def pl_r_hit_step(x, t, c, r, p, z, hz, hlt, ih):
  match z:
    case True{}:
      hz
    case False{}:
      ih(hlt)

# Short of the end, the run stops at a c.
law pl_r_hit:
  for +zs: List<&2, U32>
  for +n: Nat
  for +c: U32
  for +ht: {Nat.is_le(n, List.length(&2, U32, zs)) == True{} : Bool}
  for +hlt: {Nat.is_lt(D.run_len(List.take(&2, U32, zs, n), c), n) == True{} : Bool}
  {D.has(zs, D.run_len(List.take(&2, U32, zs, n), c), c) == True{} : Bool}

def pl_r_hit(zs, n, c, ht, hlt):
  match zs n:
    case Nil{} 0n:
      Empty.absurd({D.has(Nil{}, 0n, c) == True{} : Bool}, pl_ft(hlt))
    case Nil{} 1n+p:
      Empty.absurd({D.has(Nil{}, 0n, c) == True{} : Bool}, pl_ft(ht))
    case Con{x, t} 0n:
      Empty.absurd({D.has(Con{x, t}, 0n, c) == True{} : Bool}, pl_ft(hlt))
    case Con{x, t} 1n+p:
      pl_r_hit_step(x, t, c, D.run_len(List.take(&2, U32, t, p), c), p, U32.is_eq(x, c), {==}, hlt,
        h => pl_r_hit(t, p, c, ht, h))

law pl_r_miss_step:
  for +x: U32
  for +t: List<&2, U32>
  for +c: U32
  for +r: Nat
  for +z: Bool
  for +k: Nat
  for +hz: {U32.is_eq(x, c) == z : Bool}
  for +hk: {Nat.is_lt(k, Bool.pick(Nat, z, 0n, 1n+r)) == True{} : Bool}
  for ih: @k2: Nat -> {Nat.is_lt(k2, r) == True{} : Bool} -> {D.has(t, k2, c) == False{} : Bool}
  {D.has(Con{x, t}, k, c) == False{} : Bool}

def pl_r_miss_step(x, t, c, r, z, k, hz, hk, ih):
  match z k:
    case True{} k:
      Empty.absurd({D.has(Con{x, t}, k, c) == False{} : Bool}, pl_lt0(k, hk))
    case False{} 0n:
      hz
    case False{} 1n+k2:
      ih(k2, hk)

# Before the end of the run, no c.
law pl_r_miss:
  for +zs: List<&2, U32>
  for +n: Nat
  for +c: U32
  for +k: Nat
  for +hk: {Nat.is_lt(k, D.run_len(List.take(&2, U32, zs, n), c)) == True{} : Bool}
  {D.has(zs, k, c) == False{} : Bool}

def pl_r_miss(zs, n, c, k, hk):
  match zs n:
    case Nil{} n:
      {==}
    case Con{x, t} 0n:
      Empty.absurd({D.has(Con{x, t}, k, c) == False{} : Bool}, pl_lt0(k, hk))
    case Con{x, t} 1n+p:
      pl_r_miss_step(x, t, c, D.run_len(List.take(&2, U32, t, p), c), U32.is_eq(x, c), k, {==}, hk,
        k2 => h => pl_r_miss(t, p, c, k2, h))

# The search laws
# ===============

law first_range:
  for +xs: List<&2, U32>
  for +from: Nat
  for +to: Nat
  for +c: U32
  for +hft: {Nat.is_le(from, to) == True{} : Bool}
  for +ht: {Nat.is_le(to, List.length(&2, U32, xs)) == True{} : Bool}
  {(Nat.is_le(from, D.first(xs, from, to, c)) && Nat.is_le(D.first(xs, from, to, c), to)) == True{} : Bool}

def first_range(xs, from, to, c, hft, ht):
  match xs from to:
    case Nil{} 0n 0n:
      {==}
    case Nil{} 0n 1n+t:
      Empty.absurd({(Nat.is_le(0n, D.first(Nil{}, 0n, 1n+t, c)) && Nat.is_le(D.first(Nil{}, 0n, 1n+t, c), 1n+t)) == True{} : Bool}, pl_ft(ht))
    case Nil{} 1n+f 0n:
      Empty.absurd({(Nat.is_le(1n+f, D.first(Nil{}, 1n+f, 0n, c)) && Nat.is_le(D.first(Nil{}, 1n+f, 0n, c), 0n)) == True{} : Bool}, pl_ft(hft))
    case Nil{} 1n+f 1n+t:
      Empty.absurd({(Nat.is_le(1n+f, D.first(Nil{}, 1n+f, 1n+t, c)) && Nat.is_le(D.first(Nil{}, 1n+f, 1n+t, c), 1n+t)) == True{} : Bool}, pl_ft(ht))
    case Con{x, rest} 0n 0n:
      {==}
    case Con{x, rest} 0n 1n+t:
      pl_le0_and(D.first(Con{x, rest}, 0n, 1n+t, c), Nat.is_le(D.first(Con{x, rest}, 0n, 1n+t, c), 1n+t),
        pl_r_le(Con{x, rest}, 1n+t, c))
    case Con{x, rest} 1n+f 0n:
      Empty.absurd({(Nat.is_le(1n+f, D.first(Con{x, rest}, 1n+f, 0n, c)) && Nat.is_le(D.first(Con{x, rest}, 1n+f, 0n, c), 0n)) == True{} : Bool}, pl_ft(hft))
    case Con{x, rest} 1n+f 1n+t:
      first_range(rest, f, t, c, hft, ht)

# Below to, the answer holds c.
law first_hit:
  for +xs: List<&2, U32>
  for +from: Nat
  for +to: Nat
  for +c: U32
  for +hft: {Nat.is_le(from, to) == True{} : Bool}
  for +ht: {Nat.is_le(to, List.length(&2, U32, xs)) == True{} : Bool}
  for +hlt: {Nat.is_lt(D.first(xs, from, to, c), to) == True{} : Bool}
  {D.has(xs, D.first(xs, from, to, c), c) == True{} : Bool}

def first_hit(xs, from, to, c, hft, ht, hlt):
  match xs from to:
    case Nil{} 0n 0n:
      Empty.absurd({D.has(Nil{}, D.first(Nil{}, 0n, 0n, c), c) == True{} : Bool}, pl_ft(hlt))
    case Nil{} 0n 1n+t:
      Empty.absurd({D.has(Nil{}, D.first(Nil{}, 0n, 1n+t, c), c) == True{} : Bool}, pl_ft(ht))
    case Nil{} 1n+f 0n:
      Empty.absurd({D.has(Nil{}, D.first(Nil{}, 1n+f, 0n, c), c) == True{} : Bool}, pl_ft(hft))
    case Nil{} 1n+f 1n+t:
      Empty.absurd({D.has(Nil{}, D.first(Nil{}, 1n+f, 1n+t, c), c) == True{} : Bool}, pl_ft(ht))
    case Con{x, rest} 0n 0n:
      Empty.absurd({D.has(Con{x, rest}, D.first(Con{x, rest}, 0n, 0n, c), c) == True{} : Bool}, pl_ft(hlt))
    case Con{x, rest} 0n 1n+t:
      pl_r_hit(Con{x, rest}, 1n+t, c, ht, hlt)
    case Con{x, rest} 1n+f 0n:
      Empty.absurd({D.has(Con{x, rest}, D.first(Con{x, rest}, 1n+f, 0n, c), c) == True{} : Bool}, pl_ft(hft))
    case Con{x, rest} 1n+f 1n+t:
      first_hit(rest, f, t, c, hft, ht, hlt)

# No index from from up to the answer holds c.
law first_miss:
  for +xs: List<&2, U32>
  for +from: Nat
  for +to: Nat
  for +c: U32
  for +k: Nat
  for +hk1: {Nat.is_le(from, k) == True{} : Bool}
  for +hk2: {Nat.is_lt(k, D.first(xs, from, to, c)) == True{} : Bool}
  {D.has(xs, k, c) == False{} : Bool}

def first_miss(xs, from, to, c, k, hk1, hk2):
  match xs from to k:
    case Nil{} from to k:
      {==}
    case Con{x, rest} 0n 0n k:
      pl_r_miss(Con{x, rest}, 0n, c, k, hk2)
    case Con{x, rest} 0n 1n+t k:
      pl_r_miss(Con{x, rest}, 1n+t, c, k, hk2)
    case Con{x, rest} 1n+f to 0n:
      Empty.absurd({D.has(Con{x, rest}, 0n, c) == False{} : Bool}, pl_ft(hk1))
    case Con{x, rest} 1n+f 0n 1n+k2:
      first_miss(rest, f, 0n, c, k2, hk1, hk2)
    case Con{x, rest} 1n+f 1n+t 1n+k2:
      first_miss(rest, f, t, c, k2, hk1, hk2)

# Lists compared element by element
# =================================

law list_eq_true:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +h: {D.list_eq(xs, ys) == True{} : Bool}
  {xs == ys : List<&2, U32>}

def list_eq_true(xs, ys, h):
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Con{x, xt} Con{y, yt}:
      +ex = WU.is_eq_true(x, y, pl_and_l(U32.is_eq(x, y), D.list_eq(xt, yt), h))
      +et = list_eq_true(xt, yt, pl_and_r(U32.is_eq(x, y), D.list_eq(xt, yt), h))
      %ex : {Con{x, xt} == Con{_, yt} : List<&2, U32>}
      %et : {Con{x, xt} == Con{x, _} : List<&2, U32>}
      {==}
    case Nil{} Con{y, yt}:
      Empty.absurd({Nil{} == Con{y, yt} : List<&2, U32>}, pl_ft(h))
    case Con{x, xt} Nil{}:
      Empty.absurd({Con{x, xt} == Nil{} : List<&2, U32>}, pl_ft(h))

law list_eq_refl:
  for +xs: List<&2, U32>
  {D.list_eq(xs, xs) == True{} : Bool}

def list_eq_refl(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      %Equal.sym(Bool, U32.is_eq(x, x), True{}, pl_u32_eq_refl(x)) :
        {Bool.and(_, D.list_eq(t, t)) == True{} : Bool}
      list_eq_refl(t)

# run_len2 over a prefix (from = 0n), as for run_len
# ==================================================

law pl_r2_le:
  for +zs: List<&2, U32>
  for +n: Nat
  for +c1: U32
  for +c2: U32
  {Nat.is_le(D.run_len2(List.take(&2, U32, zs, n), c1, c2), n) == True{} : Bool}

def pl_r2_le(zs, n, c1, c2):
  match zs n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      {==}
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+p:
      pl_r_step_le(U32.is_eq(x, c1) || U32.is_eq(x, c2), D.run_len2(List.take(&2, U32, t, p), c1, c2), p,
        pl_r2_le(t, p, c1, c2))

law pl_r2_hit_step:
  for +x: U32
  for +t: List<&2, U32>
  for +c1: U32
  for +c2: U32
  for +r: Nat
  for +p: Nat
  for +z: Bool
  for +hz: {(U32.is_eq(x, c1) || U32.is_eq(x, c2)) == z : Bool}
  for +hlt: {Nat.is_lt(Bool.pick(Nat, z, 0n, 1n+r), 1n+p) == True{} : Bool}
  for ih: {Nat.is_lt(r, p) == True{} : Bool} -> {D.has2(t, r, c1, c2) == True{} : Bool}
  {D.has2(Con{x, t}, Bool.pick(Nat, z, 0n, 1n+r), c1, c2) == True{} : Bool}

def pl_r2_hit_step(x, t, c1, c2, r, p, z, hz, hlt, ih):
  match z:
    case True{}:
      hz
    case False{}:
      ih(hlt)

law pl_r2_hit:
  for +zs: List<&2, U32>
  for +n: Nat
  for +c1: U32
  for +c2: U32
  for +ht: {Nat.is_le(n, List.length(&2, U32, zs)) == True{} : Bool}
  for +hlt: {Nat.is_lt(D.run_len2(List.take(&2, U32, zs, n), c1, c2), n) == True{} : Bool}
  {D.has2(zs, D.run_len2(List.take(&2, U32, zs, n), c1, c2), c1, c2) == True{} : Bool}

def pl_r2_hit(zs, n, c1, c2, ht, hlt):
  match zs n:
    case Nil{} 0n:
      Empty.absurd({D.has2(Nil{}, 0n, c1, c2) == True{} : Bool}, pl_ft(hlt))
    case Nil{} 1n+p:
      Empty.absurd({D.has2(Nil{}, 0n, c1, c2) == True{} : Bool}, pl_ft(ht))
    case Con{x, t} 0n:
      Empty.absurd({D.has2(Con{x, t}, 0n, c1, c2) == True{} : Bool}, pl_ft(hlt))
    case Con{x, t} 1n+p:
      pl_r2_hit_step(x, t, c1, c2, D.run_len2(List.take(&2, U32, t, p), c1, c2), p,
        U32.is_eq(x, c1) || U32.is_eq(x, c2), {==}, hlt, h => pl_r2_hit(t, p, c1, c2, ht, h))

law pl_r2_miss_step:
  for +x: U32
  for +t: List<&2, U32>
  for +c1: U32
  for +c2: U32
  for +r: Nat
  for +z: Bool
  for +k: Nat
  for +hz: {(U32.is_eq(x, c1) || U32.is_eq(x, c2)) == z : Bool}
  for +hk: {Nat.is_lt(k, Bool.pick(Nat, z, 0n, 1n+r)) == True{} : Bool}
  for ih: @k2: Nat -> {Nat.is_lt(k2, r) == True{} : Bool} -> {D.has2(t, k2, c1, c2) == False{} : Bool}
  {D.has2(Con{x, t}, k, c1, c2) == False{} : Bool}

def pl_r2_miss_step(x, t, c1, c2, r, z, k, hz, hk, ih):
  match z k:
    case True{} k:
      Empty.absurd({D.has2(Con{x, t}, k, c1, c2) == False{} : Bool}, pl_lt0(k, hk))
    case False{} 0n:
      hz
    case False{} 1n+k2:
      ih(k2, hk)

law pl_r2_miss:
  for +zs: List<&2, U32>
  for +n: Nat
  for +c1: U32
  for +c2: U32
  for +k: Nat
  for +hk: {Nat.is_lt(k, D.run_len2(List.take(&2, U32, zs, n), c1, c2)) == True{} : Bool}
  {D.has2(zs, k, c1, c2) == False{} : Bool}

def pl_r2_miss(zs, n, c1, c2, k, hk):
  match zs n:
    case Nil{} n:
      {==}
    case Con{x, t} 0n:
      Empty.absurd({D.has2(Con{x, t}, k, c1, c2) == False{} : Bool}, pl_lt0(k, hk))
    case Con{x, t} 1n+p:
      pl_r2_miss_step(x, t, c1, c2, D.run_len2(List.take(&2, U32, t, p), c1, c2),
        U32.is_eq(x, c1) || U32.is_eq(x, c2), k, {==}, hk, k2 => h => pl_r2_miss(t, p, c1, c2, k2, h))

# The two-value search laws
# =========================

law first2_range:
  for +xs: List<&2, U32>
  for +from: Nat
  for +to: Nat
  for +c1: U32
  for +c2: U32
  for +hft: {Nat.is_le(from, to) == True{} : Bool}
  for +ht: {Nat.is_le(to, List.length(&2, U32, xs)) == True{} : Bool}
  {(Nat.is_le(from, D.first2(xs, from, to, c1, c2)) && Nat.is_le(D.first2(xs, from, to, c1, c2), to)) == True{} : Bool}

def first2_range(xs, from, to, c1, c2, hft, ht):
  match xs from to:
    case Nil{} 0n 0n:
      {==}
    case Nil{} 0n 1n+t:
      Empty.absurd({(Nat.is_le(0n, D.first2(Nil{}, 0n, 1n+t, c1, c2)) && Nat.is_le(D.first2(Nil{}, 0n, 1n+t, c1, c2), 1n+t)) == True{} : Bool}, pl_ft(ht))
    case Nil{} 1n+f 0n:
      Empty.absurd({(Nat.is_le(1n+f, D.first2(Nil{}, 1n+f, 0n, c1, c2)) && Nat.is_le(D.first2(Nil{}, 1n+f, 0n, c1, c2), 0n)) == True{} : Bool}, pl_ft(hft))
    case Nil{} 1n+f 1n+t:
      Empty.absurd({(Nat.is_le(1n+f, D.first2(Nil{}, 1n+f, 1n+t, c1, c2)) && Nat.is_le(D.first2(Nil{}, 1n+f, 1n+t, c1, c2), 1n+t)) == True{} : Bool}, pl_ft(ht))
    case Con{x, rest} 0n 0n:
      {==}
    case Con{x, rest} 0n 1n+t:
      pl_le0_and(D.first2(Con{x, rest}, 0n, 1n+t, c1, c2), Nat.is_le(D.first2(Con{x, rest}, 0n, 1n+t, c1, c2), 1n+t),
        pl_r2_le(Con{x, rest}, 1n+t, c1, c2))
    case Con{x, rest} 1n+f 0n:
      Empty.absurd({(Nat.is_le(1n+f, D.first2(Con{x, rest}, 1n+f, 0n, c1, c2)) && Nat.is_le(D.first2(Con{x, rest}, 1n+f, 0n, c1, c2), 0n)) == True{} : Bool}, pl_ft(hft))
    case Con{x, rest} 1n+f 1n+t:
      first2_range(rest, f, t, c1, c2, hft, ht)

law first2_hit:
  for +xs: List<&2, U32>
  for +from: Nat
  for +to: Nat
  for +c1: U32
  for +c2: U32
  for +hft: {Nat.is_le(from, to) == True{} : Bool}
  for +ht: {Nat.is_le(to, List.length(&2, U32, xs)) == True{} : Bool}
  for +hlt: {Nat.is_lt(D.first2(xs, from, to, c1, c2), to) == True{} : Bool}
  {D.has2(xs, D.first2(xs, from, to, c1, c2), c1, c2) == True{} : Bool}

def first2_hit(xs, from, to, c1, c2, hft, ht, hlt):
  match xs from to:
    case Nil{} 0n 0n:
      Empty.absurd({D.has2(Nil{}, D.first2(Nil{}, 0n, 0n, c1, c2), c1, c2) == True{} : Bool}, pl_ft(hlt))
    case Nil{} 0n 1n+t:
      Empty.absurd({D.has2(Nil{}, D.first2(Nil{}, 0n, 1n+t, c1, c2), c1, c2) == True{} : Bool}, pl_ft(ht))
    case Nil{} 1n+f 0n:
      Empty.absurd({D.has2(Nil{}, D.first2(Nil{}, 1n+f, 0n, c1, c2), c1, c2) == True{} : Bool}, pl_ft(hft))
    case Nil{} 1n+f 1n+t:
      Empty.absurd({D.has2(Nil{}, D.first2(Nil{}, 1n+f, 1n+t, c1, c2), c1, c2) == True{} : Bool}, pl_ft(ht))
    case Con{x, rest} 0n 0n:
      Empty.absurd({D.has2(Con{x, rest}, D.first2(Con{x, rest}, 0n, 0n, c1, c2), c1, c2) == True{} : Bool}, pl_ft(hlt))
    case Con{x, rest} 0n 1n+t:
      pl_r2_hit(Con{x, rest}, 1n+t, c1, c2, ht, hlt)
    case Con{x, rest} 1n+f 0n:
      Empty.absurd({D.has2(Con{x, rest}, D.first2(Con{x, rest}, 1n+f, 0n, c1, c2), c1, c2) == True{} : Bool}, pl_ft(hft))
    case Con{x, rest} 1n+f 1n+t:
      first2_hit(rest, f, t, c1, c2, hft, ht, hlt)

law first2_miss:
  for +xs: List<&2, U32>
  for +from: Nat
  for +to: Nat
  for +c1: U32
  for +c2: U32
  for +k: Nat
  for +hk1: {Nat.is_le(from, k) == True{} : Bool}
  for +hk2: {Nat.is_lt(k, D.first2(xs, from, to, c1, c2)) == True{} : Bool}
  {D.has2(xs, k, c1, c2) == False{} : Bool}

def first2_miss(xs, from, to, c1, c2, k, hk1, hk2):
  match xs from to k:
    case Nil{} from to k:
      {==}
    case Con{x, rest} 0n 0n k:
      pl_r2_miss(Con{x, rest}, 0n, c1, c2, k, hk2)
    case Con{x, rest} 0n 1n+t k:
      pl_r2_miss(Con{x, rest}, 1n+t, c1, c2, k, hk2)
    case Con{x, rest} 1n+f to 0n:
      Empty.absurd({D.has2(Con{x, rest}, 0n, c1, c2) == False{} : Bool}, pl_ft(hk1))
    case Con{x, rest} 1n+f 0n 1n+k2:
      first2_miss(rest, f, 0n, c1, c2, k2, hk1, hk2)
    case Con{x, rest} 1n+f 1n+t 1n+k2:
      first2_miss(rest, f, t, c1, c2, k2, hk1, hk2)
