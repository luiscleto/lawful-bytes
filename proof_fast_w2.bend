import Base
import ../lawful-words/defs.bend as W
import ../lawful-words/proof_nat.bend as N
import ../lawful-words/proof_u32.bend as U
import ../lawful-words/proof_bytes.bend as Y
import ../lawful-words/proof_zb.bend as Z
import ../lawful-arrays/proof_base.bend as AB
import ./fast.bend as FA

# Or, the broadcast byte, the bytes of the masked first word, and the tables
# that turn the per-byte tests into places (4 Bools per word, checked case by
# case).

# Or and the zero test
# ====================

law allz_orm:
  for +n: Nat
  for +x: Word(n)
  for +y: Word(n)
  for +z: Word(n)
  {Z.allz(n, Word.and(n, Word.or(n, x, y), z)) == Bool.and(Z.allz(n, Word.and(n, x, z)), Z.allz(n, Word.and(n, y, z))) : Bool}

def allz_orm(n, x, y, z):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match x y z:
        case WCon{False{}, +xt} WCon{False{}, +yt} WCon{False{}, +zt}:
          allz_orm(p, xt, yt, zt)
        case WCon{False{}, +xt} WCon{False{}, +yt} WCon{True{}, +zt}:
          allz_orm(p, xt, yt, zt)
        case WCon{False{}, +xt} WCon{True{}, +yt} WCon{False{}, +zt}:
          allz_orm(p, xt, yt, zt)
        case WCon{False{}, +xt} WCon{True{}, +yt} WCon{True{}, +zt}:
          Equal.sym(Bool, Bool.and(Z.allz(p, Word.and(p, xt, zt)), False{}), False{}, N.and_false_r(Z.allz(p, Word.and(p, xt, zt))))
        case WCon{True{}, +xt} WCon{False{}, +yt} WCon{False{}, +zt}:
          allz_orm(p, xt, yt, zt)
        case WCon{True{}, +xt} WCon{False{}, +yt} WCon{True{}, +zt}:
          {==}
        case WCon{True{}, +xt} WCon{True{}, +yt} WCon{False{}, +zt}:
          allz_orm(p, xt, yt, zt)
        case WCon{True{}, +xt} WCon{True{}, +yt} WCon{True{}, +zt}:
          {==}

law allz_or:
  for +n: Nat
  for +x: Word(n)
  for +y: Word(n)
  {Z.allz(n, Word.or(n, x, y)) == Bool.and(Z.allz(n, x), Z.allz(n, y)) : Bool}

def allz_or(n, x, y):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match x y:
        case WCon{False{}, +xt} WCon{False{}, +yt}:
          allz_or(p, xt, yt)
        case WCon{False{}, +xt} WCon{True{}, +yt}:
          Equal.sym(Bool, Bool.and(Z.allz(p, xt), False{}), False{}, N.and_false_r(Z.allz(p, xt)))
        case WCon{True{}, +xt} WCon{+b, +yt}:
          {==}

law iz:
  for +w: Word(32n)
  {U32.is_zero(U32{w}) == Z.allz(32n, w) : Bool}

def iz(w):
  Z.allz_cmp(32n, w)

law uorm:
  for +a: U32
  for +b: U32
  for +h: U32
  {U32.is_zero(U32.and(U32.or(a, b), h)) == Bool.and(U32.is_zero(U32.and(a, h)), U32.is_zero(U32.and(b, h))) : Bool}

def uorm(a, b, h):
  match a b h:
    case U32{+x} U32{+y} U32{+z}:
      %Equal.sym(Bool, U32.is_zero(U32{Word.and(32n, x, z)}), Z.allz(32n, Word.and(32n, x, z)), iz(Word.and(32n, x, z))) :
        {U32.is_zero(U32{Word.and(32n, Word.or(32n, x, y), z)}) == Bool.and(_, U32.is_zero(U32{Word.and(32n, y, z)})) : Bool}
      %Equal.sym(Bool, U32.is_zero(U32{Word.and(32n, y, z)}), Z.allz(32n, Word.and(32n, y, z)), iz(Word.and(32n, y, z))) :
        {U32.is_zero(U32{Word.and(32n, Word.or(32n, x, y), z)}) == Bool.and(Z.allz(32n, Word.and(32n, x, z)), _) : Bool}
      Equal.trans(Bool, U32.is_zero(U32{Word.and(32n, Word.or(32n, x, y), z)}), Z.allz(32n, Word.and(32n, Word.or(32n, x, y), z)),
        Bool.and(Z.allz(32n, Word.and(32n, x, z)), Z.allz(32n, Word.and(32n, y, z))),
        iz(Word.and(32n, Word.or(32n, x, y), z)), allz_orm(32n, x, y, z))

law uor0:
  for +a: U32
  for +b: U32
  {U32.is_zero(U32.or(a, b)) == Bool.and(U32.is_zero(a), U32.is_zero(b)) : Bool}

def uor0(a, b):
  match a b:
    case U32{+x} U32{+y}:
      %Equal.sym(Bool, U32.is_zero(U32{x}), Z.allz(32n, x), iz(x)) :
        {U32.is_zero(U32{Word.or(32n, x, y)}) == Bool.and(_, U32.is_zero(U32{y})) : Bool}
      %Equal.sym(Bool, U32.is_zero(U32{y}), Z.allz(32n, y), iz(y)) :
        {U32.is_zero(U32{Word.or(32n, x, y)}) == Bool.and(Z.allz(32n, x), _) : Bool}
      Equal.trans(Bool, U32.is_zero(U32{Word.or(32n, x, y)}), Z.allz(32n, Word.or(32n, x, y)), Bool.and(Z.allz(32n, x), Z.allz(32n, y)),
        iz(Word.or(32n, x, y)), allz_or(32n, x, y))

def or_false(-p: Nat, +b: Bool, +t: Word(p)) -> {WCon{Bool.or(b, False{}), t} == WCon{b, t} : Word(1n+p)}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

law wor0:
  for +n: Nat
  for +x: Word(n)
  {Word.or(n, x, Word.zero(n)) == x : Word(n)}

def wor0(n, x):
  match n:
    case 0n:
      match x:
        case WNil{}:
          {==}
    case 1n+p:
      match x:
        case WCon{+b, +t}:
          %Equal.sym(Word(p), Word.or(p, t, Word.zero(p)), t, wor0(p, t)) : {WCon{Bool.or(b, False{}), _} == WCon{b, t} : Word(1n+p)}
          or_false(p, b, t)

law or0r:
  for +y: U32
  {U32.or(y, 0) == y : U32}

def or0r(y):
  match y:
    case U32{+x}:
      %Equal.sym(Word(32n), Word.or(32n, x, Word.zero(32n)), x, wor0(32n, x)) : {U32{_} == U32{x} : U32}
      {==}

law or255:
  for +y: U32
  {U32.is_eq(U32.or(y, 255), 0) == False{} : Bool}

def or255(y):
  Equal.trans(Bool, U32.is_zero(U32.or(y, 255)), Bool.and(U32.is_zero(y), False{}), False{}, uor0(y, 255), N.and_false_r(U32.is_zero(y)))

# The broadcast byte
# ==================

law nth4_same:
  for +j: Nat
  for +c: U32
  {W.nth4(j, c, c, c, c) == c : U32}

def nth4_same(j, c):
  match j:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          {==}
        case 1n+q:
          match q:
            case 0n:
              {==}
            case 1n+r:
              {==}

law nk:
  for +x: Nat
  for +A: Nat
  for +B: Nat
  for +E: Nat
  {Nat.mul(x, Nat.add(1n, Nat.add(Nat.mul(1n, A), Nat.add(Nat.mul(1n, B), Nat.mul(1n, E))))) == Nat.add(x, Nat.add(Nat.mul(x, A), Nat.add(Nat.mul(x, B), Nat.mul(x, E)))) : Nat}

def nk(x, A, B, E):
  +RHS = Nat.add(x, Nat.add(Nat.mul(x, A), Nat.add(Nat.mul(x, B), Nat.mul(x, E))))
  %Equal.sym(Nat, Nat.add(A, 0n), A, N.add_zero(A)) :
    {Nat.mul(x, Nat.add(1n, Nat.add(_, Nat.add(Nat.mul(1n, B), Nat.mul(1n, E))))) == RHS : Nat}
  %Equal.sym(Nat, Nat.add(B, 0n), B, N.add_zero(B)) :
    {Nat.mul(x, Nat.add(1n, Nat.add(A, Nat.add(_, Nat.mul(1n, E))))) == RHS : Nat}
  %Equal.sym(Nat, Nat.add(E, 0n), E, N.add_zero(E)) :
    {Nat.mul(x, Nat.add(1n, Nat.add(A, Nat.add(B, _)))) == RHS : Nat}
  %Equal.sym(Nat, Nat.mul(x, Nat.add(1n, Nat.add(A, Nat.add(B, E)))), Nat.add(Nat.mul(x, 1n), Nat.mul(x, Nat.add(A, Nat.add(B, E)))), N.mul_add(x, 1n, Nat.add(A, Nat.add(B, E)))) : {_ == RHS : Nat}
  %Equal.sym(Nat, Nat.mul(x, 1n), x, N.mul_one(x)) : {Nat.add(_, Nat.mul(x, Nat.add(A, Nat.add(B, E)))) == RHS : Nat}
  %Equal.sym(Nat, Nat.mul(x, Nat.add(A, Nat.add(B, E))), Nat.add(Nat.mul(x, A), Nat.mul(x, Nat.add(B, E))), N.mul_add(x, A, Nat.add(B, E))) : {Nat.add(x, _) == RHS : Nat}
  %Equal.sym(Nat, Nat.mul(x, Nat.add(B, E)), Nat.add(Nat.mul(x, B), Nat.mul(x, E)), N.mul_add(x, B, E)) : {Nat.add(x, Nat.add(Nat.mul(x, A), _)) == RHS : Nat}
  {==}

# rep(c) == pack4(c, c, c, c), as numbers with 2^32, 2^8, 2^16, 2^24 abstract.
law rg:
  for +c: U32
  for +M: Nat
  for +A: Nat
  for +B: Nat
  for +E: Nat
  for +h1: {U32.to_nat(U32.mul(c, W.pack4(1, 1, 1, 1))) == Nat.mod(Nat.mul(U32.to_nat(c), U32.to_nat(W.pack4(1, 1, 1, 1))), M) : Nat}
  for +h2: {U32.to_nat(W.pack4(1, 1, 1, 1)) == Nat.add(U32.to_nat(1), Nat.add(Nat.mul(U32.to_nat(1), A), Nat.add(Nat.mul(U32.to_nat(1), B), Nat.mul(U32.to_nat(1), E)))) : Nat}
  for +h3: {U32.to_nat(W.pack4(c, c, c, c)) == Nat.add(U32.to_nat(c), Nat.add(Nat.mul(U32.to_nat(c), A), Nat.add(Nat.mul(U32.to_nat(c), B), Nat.mul(U32.to_nat(c), E)))) : Nat}
  for +h4: {Nat.is_lt(U32.to_nat(W.pack4(c, c, c, c)), M) == True{} : Bool}
  {U32.to_nat(U32.mul(c, W.pack4(1, 1, 1, 1))) == U32.to_nat(W.pack4(c, c, c, c)) : Nat}

def rg(c, M, A, B, E, h1, h2, h3, h4):
  +x = U32.to_nat(c)
  +P = U32.to_nat(W.pack4(c, c, c, c))
  +KX = Nat.add(U32.to_nat(1), Nat.add(Nat.mul(U32.to_nat(1), A), Nat.add(Nat.mul(U32.to_nat(1), B), Nat.mul(U32.to_nat(1), E))))
  +PX = Nat.add(x, Nat.add(Nat.mul(x, A), Nat.add(Nat.mul(x, B), Nat.mul(x, E))))
  %Equal.sym(Nat, U32.to_nat(U32.mul(c, W.pack4(1, 1, 1, 1))), Nat.mod(Nat.mul(x, U32.to_nat(W.pack4(1, 1, 1, 1))), M), h1) : {_ == P : Nat}
  %Equal.sym(Nat, U32.to_nat(W.pack4(1, 1, 1, 1)), KX, h2) : {Nat.mod(Nat.mul(x, _), M) == P : Nat}
  %Equal.sym(Nat, Nat.mul(x, KX), PX, nk(x, A, B, E)) : {Nat.mod(_, M) == P : Nat}
  %h3 : {Nat.mod(_, M) == P : Nat}
  N.mod_small(P, M, h4)

law rep_pack:
  for +c: U32
  for +hc: {U32.is_lt(c, 256) == True{} : Bool}
  {FA.rep(c) == W.pack4(c, c, c, c) : U32}

def rep_pack(c, hc):
  U.to_nat_inj(FA.rep(c), W.pack4(c, c, c, c),
    rg(c, Nat.pow(2n, 32n), Nat.pow(2n, 8n), Nat.pow(2n, 16n), Nat.pow(2n, 24n), U.to_nat_mul_p(c, W.pack4(1, 1, 1, 1)),
      Y.to_nat_pack4(1, 1, 1, 1, {==}, {==}, {==}, {==}), Y.to_nat_pack4(c, c, c, c, hc, hc, hc, hc), U.to_nat_lt_p(W.pack4(c, c, c, c))))

law rep_byte:
  for +c: U32
  for +j: Nat
  for +hc: {U32.is_lt(c, 256) == True{} : Bool}
  for +hj: {Nat.is_lt(j, 4n) == True{} : Bool}
  {W.byte(FA.rep(c), j) == c : U32}

def rep_byte(c, j, hc, hj):
  %Equal.sym(U32, FA.rep(c), W.pack4(c, c, c, c), rep_pack(c, hc)) : {W.byte(_, j) == c : U32}
  Equal.trans(U32, W.byte(W.pack4(c, c, c, c), j), W.nth4(j, c, c, c, c), c, Y.byte_pack4(c, c, c, c, j, hc, hc, hc, hc, hj), nth4_same(j, c))

# The byte tests of the searched words
# ====================================

law ej_xor:
  for +w: U32
  for +c: U32
  for +j: Nat
  for +hc: {U32.is_lt(c, 256) == True{} : Bool}
  for +hj: {Nat.is_lt(j, 4n) == True{} : Bool}
  {U32.is_eq(W.byte(U32.xor(w, FA.rep(c)), j), 0) == U32.is_eq(W.byte(w, j), c) : Bool}

def ej_xor(w, c, j, hc, hj):
  +RHS = U32.is_eq(W.byte(w, j), c)
  %Equal.sym(U32, W.byte(U32.xor(w, FA.rep(c)), j), U32.xor(W.byte(w, j), W.byte(FA.rep(c), j)), Y.byte_xor(w, FA.rep(c), j)) :
    {U32.is_eq(_, 0) == RHS : Bool}
  %Equal.sym(U32, W.byte(FA.rep(c), j), c, rep_byte(c, j, hc, hj)) : {U32.is_eq(U32.xor(W.byte(w, j), _), 0) == RHS : Bool}
  U.is_zero_xor(W.byte(w, j), c)

# A byte of the first word at or above the start: the test of c.
law e_hi:
  for +w: U32
  for +c: U32
  for +m: U32
  for +j: Nat
  for +hc: {U32.is_lt(c, 256) == True{} : Bool}
  for +hj: {Nat.is_lt(j, 4n) == True{} : Bool}
  for +hm: {W.byte(m, j) == 0 : U32}
  {U32.is_eq(W.byte(U32.or(U32.xor(w, FA.rep(c)), m), j), 0) == U32.is_eq(W.byte(w, j), c) : Bool}

def e_hi(w, c, m, j, hc, hj, hm):
  +X = U32.xor(w, FA.rep(c))
  +RHS = U32.is_eq(W.byte(w, j), c)
  %Equal.sym(U32, W.byte(U32.or(X, m), j), U32.or(W.byte(X, j), W.byte(m, j)), Y.byte_or(X, m, j)) : {U32.is_eq(_, 0) == RHS : Bool}
  %Equal.sym(U32, W.byte(m, j), 0, hm) : {U32.is_eq(U32.or(W.byte(X, j), _), 0) == RHS : Bool}
  %Equal.sym(U32, U32.or(W.byte(X, j), 0), W.byte(X, j), or0r(W.byte(X, j))) : {U32.is_eq(_, 0) == RHS : Bool}
  ej_xor(w, c, j, hc, hj)

# A byte below the start: set to 0xFF, never zero.
law e_lo:
  for +w: U32
  for +c: U32
  for +m: U32
  for +j: Nat
  for +hm: {W.byte(m, j) == 255 : U32}
  {U32.is_eq(W.byte(U32.or(U32.xor(w, FA.rep(c)), m), j), 0) == False{} : Bool}

def e_lo(w, c, m, j, hm):
  +X = U32.xor(w, FA.rep(c))
  %Equal.sym(U32, W.byte(U32.or(X, m), j), U32.or(W.byte(X, j), W.byte(m, j)), Y.byte_or(X, m, j)) : {U32.is_eq(_, 0) == False{} : Bool}
  %Equal.sym(U32, W.byte(m, j), 255, hm) : {U32.is_eq(U32.or(W.byte(X, j), _), 0) == False{} : Bool}
  or255(W.byte(X, j))

# Tables
# ======

# run_len over the four byte tests of a word.
def R4(e0: Bool, e1: Bool, e2: Bool, e3: Bool) -> Nat:
  Bool.pick(Nat, e0, 0n, Nat.add(1n, Bool.pick(Nat, e1, 0n, Nat.add(1n, Bool.pick(Nat, e2, 0n, Nat.add(1n, Bool.pick(Nat, e3, 0n, Nat.add(1n, 0n))))))))

law bt_none:
  for +e0: Bool
  for +e1: Bool
  for +e2: Bool
  for +e3: Bool
  {Bool.and(Bool.not(e0), Bool.and(Bool.not(e1), Bool.and(Bool.not(e2), Bool.not(e3)))) == Nat.is_eq(R4(e0, e1, e2, e3), 4n) : Bool}

def bt_none(e0, e1, e2, e3):
  match e0 e1 e2 e3:
    case False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

law bt_bidx:
  for +e0: Bool
  for +e1: Bool
  for +e2: Bool
  for +e3: Bool
  for +h: {Nat.is_lt(R4(e0, e1, e2, e3), 4n) == True{} : Bool}
  {U32.to_nat(U32.add(U32.add(FA.b2u(Bool.and(Bool.not(e0), True{})), FA.b2u(Bool.and(Bool.not(e0), Bool.and(Bool.not(e1), True{})))), FA.b2u(Bool.and(Bool.not(e0), Bool.and(Bool.not(e1), Bool.and(Bool.not(e2), True{})))))) == R4(e0, e1, e2, e3) : Nat}

def bt_bidx(e0, e1, e2, e3, h):
  match e0 e1 e2 e3:
    case False{} False{} False{} False{}:
      Empty.absurd({U32.to_nat(U32.add(U32.add(FA.b2u(Bool.and(Bool.not(False{}), True{})), FA.b2u(Bool.and(Bool.not(False{}), Bool.and(Bool.not(False{}), True{})))), FA.b2u(Bool.and(Bool.not(False{}), Bool.and(Bool.not(False{}), Bool.and(Bool.not(False{}), True{})))))) == R4(False{}, False{}, False{}, False{}) : Nat}, AB.false_ne_true(h))
    case False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

law bt2_none:
  for +e0: Bool
  for +e1: Bool
  for +e2: Bool
  for +e3: Bool
  for +f0: Bool
  for +f1: Bool
  for +f2: Bool
  for +f3: Bool
  {Bool.and(Bool.and(Bool.not(e0), Bool.and(Bool.not(e1), Bool.and(Bool.not(e2), Bool.not(e3)))), Bool.and(Bool.not(f0), Bool.and(Bool.not(f1), Bool.and(Bool.not(f2), Bool.not(f3))))) == Nat.is_eq(Nat.min(R4(e0, e1, e2, e3), R4(f0, f1, f2, f3)), 4n) : Bool}

def bt2_none(e0, e1, e2, e3, f0, f1, f2, f3):
  match e0 e1 e2 e3 f0 f1 f2 f3:
    case False{} False{} False{} False{} False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} False{} False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} False{} False{} False{} True{} False{}:
      {==}
    case False{} False{} False{} False{} False{} False{} True{} True{}:
      {==}
    case False{} False{} False{} False{} False{} True{} False{} False{}:
      {==}
    case False{} False{} False{} False{} False{} True{} False{} True{}:
      {==}
    case False{} False{} False{} False{} False{} True{} True{} False{}:
      {==}
    case False{} False{} False{} False{} False{} True{} True{} True{}:
      {==}
    case False{} False{} False{} False{} True{} False{} False{} False{}:
      {==}
    case False{} False{} False{} False{} True{} False{} False{} True{}:
      {==}
    case False{} False{} False{} False{} True{} False{} True{} False{}:
      {==}
    case False{} False{} False{} False{} True{} False{} True{} True{}:
      {==}
    case False{} False{} False{} False{} True{} True{} False{} False{}:
      {==}
    case False{} False{} False{} False{} True{} True{} False{} True{}:
      {==}
    case False{} False{} False{} False{} True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} False{} True{} True{} True{} True{}:
      {==}
    case False{} False{} False{} True{} False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{} False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} True{} False{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{} False{} False{} True{} True{}:
      {==}
    case False{} False{} False{} True{} False{} True{} False{} False{}:
      {==}
    case False{} False{} False{} True{} False{} True{} False{} True{}:
      {==}
    case False{} False{} False{} True{} False{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{} False{} True{} True{} True{}:
      {==}
    case False{} False{} False{} True{} True{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{} True{} False{} False{} True{}:
      {==}
    case False{} False{} False{} True{} True{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{} True{} False{} True{} True{}:
      {==}
    case False{} False{} False{} True{} True{} True{} False{} False{}:
      {==}
    case False{} False{} False{} True{} True{} True{} False{} True{}:
      {==}
    case False{} False{} False{} True{} True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{} True{} True{} True{} True{}:
      {==}
    case False{} False{} True{} False{} False{} False{} False{} False{}:
      {==}
    case False{} False{} True{} False{} False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{} False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} False{} False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{} False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{} False{} True{} False{} True{}:
      {==}
    case False{} False{} True{} False{} False{} True{} True{} False{}:
      {==}
    case False{} False{} True{} False{} False{} True{} True{} True{}:
      {==}
    case False{} False{} True{} False{} True{} False{} False{} False{}:
      {==}
    case False{} False{} True{} False{} True{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{} True{} False{} True{} False{}:
      {==}
    case False{} False{} True{} False{} True{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{} True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{} True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} False{} True{} True{} True{} False{}:
      {==}
    case False{} False{} True{} False{} True{} True{} True{} True{}:
      {==}
    case False{} False{} True{} True{} False{} False{} False{} False{}:
      {==}
    case False{} False{} True{} True{} False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} True{} False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} True{} False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} True{} False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} True{} False{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{} False{} True{} True{} False{}:
      {==}
    case False{} False{} True{} True{} False{} True{} True{} True{}:
      {==}
    case False{} False{} True{} True{} True{} False{} False{} False{}:
      {==}
    case False{} False{} True{} True{} True{} False{} False{} True{}:
      {==}
    case False{} False{} True{} True{} True{} False{} True{} False{}:
      {==}
    case False{} False{} True{} True{} True{} False{} True{} True{}:
      {==}
    case False{} False{} True{} True{} True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} True{} True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{} True{} True{} True{} False{}:
      {==}
    case False{} False{} True{} True{} True{} True{} True{} True{}:
      {==}
    case False{} True{} False{} False{} False{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{} False{} False{} False{} True{}:
      {==}
    case False{} True{} False{} False{} False{} False{} True{} False{}:
      {==}
    case False{} True{} False{} False{} False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{} False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} False{} False{} True{} False{} True{}:
      {==}
    case False{} True{} False{} False{} False{} True{} True{} False{}:
      {==}
    case False{} True{} False{} False{} False{} True{} True{} True{}:
      {==}
    case False{} True{} False{} False{} True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{} True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} False{} True{} False{} True{} False{}:
      {==}
    case False{} True{} False{} False{} True{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{} True{} True{} False{} False{}:
      {==}
    case False{} True{} False{} False{} True{} True{} False{} True{}:
      {==}
    case False{} True{} False{} False{} True{} True{} True{} False{}:
      {==}
    case False{} True{} False{} False{} True{} True{} True{} True{}:
      {==}
    case False{} True{} False{} True{} False{} False{} False{} False{}:
      {==}
    case False{} True{} False{} True{} False{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{} False{} False{} True{} False{}:
      {==}
    case False{} True{} False{} True{} False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} True{} False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{} False{} True{} False{} True{}:
      {==}
    case False{} True{} False{} True{} False{} True{} True{} False{}:
      {==}
    case False{} True{} False{} True{} False{} True{} True{} True{}:
      {==}
    case False{} True{} False{} True{} True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} True{} True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{} True{} False{} True{} False{}:
      {==}
    case False{} True{} False{} True{} True{} False{} True{} True{}:
      {==}
    case False{} True{} False{} True{} True{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{} True{} True{} False{} True{}:
      {==}
    case False{} True{} False{} True{} True{} True{} True{} False{}:
      {==}
    case False{} True{} False{} True{} True{} True{} True{} True{}:
      {==}
    case False{} True{} True{} False{} False{} False{} False{} False{}:
      {==}
    case False{} True{} True{} False{} False{} False{} False{} True{}:
      {==}
    case False{} True{} True{} False{} False{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{} False{} False{} True{} True{}:
      {==}
    case False{} True{} True{} False{} False{} True{} False{} False{}:
      {==}
    case False{} True{} True{} False{} False{} True{} False{} True{}:
      {==}
    case False{} True{} True{} False{} False{} True{} True{} False{}:
      {==}
    case False{} True{} True{} False{} False{} True{} True{} True{}:
      {==}
    case False{} True{} True{} False{} True{} False{} False{} False{}:
      {==}
    case False{} True{} True{} False{} True{} False{} False{} True{}:
      {==}
    case False{} True{} True{} False{} True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{} True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} False{} True{} True{} False{} False{}:
      {==}
    case False{} True{} True{} False{} True{} True{} False{} True{}:
      {==}
    case False{} True{} True{} False{} True{} True{} True{} False{}:
      {==}
    case False{} True{} True{} False{} True{} True{} True{} True{}:
      {==}
    case False{} True{} True{} True{} False{} False{} False{} False{}:
      {==}
    case False{} True{} True{} True{} False{} False{} False{} True{}:
      {==}
    case False{} True{} True{} True{} False{} False{} True{} False{}:
      {==}
    case False{} True{} True{} True{} False{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{} False{} True{} False{} False{}:
      {==}
    case False{} True{} True{} True{} False{} True{} False{} True{}:
      {==}
    case False{} True{} True{} True{} False{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{} False{} True{} True{} True{}:
      {==}
    case False{} True{} True{} True{} True{} False{} False{} False{}:
      {==}
    case False{} True{} True{} True{} True{} False{} False{} True{}:
      {==}
    case False{} True{} True{} True{} True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} True{} True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{} True{} True{} False{} False{}:
      {==}
    case False{} True{} True{} True{} True{} True{} False{} True{}:
      {==}
    case False{} True{} True{} True{} True{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{} True{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{} False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{} False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} False{} False{} False{} True{} False{}:
      {==}
    case True{} False{} False{} False{} False{} False{} True{} True{}:
      {==}
    case True{} False{} False{} False{} False{} True{} False{} False{}:
      {==}
    case True{} False{} False{} False{} False{} True{} False{} True{}:
      {==}
    case True{} False{} False{} False{} False{} True{} True{} False{}:
      {==}
    case True{} False{} False{} False{} False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{} True{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{} True{} False{} False{} True{}:
      {==}
    case True{} False{} False{} False{} True{} False{} True{} False{}:
      {==}
    case True{} False{} False{} False{} True{} False{} True{} True{}:
      {==}
    case True{} False{} False{} False{} True{} True{} False{} False{}:
      {==}
    case True{} False{} False{} False{} True{} True{} False{} True{}:
      {==}
    case True{} False{} False{} False{} True{} True{} True{} False{}:
      {==}
    case True{} False{} False{} False{} True{} True{} True{} True{}:
      {==}
    case True{} False{} False{} True{} False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} True{} False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{} False{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{} False{} False{} True{} True{}:
      {==}
    case True{} False{} False{} True{} False{} True{} False{} False{}:
      {==}
    case True{} False{} False{} True{} False{} True{} False{} True{}:
      {==}
    case True{} False{} False{} True{} False{} True{} True{} False{}:
      {==}
    case True{} False{} False{} True{} False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} True{} True{} False{} False{} False{}:
      {==}
    case True{} False{} False{} True{} True{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{} True{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{} True{} False{} True{} True{}:
      {==}
    case True{} False{} False{} True{} True{} True{} False{} False{}:
      {==}
    case True{} False{} False{} True{} True{} True{} False{} True{}:
      {==}
    case True{} False{} False{} True{} True{} True{} True{} False{}:
      {==}
    case True{} False{} False{} True{} True{} True{} True{} True{}:
      {==}
    case True{} False{} True{} False{} False{} False{} False{} False{}:
      {==}
    case True{} False{} True{} False{} False{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{} False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{} False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{} False{} True{} False{} False{}:
      {==}
    case True{} False{} True{} False{} False{} True{} False{} True{}:
      {==}
    case True{} False{} True{} False{} False{} True{} True{} False{}:
      {==}
    case True{} False{} True{} False{} False{} True{} True{} True{}:
      {==}
    case True{} False{} True{} False{} True{} False{} False{} False{}:
      {==}
    case True{} False{} True{} False{} True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{} True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{} True{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{} True{} True{} False{} False{}:
      {==}
    case True{} False{} True{} False{} True{} True{} False{} True{}:
      {==}
    case True{} False{} True{} False{} True{} True{} True{} False{}:
      {==}
    case True{} False{} True{} False{} True{} True{} True{} True{}:
      {==}
    case True{} False{} True{} True{} False{} False{} False{} False{}:
      {==}
    case True{} False{} True{} True{} False{} False{} False{} True{}:
      {==}
    case True{} False{} True{} True{} False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} True{} False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{} False{} True{} False{} False{}:
      {==}
    case True{} False{} True{} True{} False{} True{} False{} True{}:
      {==}
    case True{} False{} True{} True{} False{} True{} True{} False{}:
      {==}
    case True{} False{} True{} True{} False{} True{} True{} True{}:
      {==}
    case True{} False{} True{} True{} True{} False{} False{} False{}:
      {==}
    case True{} False{} True{} True{} True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} True{} True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} True{} True{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{} True{} True{} False{} False{}:
      {==}
    case True{} False{} True{} True{} True{} True{} False{} True{}:
      {==}
    case True{} False{} True{} True{} True{} True{} True{} False{}:
      {==}
    case True{} False{} True{} True{} True{} True{} True{} True{}:
      {==}
    case True{} True{} False{} False{} False{} False{} False{} False{}:
      {==}
    case True{} True{} False{} False{} False{} False{} False{} True{}:
      {==}
    case True{} True{} False{} False{} False{} False{} True{} False{}:
      {==}
    case True{} True{} False{} False{} False{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{} False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{} False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} False{} False{} True{} True{} False{}:
      {==}
    case True{} True{} False{} False{} False{} True{} True{} True{}:
      {==}
    case True{} True{} False{} False{} True{} False{} False{} False{}:
      {==}
    case True{} True{} False{} False{} True{} False{} False{} True{}:
      {==}
    case True{} True{} False{} False{} True{} False{} True{} False{}:
      {==}
    case True{} True{} False{} False{} True{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{} True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{} True{} True{} False{} True{}:
      {==}
    case True{} True{} False{} False{} True{} True{} True{} False{}:
      {==}
    case True{} True{} False{} False{} True{} True{} True{} True{}:
      {==}
    case True{} True{} False{} True{} False{} False{} False{} False{}:
      {==}
    case True{} True{} False{} True{} False{} False{} False{} True{}:
      {==}
    case True{} True{} False{} True{} False{} False{} True{} False{}:
      {==}
    case True{} True{} False{} True{} False{} False{} True{} True{}:
      {==}
    case True{} True{} False{} True{} False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{} False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{} False{} True{} True{} False{}:
      {==}
    case True{} True{} False{} True{} False{} True{} True{} True{}:
      {==}
    case True{} True{} False{} True{} True{} False{} False{} False{}:
      {==}
    case True{} True{} False{} True{} True{} False{} False{} True{}:
      {==}
    case True{} True{} False{} True{} True{} False{} True{} False{}:
      {==}
    case True{} True{} False{} True{} True{} False{} True{} True{}:
      {==}
    case True{} True{} False{} True{} True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{} True{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{} True{} True{} True{} False{}:
      {==}
    case True{} True{} False{} True{} True{} True{} True{} True{}:
      {==}
    case True{} True{} True{} False{} False{} False{} False{} False{}:
      {==}
    case True{} True{} True{} False{} False{} False{} False{} True{}:
      {==}
    case True{} True{} True{} False{} False{} False{} True{} False{}:
      {==}
    case True{} True{} True{} False{} False{} False{} True{} True{}:
      {==}
    case True{} True{} True{} False{} False{} True{} False{} False{}:
      {==}
    case True{} True{} True{} False{} False{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{} False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{} False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} False{} True{} False{} False{} False{}:
      {==}
    case True{} True{} True{} False{} True{} False{} False{} True{}:
      {==}
    case True{} True{} True{} False{} True{} False{} True{} False{}:
      {==}
    case True{} True{} True{} False{} True{} False{} True{} True{}:
      {==}
    case True{} True{} True{} False{} True{} True{} False{} False{}:
      {==}
    case True{} True{} True{} False{} True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{} True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{} True{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{} False{} False{} False{} False{}:
      {==}
    case True{} True{} True{} True{} False{} False{} False{} True{}:
      {==}
    case True{} True{} True{} True{} False{} False{} True{} False{}:
      {==}
    case True{} True{} True{} True{} False{} False{} True{} True{}:
      {==}
    case True{} True{} True{} True{} False{} True{} False{} False{}:
      {==}
    case True{} True{} True{} True{} False{} True{} False{} True{}:
      {==}
    case True{} True{} True{} True{} False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{} False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{} True{} False{} False{} False{}:
      {==}
    case True{} True{} True{} True{} True{} False{} False{} True{}:
      {==}
    case True{} True{} True{} True{} True{} False{} True{} False{}:
      {==}
    case True{} True{} True{} True{} True{} False{} True{} True{}:
      {==}
    case True{} True{} True{} True{} True{} True{} False{} False{}:
      {==}
    case True{} True{} True{} True{} True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} True{} True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{} True{} True{} True{} True{}:
      {==}

law bt2_bidx:
  for +e0: Bool
  for +e1: Bool
  for +e2: Bool
  for +e3: Bool
  for +f0: Bool
  for +f1: Bool
  for +f2: Bool
  for +f3: Bool
  for +h: {Nat.is_lt(Nat.min(R4(e0, e1, e2, e3), R4(f0, f1, f2, f3)), 4n) == True{} : Bool}
  {U32.to_nat(U32.add(U32.add(FA.b2u(Bool.and(Bool.and(Bool.not(e0), True{}), Bool.and(Bool.not(f0), True{}))), FA.b2u(Bool.and(Bool.and(Bool.not(e0), Bool.and(Bool.not(e1), True{})), Bool.and(Bool.not(f0), Bool.and(Bool.not(f1), True{}))))), FA.b2u(Bool.and(Bool.and(Bool.not(e0), Bool.and(Bool.not(e1), Bool.and(Bool.not(e2), True{}))), Bool.and(Bool.not(f0), Bool.and(Bool.not(f1), Bool.and(Bool.not(f2), True{}))))))) == Nat.min(R4(e0, e1, e2, e3), R4(f0, f1, f2, f3)) : Nat}

def bt2_bidx(e0, e1, e2, e3, f0, f1, f2, f3, h):
  match e0 e1 e2 e3 f0 f1 f2 f3:
    case False{} False{} False{} False{} False{} False{} False{} False{}:
      Empty.absurd({U32.to_nat(U32.add(U32.add(FA.b2u(Bool.and(Bool.and(Bool.not(False{}), True{}), Bool.and(Bool.not(False{}), True{}))), FA.b2u(Bool.and(Bool.and(Bool.not(False{}), Bool.and(Bool.not(False{}), True{})), Bool.and(Bool.not(False{}), Bool.and(Bool.not(False{}), True{}))))), FA.b2u(Bool.and(Bool.and(Bool.not(False{}), Bool.and(Bool.not(False{}), Bool.and(Bool.not(False{}), True{}))), Bool.and(Bool.not(False{}), Bool.and(Bool.not(False{}), Bool.and(Bool.not(False{}), True{}))))))) == Nat.min(R4(False{}, False{}, False{}, False{}), R4(False{}, False{}, False{}, False{})) : Nat}, AB.false_ne_true(h))
    case False{} False{} False{} False{} False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} False{} False{} False{} True{} False{}:
      {==}
    case False{} False{} False{} False{} False{} False{} True{} True{}:
      {==}
    case False{} False{} False{} False{} False{} True{} False{} False{}:
      {==}
    case False{} False{} False{} False{} False{} True{} False{} True{}:
      {==}
    case False{} False{} False{} False{} False{} True{} True{} False{}:
      {==}
    case False{} False{} False{} False{} False{} True{} True{} True{}:
      {==}
    case False{} False{} False{} False{} True{} False{} False{} False{}:
      {==}
    case False{} False{} False{} False{} True{} False{} False{} True{}:
      {==}
    case False{} False{} False{} False{} True{} False{} True{} False{}:
      {==}
    case False{} False{} False{} False{} True{} False{} True{} True{}:
      {==}
    case False{} False{} False{} False{} True{} True{} False{} False{}:
      {==}
    case False{} False{} False{} False{} True{} True{} False{} True{}:
      {==}
    case False{} False{} False{} False{} True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} False{} True{} True{} True{} True{}:
      {==}
    case False{} False{} False{} True{} False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{} False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} True{} False{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{} False{} False{} True{} True{}:
      {==}
    case False{} False{} False{} True{} False{} True{} False{} False{}:
      {==}
    case False{} False{} False{} True{} False{} True{} False{} True{}:
      {==}
    case False{} False{} False{} True{} False{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{} False{} True{} True{} True{}:
      {==}
    case False{} False{} False{} True{} True{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{} True{} False{} False{} True{}:
      {==}
    case False{} False{} False{} True{} True{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{} True{} False{} True{} True{}:
      {==}
    case False{} False{} False{} True{} True{} True{} False{} False{}:
      {==}
    case False{} False{} False{} True{} True{} True{} False{} True{}:
      {==}
    case False{} False{} False{} True{} True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{} True{} True{} True{} True{}:
      {==}
    case False{} False{} True{} False{} False{} False{} False{} False{}:
      {==}
    case False{} False{} True{} False{} False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{} False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} False{} False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{} False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{} False{} True{} False{} True{}:
      {==}
    case False{} False{} True{} False{} False{} True{} True{} False{}:
      {==}
    case False{} False{} True{} False{} False{} True{} True{} True{}:
      {==}
    case False{} False{} True{} False{} True{} False{} False{} False{}:
      {==}
    case False{} False{} True{} False{} True{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{} True{} False{} True{} False{}:
      {==}
    case False{} False{} True{} False{} True{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{} True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{} True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} False{} True{} True{} True{} False{}:
      {==}
    case False{} False{} True{} False{} True{} True{} True{} True{}:
      {==}
    case False{} False{} True{} True{} False{} False{} False{} False{}:
      {==}
    case False{} False{} True{} True{} False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} True{} False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} True{} False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} True{} False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} True{} False{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{} False{} True{} True{} False{}:
      {==}
    case False{} False{} True{} True{} False{} True{} True{} True{}:
      {==}
    case False{} False{} True{} True{} True{} False{} False{} False{}:
      {==}
    case False{} False{} True{} True{} True{} False{} False{} True{}:
      {==}
    case False{} False{} True{} True{} True{} False{} True{} False{}:
      {==}
    case False{} False{} True{} True{} True{} False{} True{} True{}:
      {==}
    case False{} False{} True{} True{} True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} True{} True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{} True{} True{} True{} False{}:
      {==}
    case False{} False{} True{} True{} True{} True{} True{} True{}:
      {==}
    case False{} True{} False{} False{} False{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{} False{} False{} False{} True{}:
      {==}
    case False{} True{} False{} False{} False{} False{} True{} False{}:
      {==}
    case False{} True{} False{} False{} False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{} False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} False{} False{} True{} False{} True{}:
      {==}
    case False{} True{} False{} False{} False{} True{} True{} False{}:
      {==}
    case False{} True{} False{} False{} False{} True{} True{} True{}:
      {==}
    case False{} True{} False{} False{} True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{} True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} False{} True{} False{} True{} False{}:
      {==}
    case False{} True{} False{} False{} True{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{} True{} True{} False{} False{}:
      {==}
    case False{} True{} False{} False{} True{} True{} False{} True{}:
      {==}
    case False{} True{} False{} False{} True{} True{} True{} False{}:
      {==}
    case False{} True{} False{} False{} True{} True{} True{} True{}:
      {==}
    case False{} True{} False{} True{} False{} False{} False{} False{}:
      {==}
    case False{} True{} False{} True{} False{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{} False{} False{} True{} False{}:
      {==}
    case False{} True{} False{} True{} False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} True{} False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{} False{} True{} False{} True{}:
      {==}
    case False{} True{} False{} True{} False{} True{} True{} False{}:
      {==}
    case False{} True{} False{} True{} False{} True{} True{} True{}:
      {==}
    case False{} True{} False{} True{} True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} True{} True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{} True{} False{} True{} False{}:
      {==}
    case False{} True{} False{} True{} True{} False{} True{} True{}:
      {==}
    case False{} True{} False{} True{} True{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{} True{} True{} False{} True{}:
      {==}
    case False{} True{} False{} True{} True{} True{} True{} False{}:
      {==}
    case False{} True{} False{} True{} True{} True{} True{} True{}:
      {==}
    case False{} True{} True{} False{} False{} False{} False{} False{}:
      {==}
    case False{} True{} True{} False{} False{} False{} False{} True{}:
      {==}
    case False{} True{} True{} False{} False{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{} False{} False{} True{} True{}:
      {==}
    case False{} True{} True{} False{} False{} True{} False{} False{}:
      {==}
    case False{} True{} True{} False{} False{} True{} False{} True{}:
      {==}
    case False{} True{} True{} False{} False{} True{} True{} False{}:
      {==}
    case False{} True{} True{} False{} False{} True{} True{} True{}:
      {==}
    case False{} True{} True{} False{} True{} False{} False{} False{}:
      {==}
    case False{} True{} True{} False{} True{} False{} False{} True{}:
      {==}
    case False{} True{} True{} False{} True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{} True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} False{} True{} True{} False{} False{}:
      {==}
    case False{} True{} True{} False{} True{} True{} False{} True{}:
      {==}
    case False{} True{} True{} False{} True{} True{} True{} False{}:
      {==}
    case False{} True{} True{} False{} True{} True{} True{} True{}:
      {==}
    case False{} True{} True{} True{} False{} False{} False{} False{}:
      {==}
    case False{} True{} True{} True{} False{} False{} False{} True{}:
      {==}
    case False{} True{} True{} True{} False{} False{} True{} False{}:
      {==}
    case False{} True{} True{} True{} False{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{} False{} True{} False{} False{}:
      {==}
    case False{} True{} True{} True{} False{} True{} False{} True{}:
      {==}
    case False{} True{} True{} True{} False{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{} False{} True{} True{} True{}:
      {==}
    case False{} True{} True{} True{} True{} False{} False{} False{}:
      {==}
    case False{} True{} True{} True{} True{} False{} False{} True{}:
      {==}
    case False{} True{} True{} True{} True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} True{} True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{} True{} True{} False{} False{}:
      {==}
    case False{} True{} True{} True{} True{} True{} False{} True{}:
      {==}
    case False{} True{} True{} True{} True{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{} True{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{} False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{} False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} False{} False{} False{} True{} False{}:
      {==}
    case True{} False{} False{} False{} False{} False{} True{} True{}:
      {==}
    case True{} False{} False{} False{} False{} True{} False{} False{}:
      {==}
    case True{} False{} False{} False{} False{} True{} False{} True{}:
      {==}
    case True{} False{} False{} False{} False{} True{} True{} False{}:
      {==}
    case True{} False{} False{} False{} False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{} True{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{} True{} False{} False{} True{}:
      {==}
    case True{} False{} False{} False{} True{} False{} True{} False{}:
      {==}
    case True{} False{} False{} False{} True{} False{} True{} True{}:
      {==}
    case True{} False{} False{} False{} True{} True{} False{} False{}:
      {==}
    case True{} False{} False{} False{} True{} True{} False{} True{}:
      {==}
    case True{} False{} False{} False{} True{} True{} True{} False{}:
      {==}
    case True{} False{} False{} False{} True{} True{} True{} True{}:
      {==}
    case True{} False{} False{} True{} False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} True{} False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{} False{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{} False{} False{} True{} True{}:
      {==}
    case True{} False{} False{} True{} False{} True{} False{} False{}:
      {==}
    case True{} False{} False{} True{} False{} True{} False{} True{}:
      {==}
    case True{} False{} False{} True{} False{} True{} True{} False{}:
      {==}
    case True{} False{} False{} True{} False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} True{} True{} False{} False{} False{}:
      {==}
    case True{} False{} False{} True{} True{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{} True{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{} True{} False{} True{} True{}:
      {==}
    case True{} False{} False{} True{} True{} True{} False{} False{}:
      {==}
    case True{} False{} False{} True{} True{} True{} False{} True{}:
      {==}
    case True{} False{} False{} True{} True{} True{} True{} False{}:
      {==}
    case True{} False{} False{} True{} True{} True{} True{} True{}:
      {==}
    case True{} False{} True{} False{} False{} False{} False{} False{}:
      {==}
    case True{} False{} True{} False{} False{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{} False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{} False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{} False{} True{} False{} False{}:
      {==}
    case True{} False{} True{} False{} False{} True{} False{} True{}:
      {==}
    case True{} False{} True{} False{} False{} True{} True{} False{}:
      {==}
    case True{} False{} True{} False{} False{} True{} True{} True{}:
      {==}
    case True{} False{} True{} False{} True{} False{} False{} False{}:
      {==}
    case True{} False{} True{} False{} True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{} True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{} True{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{} True{} True{} False{} False{}:
      {==}
    case True{} False{} True{} False{} True{} True{} False{} True{}:
      {==}
    case True{} False{} True{} False{} True{} True{} True{} False{}:
      {==}
    case True{} False{} True{} False{} True{} True{} True{} True{}:
      {==}
    case True{} False{} True{} True{} False{} False{} False{} False{}:
      {==}
    case True{} False{} True{} True{} False{} False{} False{} True{}:
      {==}
    case True{} False{} True{} True{} False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} True{} False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{} False{} True{} False{} False{}:
      {==}
    case True{} False{} True{} True{} False{} True{} False{} True{}:
      {==}
    case True{} False{} True{} True{} False{} True{} True{} False{}:
      {==}
    case True{} False{} True{} True{} False{} True{} True{} True{}:
      {==}
    case True{} False{} True{} True{} True{} False{} False{} False{}:
      {==}
    case True{} False{} True{} True{} True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} True{} True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} True{} True{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{} True{} True{} False{} False{}:
      {==}
    case True{} False{} True{} True{} True{} True{} False{} True{}:
      {==}
    case True{} False{} True{} True{} True{} True{} True{} False{}:
      {==}
    case True{} False{} True{} True{} True{} True{} True{} True{}:
      {==}
    case True{} True{} False{} False{} False{} False{} False{} False{}:
      {==}
    case True{} True{} False{} False{} False{} False{} False{} True{}:
      {==}
    case True{} True{} False{} False{} False{} False{} True{} False{}:
      {==}
    case True{} True{} False{} False{} False{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{} False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{} False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} False{} False{} True{} True{} False{}:
      {==}
    case True{} True{} False{} False{} False{} True{} True{} True{}:
      {==}
    case True{} True{} False{} False{} True{} False{} False{} False{}:
      {==}
    case True{} True{} False{} False{} True{} False{} False{} True{}:
      {==}
    case True{} True{} False{} False{} True{} False{} True{} False{}:
      {==}
    case True{} True{} False{} False{} True{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{} True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{} True{} True{} False{} True{}:
      {==}
    case True{} True{} False{} False{} True{} True{} True{} False{}:
      {==}
    case True{} True{} False{} False{} True{} True{} True{} True{}:
      {==}
    case True{} True{} False{} True{} False{} False{} False{} False{}:
      {==}
    case True{} True{} False{} True{} False{} False{} False{} True{}:
      {==}
    case True{} True{} False{} True{} False{} False{} True{} False{}:
      {==}
    case True{} True{} False{} True{} False{} False{} True{} True{}:
      {==}
    case True{} True{} False{} True{} False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{} False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{} False{} True{} True{} False{}:
      {==}
    case True{} True{} False{} True{} False{} True{} True{} True{}:
      {==}
    case True{} True{} False{} True{} True{} False{} False{} False{}:
      {==}
    case True{} True{} False{} True{} True{} False{} False{} True{}:
      {==}
    case True{} True{} False{} True{} True{} False{} True{} False{}:
      {==}
    case True{} True{} False{} True{} True{} False{} True{} True{}:
      {==}
    case True{} True{} False{} True{} True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{} True{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{} True{} True{} True{} False{}:
      {==}
    case True{} True{} False{} True{} True{} True{} True{} True{}:
      {==}
    case True{} True{} True{} False{} False{} False{} False{} False{}:
      {==}
    case True{} True{} True{} False{} False{} False{} False{} True{}:
      {==}
    case True{} True{} True{} False{} False{} False{} True{} False{}:
      {==}
    case True{} True{} True{} False{} False{} False{} True{} True{}:
      {==}
    case True{} True{} True{} False{} False{} True{} False{} False{}:
      {==}
    case True{} True{} True{} False{} False{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{} False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{} False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} False{} True{} False{} False{} False{}:
      {==}
    case True{} True{} True{} False{} True{} False{} False{} True{}:
      {==}
    case True{} True{} True{} False{} True{} False{} True{} False{}:
      {==}
    case True{} True{} True{} False{} True{} False{} True{} True{}:
      {==}
    case True{} True{} True{} False{} True{} True{} False{} False{}:
      {==}
    case True{} True{} True{} False{} True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{} True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{} True{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{} False{} False{} False{} False{}:
      {==}
    case True{} True{} True{} True{} False{} False{} False{} True{}:
      {==}
    case True{} True{} True{} True{} False{} False{} True{} False{}:
      {==}
    case True{} True{} True{} True{} False{} False{} True{} True{}:
      {==}
    case True{} True{} True{} True{} False{} True{} False{} False{}:
      {==}
    case True{} True{} True{} True{} False{} True{} False{} True{}:
      {==}
    case True{} True{} True{} True{} False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{} False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{} True{} False{} False{} False{}:
      {==}
    case True{} True{} True{} True{} True{} False{} False{} True{}:
      {==}
    case True{} True{} True{} True{} True{} False{} True{} False{}:
      {==}
    case True{} True{} True{} True{} True{} False{} True{} True{}:
      {==}
    case True{} True{} True{} True{} True{} True{} False{} False{}:
      {==}
    case True{} True{} True{} True{} True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} True{} True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{} True{} True{} True{} True{}:
      {==}

