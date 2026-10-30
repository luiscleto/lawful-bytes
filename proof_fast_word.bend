import Base
import lawful-words@0.1.0.0/defs.bend as W
import ./defs.bend as D
import ./fast.bend as FA
import ./proof_core.bend as C
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U
import lawful-words@0.1.0.0/proof_zb.bend as Z
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import ./proof_fast_w1.bend as W1
import ./proof_fast_w2.bend as W2

# Word facts behind fast.bend's find: the zero-byte flags (FA.zb) and the
# place of the lowest flag (FA.bidx), the broadcast byte (FA.rep) and the mask
# of the bytes below a start (FA.low).

# The place of the first zero byte of v (4 when there is none).
def P0(+v: U32) -> Nat:
  D.run_len(C.L4(v), 0)

# The k = 1 test of the or of two flag words.
law tko1:
  for +v1: U32
  for +v2: U32
  {U32.is_zero(U32.and(U32.or(W.zb(v1), W.zb(v2)), 128)) == Bool.and(Bool.and(U32.is_ne(W.byte(v1, 0n), 0), True{}), Bool.and(U32.is_ne(W.byte(v2, 0n), 0), True{})) : Bool}

def tko1(v1, v2):
  %W1.tk1(v1) :
    {U32.is_zero(U32.and(U32.or(W.zb(v1), W.zb(v2)), 128)) == Bool.and(_, Bool.and(U32.is_ne(W.byte(v2, 0n), 0), True{})) : Bool}
  %W1.tk1(v2) :
    {U32.is_zero(U32.and(U32.or(W.zb(v1), W.zb(v2)), 128)) == Bool.and(U32.is_zero(U32.and(W.zb(v1), 128)), _) : Bool}
  W2.uorm(W.zb(v1), W.zb(v2), 128)

# The k = 2 test of the or of two flag words.
law tko2:
  for +v1: U32
  for +v2: U32
  {U32.is_zero(U32.and(U32.or(W.zb(v1), W.zb(v2)), 32896)) == Bool.and(Bool.and(U32.is_ne(W.byte(v1, 0n), 0), Bool.and(U32.is_ne(W.byte(v1, 1n), 0), True{})), Bool.and(U32.is_ne(W.byte(v2, 0n), 0), Bool.and(U32.is_ne(W.byte(v2, 1n), 0), True{}))) : Bool}

def tko2(v1, v2):
  %W1.tk2(v1) :
    {U32.is_zero(U32.and(U32.or(W.zb(v1), W.zb(v2)), 32896)) == Bool.and(_, Bool.and(U32.is_ne(W.byte(v2, 0n), 0), Bool.and(U32.is_ne(W.byte(v2, 1n), 0), True{}))) : Bool}
  %W1.tk2(v2) :
    {U32.is_zero(U32.and(U32.or(W.zb(v1), W.zb(v2)), 32896)) == Bool.and(U32.is_zero(U32.and(W.zb(v1), 32896)), _) : Bool}
  W2.uorm(W.zb(v1), W.zb(v2), 32896)

# The k = 3 test of the or of two flag words.
law tko3:
  for +v1: U32
  for +v2: U32
  {U32.is_zero(U32.and(U32.or(W.zb(v1), W.zb(v2)), 8421504)) == Bool.and(Bool.and(U32.is_ne(W.byte(v1, 0n), 0), Bool.and(U32.is_ne(W.byte(v1, 1n), 0), Bool.and(U32.is_ne(W.byte(v1, 2n), 0), True{}))), Bool.and(U32.is_ne(W.byte(v2, 0n), 0), Bool.and(U32.is_ne(W.byte(v2, 1n), 0), Bool.and(U32.is_ne(W.byte(v2, 2n), 0), True{})))) : Bool}

def tko3(v1, v2):
  %W1.tk3(v1) :
    {U32.is_zero(U32.and(U32.or(W.zb(v1), W.zb(v2)), 8421504)) == Bool.and(_, Bool.and(U32.is_ne(W.byte(v2, 0n), 0), Bool.and(U32.is_ne(W.byte(v2, 1n), 0), Bool.and(U32.is_ne(W.byte(v2, 2n), 0), True{})))) : Bool}
  %W1.tk3(v2) :
    {U32.is_zero(U32.and(U32.or(W.zb(v1), W.zb(v2)), 8421504)) == Bool.and(U32.is_zero(U32.and(W.zb(v1), 8421504)), _) : Bool}
  W2.uorm(W.zb(v1), W.zb(v2), 8421504)

# The zero-byte flags are all clear exactly when no byte is zero.
law zb_none:
  for +v: U32
  {U32.is_zero(FA.zb(v)) == Nat.is_eq(P0(v), 4n) : Bool}

def zb_none(v):
  %Equal.sym(U32, FA.zb(v), W.zb(v), W1.zb_eq(v)) : {U32.is_zero(_) == Nat.is_eq(P0(v), 4n) : Bool}
  Equal.trans(Bool, U32.is_zero(W.zb(v)), Bool.and(U32.is_ne(W.byte(v, 0n), 0), Bool.and(U32.is_ne(W.byte(v, 1n), 0), Bool.and(U32.is_ne(W.byte(v, 2n), 0), U32.is_ne(W.byte(v, 3n), 0)))),
    Nat.is_eq(P0(v), 4n), Z.zb_zero(v), W2.bt_none(U32.is_eq(W.byte(v, 0n), 0), U32.is_eq(W.byte(v, 1n), 0), U32.is_eq(W.byte(v, 2n), 0), U32.is_eq(W.byte(v, 3n), 0)))

# bidx finds the first zero byte.
law zb_bidx:
  for +v: U32
  for +h: {Nat.is_lt(P0(v), 4n) == True{} : Bool}
  {U32.to_nat(FA.bidx(FA.zb(v))) == P0(v) : Nat}

def zb_bidx(v, h):
  %Equal.sym(U32, FA.zb(v), W.zb(v), W1.zb_eq(v)) : {U32.to_nat(FA.bidx(_)) == P0(v) : Nat}
  %Equal.sym(Bool, U32.is_zero(U32.and(W.zb(v), 128)), Bool.and(U32.is_ne(W.byte(v, 0n), 0), True{}), W1.tk1(v)) : {U32.to_nat(U32.add(U32.add(FA.b2u(_), FA.b2u(U32.is_zero(U32.and(W.zb(v), 32896)))), FA.b2u(U32.is_zero(U32.and(W.zb(v), 8421504))))) == P0(v) : Nat}
  %Equal.sym(Bool, U32.is_zero(U32.and(W.zb(v), 32896)), Bool.and(U32.is_ne(W.byte(v, 0n), 0), Bool.and(U32.is_ne(W.byte(v, 1n), 0), True{})), W1.tk2(v)) : {U32.to_nat(U32.add(U32.add(FA.b2u(Bool.and(U32.is_ne(W.byte(v, 0n), 0), True{})), FA.b2u(_)), FA.b2u(U32.is_zero(U32.and(W.zb(v), 8421504))))) == P0(v) : Nat}
  %Equal.sym(Bool, U32.is_zero(U32.and(W.zb(v), 8421504)), Bool.and(U32.is_ne(W.byte(v, 0n), 0), Bool.and(U32.is_ne(W.byte(v, 1n), 0), Bool.and(U32.is_ne(W.byte(v, 2n), 0), True{}))), W1.tk3(v)) : {U32.to_nat(U32.add(U32.add(FA.b2u(Bool.and(U32.is_ne(W.byte(v, 0n), 0), True{})), FA.b2u(Bool.and(U32.is_ne(W.byte(v, 0n), 0), Bool.and(U32.is_ne(W.byte(v, 1n), 0), True{})))), FA.b2u(_))) == P0(v) : Nat}
  W2.bt_bidx(U32.is_eq(W.byte(v, 0n), 0), U32.is_eq(W.byte(v, 1n), 0), U32.is_eq(W.byte(v, 2n), 0), U32.is_eq(W.byte(v, 3n), 0), h)

# The same for the flags of two words or-ed (find2).
law zb2_none:
  for +v1: U32
  for +v2: U32
  {U32.is_zero(U32.or(FA.zb(v1), FA.zb(v2))) == Nat.is_eq(Nat.min(P0(v1), P0(v2)), 4n) : Bool}

def zb2_none(v1, v2):
  %Equal.sym(U32, FA.zb(v1), W.zb(v1), W1.zb_eq(v1)) : {U32.is_zero(U32.or(_, FA.zb(v2))) == Nat.is_eq(Nat.min(P0(v1), P0(v2)), 4n) : Bool}
  %Equal.sym(U32, FA.zb(v2), W.zb(v2), W1.zb_eq(v2)) : {U32.is_zero(U32.or(W.zb(v1), _)) == Nat.is_eq(Nat.min(P0(v1), P0(v2)), 4n) : Bool}
  %Equal.sym(Bool, U32.is_zero(U32.or(W.zb(v1), W.zb(v2))), Bool.and(U32.is_zero(W.zb(v1)), U32.is_zero(W.zb(v2))), W2.uor0(W.zb(v1), W.zb(v2))) : {_ == Nat.is_eq(Nat.min(P0(v1), P0(v2)), 4n) : Bool}
  %Equal.sym(Bool, U32.is_zero(W.zb(v1)), Bool.and(U32.is_ne(W.byte(v1, 0n), 0), Bool.and(U32.is_ne(W.byte(v1, 1n), 0), Bool.and(U32.is_ne(W.byte(v1, 2n), 0), U32.is_ne(W.byte(v1, 3n), 0)))), Z.zb_zero(v1)) : {Bool.and(_, U32.is_zero(W.zb(v2))) == Nat.is_eq(Nat.min(P0(v1), P0(v2)), 4n) : Bool}
  %Equal.sym(Bool, U32.is_zero(W.zb(v2)), Bool.and(U32.is_ne(W.byte(v2, 0n), 0), Bool.and(U32.is_ne(W.byte(v2, 1n), 0), Bool.and(U32.is_ne(W.byte(v2, 2n), 0), U32.is_ne(W.byte(v2, 3n), 0)))), Z.zb_zero(v2)) : {Bool.and(Bool.and(U32.is_ne(W.byte(v1, 0n), 0), Bool.and(U32.is_ne(W.byte(v1, 1n), 0), Bool.and(U32.is_ne(W.byte(v1, 2n), 0), U32.is_ne(W.byte(v1, 3n), 0)))), _) == Nat.is_eq(Nat.min(P0(v1), P0(v2)), 4n) : Bool}
  W2.bt2_none(U32.is_eq(W.byte(v1, 0n), 0), U32.is_eq(W.byte(v1, 1n), 0), U32.is_eq(W.byte(v1, 2n), 0), U32.is_eq(W.byte(v1, 3n), 0), U32.is_eq(W.byte(v2, 0n), 0), U32.is_eq(W.byte(v2, 1n), 0), U32.is_eq(W.byte(v2, 2n), 0), U32.is_eq(W.byte(v2, 3n), 0))

law zb2_bidx:
  for +v1: U32
  for +v2: U32
  for +h: {Nat.is_lt(Nat.min(P0(v1), P0(v2)), 4n) == True{} : Bool}
  {U32.to_nat(FA.bidx(U32.or(FA.zb(v1), FA.zb(v2)))) == Nat.min(P0(v1), P0(v2)) : Nat}

def zb2_bidx(v1, v2, h):
  %Equal.sym(U32, FA.zb(v1), W.zb(v1), W1.zb_eq(v1)) : {U32.to_nat(FA.bidx(U32.or(_, FA.zb(v2)))) == Nat.min(P0(v1), P0(v2)) : Nat}
  %Equal.sym(U32, FA.zb(v2), W.zb(v2), W1.zb_eq(v2)) : {U32.to_nat(FA.bidx(U32.or(W.zb(v1), _))) == Nat.min(P0(v1), P0(v2)) : Nat}
  %Equal.sym(Bool, U32.is_zero(U32.and(U32.or(W.zb(v1), W.zb(v2)), 128)), Bool.and(Bool.and(U32.is_ne(W.byte(v1, 0n), 0), True{}), Bool.and(U32.is_ne(W.byte(v2, 0n), 0), True{})), tko1(v1, v2)) : {U32.to_nat(U32.add(U32.add(FA.b2u(_), FA.b2u(U32.is_zero(U32.and(U32.or(W.zb(v1), W.zb(v2)), 32896)))), FA.b2u(U32.is_zero(U32.and(U32.or(W.zb(v1), W.zb(v2)), 8421504))))) == Nat.min(P0(v1), P0(v2)) : Nat}
  %Equal.sym(Bool, U32.is_zero(U32.and(U32.or(W.zb(v1), W.zb(v2)), 32896)), Bool.and(Bool.and(U32.is_ne(W.byte(v1, 0n), 0), Bool.and(U32.is_ne(W.byte(v1, 1n), 0), True{})), Bool.and(U32.is_ne(W.byte(v2, 0n), 0), Bool.and(U32.is_ne(W.byte(v2, 1n), 0), True{}))), tko2(v1, v2)) : {U32.to_nat(U32.add(U32.add(FA.b2u(Bool.and(Bool.and(U32.is_ne(W.byte(v1, 0n), 0), True{}), Bool.and(U32.is_ne(W.byte(v2, 0n), 0), True{}))), FA.b2u(_)), FA.b2u(U32.is_zero(U32.and(U32.or(W.zb(v1), W.zb(v2)), 8421504))))) == Nat.min(P0(v1), P0(v2)) : Nat}
  %Equal.sym(Bool, U32.is_zero(U32.and(U32.or(W.zb(v1), W.zb(v2)), 8421504)), Bool.and(Bool.and(U32.is_ne(W.byte(v1, 0n), 0), Bool.and(U32.is_ne(W.byte(v1, 1n), 0), Bool.and(U32.is_ne(W.byte(v1, 2n), 0), True{}))), Bool.and(U32.is_ne(W.byte(v2, 0n), 0), Bool.and(U32.is_ne(W.byte(v2, 1n), 0), Bool.and(U32.is_ne(W.byte(v2, 2n), 0), True{})))), tko3(v1, v2)) : {U32.to_nat(U32.add(U32.add(FA.b2u(Bool.and(Bool.and(U32.is_ne(W.byte(v1, 0n), 0), True{}), Bool.and(U32.is_ne(W.byte(v2, 0n), 0), True{}))), FA.b2u(Bool.and(Bool.and(U32.is_ne(W.byte(v1, 0n), 0), Bool.and(U32.is_ne(W.byte(v1, 1n), 0), True{})), Bool.and(U32.is_ne(W.byte(v2, 0n), 0), Bool.and(U32.is_ne(W.byte(v2, 1n), 0), True{}))))), FA.b2u(_))) == Nat.min(P0(v1), P0(v2)) : Nat}
  W2.bt2_bidx(U32.is_eq(W.byte(v1, 0n), 0), U32.is_eq(W.byte(v1, 1n), 0), U32.is_eq(W.byte(v1, 2n), 0), U32.is_eq(W.byte(v1, 3n), 0), U32.is_eq(W.byte(v2, 0n), 0), U32.is_eq(W.byte(v2, 1n), 0), U32.is_eq(W.byte(v2, 2n), 0), U32.is_eq(W.byte(v2, 3n), 0), h)

# Searching w for c is searching w xor rep(c) for a zero byte.
law p0_xor:
  for +w: U32
  for +c: U32
  for +hc: {U32.is_lt(c, 256) == True{} : Bool}
  {P0(U32.xor(w, FA.rep(c))) == D.run_len(C.L4(w), c) : Nat}

def p0_xor(w, c, hc):
  %Equal.sym(Bool, U32.is_eq(W.byte(U32.xor(w, FA.rep(c)), 0n), 0), U32.is_eq(W.byte(w, 0n), c), W2.ej_xor(w, c, 0n, hc, {==})) :
    {W2.R4(_, U32.is_eq(W.byte(U32.xor(w, FA.rep(c)), 1n), 0), U32.is_eq(W.byte(U32.xor(w, FA.rep(c)), 2n), 0), U32.is_eq(W.byte(U32.xor(w, FA.rep(c)), 3n), 0)) == D.run_len(C.L4(w), c) : Nat}
  %Equal.sym(Bool, U32.is_eq(W.byte(U32.xor(w, FA.rep(c)), 1n), 0), U32.is_eq(W.byte(w, 1n), c), W2.ej_xor(w, c, 1n, hc, {==})) :
    {W2.R4(U32.is_eq(W.byte(w, 0n), c), _, U32.is_eq(W.byte(U32.xor(w, FA.rep(c)), 2n), 0), U32.is_eq(W.byte(U32.xor(w, FA.rep(c)), 3n), 0)) == D.run_len(C.L4(w), c) : Nat}
  %Equal.sym(Bool, U32.is_eq(W.byte(U32.xor(w, FA.rep(c)), 2n), 0), U32.is_eq(W.byte(w, 2n), c), W2.ej_xor(w, c, 2n, hc, {==})) :
    {W2.R4(U32.is_eq(W.byte(w, 0n), c), U32.is_eq(W.byte(w, 1n), c), _, U32.is_eq(W.byte(U32.xor(w, FA.rep(c)), 3n), 0)) == D.run_len(C.L4(w), c) : Nat}
  %Equal.sym(Bool, U32.is_eq(W.byte(U32.xor(w, FA.rep(c)), 3n), 0), U32.is_eq(W.byte(w, 3n), c), W2.ej_xor(w, c, 3n, hc, {==})) :
    {W2.R4(U32.is_eq(W.byte(w, 0n), c), U32.is_eq(W.byte(w, 1n), c), U32.is_eq(W.byte(w, 2n), c), _) == D.run_len(C.L4(w), c) : Nat}
  {==}

law plk0:
  for +w: U32
  for +c: U32
  for +hc: {U32.is_lt(c, 256) == True{} : Bool}
  {P0(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(0, 3n)))))) == Nat.add(U32.to_nat(0), D.run_len(List.drop(&2, U32, C.L4(w), U32.to_nat(0)), c)) : Nat}

def plk0(w, c, hc):
  %Equal.sym(Bool, U32.is_eq(W.byte(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(0, 3n))))), 0n), 0), U32.is_eq(W.byte(w, 0n), c), W2.e_hi(w, c, U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(0, 3n)))), 0n, hc, {==}, {==})) :
    {W2.R4(_, U32.is_eq(W.byte(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(0, 3n))))), 1n), 0), U32.is_eq(W.byte(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(0, 3n))))), 2n), 0), U32.is_eq(W.byte(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(0, 3n))))), 3n), 0)) == Nat.add(U32.to_nat(0), D.run_len(List.drop(&2, U32, C.L4(w), U32.to_nat(0)), c)) : Nat}
  %Equal.sym(Bool, U32.is_eq(W.byte(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(0, 3n))))), 1n), 0), U32.is_eq(W.byte(w, 1n), c), W2.e_hi(w, c, U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(0, 3n)))), 1n, hc, {==}, {==})) :
    {W2.R4(U32.is_eq(W.byte(w, 0n), c), _, U32.is_eq(W.byte(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(0, 3n))))), 2n), 0), U32.is_eq(W.byte(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(0, 3n))))), 3n), 0)) == Nat.add(U32.to_nat(0), D.run_len(List.drop(&2, U32, C.L4(w), U32.to_nat(0)), c)) : Nat}
  %Equal.sym(Bool, U32.is_eq(W.byte(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(0, 3n))))), 2n), 0), U32.is_eq(W.byte(w, 2n), c), W2.e_hi(w, c, U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(0, 3n)))), 2n, hc, {==}, {==})) :
    {W2.R4(U32.is_eq(W.byte(w, 0n), c), U32.is_eq(W.byte(w, 1n), c), _, U32.is_eq(W.byte(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(0, 3n))))), 3n), 0)) == Nat.add(U32.to_nat(0), D.run_len(List.drop(&2, U32, C.L4(w), U32.to_nat(0)), c)) : Nat}
  %Equal.sym(Bool, U32.is_eq(W.byte(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(0, 3n))))), 3n), 0), U32.is_eq(W.byte(w, 3n), c), W2.e_hi(w, c, U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(0, 3n)))), 3n, hc, {==}, {==})) :
    {W2.R4(U32.is_eq(W.byte(w, 0n), c), U32.is_eq(W.byte(w, 1n), c), U32.is_eq(W.byte(w, 2n), c), _) == Nat.add(U32.to_nat(0), D.run_len(List.drop(&2, U32, C.L4(w), U32.to_nat(0)), c)) : Nat}
  {==}

law plk1:
  for +w: U32
  for +c: U32
  for +hc: {U32.is_lt(c, 256) == True{} : Bool}
  {P0(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(1, 3n)))))) == Nat.add(U32.to_nat(1), D.run_len(List.drop(&2, U32, C.L4(w), U32.to_nat(1)), c)) : Nat}

def plk1(w, c, hc):
  %Equal.sym(Bool, U32.is_eq(W.byte(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(1, 3n))))), 0n), 0), False{}, W2.e_lo(w, c, U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(1, 3n)))), 0n, {==})) :
    {W2.R4(_, U32.is_eq(W.byte(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(1, 3n))))), 1n), 0), U32.is_eq(W.byte(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(1, 3n))))), 2n), 0), U32.is_eq(W.byte(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(1, 3n))))), 3n), 0)) == Nat.add(U32.to_nat(1), D.run_len(List.drop(&2, U32, C.L4(w), U32.to_nat(1)), c)) : Nat}
  %Equal.sym(Bool, U32.is_eq(W.byte(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(1, 3n))))), 1n), 0), U32.is_eq(W.byte(w, 1n), c), W2.e_hi(w, c, U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(1, 3n)))), 1n, hc, {==}, {==})) :
    {W2.R4(False{}, _, U32.is_eq(W.byte(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(1, 3n))))), 2n), 0), U32.is_eq(W.byte(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(1, 3n))))), 3n), 0)) == Nat.add(U32.to_nat(1), D.run_len(List.drop(&2, U32, C.L4(w), U32.to_nat(1)), c)) : Nat}
  %Equal.sym(Bool, U32.is_eq(W.byte(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(1, 3n))))), 2n), 0), U32.is_eq(W.byte(w, 2n), c), W2.e_hi(w, c, U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(1, 3n)))), 2n, hc, {==}, {==})) :
    {W2.R4(False{}, U32.is_eq(W.byte(w, 1n), c), _, U32.is_eq(W.byte(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(1, 3n))))), 3n), 0)) == Nat.add(U32.to_nat(1), D.run_len(List.drop(&2, U32, C.L4(w), U32.to_nat(1)), c)) : Nat}
  %Equal.sym(Bool, U32.is_eq(W.byte(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(1, 3n))))), 3n), 0), U32.is_eq(W.byte(w, 3n), c), W2.e_hi(w, c, U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(1, 3n)))), 3n, hc, {==}, {==})) :
    {W2.R4(False{}, U32.is_eq(W.byte(w, 1n), c), U32.is_eq(W.byte(w, 2n), c), _) == Nat.add(U32.to_nat(1), D.run_len(List.drop(&2, U32, C.L4(w), U32.to_nat(1)), c)) : Nat}
  {==}

law plk2:
  for +w: U32
  for +c: U32
  for +hc: {U32.is_lt(c, 256) == True{} : Bool}
  {P0(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(2, 3n)))))) == Nat.add(U32.to_nat(2), D.run_len(List.drop(&2, U32, C.L4(w), U32.to_nat(2)), c)) : Nat}

def plk2(w, c, hc):
  %Equal.sym(Bool, U32.is_eq(W.byte(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(2, 3n))))), 0n), 0), False{}, W2.e_lo(w, c, U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(2, 3n)))), 0n, {==})) :
    {W2.R4(_, U32.is_eq(W.byte(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(2, 3n))))), 1n), 0), U32.is_eq(W.byte(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(2, 3n))))), 2n), 0), U32.is_eq(W.byte(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(2, 3n))))), 3n), 0)) == Nat.add(U32.to_nat(2), D.run_len(List.drop(&2, U32, C.L4(w), U32.to_nat(2)), c)) : Nat}
  %Equal.sym(Bool, U32.is_eq(W.byte(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(2, 3n))))), 1n), 0), False{}, W2.e_lo(w, c, U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(2, 3n)))), 1n, {==})) :
    {W2.R4(False{}, _, U32.is_eq(W.byte(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(2, 3n))))), 2n), 0), U32.is_eq(W.byte(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(2, 3n))))), 3n), 0)) == Nat.add(U32.to_nat(2), D.run_len(List.drop(&2, U32, C.L4(w), U32.to_nat(2)), c)) : Nat}
  %Equal.sym(Bool, U32.is_eq(W.byte(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(2, 3n))))), 2n), 0), U32.is_eq(W.byte(w, 2n), c), W2.e_hi(w, c, U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(2, 3n)))), 2n, hc, {==}, {==})) :
    {W2.R4(False{}, False{}, _, U32.is_eq(W.byte(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(2, 3n))))), 3n), 0)) == Nat.add(U32.to_nat(2), D.run_len(List.drop(&2, U32, C.L4(w), U32.to_nat(2)), c)) : Nat}
  %Equal.sym(Bool, U32.is_eq(W.byte(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(2, 3n))))), 3n), 0), U32.is_eq(W.byte(w, 3n), c), W2.e_hi(w, c, U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(2, 3n)))), 3n, hc, {==}, {==})) :
    {W2.R4(False{}, False{}, U32.is_eq(W.byte(w, 2n), c), _) == Nat.add(U32.to_nat(2), D.run_len(List.drop(&2, U32, C.L4(w), U32.to_nat(2)), c)) : Nat}
  {==}

law plk3:
  for +w: U32
  for +c: U32
  for +hc: {U32.is_lt(c, 256) == True{} : Bool}
  {P0(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(3, 3n)))))) == Nat.add(U32.to_nat(3), D.run_len(List.drop(&2, U32, C.L4(w), U32.to_nat(3)), c)) : Nat}

def plk3(w, c, hc):
  %Equal.sym(Bool, U32.is_eq(W.byte(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(3, 3n))))), 0n), 0), False{}, W2.e_lo(w, c, U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(3, 3n)))), 0n, {==})) :
    {W2.R4(_, U32.is_eq(W.byte(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(3, 3n))))), 1n), 0), U32.is_eq(W.byte(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(3, 3n))))), 2n), 0), U32.is_eq(W.byte(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(3, 3n))))), 3n), 0)) == Nat.add(U32.to_nat(3), D.run_len(List.drop(&2, U32, C.L4(w), U32.to_nat(3)), c)) : Nat}
  %Equal.sym(Bool, U32.is_eq(W.byte(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(3, 3n))))), 1n), 0), False{}, W2.e_lo(w, c, U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(3, 3n)))), 1n, {==})) :
    {W2.R4(False{}, _, U32.is_eq(W.byte(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(3, 3n))))), 2n), 0), U32.is_eq(W.byte(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(3, 3n))))), 3n), 0)) == Nat.add(U32.to_nat(3), D.run_len(List.drop(&2, U32, C.L4(w), U32.to_nat(3)), c)) : Nat}
  %Equal.sym(Bool, U32.is_eq(W.byte(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(3, 3n))))), 2n), 0), False{}, W2.e_lo(w, c, U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(3, 3n)))), 2n, {==})) :
    {W2.R4(False{}, False{}, _, U32.is_eq(W.byte(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(3, 3n))))), 3n), 0)) == Nat.add(U32.to_nat(3), D.run_len(List.drop(&2, U32, C.L4(w), U32.to_nat(3)), c)) : Nat}
  %Equal.sym(Bool, U32.is_eq(W.byte(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(3, 3n))))), 3n), 0), U32.is_eq(W.byte(w, 3n), c), W2.e_hi(w, c, U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(3, 3n)))), 3n, hc, {==}, {==})) :
    {W2.R4(False{}, False{}, False{}, _) == Nat.add(U32.to_nat(3), D.run_len(List.drop(&2, U32, C.L4(w), U32.to_nat(3)), c)) : Nat}
  {==}

# The first word for a start place a (0 to 3, given as r).
law pl:
  for +w: U32
  for +c: U32
  for +a: U32
  for +r: Nat
  for +hc: {U32.is_lt(c, 256) == True{} : Bool}
  for +hr: {U32.to_nat(a) == r : Nat}
  for +hlt: {Nat.is_lt(r, 4n) == True{} : Bool}
  {P0(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(a, 3n)))))) == Nat.add(U32.to_nat(a), D.run_len(List.drop(&2, U32, C.L4(w), U32.to_nat(a)), c)) : Nat}

def pl(w, c, a, r, hc, hr, hlt):
  match r:
    case 0n:
      %Equal.sym(U32, a, 0, U.to_nat_inj(a, 0, hr)) :
        {P0(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(_, 3n)))))) == Nat.add(U32.to_nat(_), D.run_len(List.drop(&2, U32, C.L4(w), U32.to_nat(_)), c)) : Nat}
      plk0(w, c, hc)
    case 1n+r1:
      match r1:
        case 0n:
          %Equal.sym(U32, a, 1, U.to_nat_inj(a, 1, hr)) :
            {P0(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(_, 3n)))))) == Nat.add(U32.to_nat(_), D.run_len(List.drop(&2, U32, C.L4(w), U32.to_nat(_)), c)) : Nat}
          plk1(w, c, hc)
        case 1n+r2:
          match r2:
            case 0n:
              %Equal.sym(U32, a, 2, U.to_nat_inj(a, 2, hr)) :
                {P0(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(_, 3n)))))) == Nat.add(U32.to_nat(_), D.run_len(List.drop(&2, U32, C.L4(w), U32.to_nat(_)), c)) : Nat}
              plk2(w, c, hc)
            case 1n+r3:
              match r3:
                case 0n:
                  %Equal.sym(U32, a, 3, U.to_nat_inj(a, 3, hr)) :
                    {P0(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(_, 3n)))))) == Nat.add(U32.to_nat(_), D.run_len(List.drop(&2, U32, C.L4(w), U32.to_nat(_)), c)) : Nat}
                  plk3(w, c, hc)
                case 1n+r4:
                  Empty.absurd({P0(U32.or(U32.xor(w, FA.rep(c)), U32.not(U32.shln(4294967295, U32.to_nat(U32.shln(a, 3n)))))) == Nat.add(U32.to_nat(a), D.run_len(List.drop(&2, U32, C.L4(w), U32.to_nat(a)), c)) : Nat}, AB.lt_zero_absurd(r4, hlt))

# The first word of a search: the bytes below i's place are set to 0xFF, so
# the first zero byte is the first c at or above that place.
law p0_low:
  for +w: U32
  for +c: U32
  for +i: U32
  for +hc: {U32.is_lt(c, 256) == True{} : Bool}
  {P0(U32.or(U32.xor(w, FA.rep(c)), U32.not(FA.low(i)))) == Nat.add(U32.to_nat((i .&. 3 : U32)), D.run_len(List.drop(&2, U32, C.L4(w), U32.to_nat((i .&. 3 : U32))), c)) : Nat}

def p0_low(w, c, i, hc):
  +a = (i .&. 3 : U32)
  pl(w, c, a, U32.to_nat(a), hc, {==},
    AB.subst(Nat, y => {Nat.is_lt(y, 4n) == True{} : Bool}, Nat.mod(U32.to_nat(i), Nat.pow(2n, 2n)), U32.to_nat(a),
      Equal.sym(Nat, U32.to_nat(a), Nat.mod(U32.to_nat(i), Nat.pow(2n, 2n)), U.to_nat_and_mask(i, 3, 2n, {==})),
      N.mod_lt(U32.to_nat(i), Nat.pow(2n, 2n), {==})))
