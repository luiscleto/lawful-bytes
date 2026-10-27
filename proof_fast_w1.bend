import Base
import ../lawful-words/defs.bend as W
import ../lawful-words/proof_nat.bend as N
import ../lawful-words/proof_u32.bend as U
import ../lawful-words/proof_bytes.bend as Y
import ../lawful-words/proof_zb.bend as Z
import ../lawful-arrays/proof_base.bend as AB
import ./fast.bend as FA

# Word facts for fast.bend's zero-byte search, at the level of bits (the
# style of lawful-words' proof_zb.bend: a word is four bytes, app8, and a
# per-byte lemma checked on all 256 bytes).

# And is associative
# ==================

law wand_assoc:
  for +n: Nat
  for +x: Word(n)
  for +y: Word(n)
  for +z: Word(n)
  {Word.and(n, x, Word.and(n, y, z)) == Word.and(n, Word.and(n, x, y), z) : Word(n)}

def wand_assoc(n, x, y, z):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match x y z:
        case WCon{False{}, +xt} WCon{+b, +yt} WCon{+c, +zt}:
          %wand_assoc(p, xt, yt, zt) :
            {WCon{False{}, Word.and(p, xt, Word.and(p, yt, zt))} == WCon{False{}, _} : Word(1n+p)}
          {==}
        case WCon{True{}, +xt} WCon{+b, +yt} WCon{+c, +zt}:
          %wand_assoc(p, xt, yt, zt) :
            {WCon{Bool.and(b, c), Word.and(p, xt, Word.and(p, yt, zt))} == WCon{Bool.and(b, c), _} : Word(1n+p)}
          {==}

law uand_assoc:
  for +a: U32
  for +b: U32
  for +c: U32
  {U32.and(a, U32.and(b, c)) == U32.and(U32.and(a, b), c) : U32}

def uand_assoc(a, b, c):
  match a b c:
    case U32{+x} U32{+y} U32{+z}:
      %wand_assoc(32n, x, y, z) : {U32{Word.and(32n, x, Word.and(32n, y, z))} == U32{_} : U32}
      {==}

# fast.bend's zb is lawful-words' zb.
law zb_eq:
  for +v: U32
  {FA.zb(v) == W.zb(v) : U32}

def zb_eq(v):
  uand_assoc(U32.sub(v, 16843009), U32.not(v), 2155905152)

# One byte of the masked zero-byte test
# =====================================

# With no borrow in and the byte's flag kept by the mask, the masked flags are
# all clear exactly when the byte is not zero and the rest are clear.
law zbk_byte:
  for +n: Nat
  for +x: Word(8n)
  for +r: Word(n)
  for +kr: Word(n)
  for +hr: Word(n)
  for +mr: Word(n)
  {Z.allz(Nat.add(8n, n), Word.and(Nat.add(8n, n), Z.zf(Nat.add(8n, n), Z.app8(n, x, r), Z.app8(n, Z.one8(), kr), Z.app8(n, Z.h8(), hr), True{}), Z.app8(n, Z.h8(), mr)))
    == Bool.and(Bool.not(Z.allz(8n, x)), Z.allz(n, Word.and(n, Z.zf(n, r, kr, hr, True{}), mr))) : Bool}

def zbk_byte(n, x, r, kr, hr, mr):
  match x:
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}:
      {==}

# The flags of the low 1 byte(s), as words of four bytes.
law tkw1:
  for +X0: Word(8n)
  for +X1: Word(8n)
  for +X2: Word(8n)
  for +X3: Word(8n)
  {Z.allz(32n, Word.and(32n, Z.zf(32n, Z.app8(24n, X0, Z.app8(16n, X1, Z.app8(8n, X2, Z.app8(0n, X3, WNil{})))), Z.app8(24n, Z.one8(), Z.app8(16n, Z.one8(), Z.app8(8n, Z.one8(), Z.app8(0n, Z.one8(), WNil{})))), Z.app8(24n, Z.h8(), Z.app8(16n, Z.h8(), Z.app8(8n, Z.h8(), Z.app8(0n, Z.h8(), WNil{})))), True{}), Z.app8(24n, Z.h8(), Word.zero(24n)))) == Bool.and(Bool.not(Z.allz(8n, X0)), True{}) : Bool}

def tkw1(X0, X1, X2, X3):
  %Equal.sym(Bool, Z.allz(Nat.add(8n, 24n), Word.and(Nat.add(8n, 24n), Z.zf(Nat.add(8n, 24n), Z.app8(24n, X0, Z.app8(16n, X1, Z.app8(8n, X2, Z.app8(0n, X3, WNil{})))), Z.app8(24n, Z.one8(), Z.app8(16n, Z.one8(), Z.app8(8n, Z.one8(), Z.app8(0n, Z.one8(), WNil{})))), Z.app8(24n, Z.h8(), Z.app8(16n, Z.h8(), Z.app8(8n, Z.h8(), Z.app8(0n, Z.h8(), WNil{})))), True{}), Z.app8(24n, Z.h8(), Word.zero(24n)))),
    Bool.and(Bool.not(Z.allz(8n, X0)), Z.allz(24n, Word.and(24n, Z.zf(24n, Z.app8(16n, X1, Z.app8(8n, X2, Z.app8(0n, X3, WNil{}))), Z.app8(16n, Z.one8(), Z.app8(8n, Z.one8(), Z.app8(0n, Z.one8(), WNil{}))), Z.app8(16n, Z.h8(), Z.app8(8n, Z.h8(), Z.app8(0n, Z.h8(), WNil{}))), True{}), Word.zero(24n)))),
    zbk_byte(24n, X0, Z.app8(16n, X1, Z.app8(8n, X2, Z.app8(0n, X3, WNil{}))), Z.app8(16n, Z.one8(), Z.app8(8n, Z.one8(), Z.app8(0n, Z.one8(), WNil{}))), Z.app8(16n, Z.h8(), Z.app8(8n, Z.h8(), Z.app8(0n, Z.h8(), WNil{}))), Word.zero(24n))) :
    {_ == Bool.and(Bool.not(Z.allz(8n, X0)), True{}) : Bool}
  %Equal.sym(Bool, Z.allz(24n, Word.and(24n, Z.zf(24n, Z.app8(16n, X1, Z.app8(8n, X2, Z.app8(0n, X3, WNil{}))), Z.app8(16n, Z.one8(), Z.app8(8n, Z.one8(), Z.app8(0n, Z.one8(), WNil{}))), Z.app8(16n, Z.h8(), Z.app8(8n, Z.h8(), Z.app8(0n, Z.h8(), WNil{}))), True{}), Word.zero(24n))), True{},
    Z.allz_andz(24n, Z.zf(24n, Z.app8(16n, X1, Z.app8(8n, X2, Z.app8(0n, X3, WNil{}))), Z.app8(16n, Z.one8(), Z.app8(8n, Z.one8(), Z.app8(0n, Z.one8(), WNil{}))), Z.app8(16n, Z.h8(), Z.app8(8n, Z.h8(), Z.app8(0n, Z.h8(), WNil{}))), True{}))) :
    {Bool.and(Bool.not(Z.allz(8n, X0)), _) == Bool.and(Bool.not(Z.allz(8n, X0)), True{}) : Bool}
  {==}

# The flags of the low 2 byte(s), as words of four bytes.
law tkw2:
  for +X0: Word(8n)
  for +X1: Word(8n)
  for +X2: Word(8n)
  for +X3: Word(8n)
  {Z.allz(32n, Word.and(32n, Z.zf(32n, Z.app8(24n, X0, Z.app8(16n, X1, Z.app8(8n, X2, Z.app8(0n, X3, WNil{})))), Z.app8(24n, Z.one8(), Z.app8(16n, Z.one8(), Z.app8(8n, Z.one8(), Z.app8(0n, Z.one8(), WNil{})))), Z.app8(24n, Z.h8(), Z.app8(16n, Z.h8(), Z.app8(8n, Z.h8(), Z.app8(0n, Z.h8(), WNil{})))), True{}), Z.app8(24n, Z.h8(), Z.app8(16n, Z.h8(), Word.zero(16n))))) == Bool.and(Bool.not(Z.allz(8n, X0)), Bool.and(Bool.not(Z.allz(8n, X1)), True{})) : Bool}

def tkw2(X0, X1, X2, X3):
  %Equal.sym(Bool, Z.allz(Nat.add(8n, 24n), Word.and(Nat.add(8n, 24n), Z.zf(Nat.add(8n, 24n), Z.app8(24n, X0, Z.app8(16n, X1, Z.app8(8n, X2, Z.app8(0n, X3, WNil{})))), Z.app8(24n, Z.one8(), Z.app8(16n, Z.one8(), Z.app8(8n, Z.one8(), Z.app8(0n, Z.one8(), WNil{})))), Z.app8(24n, Z.h8(), Z.app8(16n, Z.h8(), Z.app8(8n, Z.h8(), Z.app8(0n, Z.h8(), WNil{})))), True{}), Z.app8(24n, Z.h8(), Z.app8(16n, Z.h8(), Word.zero(16n))))),
    Bool.and(Bool.not(Z.allz(8n, X0)), Z.allz(24n, Word.and(24n, Z.zf(24n, Z.app8(16n, X1, Z.app8(8n, X2, Z.app8(0n, X3, WNil{}))), Z.app8(16n, Z.one8(), Z.app8(8n, Z.one8(), Z.app8(0n, Z.one8(), WNil{}))), Z.app8(16n, Z.h8(), Z.app8(8n, Z.h8(), Z.app8(0n, Z.h8(), WNil{}))), True{}), Z.app8(16n, Z.h8(), Word.zero(16n))))),
    zbk_byte(24n, X0, Z.app8(16n, X1, Z.app8(8n, X2, Z.app8(0n, X3, WNil{}))), Z.app8(16n, Z.one8(), Z.app8(8n, Z.one8(), Z.app8(0n, Z.one8(), WNil{}))), Z.app8(16n, Z.h8(), Z.app8(8n, Z.h8(), Z.app8(0n, Z.h8(), WNil{}))), Z.app8(16n, Z.h8(), Word.zero(16n)))) :
    {_ == Bool.and(Bool.not(Z.allz(8n, X0)), Bool.and(Bool.not(Z.allz(8n, X1)), True{})) : Bool}
  %Equal.sym(Bool, Z.allz(Nat.add(8n, 16n), Word.and(Nat.add(8n, 16n), Z.zf(Nat.add(8n, 16n), Z.app8(16n, X1, Z.app8(8n, X2, Z.app8(0n, X3, WNil{}))), Z.app8(16n, Z.one8(), Z.app8(8n, Z.one8(), Z.app8(0n, Z.one8(), WNil{}))), Z.app8(16n, Z.h8(), Z.app8(8n, Z.h8(), Z.app8(0n, Z.h8(), WNil{}))), True{}), Z.app8(16n, Z.h8(), Word.zero(16n)))),
    Bool.and(Bool.not(Z.allz(8n, X1)), Z.allz(16n, Word.and(16n, Z.zf(16n, Z.app8(8n, X2, Z.app8(0n, X3, WNil{})), Z.app8(8n, Z.one8(), Z.app8(0n, Z.one8(), WNil{})), Z.app8(8n, Z.h8(), Z.app8(0n, Z.h8(), WNil{})), True{}), Word.zero(16n)))),
    zbk_byte(16n, X1, Z.app8(8n, X2, Z.app8(0n, X3, WNil{})), Z.app8(8n, Z.one8(), Z.app8(0n, Z.one8(), WNil{})), Z.app8(8n, Z.h8(), Z.app8(0n, Z.h8(), WNil{})), Word.zero(16n))) :
    {Bool.and(Bool.not(Z.allz(8n, X0)), _) == Bool.and(Bool.not(Z.allz(8n, X0)), Bool.and(Bool.not(Z.allz(8n, X1)), True{})) : Bool}
  %Equal.sym(Bool, Z.allz(16n, Word.and(16n, Z.zf(16n, Z.app8(8n, X2, Z.app8(0n, X3, WNil{})), Z.app8(8n, Z.one8(), Z.app8(0n, Z.one8(), WNil{})), Z.app8(8n, Z.h8(), Z.app8(0n, Z.h8(), WNil{})), True{}), Word.zero(16n))), True{},
    Z.allz_andz(16n, Z.zf(16n, Z.app8(8n, X2, Z.app8(0n, X3, WNil{})), Z.app8(8n, Z.one8(), Z.app8(0n, Z.one8(), WNil{})), Z.app8(8n, Z.h8(), Z.app8(0n, Z.h8(), WNil{})), True{}))) :
    {Bool.and(Bool.not(Z.allz(8n, X0)), Bool.and(Bool.not(Z.allz(8n, X1)), _)) == Bool.and(Bool.not(Z.allz(8n, X0)), Bool.and(Bool.not(Z.allz(8n, X1)), True{})) : Bool}
  {==}

# The flags of the low 3 byte(s), as words of four bytes.
law tkw3:
  for +X0: Word(8n)
  for +X1: Word(8n)
  for +X2: Word(8n)
  for +X3: Word(8n)
  {Z.allz(32n, Word.and(32n, Z.zf(32n, Z.app8(24n, X0, Z.app8(16n, X1, Z.app8(8n, X2, Z.app8(0n, X3, WNil{})))), Z.app8(24n, Z.one8(), Z.app8(16n, Z.one8(), Z.app8(8n, Z.one8(), Z.app8(0n, Z.one8(), WNil{})))), Z.app8(24n, Z.h8(), Z.app8(16n, Z.h8(), Z.app8(8n, Z.h8(), Z.app8(0n, Z.h8(), WNil{})))), True{}), Z.app8(24n, Z.h8(), Z.app8(16n, Z.h8(), Z.app8(8n, Z.h8(), Word.zero(8n)))))) == Bool.and(Bool.not(Z.allz(8n, X0)), Bool.and(Bool.not(Z.allz(8n, X1)), Bool.and(Bool.not(Z.allz(8n, X2)), True{}))) : Bool}

def tkw3(X0, X1, X2, X3):
  %Equal.sym(Bool, Z.allz(Nat.add(8n, 24n), Word.and(Nat.add(8n, 24n), Z.zf(Nat.add(8n, 24n), Z.app8(24n, X0, Z.app8(16n, X1, Z.app8(8n, X2, Z.app8(0n, X3, WNil{})))), Z.app8(24n, Z.one8(), Z.app8(16n, Z.one8(), Z.app8(8n, Z.one8(), Z.app8(0n, Z.one8(), WNil{})))), Z.app8(24n, Z.h8(), Z.app8(16n, Z.h8(), Z.app8(8n, Z.h8(), Z.app8(0n, Z.h8(), WNil{})))), True{}), Z.app8(24n, Z.h8(), Z.app8(16n, Z.h8(), Z.app8(8n, Z.h8(), Word.zero(8n)))))),
    Bool.and(Bool.not(Z.allz(8n, X0)), Z.allz(24n, Word.and(24n, Z.zf(24n, Z.app8(16n, X1, Z.app8(8n, X2, Z.app8(0n, X3, WNil{}))), Z.app8(16n, Z.one8(), Z.app8(8n, Z.one8(), Z.app8(0n, Z.one8(), WNil{}))), Z.app8(16n, Z.h8(), Z.app8(8n, Z.h8(), Z.app8(0n, Z.h8(), WNil{}))), True{}), Z.app8(16n, Z.h8(), Z.app8(8n, Z.h8(), Word.zero(8n)))))),
    zbk_byte(24n, X0, Z.app8(16n, X1, Z.app8(8n, X2, Z.app8(0n, X3, WNil{}))), Z.app8(16n, Z.one8(), Z.app8(8n, Z.one8(), Z.app8(0n, Z.one8(), WNil{}))), Z.app8(16n, Z.h8(), Z.app8(8n, Z.h8(), Z.app8(0n, Z.h8(), WNil{}))), Z.app8(16n, Z.h8(), Z.app8(8n, Z.h8(), Word.zero(8n))))) :
    {_ == Bool.and(Bool.not(Z.allz(8n, X0)), Bool.and(Bool.not(Z.allz(8n, X1)), Bool.and(Bool.not(Z.allz(8n, X2)), True{}))) : Bool}
  %Equal.sym(Bool, Z.allz(Nat.add(8n, 16n), Word.and(Nat.add(8n, 16n), Z.zf(Nat.add(8n, 16n), Z.app8(16n, X1, Z.app8(8n, X2, Z.app8(0n, X3, WNil{}))), Z.app8(16n, Z.one8(), Z.app8(8n, Z.one8(), Z.app8(0n, Z.one8(), WNil{}))), Z.app8(16n, Z.h8(), Z.app8(8n, Z.h8(), Z.app8(0n, Z.h8(), WNil{}))), True{}), Z.app8(16n, Z.h8(), Z.app8(8n, Z.h8(), Word.zero(8n))))),
    Bool.and(Bool.not(Z.allz(8n, X1)), Z.allz(16n, Word.and(16n, Z.zf(16n, Z.app8(8n, X2, Z.app8(0n, X3, WNil{})), Z.app8(8n, Z.one8(), Z.app8(0n, Z.one8(), WNil{})), Z.app8(8n, Z.h8(), Z.app8(0n, Z.h8(), WNil{})), True{}), Z.app8(8n, Z.h8(), Word.zero(8n))))),
    zbk_byte(16n, X1, Z.app8(8n, X2, Z.app8(0n, X3, WNil{})), Z.app8(8n, Z.one8(), Z.app8(0n, Z.one8(), WNil{})), Z.app8(8n, Z.h8(), Z.app8(0n, Z.h8(), WNil{})), Z.app8(8n, Z.h8(), Word.zero(8n)))) :
    {Bool.and(Bool.not(Z.allz(8n, X0)), _) == Bool.and(Bool.not(Z.allz(8n, X0)), Bool.and(Bool.not(Z.allz(8n, X1)), Bool.and(Bool.not(Z.allz(8n, X2)), True{}))) : Bool}
  %Equal.sym(Bool, Z.allz(Nat.add(8n, 8n), Word.and(Nat.add(8n, 8n), Z.zf(Nat.add(8n, 8n), Z.app8(8n, X2, Z.app8(0n, X3, WNil{})), Z.app8(8n, Z.one8(), Z.app8(0n, Z.one8(), WNil{})), Z.app8(8n, Z.h8(), Z.app8(0n, Z.h8(), WNil{})), True{}), Z.app8(8n, Z.h8(), Word.zero(8n)))),
    Bool.and(Bool.not(Z.allz(8n, X2)), Z.allz(8n, Word.and(8n, Z.zf(8n, Z.app8(0n, X3, WNil{}), Z.app8(0n, Z.one8(), WNil{}), Z.app8(0n, Z.h8(), WNil{}), True{}), Word.zero(8n)))),
    zbk_byte(8n, X2, Z.app8(0n, X3, WNil{}), Z.app8(0n, Z.one8(), WNil{}), Z.app8(0n, Z.h8(), WNil{}), Word.zero(8n))) :
    {Bool.and(Bool.not(Z.allz(8n, X0)), Bool.and(Bool.not(Z.allz(8n, X1)), _)) == Bool.and(Bool.not(Z.allz(8n, X0)), Bool.and(Bool.not(Z.allz(8n, X1)), Bool.and(Bool.not(Z.allz(8n, X2)), True{}))) : Bool}
  %Equal.sym(Bool, Z.allz(8n, Word.and(8n, Z.zf(8n, Z.app8(0n, X3, WNil{}), Z.app8(0n, Z.one8(), WNil{}), Z.app8(0n, Z.h8(), WNil{}), True{}), Word.zero(8n))), True{},
    Z.allz_andz(8n, Z.zf(8n, Z.app8(0n, X3, WNil{}), Z.app8(0n, Z.one8(), WNil{}), Z.app8(0n, Z.h8(), WNil{}), True{}))) :
    {Bool.and(Bool.not(Z.allz(8n, X0)), Bool.and(Bool.not(Z.allz(8n, X1)), Bool.and(Bool.not(Z.allz(8n, X2)), _))) == Bool.and(Bool.not(Z.allz(8n, X0)), Bool.and(Bool.not(Z.allz(8n, X1)), Bool.and(Bool.not(Z.allz(8n, X2)), True{}))) : Bool}
  {==}

law tk1:
  for +v: U32
  {U32.is_zero(U32.and(W.zb(v), 128)) == Bool.and(U32.is_ne(W.byte(v, 0n), 0), True{}) : Bool}

def tk1(v):
  match v:
    case U32{WCon{+c0, WCon{+c1, WCon{+c2, WCon{+c3, WCon{+c4, WCon{+c5, WCon{+c6, WCon{+c7, WCon{+c8, WCon{+c9, WCon{+c10, WCon{+c11, WCon{+c12, WCon{+c13, WCon{+c14, WCon{+c15, WCon{+c16, WCon{+c17, WCon{+c18, WCon{+c19, WCon{+c20, WCon{+c21, WCon{+c22, WCon{+c23, WCon{+c24, WCon{+c25, WCon{+c26, WCon{+c27, WCon{+c28, WCon{+c29, WCon{+c30, WCon{+c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      +X0 = {WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WNil{}}}}}}}}} : Word(8n)}
      +X1 = {WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WNil{}}}}}}}}} : Word(8n)}
      +X2 = {WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}} : Word(8n)}
      +X3 = {WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}} : Word(8n)}
      %Equal.sym(Bool, U32.is_ne(W.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Bool.not(Z.allz(8n, X0)), Z.zb_ne0(c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31)) :
        {U32.is_zero(U32.and(W.zb(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}), 128)) == Bool.and(_, True{}) : Bool}
      Equal.trans(Bool, Cmp.is_eq(Word.cmp(32n, Word.and(32n, Z.zf(32n, Z.app8(24n, X0, Z.app8(16n, X1, Z.app8(8n, X2, Z.app8(0n, X3, WNil{})))), Z.app8(24n, Z.one8(), Z.app8(16n, Z.one8(), Z.app8(8n, Z.one8(), Z.app8(0n, Z.one8(), WNil{})))), Z.app8(24n, Z.h8(), Z.app8(16n, Z.h8(), Z.app8(8n, Z.h8(), Z.app8(0n, Z.h8(), WNil{})))), True{}), Z.app8(24n, Z.h8(), Word.zero(24n))), Word.zero(32n))), Z.allz(32n, Word.and(32n, Z.zf(32n, Z.app8(24n, X0, Z.app8(16n, X1, Z.app8(8n, X2, Z.app8(0n, X3, WNil{})))), Z.app8(24n, Z.one8(), Z.app8(16n, Z.one8(), Z.app8(8n, Z.one8(), Z.app8(0n, Z.one8(), WNil{})))), Z.app8(24n, Z.h8(), Z.app8(16n, Z.h8(), Z.app8(8n, Z.h8(), Z.app8(0n, Z.h8(), WNil{})))), True{}), Z.app8(24n, Z.h8(), Word.zero(24n)))), Bool.and(Bool.not(Z.allz(8n, X0)), True{}),
        Z.allz_cmp(32n, Word.and(32n, Z.zf(32n, Z.app8(24n, X0, Z.app8(16n, X1, Z.app8(8n, X2, Z.app8(0n, X3, WNil{})))), Z.app8(24n, Z.one8(), Z.app8(16n, Z.one8(), Z.app8(8n, Z.one8(), Z.app8(0n, Z.one8(), WNil{})))), Z.app8(24n, Z.h8(), Z.app8(16n, Z.h8(), Z.app8(8n, Z.h8(), Z.app8(0n, Z.h8(), WNil{})))), True{}), Z.app8(24n, Z.h8(), Word.zero(24n)))), tkw1(X0, X1, X2, X3))

law tk2:
  for +v: U32
  {U32.is_zero(U32.and(W.zb(v), 32896)) == Bool.and(U32.is_ne(W.byte(v, 0n), 0), Bool.and(U32.is_ne(W.byte(v, 1n), 0), True{})) : Bool}

def tk2(v):
  match v:
    case U32{WCon{+c0, WCon{+c1, WCon{+c2, WCon{+c3, WCon{+c4, WCon{+c5, WCon{+c6, WCon{+c7, WCon{+c8, WCon{+c9, WCon{+c10, WCon{+c11, WCon{+c12, WCon{+c13, WCon{+c14, WCon{+c15, WCon{+c16, WCon{+c17, WCon{+c18, WCon{+c19, WCon{+c20, WCon{+c21, WCon{+c22, WCon{+c23, WCon{+c24, WCon{+c25, WCon{+c26, WCon{+c27, WCon{+c28, WCon{+c29, WCon{+c30, WCon{+c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      +X0 = {WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WNil{}}}}}}}}} : Word(8n)}
      +X1 = {WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WNil{}}}}}}}}} : Word(8n)}
      +X2 = {WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}} : Word(8n)}
      +X3 = {WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}} : Word(8n)}
      %Equal.sym(Bool, U32.is_ne(W.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Bool.not(Z.allz(8n, X0)), Z.zb_ne0(c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31)) :
        {U32.is_zero(U32.and(W.zb(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}), 32896)) == Bool.and(_, Bool.and(U32.is_ne(W.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), True{})) : Bool}
      %Equal.sym(Bool, U32.is_ne(W.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Bool.not(Z.allz(8n, X1)), Z.zb_ne1(c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31)) :
        {U32.is_zero(U32.and(W.zb(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}), 32896)) == Bool.and(Bool.not(Z.allz(8n, X0)), Bool.and(_, True{})) : Bool}
      Equal.trans(Bool, Cmp.is_eq(Word.cmp(32n, Word.and(32n, Z.zf(32n, Z.app8(24n, X0, Z.app8(16n, X1, Z.app8(8n, X2, Z.app8(0n, X3, WNil{})))), Z.app8(24n, Z.one8(), Z.app8(16n, Z.one8(), Z.app8(8n, Z.one8(), Z.app8(0n, Z.one8(), WNil{})))), Z.app8(24n, Z.h8(), Z.app8(16n, Z.h8(), Z.app8(8n, Z.h8(), Z.app8(0n, Z.h8(), WNil{})))), True{}), Z.app8(24n, Z.h8(), Z.app8(16n, Z.h8(), Word.zero(16n)))), Word.zero(32n))), Z.allz(32n, Word.and(32n, Z.zf(32n, Z.app8(24n, X0, Z.app8(16n, X1, Z.app8(8n, X2, Z.app8(0n, X3, WNil{})))), Z.app8(24n, Z.one8(), Z.app8(16n, Z.one8(), Z.app8(8n, Z.one8(), Z.app8(0n, Z.one8(), WNil{})))), Z.app8(24n, Z.h8(), Z.app8(16n, Z.h8(), Z.app8(8n, Z.h8(), Z.app8(0n, Z.h8(), WNil{})))), True{}), Z.app8(24n, Z.h8(), Z.app8(16n, Z.h8(), Word.zero(16n))))), Bool.and(Bool.not(Z.allz(8n, X0)), Bool.and(Bool.not(Z.allz(8n, X1)), True{})),
        Z.allz_cmp(32n, Word.and(32n, Z.zf(32n, Z.app8(24n, X0, Z.app8(16n, X1, Z.app8(8n, X2, Z.app8(0n, X3, WNil{})))), Z.app8(24n, Z.one8(), Z.app8(16n, Z.one8(), Z.app8(8n, Z.one8(), Z.app8(0n, Z.one8(), WNil{})))), Z.app8(24n, Z.h8(), Z.app8(16n, Z.h8(), Z.app8(8n, Z.h8(), Z.app8(0n, Z.h8(), WNil{})))), True{}), Z.app8(24n, Z.h8(), Z.app8(16n, Z.h8(), Word.zero(16n))))), tkw2(X0, X1, X2, X3))

law tk3:
  for +v: U32
  {U32.is_zero(U32.and(W.zb(v), 8421504)) == Bool.and(U32.is_ne(W.byte(v, 0n), 0), Bool.and(U32.is_ne(W.byte(v, 1n), 0), Bool.and(U32.is_ne(W.byte(v, 2n), 0), True{}))) : Bool}

def tk3(v):
  match v:
    case U32{WCon{+c0, WCon{+c1, WCon{+c2, WCon{+c3, WCon{+c4, WCon{+c5, WCon{+c6, WCon{+c7, WCon{+c8, WCon{+c9, WCon{+c10, WCon{+c11, WCon{+c12, WCon{+c13, WCon{+c14, WCon{+c15, WCon{+c16, WCon{+c17, WCon{+c18, WCon{+c19, WCon{+c20, WCon{+c21, WCon{+c22, WCon{+c23, WCon{+c24, WCon{+c25, WCon{+c26, WCon{+c27, WCon{+c28, WCon{+c29, WCon{+c30, WCon{+c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      +X0 = {WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WNil{}}}}}}}}} : Word(8n)}
      +X1 = {WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WNil{}}}}}}}}} : Word(8n)}
      +X2 = {WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WNil{}}}}}}}}} : Word(8n)}
      +X3 = {WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}} : Word(8n)}
      %Equal.sym(Bool, U32.is_ne(W.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Bool.not(Z.allz(8n, X0)), Z.zb_ne0(c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31)) :
        {U32.is_zero(U32.and(W.zb(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}), 8421504)) == Bool.and(_, Bool.and(U32.is_ne(W.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Bool.and(U32.is_ne(W.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), True{}))) : Bool}
      %Equal.sym(Bool, U32.is_ne(W.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Bool.not(Z.allz(8n, X1)), Z.zb_ne1(c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31)) :
        {U32.is_zero(U32.and(W.zb(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}), 8421504)) == Bool.and(Bool.not(Z.allz(8n, X0)), Bool.and(_, Bool.and(U32.is_ne(W.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), True{}))) : Bool}
      %Equal.sym(Bool, U32.is_ne(W.byte(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Bool.not(Z.allz(8n, X2)), Z.zb_ne2(c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31)) :
        {U32.is_zero(U32.and(W.zb(U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}), 8421504)) == Bool.and(Bool.not(Z.allz(8n, X0)), Bool.and(Bool.not(Z.allz(8n, X1)), Bool.and(_, True{}))) : Bool}
      Equal.trans(Bool, Cmp.is_eq(Word.cmp(32n, Word.and(32n, Z.zf(32n, Z.app8(24n, X0, Z.app8(16n, X1, Z.app8(8n, X2, Z.app8(0n, X3, WNil{})))), Z.app8(24n, Z.one8(), Z.app8(16n, Z.one8(), Z.app8(8n, Z.one8(), Z.app8(0n, Z.one8(), WNil{})))), Z.app8(24n, Z.h8(), Z.app8(16n, Z.h8(), Z.app8(8n, Z.h8(), Z.app8(0n, Z.h8(), WNil{})))), True{}), Z.app8(24n, Z.h8(), Z.app8(16n, Z.h8(), Z.app8(8n, Z.h8(), Word.zero(8n))))), Word.zero(32n))), Z.allz(32n, Word.and(32n, Z.zf(32n, Z.app8(24n, X0, Z.app8(16n, X1, Z.app8(8n, X2, Z.app8(0n, X3, WNil{})))), Z.app8(24n, Z.one8(), Z.app8(16n, Z.one8(), Z.app8(8n, Z.one8(), Z.app8(0n, Z.one8(), WNil{})))), Z.app8(24n, Z.h8(), Z.app8(16n, Z.h8(), Z.app8(8n, Z.h8(), Z.app8(0n, Z.h8(), WNil{})))), True{}), Z.app8(24n, Z.h8(), Z.app8(16n, Z.h8(), Z.app8(8n, Z.h8(), Word.zero(8n)))))), Bool.and(Bool.not(Z.allz(8n, X0)), Bool.and(Bool.not(Z.allz(8n, X1)), Bool.and(Bool.not(Z.allz(8n, X2)), True{}))),
        Z.allz_cmp(32n, Word.and(32n, Z.zf(32n, Z.app8(24n, X0, Z.app8(16n, X1, Z.app8(8n, X2, Z.app8(0n, X3, WNil{})))), Z.app8(24n, Z.one8(), Z.app8(16n, Z.one8(), Z.app8(8n, Z.one8(), Z.app8(0n, Z.one8(), WNil{})))), Z.app8(24n, Z.h8(), Z.app8(16n, Z.h8(), Z.app8(8n, Z.h8(), Z.app8(0n, Z.h8(), WNil{})))), True{}), Z.app8(24n, Z.h8(), Z.app8(16n, Z.h8(), Z.app8(8n, Z.h8(), Word.zero(8n)))))), tkw3(X0, X1, X2, X3))

