import Base
import ../defs.bend as D
import ../bytes.bend as B

# Spot checks: both sides of laws on small examples.

def of_list.go(xs: List<&2, U32>, b: D.Bytes) -> D.Bytes:
  match xs:
    case Nil{}:
      b
    case Con{x, t}:
      of_list.go(t, B.push(b, x))

def of_list(b: D.Bytes, xs: List<&2, U32>) -> D.Bytes:
  of_list.go(xs, b)

# "ab\tcd\nxy": 97 98 9 99 100 10 120 121
def s1() -> D.Bytes:
  of_list(B.empty(2n), [97, 98, 9, 99, 100, 10, 120, 121])

def eql(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  D.list_eq(xs, ys)

def eqm(x: Maybe<&2, U32>, y: Maybe<&2, U32>) -> Bool:
  match x y:
    case Some{a} Some{b}:
      U32.is_eq(a, b)
    case None{} None{}:
      True{}
    case Some{a} None{}:
      False{}
    case None{} Some{b}:
      False{}

def sflag(r: D.Bytes & (D.Bytes & Bool)) -> Bool:
  Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, r))

# One byte, 65, with different padding in the rest of its word.
def pz() -> D.Bytes:
  D.Bytes{1, ALeaf{65}}

def pg() -> D.Bytes:
  D.Bytes{1, ALeaf{4294967105}}

def main() -> List<Bool>:
  [ eql(D.view(s1()), [97, 98, 9, 99, 100, 10, 120, 121])
  , Nat.is_eq(D.size(s1()), 8n)
  , Nat.is_eq(D.cap(s1()), 16n)
  , D.ok(s1(), 2n)
  , eql(D.view(B.empty(3n)), [])
  , eqm(Some{Pair.snd(D.Bytes, U32, B.at(s1(), 4))}, List.get(&2, U32, D.view(s1()), 4n))
  , eqm(Some{Pair.snd(D.Bytes, U32, B.at(s1(), 7))}, Some{121})
  , Nat.is_eq(U32.to_nat(Pair.snd(D.Bytes, U32, B.find(s1(), 0, 8, 10))), D.first(D.view(s1()), 0n, 8n, 10))
  , Nat.is_eq(U32.to_nat(Pair.snd(D.Bytes, U32, B.find(s1(), 0, 8, 10))), 5n)
  , Nat.is_eq(U32.to_nat(Pair.snd(D.Bytes, U32, B.find(s1(), 6, 8, 10))), 8n)
  , Nat.is_eq(U32.to_nat(Pair.snd(D.Bytes, U32, B.find(s1(), 3, 3, 10))), 3n)
  , Nat.is_eq(U32.to_nat(Pair.snd(D.Bytes, U32, B.find(s1(), 0, 4, 10))), 4n)
  , Nat.is_eq(U32.to_nat(Pair.snd(D.Bytes, U32, B.find2(s1(), 0, 8, 9, 10))), 2n)
  , Nat.is_eq(U32.to_nat(Pair.snd(D.Bytes, U32, B.find2(s1(), 3, 8, 9, 10))), D.first2(D.view(s1()), 3n, 8n, 9, 10))
  , sflag(B.same(s1(), 3, of_list(B.empty(1n), [99, 100]), 0, 2))
  , Bool.not(sflag(B.same(s1(), 3, of_list(B.empty(1n), [99, 101]), 0, 2)))
  , sflag(B.same(s1(), 3, B.empty(0n), 0, 0))
  , eql(D.view(B.set(s1(), 2, 32)), List.set(&2, U32, D.view(s1()), 2n, 32))
  , eql(D.view(B.push(s1(), 33)), List.append(&2, U32, D.view(s1()), [33]))
  , eql(D.view(Pair.fst(D.Bytes, D.Bytes, B.append(of_list(B.empty(2n), [1, 2]), s1(), 3, 4))), [1, 2, 99, 100, 10, 120])
  , eql(D.view(Pair.fst(D.Bytes, D.Bytes, B.append(of_list(B.empty(2n), [1, 2, 3]), s1(), 1, 5))), [1, 2, 3, 98, 9, 99, 100, 10])
  , eql(D.view(B.grow(s1(), 4n)), D.view(s1()))
  , D.ok(B.grow(s1(), 4n), 4n)
  , eql(D.view(Pair.fst(D.Bytes, U32, B.find(s1(), 1, 7, 99))), D.view(s1()))
    , sflag(B.same(pz(), 0, pg(), 0, 1))
  , Nat.is_eq(U32.to_nat(Pair.snd(D.Bytes, U32, B.find(pz(), 0, 1, 0))), 1n)
  , Nat.is_eq(U32.to_nat(Pair.snd(D.Bytes, U32, B.find(pg(), 0, 1, 255))), 1n)
  , eql(D.view(pg()), [65])
  , Nat.is_eq(U32.to_nat(Pair.snd(D.Bytes, U32, B.find(s1(), 8, 8, 10))), 8n)
  , eql(D.view(B.set(s1(), 7, 0)), List.set(&2, U32, D.view(s1()), 7n, 0))
  , eql(D.view(Pair.fst(D.Bytes, D.Bytes, B.append(s1(), pz(), 0, 0))), D.view(s1()))
  , Nat.is_eq(U32.to_nat(Pair.snd(D.Bytes, U32, B.len(s1()))), 8n)
  , Nat.is_eq(U32.to_nat(Pair.snd(D.Bytes, U32, B.capacity(s1()))), 16n)
  , eql(D.view(B.truncate(s1(), 3)), [97, 98, 9])
  , eql(D.view(B.shift(s1(), 3)), [99, 100, 10, 120, 121])
  , eql(D.view(B.shift(s1(), 0)), D.view(s1()))
  , eql(D.view(B.shift(s1(), 8)), [])
  , eql(D.view(B.of_list(1n, [5, 6, 7, 8, 9])), [5, 6, 7, 8, 9])
  , eql(Pair.snd(D.Bytes, List<&2, U32>, B.to_list(s1(), 2, 3)), [9, 99, 100])
  , Pair.snd(D.Bytes, Bool, B.same1(of_list(B.empty(2n), [1, 2, 3, 1, 2, 4]), 0, 3, 2))
  , Bool.not(Pair.snd(D.Bytes, Bool, B.same1(of_list(B.empty(2n), [1, 2, 3, 1, 2, 4]), 0, 3, 3)))
  , D.has(D.view(s1()), D.first(D.view(s1()), 0n, 8n, 10), 10)
  , Bool.not(D.has(D.view(s1()), 4n, 10))
  , D.has2(D.view(s1()), 2n, 9, 10)
  ]
