import Base
import ../defs.bend as D
import ../bytes.bend as B
import ../fast.bend as F

# fast.bend against bytes.bend on every range of a few buffers.

def of_list.go(xs: List<&2, U32>, b: D.Bytes) -> D.Bytes:
  match xs:
    case Nil{}:
      b
    case Con{x, t}:
      of_list.go(t, B.push(b, x))

def buf() -> List<&2, U32>:
  [97, 9, 98, 10, 9, 9, 99, 100, 101, 10, 120, 9, 121, 122, 10, 97, 98, 99, 9, 100, 10, 10]

def bytes() -> D.Bytes:
  of_list.go(buf(), B.empty(3n))

def find_ok(+i: U32, +j: U32, +c: U32) -> Bool:
  U32.is_eq(Pair.snd(D.Bytes, U32, F.find(bytes(), i, j, c)), Pair.snd(D.Bytes, U32, B.find(bytes(), i, j, c)))

def find2_ok(+i: U32, +j: U32) -> Bool:
  U32.is_eq(Pair.snd(D.Bytes, U32, F.find2(bytes(), i, j, 9, 10)), Pair.snd(D.Bytes, U32, B.find2(bytes(), i, j, 9, 10)))

def view_eq(a: D.Bytes, b: D.Bytes) -> Bool:
  D.list_eq(D.view(a), D.view(b))

# dst holds the first k bytes of buf; append n bytes from s.
def app_ok(+k: Nat, +s: U32, +n: U32) -> Bool:
  +d = {List.take(&2, U32, buf(), k) : List<&2, U32>}
  view_eq(Pair.fst(D.Bytes, D.Bytes, F.append(of_list.go(d, B.empty(4n)), bytes(), s, n)), Pair.fst(D.Bytes, D.Bytes, B.append(of_list.go(d, B.empty(4n)), bytes(), s, n)))

def all(xs: List<&2, Bool>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, t}:
      x && all(t)

def range(+n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      Con{U32.from_nat(m), range(m)}

def finds(+i: U32, js: List<&2, U32>) -> Bool:
  match js:
    case Nil{}:
      True{}
    case Con{+j, t}:
      find_ok(i, j, 10) && find_ok(i, j, 9) && find_ok(i, j, 122) && find2_ok(i, j) && finds(i, t)

def finds_all(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+i, t}:
      finds(i, range(23n)) && finds_all(t)

def apps(+k: Nat, ss: List<&2, U32>) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case Con{+s, t}:
      app_ok(k, s, 0) && app_ok(k, s, 1) && app_ok(k, s, 3) && app_ok(k, s, 5) && app_ok(k, s, 9) && apps(k, t)

def main() -> List<Bool>:
  [ finds_all(range(23n))
  , apps(0n, range(12n))
  , apps(1n, range(12n))
  , apps(2n, range(12n))
  , apps(3n, range(12n))
  , apps(4n, range(12n))
  , apps(7n, range(12n))
  ]
