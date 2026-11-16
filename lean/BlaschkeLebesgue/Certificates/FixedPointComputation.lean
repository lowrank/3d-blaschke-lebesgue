module

public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Int.Notation

/-!
# Executable fixed-point arithmetic

This file contains the integer computations and data structures only. Their
real containment and derivative theorems are proved in the soundness modules.
Keeping this layer independent of analysis reduces certificate-check memory.
-/

@[expose] public section

namespace BlaschkeLebesgue.Certificates.FixedPoint

def scale (precision : ℕ) : ℕ := 2 ^ precision

def floorDiv (a b : ℤ) : ℤ := if 0 ≤ b then a / b else (-a) / (-b)
def ceilDiv (a b : ℤ) : ℤ := -floorDiv (-a) b

def sqrtFloor (a : ℤ) : ℤ := a.toNat.sqrt
def sqrtCeil (a : ℤ) : ℤ := let r := sqrtFloor a; if r * r = a then r else r + 1

def newtonProposal : ℕ → ℕ → ℕ → ℕ
  | 0, _, guess => guess
  | fuel + 1, n, guess =>
    let next := (guess + n / guess) / 2
    if next < guess then newtonProposal fuel n next else guess

def checkedNatSqrt (p n : ℕ) : ℕ :=
  let r := newtonProposal 12 n (2 ^ (p + 2))
  if r * r ≤ n ∧ n < (r + 1) * (r + 1) then r else Nat.sqrt n

def checkedSqrtFloor (p : ℕ) (a : ℤ) : ℤ := checkedNatSqrt p a.toNat
def checkedSqrtCeil (p : ℕ) (a : ℤ) : ℤ :=
  let r := checkedSqrtFloor p a
  if r * r = a then r else r + 1

structure Interval where
  lo : ℤ
  hi : ℤ
  deriving DecidableEq, Inhabited

namespace Interval

def integer (p : ℕ) (a : ℤ) : Interval := ⟨a * scale p, a * scale p⟩
def rational (p : ℕ) (a b : ℤ) : Interval :=
  ⟨floorDiv (a * scale p) b, ceilDiv (a * scale p) b⟩
def span (I J : Interval) : Interval := ⟨I.lo, J.hi⟩
def neg (I : Interval) : Interval := ⟨-I.hi, -I.lo⟩
def add (I J : Interval) : Interval := ⟨I.lo + J.lo, I.hi + J.hi⟩
def sub (I J : Interval) : Interval := add I (neg J)
def mul (p : ℕ) (I J : Interval) : Interval :=
  ⟨floorDiv (min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi))) (scale p),
    ceilDiv (max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))) (scale p)⟩
def inv (p : ℕ) (I : Interval) : Interval :=
  ⟨floorDiv ((scale p : ℤ) ^ 2) I.hi, ceilDiv ((scale p : ℤ) ^ 2) I.lo⟩
def div (p : ℕ) (I J : Interval) : Interval := mul p I (inv p J)
def sqrt (p : ℕ) (I : Interval) : Interval :=
  ⟨checkedSqrtFloor p (I.lo * scale p), checkedSqrtCeil p (I.hi * scale p)⟩
def sq (p : ℕ) (I : Interval) : Interval :=
  if 0 ≤ I.lo then mul p I I
  else if I.hi ≤ 0 then mul p (neg I) (neg I)
  else ⟨0, ceilDiv (max (I.lo * I.lo) (I.hi * I.hi)) (scale p)⟩
def pos (I : Interval) : Interval := ⟨max 0 I.lo, max 0 I.hi⟩
def hullzero (I : Interval) : Interval := ⟨min 0 I.lo, max 0 I.hi⟩
def absMax (I : Interval) : ℤ := max (-I.lo) I.hi
def invCheck (I : Interval) : Bool := decide (0 < I.lo ∨ I.hi < 0)
def sqrtCheck (I : Interval) : Bool := decide (0 ≤ I.lo)
def positiveCheck (I : Interval) : Bool := decide (0 < I.lo)

end Interval

structure Jet where
  v : Interval
  d : Interval
  dd : Interval
  deriving DecidableEq, Inhabited

namespace Jet

def const (p : ℕ) (v : Interval) : Jet := ⟨v, Interval.integer p 0, Interval.integer p 0⟩
def var (p : ℕ) (v : Interval) : Jet := ⟨v, Interval.integer p 1, Interval.integer p 0⟩
def neg (a : Jet) : Jet := ⟨a.v.neg, a.d.neg, a.dd.neg⟩
def add (a b : Jet) : Jet := ⟨a.v.add b.v, a.d.add b.d, a.dd.add b.dd⟩
def sub (a b : Jet) : Jet := add a b.neg
def mul (p : ℕ) (a b : Jet) : Jet :=
  ⟨Interval.mul p a.v b.v,
    (Interval.mul p a.d b.v).add (Interval.mul p a.v b.d),
    ((Interval.mul p a.dd b.v).add (Interval.mul p (Interval.mul p (Interval.integer p 2) a.d) b.d)).add
      (Interval.mul p a.v b.dd)⟩
def sq (p : ℕ) (a : Jet) : Jet :=
  ⟨Interval.sq p a.v, Interval.mul p (Interval.mul p (Interval.integer p 2) a.v) a.d,
    Interval.mul p (Interval.integer p 2) ((Interval.sq p a.d).add (Interval.mul p a.v a.dd))⟩
def comp (p : ℕ) (a : Jet) (v d dd : Interval) : Jet :=
  ⟨v, Interval.mul p d a.d, (Interval.mul p dd (Interval.sq p a.d)).add (Interval.mul p d a.dd)⟩
def inv (p : ℕ) (a : Jet) : Jet :=
  let v := Interval.inv p a.v
  comp p a v (Interval.sq p v).neg (Interval.mul p (Interval.mul p (Interval.integer p 2) v) (Interval.sq p v))
def div (p : ℕ) (a b : Jet) : Jet := mul p a (inv p b)
def sqrtDenom1 (p : ℕ) (a : Jet) : Interval := Interval.mul p (Interval.integer p 2) (Interval.sqrt p a.v)
def sqrtDenom2 (p : ℕ) (a : Jet) : Interval :=
  let v := Interval.sqrt p a.v
  Interval.mul p (Interval.mul p (Interval.integer p 4) (Interval.sq p v)) v
def sqrt (p : ℕ) (a : Jet) : Jet :=
  comp p a (Interval.sqrt p a.v) (Interval.div p (Interval.integer p 1) (sqrtDenom1 p a))
    (Interval.div p (Interval.integer p (-1)) (sqrtDenom2 p a))
def sqrtCheck (p : ℕ) (a : Jet) : Bool :=
  a.v.positiveCheck && (sqrtDenom1 p a).invCheck && (sqrtDenom2 p a).invCheck

end Jet

end BlaschkeLebesgue.Certificates.FixedPoint
