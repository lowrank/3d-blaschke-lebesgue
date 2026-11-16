module

public import BlaschkeLebesgue.Certificates.FixedPointComputation

/-! # Executable inverse-trigonometric interval arithmetic

All operations use integers and directed rounding. `n` selects an even/odd
pair of arctangent partial sums. The soundness proofs are in a separate module.
-/

@[expose] public section

namespace BlaschkeLebesgue.Certificates.FixedPoint.Interval

def atanHorner (p : ℕ) (w : Interval) (k : ℕ) : ℕ → Interval
  | 0 => integer p 0
  | n + 1 => add (rational p ((-1) ^ k) (2 * k + 1))
      (mul p w (atanHorner p w (k + 1) n))

def atanNonnegPoint (p n : ℕ) (a : ℤ) : Interval :=
  let A : Interval := ⟨a, a⟩
  let w := sq p A
  span (mul p A (atanHorner p w 0 (2 * n)))
    (mul p A (atanHorner p w 0 (2 * n + 1)))

def atanPoint (p n : ℕ) (a : ℤ) : Interval :=
  if a < 0 then neg (atanNonnegPoint p n (-a)) else atanNonnegPoint p n a

def atan (p n : ℕ) (I : Interval) : Interval :=
  span (atanPoint p n I.lo) (atanPoint p n I.hi)

def atanCheck (p : ℕ) (I : Interval) : Bool :=
  decide (-(scale p : ℤ) < I.lo ∧ I.hi < scale p)

def checkedAtan (p n : ℕ) (I : Interval) : Option Interval :=
  if atanCheck p I then some (atan p n I) else none

def pi (p n : ℕ) : Option Interval :=
  (checkedAtan p n (rational p 1 5)).bind fun a ↦
    (checkedAtan p n (rational p 1 239)).map fun b ↦
      mul p (integer p 4) (sub (mul p (integer p 4) a) b)

def asin (p n : ℕ) (I : Interval) : Option Interval :=
  let q := sub (integer p 1) (sq p I)
  if q.positiveCheck then
    let d := add (integer p 1) (sqrt p q)
    if d.invCheck then
      (checkedAtan p n (div p I d)).map (mul p (integer p 2))
    else none
  else none

def acos (p n : ℕ) (I : Interval) : Option Interval :=
  (pi p n).bind fun vpi ↦
    (asin p n I).map fun v ↦ sub (mul p (rational p 1 2) vpi) v

end BlaschkeLebesgue.Certificates.FixedPoint.Interval

namespace BlaschkeLebesgue.Certificates.FixedPoint.Jet

def atan (p n : ℕ) (a : Jet) : Option Jet :=
  (Interval.checkedAtan p n a.v).bind fun v ↦
    let w := Interval.add (Interval.integer p 1) (Interval.sq p a.v)
    if w.invCheck then
      let d := Interval.inv p w
      some (comp p a v d
        (Interval.mul p (Interval.mul p (Interval.integer p (-2)) a.v) (Interval.sq p d)))
    else none

def asin (p n : ℕ) (a : Jet) : Option Jet :=
  (Interval.asin p n a.v).bind fun v ↦
    let q := Interval.sub (Interval.integer p 1) (Interval.sq p a.v)
    let r := Interval.sqrt p q
    if q.positiveCheck && r.invCheck then
      let d := Interval.inv p r
      some (comp p a v d (Interval.mul p a.v (Interval.mul p d (Interval.sq p d))))
    else none

def acos (p n : ℕ) (a : Jet) : Option Jet :=
  (Interval.pi p n).bind fun P ↦
    (asin p n a).map fun v ↦ sub (const p (Interval.mul p (Interval.rational p 1 2) P)) v

end BlaschkeLebesgue.Certificates.FixedPoint.Jet
