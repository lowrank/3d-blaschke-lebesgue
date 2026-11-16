module

public import BlaschkeLebesgue.Certificates.FixedPointRounding

/-!
# Sound fixed-dyadic interval arithmetic

An interval stores integer endpoints at the common scale `2^precision`.
Every operation is executable integer arithmetic. Its soundness theorem
encloses the actual real operation; reciprocal and root operations explicitly
require their domain checks. No machine overflow or external oracle is used.
-/

@[expose] public section

namespace BlaschkeLebesgue.Certificates.FixedPoint

theorem value_zero (p : ℕ) : value p 0 = 0 := by simp [value]
theorem value_add (p : ℕ) (a b : ℤ) : value p (a + b) = value p a + value p b := by simp [value, add_div]
theorem value_neg (p : ℕ) (a : ℤ) : value p (-a) = -value p a := by simp [value, neg_div]
theorem value_sub (p : ℕ) (a b : ℤ) : value p (a - b) = value p a - value p b := by simp [value, sub_div]
theorem value_mono (p : ℕ) : Monotone (value p) := by
  intro a b h
  exact div_le_div_of_nonneg_right (show (a : ℝ) ≤ (b : ℝ) by exact_mod_cast h) (scale_real_pos p).le
theorem value_min (p : ℕ) (a b : ℤ) : value p (min a b) = min (value p a) (value p b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (value_mono p h)]
  · rw [min_eq_right h, min_eq_right (value_mono p h)]
theorem value_max (p : ℕ) (a b : ℤ) : value p (max a b) = max (value p a) (value p b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (value_mono p h)]
  · rw [max_eq_left h, max_eq_left (value_mono p h)]
theorem value_nonneg {p : ℕ} {a : ℤ} (ha : 0 ≤ a) : 0 ≤ value p a :=
  div_nonneg (by exact_mod_cast ha) (scale_real_pos p).le
theorem value_pos {p : ℕ} {a : ℤ} (ha : 0 < a) : 0 < value p a :=
  div_pos (by exact_mod_cast ha) (scale_real_pos p)
theorem value_neg_of_neg {p : ℕ} {a : ℤ} (ha : a < 0) : value p a < 0 :=
  div_neg_of_neg_of_pos (by exact_mod_cast ha) (scale_real_pos p)

theorem mul_interval_bounds {a b c d x y : ℝ} (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y ∧
      x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  have hf {l r z u : ℝ} (hu : l ≤ u ∧ u ≤ r) :
      min (l * z) (r * z) ≤ u * z ∧ u * z ≤ max (l * z) (r * z) := by
    by_cases hz : 0 ≤ z
    · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right hu.1 hz),
        (mul_le_mul_of_nonneg_right hu.2 hz).trans (le_max_right _ _)⟩
    · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hu.2 (le_of_not_ge hz)),
        (mul_le_mul_of_nonpos_right hu.1 (le_of_not_ge hz)).trans (le_max_left _ _)⟩
  have ha := hf (z := a) hy
  have hb := hf (z := b) hy
  simp only [mul_comm c, mul_comm d, mul_comm y] at ha hb
  have hxy := hf (z := y) hx
  exact ⟨(le_min ((min_le_left _ _).trans ha.1) ((min_le_right _ _).trans hb.1)).trans hxy.1,
    hxy.2.trans (max_le (ha.2.trans (le_max_left _ _)) (hb.2.trans (le_max_right _ _)))⟩

structure Interval where
  lo : ℤ
  hi : ℤ
  deriving DecidableEq, Inhabited

namespace Interval

def Contains (I : Interval) (p : ℕ) (x : ℝ) : Prop := value p I.lo ≤ x ∧ x ≤ value p I.hi

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
  ⟨sqrtFloor (I.lo * scale p), sqrtCeil (I.hi * scale p)⟩
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

theorem contains_ordered {I : Interval} {p : ℕ} {x : ℝ} (hx : I.Contains p x) : I.lo ≤ I.hi := by
  have h := (div_le_div_iff_of_pos_right (scale_real_pos p)).1 (hx.1.trans hx.2)
  exact_mod_cast h

theorem nonneg_of_sqrtCheck {I : Interval} {p : ℕ} {x : ℝ} (hx : I.Contains p x) (hI : sqrtCheck I = true) :
    0 ≤ x := (value_nonneg (of_decide_eq_true hI)).trans hx.1

theorem pos_of_positiveCheck {I : Interval} {p : ℕ} {x : ℝ} (hx : I.Contains p x) (hI : positiveCheck I = true) :
    0 < x := (value_pos (of_decide_eq_true hI)).trans_le hx.1

theorem ne_zero_of_invCheck {I : Interval} {p : ℕ} {x : ℝ} (hx : I.Contains p x) (hI : invCheck I = true) :
    x ≠ 0 := by
  simp only [invCheck, decide_eq_true_eq] at hI
  rcases hI with h | h
  · exact ((value_pos h).trans_le hx.1).ne'
  · exact (hx.2.trans_lt (value_neg_of_neg h)).ne

theorem contains_integer (p : ℕ) (a : ℤ) : (integer p a).Contains p (a : ℝ) := by
  have hS := (scale_real_pos p).ne'
  simp only [Contains, integer, value, Int.cast_mul, Int.cast_natCast, mul_div_cancel_right₀ _ hS, le_refl, and_self]

theorem contains_rational (p : ℕ) (a b : ℤ) : (rational p a b).Contains p ((a : ℝ) / (b : ℝ)) := by
  have hS := (scale_real_pos p).ne'
  have heq : (((a * scale p : ℤ) : ℝ) / (b : ℝ)) / (scale p : ℝ) = (a : ℝ) / (b : ℝ) := by
    simp only [Int.cast_mul, Int.cast_natCast]
    rw [div_right_comm, mul_div_cancel_right₀ _ hS]
  exact ⟨(floorDiv_value_le p _ _).trans_eq heq, heq.symm.trans_le (value_le_ceilDiv p _ _)⟩

theorem contains_span {I J : Interval} {p : ℕ} {x y z : ℝ}
    (hx : I.Contains p x) (hy : J.Contains p y) (hxz : x ≤ z) (hzy : z ≤ y) :
    (span I J).Contains p z := ⟨hx.1.trans hxz, hzy.trans hy.2⟩

theorem contains_neg {I : Interval} {p : ℕ} {x : ℝ} (hx : I.Contains p x) : (neg I).Contains p (-x) := by
  simpa only [Contains, neg, value_neg, neg_le_neg_iff] using And.intro hx.2 hx.1

theorem contains_add {I J : Interval} {p : ℕ} {x y : ℝ} (hx : I.Contains p x) (hy : J.Contains p y) :
    (add I J).Contains p (x + y) := by
  simpa only [Contains, add, value_add] using And.intro (add_le_add hx.1 hy.1) (add_le_add hx.2 hy.2)

theorem contains_sub {I J : Interval} {p : ℕ} {x y : ℝ} (hx : I.Contains p x) (hy : J.Contains p y) :
    (sub I J).Contains p (x - y) := by
  simpa only [sub, sub_eq_add_neg] using contains_add hx (contains_neg hy)

theorem contains_mul {I J : Interval} {p : ℕ} {x y : ℝ} (hx : I.Contains p x) (hy : J.Contains p y) :
    (mul p I J).Contains p (x * y) := by
  have hS := scale_real_pos p
  have hx' : (I.lo : ℝ) ≤ x * (scale p : ℝ) ∧ x * (scale p : ℝ) ≤ (I.hi : ℝ) :=
    ⟨(div_le_iff₀ hS).1 hx.1, (le_div_iff₀ hS).1 hx.2⟩
  have hy' : (J.lo : ℝ) ≤ y * (scale p : ℝ) ∧ y * (scale p : ℝ) ≤ (J.hi : ℝ) :=
    ⟨(div_le_iff₀ hS).1 hy.1, (le_div_iff₀ hS).1 hy.2⟩
  have hc := mul_interval_bounds hx' hy'
  constructor
  · apply (floorDiv_scale_value_le p _).trans
    apply (div_le_iff₀ (sq_pos_of_pos hS)).2
    simp only [Int.cast_min, Int.cast_mul]
    convert hc.1 using 1; ring
  · apply le_trans _ (value_le_ceilDiv_scale p _)
    apply (le_div_iff₀ (sq_pos_of_pos hS)).2
    simp only [Int.cast_max, Int.cast_mul]
    convert hc.2 using 1; ring

theorem contains_inv {I : Interval} {p : ℕ} {x : ℝ} (hx : I.Contains p x) (hI : invCheck I = true) :
    (inv p I).Contains p x⁻¹ := by
  have hS := (scale_real_pos p).ne'
  have heq (z : ℤ) : (((scale p : ℤ) ^ 2 : ℤ) : ℝ) / (z : ℝ) / (scale p : ℝ) = (value p z)⁻¹ := by
    simp only [value, pow_two, Int.cast_mul, Int.cast_natCast, inv_div]
    rw [div_right_comm, mul_div_cancel_right₀ _ hS]
  have hlow := floorDiv_value_le p ((scale p : ℤ) ^ 2) I.hi
  have hupp := value_le_ceilDiv p ((scale p : ℤ) ^ 2) I.lo
  rw [heq] at hlow hupp
  simp only [invCheck, decide_eq_true_eq] at hI
  rcases hI with hpos | hneg
  · have hlo : 0 < value p I.lo := value_pos hpos
    have hx0 : 0 < x := hlo.trans_le hx.1
    exact ⟨hlow.trans (inv_anti₀ hx0 hx.2), (inv_anti₀ hlo hx.1).trans hupp⟩
  · have hhi : value p I.hi < 0 := value_neg_of_neg hneg
    have hx0 : x < 0 := hx.2.trans_lt hhi
    exact ⟨hlow.trans ((inv_le_inv_of_neg hhi hx0).2 hx.2),
      ((inv_le_inv_of_neg hx0 (hx.1.trans_lt hx0)).2 hx.1).trans hupp⟩

theorem contains_div {I J : Interval} {p : ℕ} {x y : ℝ} (hx : I.Contains p x) (hy : J.Contains p y)
    (hJ : invCheck J = true) : (div p I J).Contains p (x / y) := by
  simpa only [div, div_eq_mul_inv] using contains_mul hx (contains_inv hy hJ)

theorem contains_sqrt {I : Interval} {p : ℕ} {x : ℝ} (hx : I.Contains p x) (hI : sqrtCheck I = true) :
    (sqrt p I).Contains p (Real.sqrt x) := by
  simp only [sqrtCheck, decide_eq_true_eq] at hI
  have horder := contains_ordered hx
  exact ⟨(sqrtFloor_value_le_sqrt hI p).trans (Real.sqrt_le_sqrt hx.1),
    (Real.sqrt_le_sqrt hx.2).trans (sqrt_le_sqrtCeil_value (hI.trans horder) p)⟩

/-- Squaring an interval crossing zero has exact lower endpoint zero. -/
theorem contains_sq {I : Interval} {p : ℕ} {x : ℝ} (hx : I.Contains p x) :
    (sq p I).Contains p (x ^ 2) := by
  unfold sq
  split_ifs
  · simpa only [pow_two] using contains_mul hx hx
  · simpa only [mul_neg, neg_mul, neg_neg, pow_two] using contains_mul (contains_neg hx) (contains_neg hx)
  · refine ⟨?_, ?_⟩
    · simpa only [value_zero] using sq_nonneg x
    · apply le_trans _ (value_le_ceilDiv_scale p _)
      have hS := scale_real_pos p
      have hlo : (I.lo : ℝ) ≤ x * (scale p : ℝ) := (div_le_iff₀ hS).1 hx.1
      have hhi : x * (scale p : ℝ) ≤ (I.hi : ℝ) := (le_div_iff₀ hS).1 hx.2
      have hsq : (x * (scale p : ℝ)) ^ 2 ≤ max ((I.lo : ℝ) ^ 2) ((I.hi : ℝ) ^ 2) := by
        by_cases hsign : 0 ≤ x * (scale p : ℝ)
        · exact (pow_le_pow_left₀ hsign hhi 2).trans (le_max_right _ _)
        · have hn : (x * (scale p : ℝ)) ^ 2 ≤ (I.lo : ℝ) ^ 2 := by
            have hp := mul_nonneg (sub_nonneg.mpr hlo)
              (show 0 ≤ -((I.lo : ℝ) + x * (scale p : ℝ)) by linarith)
            nlinarith only [hp]
          exact hn.trans (le_max_left _ _)
      apply (le_div_iff₀ (sq_pos_of_pos hS)).2
      rw [mul_pow] at hsq
      simpa only [Int.cast_max, Int.cast_mul, pow_two] using hsq

theorem contains_pos {I : Interval} {p : ℕ} {x : ℝ} (hx : I.Contains p x) :
    (pos I).Contains p (max x 0) := by
  simp only [Contains, pos, value_max, value_zero]
  exact ⟨max_le (le_max_right _ _) (hx.1.trans (le_max_left _ _)),
    max_le (hx.2.trans (le_max_right _ _)) (le_max_left _ _)⟩

theorem contains_hullzero {I : Interval} {p : ℕ} {x : ℝ} (hx : I.Contains p x) :
    (hullzero I).Contains p x := by
  simp only [Contains, hullzero, value_min, value_max, value_zero]
  exact ⟨(min_le_right _ _).trans hx.1, hx.2.trans (le_max_right _ _)⟩

theorem contains_hullzero_zero (I : Interval) (p : ℕ) : (hullzero I).Contains p 0 := by
  simp only [Contains, hullzero, value_min, value_max, value_zero]
  exact ⟨min_le_left _ _, le_max_left _ _⟩

theorem abs_le_absMax {I : Interval} {p : ℕ} {x : ℝ} (hx : I.Contains p x) : |x| ≤ value p I.absMax := by
  rw [absMax, value_max, value_neg]
  exact abs_le.2 ⟨by linarith [le_max_left (-value p I.lo) (value p I.hi), hx.1],
    hx.2.trans (le_max_right _ _)⟩

end Interval
end BlaschkeLebesgue.Certificates.FixedPoint
