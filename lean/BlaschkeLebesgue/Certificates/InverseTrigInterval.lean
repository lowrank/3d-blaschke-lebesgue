module

public import BlaschkeLebesgue.Certificates.InverseTrigComputation
public import BlaschkeLebesgue.Certificates.FixedInterval
public import BlaschkeLebesgue.InverseTrigSeries

/-! # Sound inverse-trigonometric interval computations -/

public section

namespace BlaschkeLebesgue.Certificates.FixedPoint

theorem value_lt_one {p : ℕ} {a : ℤ} (ha : a < scale p) : value p a < 1 := by
  apply (div_lt_one (scale_real_pos p)).2
  exact_mod_cast ha

theorem neg_one_lt_value {p : ℕ} {a : ℤ} (ha : -(scale p : ℤ) < a) : -1 < value p a := by
  have h := value_lt_one (show -a < (scale p : ℤ) by omega)
  rw [value_neg] at h
  linarith

namespace Interval

theorem contains_point (p : ℕ) (a : ℤ) : (⟨a, a⟩ : Interval).Contains p (value p a) :=
  ⟨le_rfl, le_rfl⟩

theorem contains_atanHorner {p : ℕ} {I : Interval} {w : ℝ} (hw : I.Contains p w) (k n : ℕ) :
    (atanHorner p I k n).Contains p (InverseTrig.atanHorner w k n) := by
  induction n generalizing k with
  | zero => simpa [atanHorner, InverseTrig.atanHorner] using contains_integer p 0
  | succ n ih =>
    apply contains_add ?_ (contains_mul hw (ih (k + 1)))
    simpa only [Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_add, Int.cast_mul,
      Int.cast_ofNat, Int.cast_natCast] using contains_rational p ((-1) ^ k) (2 * k + 1)

theorem contains_atanNonnegPoint {p : ℕ} (n : ℕ) {a : ℤ} (ha : 0 ≤ a) (ha1 : a < scale p) :
    (atanNonnegPoint p n a).Contains p (Real.arctan (value p a)) := by
  have hA := contains_point p a
  have hW := contains_sq hA
  have hb := InverseTrig.atan_partial_bounds (value_nonneg ha) (value_lt_one ha1) n
  exact contains_span (contains_mul hA (contains_atanHorner hW 0 (2 * n)))
    (contains_mul hA (contains_atanHorner hW 0 (2 * n + 1))) hb.1 hb.2

theorem contains_atanPoint {p : ℕ} (n : ℕ) {a : ℤ}
    (ha : -(scale p : ℤ) < a) (ha1 : a < scale p) :
    (atanPoint p n a).Contains p (Real.arctan (value p a)) := by
  unfold atanPoint
  split_ifs with hneg
  · have h := contains_neg (contains_atanNonnegPoint (p := p) n (by omega : 0 ≤ -a) (by omega))
    simpa only [value_neg, Real.arctan_neg, neg_neg] using h
  · exact contains_atanNonnegPoint n (by omega) ha1

theorem contains_atan {p n : ℕ} {I : Interval} {x : ℝ}
    (hx : I.Contains p x) (hI : atanCheck p I = true) :
    (atan p n I).Contains p (Real.arctan x) := by
  have hord := contains_ordered hx
  simp only [atanCheck, decide_eq_true_eq] at hI
  exact contains_span (contains_atanPoint n hI.1 (by omega))
    (contains_atanPoint n (by omega) hI.2) (Real.arctan_mono hx.1) (Real.arctan_mono hx.2)

theorem checkedAtan_sound {p n : ℕ} {I J : Interval} {x : ℝ}
    (h : checkedAtan p n I = some J) (hx : I.Contains p x) : J.Contains p (Real.arctan x) := by
  unfold checkedAtan at h
  split_ifs at h with hI
  cases h
  exact contains_atan hx hI

theorem pi_sound {p n : ℕ} {I : Interval} (h : pi p n = some I) : I.Contains p Real.pi := by
  simp only [pi, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨a, ha, b, hb, rfl⟩ := h
  have ha' := checkedAtan_sound ha (contains_rational p 1 5)
  have hb' := checkedAtan_sound hb (contains_rational p 1 239)
  have h4 : (integer p 4).Contains p (4 : ℝ) := by exact_mod_cast contains_integer p 4
  have hv := contains_mul h4 (contains_sub (contains_mul h4 ha') hb')
  have hm := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  simp only [Int.cast_one, Int.cast_ofNat, one_div] at hv
  rw [hm] at hv
  convert hv using 1
  ring

theorem asin_sound {p n : ℕ} {I J : Interval} {x : ℝ}
    (h : asin p n I = some J) (hx : I.Contains p x) : J.Contains p (Real.arcsin x) := by
  dsimp only [asin] at h
  split_ifs at h with hq hd
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    have h1 : (integer p 1).Contains p (1 : ℝ) := by exact_mod_cast contains_integer p 1
    have h2 : (integer p 2).Contains p (2 : ℝ) := by exact_mod_cast contains_integer p 2
    have hQ := contains_sub h1 (contains_sq hx)
    have hQ0 := pos_of_positiveCheck hQ hq
    have hs : (sub (integer p 1) (sq p I)).sqrtCheck = true := by
      simpa only [sqrtCheck, decide_eq_true_eq] using
        (show 0 ≤ (sub (integer p 1) (sq p I)).lo from (of_decide_eq_true hq).le)
    have hD := contains_add h1 (contains_sqrt hQ hs)
    have hV := checkedAtan_sound hv (contains_div hx hD hd)
    rw [InverseTrig.arcsin_eq_two_arctan (by nlinarith : -1 < x) (by nlinarith : x < 1)]
    exact contains_mul h2 hV

theorem acos_sound {p n : ℕ} {I J : Interval} {x : ℝ}
    (h : acos p n I = some J) (hx : I.Contains p x) : J.Contains p (Real.arccos x) := by
  simp only [acos, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨P, hP, A, hA, rfl⟩ := h
  have hhalf : (rational p 1 2).Contains p (1 / 2 : ℝ) := by
    simpa only [Int.cast_one, Int.cast_ofNat] using contains_rational p 1 2
  have hv := contains_sub (contains_mul hhalf (pi_sound hP)) (asin_sound hA hx)
  rw [Real.arccos_eq_pi_div_two_sub_arcsin]
  convert hv using 1
  ring

end Interval
end BlaschkeLebesgue.Certificates.FixedPoint
