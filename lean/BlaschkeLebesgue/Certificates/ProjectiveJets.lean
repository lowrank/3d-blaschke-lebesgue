module

public import BlaschkeLebesgue.Certificates.ProjectiveExpressions

/-! # Derivatives of the actual completion formulas from successful jet checks -/

@[expose] public noncomputable section

namespace BlaschkeLebesgue.Certificates.ProjectiveExpressions

open FixedPoint

def Params.ValidAt (f : ℝ → Params SecondOrder.Jet) (x : ℝ) : Prop :=
  SecondOrder.Jet.ValidAt (fun z ↦ (f z).ra) x ∧
  SecondOrder.Jet.ValidAt (fun z ↦ (f z).w) x ∧
  SecondOrder.Jet.ValidAt (fun z ↦ (f z).c) x ∧
  SecondOrder.Jet.ValidAt (fun z ↦ (f z).T) x

def Values.ValidAt (f : ℝ → Values SecondOrder.Jet) (x : ℝ) : Prop :=
  SecondOrder.Jet.ValidAt (fun z ↦ (f z).G) x ∧
  SecondOrder.Jet.ValidAt (fun z ↦ (f z).D) x ∧
  SecondOrder.Jet.ValidAt (fun z ↦ (f z).V) x

theorem parameterEnv_validAt {f g : ℝ → SecondOrder.Jet} {x : ℝ}
    (hf : SecondOrder.Jet.ValidAt f x) (hg : SecondOrder.Jet.ValidAt g x) :
    ∀ i, SecondOrder.Jet.ValidAt (fun z ↦ parameterEnv (f z) (g z) i) x := by
  intro i
  cases i with
  | zero => exact hf
  | succ i => exact hg

theorem integrandEnv_validAt {f : ℝ → Params SecondOrder.Jet} {s t : ℝ → SecondOrder.Jet} {x : ℝ}
    (hf : Params.ValidAt f x) (hs : SecondOrder.Jet.ValidAt s x) (ht : SecondOrder.Jet.ValidAt t x) :
    ∀ i, SecondOrder.Jet.ValidAt (fun z ↦ integrandEnv (f z) (s z) (t z) i) x := by
  intro i
  rcases i with _ | _ | _ | _ | _ | i
  · exact hf.1
  · exact hf.2.1
  · exact hf.2.2.1
  · exact hf.2.2.2
  · exact hs
  · exact ht

theorem paramsJet_validAt {p : ℕ} {a b : Jet} {out : Params Jet}
    {f g : ℝ → SecondOrder.Jet} {x : ℝ} (h : paramsJet p a b = some out)
    (ha : a.Contains p (f x)) (hb : b.Contains p (g x))
    (hf : SecondOrder.Jet.ValidAt f x) (hg : SecondOrder.Jet.ValidAt g x) :
    Params.ValidAt (fun z ↦ paramsRealJet (f z) (g z)) x := by
  simp only [paramsJet, Option.map_eq_some_iff] at h
  obtain ⟨env, he, rfl⟩ := h
  have hv := Program.jet_validAt he
    (parameterEnv_rel (R := fun (I : Jet) z ↦ I.Contains p z) ha hb) (parameterEnv_validAt hf hg)
  exact ⟨hv 1, hv 0, hv 7, hv 2⟩

theorem valuesJet_validAt {p : ℕ} {par : Params Jet} {s t : Jet} {out : Values Jet}
    {P : ℝ → Params SecondOrder.Jet} {S T : ℝ → SecondOrder.Jet} {x : ℝ}
    (h : valuesJet p par s t = some out) (hp : par.Rel (fun I z ↦ I.Contains p z) (P x))
    (hs : s.Contains p (S x)) (ht : t.Contains p (T x))
    (hP : Params.ValidAt P x) (hS : SecondOrder.Jet.ValidAt S x) (hT : SecondOrder.Jet.ValidAt T x) :
    Values.ValidAt (fun z ↦ valuesRealJet (P z) (S z) (T z)) x := by
  simp only [valuesJet, Option.map_eq_some_iff] at h
  obtain ⟨env, he, rfl⟩ := h
  have hv := Program.jet_validAt he (integrandEnv_rel hp hs ht) (integrandEnv_validAt hP hS hT)
  exact ⟨hv 3, hv 2, hv 0⟩

theorem Params.contains_const {p : ℕ} {I : Params Interval} {v : Params ℝ}
    (h : I.Rel (fun I x ↦ I.Contains p x) v) :
    (I.map (Jet.const p)).Rel (fun I x ↦ I.Contains p x) (v.map SecondOrder.Jet.const) :=
  ⟨Jet.contains_const h.1, Jet.contains_const h.2.1, Jet.contains_const h.2.2.1, Jet.contains_const h.2.2.2⟩

theorem Params.validAt_const (v : Params ℝ) (x : ℝ) :
    ValidAt (fun _ ↦ v.map SecondOrder.Jet.const) x :=
  ⟨SecondOrder.Jet.validAt_const v.ra x, SecondOrder.Jet.validAt_const v.w x,
    SecondOrder.Jet.validAt_const v.c x, SecondOrder.Jet.validAt_const v.T x⟩

theorem Params.map_const_v (v : Params ℝ) :
    (v.map SecondOrder.Jet.const).map SecondOrder.Jet.v = v := by
  cases v
  rfl

/-- The jet's value bounds apply to the actual gap, determinant lower bound,
and smooth density, rather than to a separate numerical surrogate. -/
theorem valuesJet_values_sound {p : ℕ} {par : Params Jet} {s t : Jet} {out : Values Jet}
    {P : Params SecondOrder.Jet} {S T : SecondOrder.Jet} {a b : ℝ}
    (h : valuesJet p par s t = some out) (hp : par.Rel (fun I z ↦ I.Contains p z) P)
    (hs : s.Contains p S) (ht : t.Contains p T) (hP : P.map SecondOrder.Jet.v = realParams a b) :
    (out.map Jet.v).Rel (fun I z ↦ I.Contains p z) (realValues a b S.v T.v) := by
  rw [← valuesRealJet_v hP S T]
  have hc := valuesJet_sound h hp hs ht
  exact ⟨hc.1.1, hc.2.1.1, hc.2.2.1⟩

/-- Specialize the input families to a constant or identity jet to obtain
any of the four pure derivatives used by quadrature and parameter variation. -/
theorem valuesJet_density_derivatives {p : ℕ} {par : Params Jet} {s t : Jet} {out : Values Jet}
    {P : ℝ → Params SecondOrder.Jet} {S T : ℝ → SecondOrder.Jet} {A B : ℝ → ℝ} {x : ℝ}
    (h : valuesJet p par s t = some out) (hp : par.Rel (fun I z ↦ I.Contains p z) (P x))
    (hs : s.Contains p (S x)) (ht : t.Contains p (T x))
    (hP : Params.ValidAt P x) (hS : SecondOrder.Jet.ValidAt S x) (hT : SecondOrder.Jet.ValidAt T x)
    (hPv : ∀ z, (P z).map SecondOrder.Jet.v = realParams (A z) (B z)) :
    HasDerivAt (fun z ↦ Completion.unitSquareSmoothDensity (A z) (B z) (S z).v (T z).v)
      (valuesRealJet (P x) (S x) (T x)).V.d x ∧
    HasDerivAt (fun z ↦ (valuesRealJet (P z) (S z) (T z)).V.d)
      (valuesRealJet (P x) (S x) (T x)).V.dd x ∧
    out.V.d.Contains p (valuesRealJet (P x) (S x) (T x)).V.d ∧
    out.V.dd.Contains p (valuesRealJet (P x) (S x) (T x)).V.dd := by
  have hv := (valuesJet_validAt h hp hs ht hP hS hT).2.2
  have hc := (valuesJet_sound h hp hs ht).2.2
  have he (z : ℝ) : (valuesRealJet (P z) (S z) (T z)).V.v =
      Completion.unitSquareSmoothDensity (A z) (B z) (S z).v (T z).v :=
    congrArg Values.V (valuesRealJet_v (hPv z) (S z) (T z))
  refine ⟨?_, hv.2, hc.2⟩
  simpa only [he] using hv.1

end BlaschkeLebesgue.Certificates.ProjectiveExpressions
