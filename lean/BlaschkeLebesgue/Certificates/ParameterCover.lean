module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

/-!
# A kernel-checkable cover of the closed completion parameter triangle

The checker bisects rational boxes. A terminal box must either be one of the
supplied boxes or have its lower corner strictly above `a+b=2/25`. The strict
test preserves the triangle boundary. No integral or derivative bounds are
part of this checker.
-/

@[expose] public section

namespace BlaschkeLebesgue.Certificates.ParameterCover

structure Box where
  aLo : ℚ
  aHi : ℚ
  bLo : ℚ
  bHi : ℚ
  deriving DecidableEq

def Box.Contains (q : Box) (a b : ℝ) : Prop :=
  (q.aLo : ℝ) ≤ a ∧ a ≤ (q.aHi : ℝ) ∧ (q.bLo : ℝ) ≤ b ∧ b ≤ (q.bHi : ℝ)

def Box.aMid (q : Box) : ℚ := (q.aLo + q.aHi) / 2
def Box.bMid (q : Box) : ℚ := (q.bLo + q.bHi) / 2
def Box.leftA (q : Box) : Box := {q with aHi := q.aMid}
def Box.rightA (q : Box) : Box := {q with aLo := q.aMid}
def Box.leftB (q : Box) : Box := {q with bHi := q.bMid}
def Box.rightB (q : Box) : Box := {q with bLo := q.bMid}

def root : Box := ⟨0, 2 / 25, 0, 2 / 25⟩

def Box.domainCheck (q : Box) : Bool :=
  decide (0 ≤ q.aLo ∧ q.aLo ≤ q.aHi ∧ 0 ≤ q.bLo ∧ q.bLo ≤ q.bHi ∧ q.aHi + q.bHi ≤ 17 / 200)

theorem Box.domainCheck_sound {q : Box} (h : q.domainCheck = true) {a b : ℝ} (hp : q.Contains a b) :
    0 ≤ a ∧ 0 ≤ b ∧ a + b ≤ 17 / 200 := by
  simp only [domainCheck, decide_eq_true_eq] at h
  have ha : (0 : ℝ) ≤ (q.aLo : ℝ) := (Rat.cast_nonneg (K := ℝ)).2 h.1
  have hb : (0 : ℝ) ≤ (q.bLo : ℝ) := (Rat.cast_nonneg (K := ℝ)).2 h.2.2.1
  have hab : (q.aHi : ℝ) + (q.bHi : ℝ) ≤ 17 / 200 := by
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).2 h.2.2.2.2
  exact ⟨ha.trans hp.1, hb.trans hp.2.2.1, (add_le_add hp.2.1 hp.2.2.2).trans hab⟩

inductive Tree where
  | accepted (index : ℕ)
  | outside
  | splitA (left right : Tree)
  | splitB (left right : Tree)

def check (boxes : List Box) (q : Box) : Tree → Bool
  | .accepted i => decide (boxes[i]? = some q)
  | .outside => decide (2 / 25 < q.aLo + q.bLo)
  | .splitA l r => check boxes q.leftA l && check boxes q.rightA r
  | .splitB l r => check boxes q.leftB l && check boxes q.rightB r

theorem check_sound {boxes : List Box} {q : Box} {tree : Tree} (h : check boxes q tree = true)
    {a b : ℝ} (hp : q.Contains a b) (hab : a + b ≤ 2 / 25) :
    ∃ c ∈ boxes, c.Contains a b := by
  induction tree generalizing q with
  | accepted i =>
    simp only [check, decide_eq_true_eq] at h
    exact ⟨q, List.mem_of_getElem? h, hp⟩
  | outside =>
    simp only [check, decide_eq_true_eq] at h
    have hr : (2 / 25 : ℝ) < (q.aLo : ℝ) + (q.bLo : ℝ) := by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_add] using (Rat.cast_lt (K := ℝ)).2 h
    exact False.elim (by linarith [hp.1, hp.2.2.1])
  | splitA l r ihl ihr =>
    simp only [check, Bool.and_eq_true] at h
    by_cases hm : a ≤ (q.aMid : ℝ)
    · exact ihl h.1 ⟨hp.1, hm, hp.2.2⟩
    · exact ihr h.2 ⟨(le_of_not_ge hm), hp.2.1, hp.2.2⟩
  | splitB l r ihl ihr =>
    simp only [check, Bool.and_eq_true] at h
    by_cases hm : b ≤ (q.bMid : ℝ)
    · exact ihl h.1 ⟨hp.1, hp.2.1, hp.2.2.1, hm⟩
    · exact ihr h.2 ⟨hp.1, hp.2.1, le_of_not_ge hm, hp.2.2.2⟩

theorem covers_triangle {boxes : List Box} {tree : Tree} (h : check boxes root tree = true)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 2 / 25) :
    ∃ c ∈ boxes, c.Contains a b := by
  apply check_sound h (hab := hab)
  norm_num only [Box.Contains, root, Rat.cast_zero, Rat.cast_div, Rat.cast_ofNat]
  exact ⟨ha, by linarith, hb, by linarith⟩

end BlaschkeLebesgue.Certificates.ParameterCover
