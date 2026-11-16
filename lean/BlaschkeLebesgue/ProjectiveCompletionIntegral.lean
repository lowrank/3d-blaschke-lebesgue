module

public import BlaschkeLebesgue.ProjectiveSphereIntegral
public import BlaschkeLebesgue.ProjectiveFourSigns

/-! # The completion chart integrand represents the actual spherical integral -/

public noncomputable section

open MeasureTheory Set

namespace BlaschkeLebesgue.ObliqueFrame

variable (f : ObliqueFrame)

theorem integral_projective_completion (D : ConvexBody Space) {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) :
    (∫ u in f.projectivePatch s, missingWidth D u * antipodalCompletionWeight D u ∂sphereMeasure) =
      ∫ q in s, projectiveCompletionIntegrand D f q.1 q.2 := by
  exact f.integral_projectivePatch hs (fun u ↦ missingWidth D u * antipodalCompletionWeight D u)

end BlaschkeLebesgue.ObliqueFrame
