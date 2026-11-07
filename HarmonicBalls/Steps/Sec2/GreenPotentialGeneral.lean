import HarmonicBalls.Draft.Section2
import HarmonicBalls.Defs.Obstacle

/-!
# General-domain Green potential estimate

The deterministic step in the proof of Proposition 2.5, paper lines 533–537:
local power-law volume growth and local finiteness imply absolute convergence
and Hölder continuity of bounded-density Green potentials on the closure of
every smooth bounded open set. The paper cites Ponce, Section 16.2 and the
remark after Proposition 13.5, for the Campanato embedding. This step also
includes the general-domain Green-function and boundary estimates needed to
apply that argument. It is an unproved mathematical step, not a literature
input. The existing disc estimate is proved in
`Proofs/Potential/GreenPotentialHolder.lean`.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped ENNReal NNReal

/-- Deterministic general-domain portion of the Green clause of Proposition 2.5. -/
def GreenPotentialGeneralStep : Prop :=
  ∀ μ : Measure ℂ, IsLocallyFiniteMeasure μ →
    (∀ R : ℝ, 0 < R → ∃ βminus βplus : ℝ, VolumeGrowth μ R βminus βplus) →
    ∀ O : Set ℂ, IsSmoothBoundedOpen O →
    ∀ f : ℂ → ℝ, MemLp f ⊤ (μ.restrict (closure O)) →
      (∀ x ∈ closure O, IntegrableOn (fun y => greenFunction O x y * f y) O μ) ∧
      ∃ C r : ℝ≥0, 0 < r ∧
        HolderOnWith C r (fun x => ∫ y in O, greenFunction O x y * f y ∂μ) (closure O)

end HarmonicBalls
