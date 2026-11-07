import LatticeProb.Prob.Birkhoff

/-!
# Pointwise ergodic theorem (Birkhoff)

This proposition records the exact statement of `LatticeProb.ae_tendsto_bAvg`
from `LatticeProb/Prob/Birkhoff.lean` (Leonardo Bonanno's LatticeProb formalization).
The named proposition is proved below from the pinned LatticeProb module;
it is not a literature assumption.
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology

/-- Birkhoff's pointwise ergodic theorem for an integrable real function on a
finite measure space. The average is definitionally the LatticeProb `bAvg`. -/
def PointwiseBirkhoff {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (T : Ω → Ω) (f : Ω → ℝ) : Prop :=
  MeasurePreserving T μ μ → Measurable f → Integrable f μ →
    ∀ᵐ x ∂μ, ∃ L : ℝ,
      Tendsto (fun n => birkhoffSum T f n x / n) atTop (𝓝 L)

/-- The pointwise ergodic theorem for finite measures, proved in LatticeProb. -/
theorem pointwiseBirkhoff_of_latticeProb {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (T : Ω → Ω) (f : Ω → ℝ) :
    PointwiseBirkhoff P T f := by
  intro hT hf hi
  exact LatticeProb.ae_tendsto_bAvg hT hf hi

end HarmonicBalls
