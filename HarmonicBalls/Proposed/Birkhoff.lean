import Mathlib

/-!
# Pending pointwise ergodic theorem

This proposition records the exact statement of `LatticeProb.ae_tendsto_bAvg`
from `LatticeProb/Prob/Birkhoff.lean`. It is an explicit hypothesis until the
pinned LatticeProb module can be built (campaign issue E34).
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

end HarmonicBalls
