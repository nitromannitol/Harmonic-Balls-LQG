import HarmonicBalls.Proofs.Sec6.ScaleUniformRelativeCollar

/-! # Probability bounds for nearby good-annulus transfer

The deterministic scale-uniform modulus bounds a transfer failure by the
relative collar-mass failure and the exceptional annulus-mass events. The
measure on configurations may be a rooted law; no recentering law is assumed.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set Metric
open scoped ENNReal

/-- At a positive deterministic radius, the probability that transfer fails at
some nearby centre is bounded by the relative
collar failure probability and the zero- or infinite-mass probabilities. -/
theorem exists_scale_uniform_goodAnnulus_transfer_failure_le
    {κ : ℝ} (hκ : 0 < κ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
      (μ : Ω → Measure ℂ) (z : Ω → ℂ) (r : ℝ), 0 < r →
      ∀ a a' amid b b' : ℝ, ∀ d : ℝ≥0∞,
      ENNReal.ofReal b + 2 * ε + ε ≤ ENNReal.ofReal b' →
      ENNReal.ofReal amid < ENNReal.ofReal a →
      ENNReal.ofReal a' + (ENNReal.ofReal a' + 1) * d ≤ ENNReal.ofReal amid →
      P {ω | IsGoodAnnulus (μ ω) r (z ω) a b ∧
        ∃ w : ℂ, dist w (z ω) < δ*r ∧
          ¬ IsGoodAnnulus (μ ω) r w a' b'} ≤
      P {ω | d * μ ω (annulus (z ω) (3*r) (5*r)) <
        μ ω (annulus (z ω) (3*r-κ*r) (5*r+κ*r) \
          annulus (z ω) (3*r+κ*r) (5*r-κ*r))} +
      P {ω | μ ω (annulus (z ω) (3*r) (5*r)) = 0} +
      P {ω | μ ω (annulus (z ω) (3*r) (5*r)) = ∞} := by
  obtain ⟨δ, hδ, htransfer⟩ := exists_scale_uniform_goodAnnulus_of_relative_collar hκ hε
  refine ⟨δ, hδ, ?_⟩
  intro Ω _ P μ z r hr a a' amid b b' d hbudget hmid hslack
  let E := {ω | IsGoodAnnulus (μ ω) r (z ω) a b ∧
    ∃ w : ℂ, dist w (z ω) < δ*r ∧
          ¬ IsGoodAnnulus (μ ω) r w a' b'}
  let C := {ω | d * μ ω (annulus (z ω) (3*r) (5*r)) <
    μ ω (annulus (z ω) (3*r-κ*r) (5*r+κ*r) \
      annulus (z ω) (3*r+κ*r) (5*r-κ*r))}
  let Z := {ω | μ ω (annulus (z ω) (3*r) (5*r)) = 0}
  let T := {ω | μ ω (annulus (z ω) (3*r) (5*r)) = ∞}
  have hsub : E ⊆ (C ∪ Z) ∪ T := by
    intro ω hω
    by_cases hz : μ ω (annulus (z ω) (3*r) (5*r)) = 0
    · exact Or.inl (Or.inr hz)
    by_cases ht : μ ω (annulus (z ω) (3*r) (5*r)) = ∞
    · exact Or.inr ht
    by_cases hc : d * μ ω (annulus (z ω) (3*r) (5*r)) <
      μ ω (annulus (z ω) (3*r-κ*r) (5*r+κ*r) \
        annulus (z ω) (3*r+κ*r) (5*r-κ*r))
    · exact Or.inl (Or.inl hc)
    · exfalso
      obtain ⟨w, hw, hbad⟩ := hω.2
      exact hbad (htransfer (μ ω) r hr (z ω) w hw a a' amid b b' d
        (pos_iff_ne_zero.mpr hz) ht hω.1 hbudget hmid hslack (le_of_not_gt hc))
  calc
    P E ≤ P ((C ∪ Z) ∪ T) := measure_mono hsub
    _ ≤ P (C ∪ Z) + P T := measure_union_le _ _
    _ ≤ P C + P Z + P T := add_le_add (measure_union_le _ _) le_rfl

end HarmonicBalls.Section6
