import HarmonicBalls.Steps.Sec11.AnnulusCoverConnectivity
import HarmonicBalls.Steps.Sec11.AnnulusCoverProbability

/-! # Puncture removal from scaled-ball estimates

The deterministic scaled annulus cover supplies the geometry for the
probabilistic puncture-removal criterion. Local metric estimates remain
explicit hypotheses.
-/

namespace HarmonicBalls

open Set Metric MeasureTheory
open scoped ENNReal

/-- For a fixed finite family of scaled balls, summable local exceedance
bounds imply puncture removal under the stated metric and Weyl assumptions. -/
theorem exists_scaled_ball_criterion_for_puncture_removal
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D E : Ω → ℂ → ℂ → ℝ) (A : Ω → ℝ≥0∞) (s ξ α β : ℝ)
    (hξ : 0 ≤ ξ) (hα : 0 ≤ α) (hgap : ξ * α < β)
    (V : Set ℂ) (hball : ball (0 : ℂ) (Real.exp (1 - s)) ⊆ V)
    (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hE : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (E ω))
    (hDnonneg : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ D ω x y)
    (hEnonneg : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ E ω x y)
    (hA : ∀ᵐ ω ∂P, A ω ≠ ∞)
    (hzero : ∀ᵐ ω ∂P, ∀ x y,
      weylScaling (D ω) ξ 0 x y = ENNReal.ofReal (D ω x y))
    (hscale : ∀ᵐ ω ∂P, ∀ x y, ENNReal.ofReal (E ω x y) =
      weylScaling (D ω) ξ (fun z => -α * Real.log ‖z‖) x y) :
    ∃ (ε : ℝ) (N : ℕ) (c : ℕ → ℂ), 0 < ε ∧
      ∀ p : ℕ → ℝ≥0∞, (∑' n, p n) ≠ ∞ →
        (∀ (n i : ℕ), i ≤ N →
          P {ω | ∃ x ∈ ball (Real.exp (-(s + n)) • c i) (Real.exp (-(s + n)) * ε),
            ∃ y ∈ ball (Real.exp (-(s + n)) • c i) (Real.exp (-(s + n)) * ε),
              A ω * ENNReal.ofReal (Real.exp (-β * (n : ℝ))) <
                internalMetric (D ω)
                  (ball (Real.exp (-(s + n)) • c i) (Real.exp (-(s + n)) * (2 * ε)))
                  x y} ≤ p n) →
        ∀ᵐ ω ∂P, ∀ x y : ℂ, x ≠ 0 → y ≠ 0 →
          internalMetric (E ω) (V \ {0}) x y = internalMetric (E ω) V x y := by
  obtain ⟨ε, N, c, z, hε, hgeometry⟩ := exists_scaled_annulus_cover_chains
  refine ⟨ε, N, c, hε, ?_⟩
  intro p hp hlocal
  exact ae_internalMetric_sdiff_zero_eq_of_local_cover_exceedance P D E A s ξ α β N
    (fun n i => ball (Real.exp (-(s + n)) • c i) (Real.exp (-(s + n)) * ε))
    (fun n i => ball (Real.exp (-(s + n)) • c i) (Real.exp (-(s + n)) * (2 * ε)))
    (z s) p hξ hα hgap V hball hD hE hDnonneg hEnonneg hA hzero hscale
    (fun n => (hgeometry s n).1) (fun n => (hgeometry s n).2.1)
    (fun n => (hgeometry s n).2.2) hlocal hp


end HarmonicBalls
