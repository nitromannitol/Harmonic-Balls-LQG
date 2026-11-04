import HarmonicBalls.Proofs.Sec11.ConeAllScales
import HarmonicBalls.Proofs.Sec11.ConeGreenPositive
import HarmonicBalls.Proposed.LQG

/-! # Cone condition at typical boundary points -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- The conclusion of Lemma 11.5 at fixed field parameters, conditional on
Lemmas 11.6 and 11.7, full support, and the staged non-atomicity input. -/
theorem ae_noConeCondition_of_comparison_and_coneScales
    (hbound : AnnulusMassBoundByHarmonicChainStmt.{u})
    (hmany : ManyConeBadScalesStmt.{u})
    (hfull : LQGMeasureFullSupportStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (Λ : Ω → ℝ → Set ℂ)
    (hnonatomic : LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hfamily : ∀ᵐ ω ∂P, IsHarmonicBallFamily (μ ω) (Λ ω) 0) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), ∀ t : ℝ, 0 < t →
      z ∈ frontier (Λ ω t) → ¬ SatisfiesConeCondition (Λ ω t) z := by
  obtain ⟨C, hCpos, hcomparison⟩ := hbound
  filter_upwards [hcomparison γ α₀ hγ hγ₂ hα Ω P hC hcirc μ hgff hμ Λ hfamily,
    ae_frequently_coneMass_all_cones hmany γ α₀ hγ hγ₂ hα (2 * C) (by linarith)
      Ω P hC hcirc μ hgff hμ,
    hfull γ α₀ hγ hγ₂ hα Ω P hC hcirc μ hgff hμ,
    hnonatomic hgff hγ hγ₂ hα μ hμ, hμ] with ω hcomparison hscales hsupport hatom hlocal
  let : IsLocallyFiniteMeasure (μ ω) := hlocal.isLocallyFiniteMeasure
  have hz0 : ∀ᵐ z ∂(μ ω), z ≠ 0 := by
    simpa only [Set.mem_singleton_iff] using (measure_eq_zero_iff_ae_notMem.1 (hatom 0))
  filter_upwards [hscales, hz0] with z hscales hz0
  intro t ht _
  exact not_satisfiesConeCondition_of_frequently_coneMass_fullSupport (μ ω) (Λ ω t) z C
    hCpos hz0 hsupport hscales (fun r hr h0 => hcomparison t ht r hr z h0)

end HarmonicBalls
