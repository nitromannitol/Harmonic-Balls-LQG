import HarmonicBalls.Proofs.Sec10.PoleAvoidingAnnulusComparison
import HarmonicBalls.Proofs.Sec10.IndependentGrowthExponent

/-! # Displaced-ball crossing bound from Lemma 6.9 -/

namespace HarmonicBalls

open MeasureTheory Metric Set Section6
open scoped ENNReal

universe u

/-- Volume growth and Lemma 6.9 give a sharp displaced-ball crossing bound,
simultaneously over poles, times and very good balls. The thresholds depend
only on the fixed annular mass exponent and very-good parameters, before γ and α₀. -/
theorem exists_ae_crossing_thresholds_independent_exponent
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h69 : OdometerHarmonicMeasureBoundStmt.{u})
    {β C₃ : ℝ} (hβ : 0 < β) (hC₃ : 0 < C₃) :
    ∃ b ∈ Ioo (0 : ℝ) 1, ∃ N₁ : ℝ → ℝ → ℝ → ℕ, ∃ α : ℝ → ℕ → ℝ → ℝ,
      (∀ a ∈ Ioo (0 : ℝ) 1, ∀ C₁m C₂p : ℝ, 0 < C₁m → 0 < C₂p →
        200 ≤ N₁ a C₁m C₂p ∧ ∀ N₀ : ℕ, N₁ a C₁m C₂p ≤ N₀ → α a N₀ C₁m ∈ Ioo (0 : ℝ) 1) ∧
      ∀ {γ α₀ : ℝ}, 0 < γ → γ < 2 → α₀ < lqgQ γ →
      ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
        {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ},
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
      ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
      ∀ ρ : ℝ, 0 < ρ → ∀ x₀ : ℂ, closedBall x₀ ρ ⊆ ball (0 : ℂ) 1 →
      ∀ w : ℂ, dist w x₀ < ρ / 6 →
      ∀ a ∈ Ioo (0 : ℝ) 1, ∀ C₁m C₁p C₂m C₂p : ℝ, 0 < C₁m → 0 < C₂p →
      ∀ N₀ : ℕ, N₁ a C₁m C₂p ≤ N₀ →
      annulusBallMassSize (μ ω) β ρ x₀ / (μ ω) (annulus x₀ (ρ / 4) (2 * ρ)) ∈
        Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p) →
      annulusGreenPotentialSup (μ ω) x₀ (ρ / 4) (2 * ρ) / (μ ω) (annulus x₀ (ρ / 4) (2 * ρ)) ∈
        Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p) →
      VeryGoodCriterionThree (μ ω) ρ x₀ N₀ a b C₃ →
      (crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ)) w (ρ / 3) (2 * ρ)).encard ≤
        ⌈1 / α a N₀ C₁m⌉₊ := by
  obtain ⟨b, hb, N₁, α, hparam, hcross⟩ :=
    exists_pole_avoiding_crossing_thresholds_independent_exponent hβ hC₃
  refine ⟨b, hb, N₁, α, hparam, ?_⟩
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨βminus, βplus, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV, h69 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hV hcompare
  intro z hz t ht ρ hρ x₀ hx₀ w hw a ha C₁m C₁p C₂m C₂p hC₁ hC₂ N₀ hN₀ hmass hgreen hgood
  let : IsLocallyFiniteMeasure (μ ω) := hV.1
  have hfin : (μ ω) (annulus x₀ (ρ / 2) ρ) ≠ ∞ :=
    ne_top_of_le_ne_top (measure_ball_lt_top (μ := μ ω)).ne (measure_mono sdiff_subset)
  apply hcross hV.1 (hV.2 1 zero_lt_one) hz ht hρ hx₀ hw hfin a ha C₁m C₁p C₂m C₂p hC₁ hC₂ N₀ hN₀ hmass hgreen hgood
  intro Λ hΛ hzΛ r hr v hv hgood' hmass'
  have hΛ' : Λ ∈ connectedComponentsIn (ball x₀ ρ ∩ cluster (μ ω) 1 z t) := by simpa [inter_comm] using hΛ
  exact component_goodAnnulus_decay_of_punctured_comparison hV.1 (hV.2 1 zero_lt_one) hz ht
    isOpen_ball (ball_subset_closedBall.trans hx₀) hΛ' hzΛ hr hv hgood' hmass' (hcompare z hz t ht)

end HarmonicBalls
