import HarmonicBalls.Steps.Sec11.ConeMassSupport
import HarmonicBalls.Steps.Sec11.PinchGreenFinite

/-! # Positive-probability mass and Green thresholds -/

namespace HarmonicBalls

/-! The cone-probability development uses Leonardo Bonanno's
Lattice-Probability formalization, including its Cameron-Martin port through
the local smooth-shift and fixed-shift decoder developments. -/

open MeasureTheory Metric Set Filter
open scoped ENNReal

universe u

/-- At the unit scale, full support and volume growth give deterministic
positive lower mass and finite upper Green thresholds on a positive-mass event. -/
theorem exists_cone_mass_green_thresholds
    (hS : WholePlaneScaledBallMassStep.{u}) (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hG : IsWholePlaneGFF P hC hcirc) (hE0 : LQGMeasureExistence P γ 0 hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (Q : Set ℂ) (hQ : IsCone Q) :
    ∃ n m : ℕ, 0 < n ∧ 0 < P {ω |
      (n : ℝ≥0∞)⁻¹ < μ ω (annulus 0 1 2 ∩ coneAt Q 0) ∧
      annulusGreenPotentialSup (μ ω) 0 3 6 < (m : ℝ≥0∞)} := by
  let : IsProbabilityMeasure P := hG.isProbabilityMeasure
  let A : Set Ω := {ω | μ ω (annulus 0 1 2 ∩ coneAt Q 0) ≠ 0 ∧
    annulusGreenPotentialSup (μ ω) 0 3 6 ≠ ∞}
  have hae : ∀ᵐ ω ∂P, ω ∈ A := by
    filter_upwards [ae_cone_annulus_mass_pos hS hγ hγ2 hG hE0 hμ,
      ae_annulusGreenPotentialSup_ne_top_of_lqgVolumeGrowth hgrowth hγ hγ2 hα hG hμ 3
        (show (0 : ℝ) < 6 by norm_num)] with ω hm hg
    have hm' : 0 < μ ω (annulus 0 1 2 ∩ coneAt Q 0) := by
      simpa using hm Q hQ 0 1 (by norm_num)
    exact ⟨hm'.ne', hg⟩
  have hpos : 0 < P A := by
    have h := measure_mono_ae (μ := P) (show (Set.univ : Set Ω) ≤ᵐ[P] A from
      hae.mono fun _ h _ => h)
    have hA : P A = 1 := by simpa using h
    rw [hA]
    exact zero_lt_one
  obtain ⟨n, m, hn, hp⟩ := exists_positive_measure_uniform_thresholds P A
    (fun ω => μ ω (annulus 0 1 2 ∩ coneAt Q 0))
    (fun ω => annulusGreenPotentialSup (μ ω) 0 3 6) hpos (fun _ h => h)
  refine ⟨n, m, hn, hp.trans_le (measure_mono ?_)⟩
  intro ω hω
  exact ⟨hω.2.1, hω.2.2⟩

end HarmonicBalls
