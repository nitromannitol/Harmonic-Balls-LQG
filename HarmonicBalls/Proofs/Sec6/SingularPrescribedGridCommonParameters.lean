import HarmonicBalls.Proofs.Sec6.SingularMassPrescribedGrid

/-! # Common parameters at a singular root and prescribed-grid centre

The annulus iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal
universe u

/-- At a singular-mass-typical root and a nearby prescribed-grid centre,
the common physical radii are good with the same threshold and avoidance
tolerance. The displacement factor still depends on the physical scale. -/
theorem exists_ae_singular_mass_prescribedGrid_common_parameters
    (hball : LiouvilleBallMassBoundStep.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ μ₀ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hμ₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {b : ℝ} (hb : 0 < b) (β : ℝ) (hβ : β ∈ Ioo (0 : ℝ) 1)
    (s : ℕ → ℝ) (hs : ∀ i, 0 < s i) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ δ : ℝ, 0 < δ ∧
      ∃ C : ℕ → ℝ, (∀ i, 1 ≤ C i) ∧
      ∀ᵐ ω ∂P, ∀ᵐ w ∂(μ ω).restrict (ball 0 1),
        ∀ i, ∀ᶠ n : ℕ in atTop,
          ∃ z ∈ prevalenceGrid (dyadicScale n),
            dist w z < δ * (s i * (C i * dyadicScale n)) ∧
            (β / 16) * Real.logb 7 ((dyadicScale n) ^ (-(1 / 2 : ℝ))) ≤
              ({r : ℝ | r ∈ Icc (dyadicScale n * s i) (Real.sqrt (dyadicScale n) * s i) ∧
                (∃ k : ℕ, 1 ≤ k ∧ r = s i * (7 : ℝ)⁻¹ ^ k) ∧
                IsGoodAnnulus (μ ω) r z ((a/8) / ((1001 : ℝ) ^ |-(γ*α)|) ^ 2) b ∧
                IsGoodAnnulus (μ ω) r w ((a/8) / ((1001 : ℝ) ^ |-(γ*α)|) ^ 2) b}.ncard : ℝ) := by
  obtain ⟨a, ha, δ, hδ, C, hC, ht⟩ :=
    exists_ae_singular_mass_common_goodAnnulus_prescribedGrid_physical
      hball h hμ hμ₀ hAff hCC hγ hγ2 hα hb β hβ s hs
  refine ⟨a, ha, δ, hδ, C, hC, ?_⟩
  have hsmall : (a / 8) / ((1001 : ℝ) ^ |-(γ*α)|) ^ 2 ≤
      a / ((1001 : ℝ) ^ |-(γ*α)|) ^ 2 := by
    apply div_le_div_of_nonneg_right (by linarith [ha.1])
    positivity
  filter_upwards [ht] with ω hω
  filter_upwards [hω] with w hw
  intro i
  filter_upwards [hw i] with n hn
  obtain ⟨z, hz, hd, hcount⟩ := hn
  refine ⟨z, hz, hd, hcount.trans ?_⟩
  have hfin : {r : ℝ | r ∈ Icc (dyadicScale n * s i) (Real.sqrt (dyadicScale n) * s i) ∧
      (∃ k : ℕ, 1 ≤ k ∧ r = s i * (7 : ℝ)⁻¹ ^ k) ∧
      IsGoodAnnulus (μ ω) r z ((a/8) / ((1001 : ℝ) ^ |-(γ*α)|) ^ 2) b ∧
      IsGoodAnnulus (μ ω) r w ((a/8) / ((1001 : ℝ) ^ |-(γ*α)|) ^ 2) b}.Finite := by
    refine finite_of_geometric (q := (7 : ℝ)⁻¹) (A := s i) (lo := dyadicScale n * s i)
      (by norm_num) (by norm_num) (mul_pos (dyadicScale_pos n) (hs i)) ?_
    intro r hr
    obtain ⟨k, _, hk⟩ := hr.2.1
    exact ⟨hr.1.1, k, hk⟩
  have hsub : {r : ℝ | r ∈ Icc (dyadicScale n * s i)
      (Real.sqrt (dyadicScale n) * s i) ∧
      (∃ k : ℕ, 1 ≤ k ∧ r = s i * (7 : ℝ)⁻¹ ^ k) ∧
      IsGoodAnnulus (μ ω) r z (a / ((1001 : ℝ) ^ |-(γ*α)|) ^ 2) (b/2) ∧
      IsGoodAnnulus (μ ω) r w ((a/8) / ((1001 : ℝ) ^ |-(γ*α)|) ^ 2) b} ⊆
      {r : ℝ | r ∈ Icc (dyadicScale n * s i)
      (Real.sqrt (dyadicScale n) * s i) ∧
      (∃ k : ℕ, 1 ≤ k ∧ r = s i * (7 : ℝ)⁻¹ ^ k) ∧
      IsGoodAnnulus (μ ω) r z ((a/8) / ((1001 : ℝ) ^ |-(γ*α)|) ^ 2) b ∧
      IsGoodAnnulus (μ ω) r w ((a/8) / ((1001 : ℝ) ^ |-(γ*α)|) ^ 2) b} := by
    intro r hr
    exact ⟨hr.1, hr.2.1,
      isGoodAnnulus_mono_avoidance (isGoodAnnulus_mono_mass hr.2.2.1 hsmall) (by linarith),
      hr.2.2.2⟩
  exact_mod_cast Set.ncard_le_ncard hsub hfin

end HarmonicBalls.Section6
