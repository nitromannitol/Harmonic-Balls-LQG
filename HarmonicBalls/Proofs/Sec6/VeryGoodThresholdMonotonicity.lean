import HarmonicBalls.Proofs.Sec6.SingularRootGridVeryGood

/-! # Threshold monotonicity for very-good annuli

The imported annulus iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
universe u

/-- Decreasing the mass threshold preserves all three very-good criteria. -/
theorem isVeryGoodAnnulus_mono_mass {μ : Measure ℂ} {β ρ a a' b C₁m C₁p C₂m C₂p C₃ : ℝ}
    {z : ℂ} {N₀ : ℕ} (hρ : 0 < ρ) (ha : a' ≤ a)
    (h : IsVeryGoodAnnulus μ β ρ z N₀ a b C₁m C₁p C₂m C₂p C₃) :
    IsVeryGoodAnnulus μ β ρ z N₀ a' b C₁m C₁p C₂m C₂p C₃ := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro n hn w hw hlat
  refine (h.2.2 n hn w hw hlat).trans ?_
  norm_cast
  refine Set.ncard_le_ncard (fun r hr => ⟨hr.1, hr.2.1,
    isGoodAnnulus_mono_mass hr.2.2 ha⟩) ?_
  refine finite_of_geometric (q := (7 : ℝ)⁻¹) (A := ρ) (lo := dyadicScale n * ρ)
    (by norm_num) (by norm_num) (mul_pos (dyadicScale_pos n) hρ) ?_
  intro r hr
  obtain ⟨k, _, hk⟩ := hr.2.1
  exact ⟨hr.1.1, k, hk⟩

/-- One positive threshold works for the root/grid good-annulus count and
the very-good-annulus count at the same prescribed-grid point. The scales
of the two counts and the scale-dependent displacement remain explicit. -/
theorem exists_ae_singular_root_prescribedGrid_common_good_veryGood_threshold
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u}) (hball : LiouvilleBallMassBoundStep.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α θ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ μ₀ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hμ₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀)
    (hE₀ : LQGMeasureExistence P γ 0 hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hθ : (2 + γ)^2 / 2 < θ) {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1)
    (β : ℝ) (hβ : β ∈ Ioo (0 : ℝ) 1) (s : ℕ → ℝ) (hs : ∀ i, 0 < s i) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ δ : ℝ, 0 < δ ∧
    ∃ C : ℕ → ℝ, (∀ i, 1 ≤ C i) ∧
    ∃ c C₃ C₁m C₁p C₂m C₂p : ℝ,
      0 < c ∧ 0 < C₃ ∧
      0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
    ∃ N₀ : ℕ, 5 ≤ N₀ ∧
    ∀ᵐ ω ∂P, ∀ᵐ w ∂(μ ω).restrict (ball 0 1),
      ∀ i, ∀ᶠ n : ℕ in atTop,
        ∃ z ∈ prevalenceGrid (dyadicScale n),
          dist w z < δ * (s i * (C i * dyadicScale n)) ∧
          (β / 16) * Real.logb 7 ((dyadicScale n) ^ (-(1 / 2 : ℝ))) ≤
            ({r : ℝ | r ∈ Icc (dyadicScale n * s i) (Real.sqrt (dyadicScale n) * s i) ∧
              (∃ k : ℕ, 1 ≤ k ∧ r = s i * (7 : ℝ)⁻¹ ^ k) ∧
              IsGoodAnnulus (μ ω) r z a b ∧
              IsGoodAnnulus (μ ω) r w a b}.ncard : ℝ) ∧
          c * Real.logb 8 ((dyadicScale n) ^ (-(1 / 2 : ℝ))) ≤
            ({ρ : ℝ | ρ ∈ Icc (dyadicScale n) (Real.sqrt (dyadicScale n)) ∧
              (∃ k : ℕ, ρ = (8 : ℝ)⁻¹ ^ k) ∧
              IsVeryGoodAnnulus (μ ω) θ ρ z N₀ a b C₁m C₁p C₂m C₂p C₃}.ncard : ℝ) := by
  obtain ⟨a₇, ha₇, δ, hδ, C, hC', c, C₃, a₈, C₁m, C₁p, C₂m, C₂p,
    hc, hC₃, ha₈, h₁m, h₁p, h₂m, h₂p, N₀, hN₀, ht⟩ :=
    exists_ae_singular_root_prescribedGrid_good_and_veryGood
      hgrowth hball h hμ hμ₀ hE₀ hAff hCC hγ hγ2 hα hθ hb β hβ s hs
  let a : ℝ := min ((a₇/8) / ((1001 : ℝ) ^ |-(γ*α)|) ^ 2) a₈
  have ha₇pos : 0 < a₇ := ha₇.1
  have ha : a ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact lt_min (by positivity) ha₈.1
    · exact (min_le_right _ _).trans_lt ha₈.2
  refine ⟨a, ha, δ, hδ, C, hC', c, C₃, C₁m, C₁p, C₂m, C₂p,
    hc, hC₃, h₁m, h₁p, h₂m, h₂p, N₀, hN₀, ?_⟩
  filter_upwards [ht] with ω hω
  filter_upwards [hω] with w hw
  intro i
  filter_upwards [hw i] with n hn
  obtain ⟨z, hz, hd, hseven, height⟩ := hn
  refine ⟨z, hz, hd, hseven.trans ?_, height.trans ?_⟩
  · norm_cast
    refine Set.ncard_le_ncard (fun r hr => ⟨hr.1, hr.2.1,
      isGoodAnnulus_mono_mass hr.2.2.1 (min_le_left _ _),
      isGoodAnnulus_mono_mass hr.2.2.2 (min_le_left _ _)⟩) ?_
    refine finite_of_geometric (q := (7 : ℝ)⁻¹) (A := s i) (lo := dyadicScale n * s i)
      (by norm_num) (by norm_num) (mul_pos (dyadicScale_pos n) (hs i)) ?_
    intro r hr
    obtain ⟨k, _, hk⟩ := hr.2.1
    exact ⟨hr.1.1, k, hk⟩
  · norm_cast
    refine Set.ncard_le_ncard (fun ρ hρ => ⟨hρ.1, hρ.2.1,
      isVeryGoodAnnulus_mono_mass ((dyadicScale_pos n).trans_le hρ.1.1)
        (min_le_right _ _) hρ.2.2⟩) ?_
    refine finite_of_geometric (q := (8 : ℝ)⁻¹) (A := 1) (lo := dyadicScale n)
      (by norm_num) (by norm_num) (dyadicScale_pos n) ?_
    intro ρ hρ
    obtain ⟨k, hk⟩ := hρ.2.1
    exact ⟨hρ.1.1, k, by simpa only [one_mul] using hk⟩

end HarmonicBalls.Section6
