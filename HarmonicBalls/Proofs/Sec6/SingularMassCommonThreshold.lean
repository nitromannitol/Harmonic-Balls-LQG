import HarmonicBalls.Proofs.Sec6.SingularMassCommonRadii

/-! # A common good-annulus threshold at singular roots and grid centres

The annulus iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal
universe u

/-- Goodness is preserved when the allowed Brownian avoidance probability is
increased. -/
theorem isGoodAnnulus_mono_avoidance {μ : Measure ℂ} {r a b b' : ℝ} {z : ℂ}
    (hg : IsGoodAnnulus μ r z a b) (hb : b ≤ b') : IsGoodAnnulus μ r z a b' := by
  intro Y hY hYA hm u hu
  exact (hg Y hY hYA hm u hu).trans (ENNReal.ofReal_le_ofReal hb)

/-- One positive mass threshold and one avoidance tolerance work for the
prescribed grid and for the same good radii at a singular-mass-typical centre
and a nearby fine-grid centre, at each of countably many physical scales. -/
theorem exists_ae_singular_mass_prescribed_grid_and_common_radii_threshold
    (hball : LiouvilleBallMassBoundStep.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hE₀ : LQGMeasureExistence P γ 0 hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) (β : ℝ) (hβ : β ∈ Ioo (0 : ℝ) 1)
    (s : ℕ → ℝ) (hs : ∀ i, 0 < s i) :
    ∃ c₀ a δ : ℝ, 0 < c₀ ∧ a ∈ Ioo (0 : ℝ) 1 ∧ 0 < δ ∧
      ∃ c : ℕ → ℝ, (∀ i, 0 < c i) ∧
      ∀ᵐ ω ∂P, ∀ᵐ w ∂(μ ω).restrict (ball 0 1),
        (∀ᶠ n : ℕ in atTop, ∀ y ∈ prevalenceGrid (dyadicScale n),
          c₀ * Real.logb 7 ((dyadicScale n) ^ (-(1 / 2 : ℝ))) ≤
            ({r : ℝ | r ∈ Icc (dyadicScale n) (Real.sqrt (dyadicScale n)) ∧
              (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
              IsGoodAnnulus (μ ω) r y a b}.ncard : ℝ)) ∧
        (∀ i, ∀ᶠ n : ℕ in atTop,
          ∃ z ∈ prevalenceGrid (c i * dyadicScale n),
            dist w z < δ * (s i * dyadicScale n) ∧
            (β / 16) * Real.logb 7 ((dyadicScale n) ^ (-1 : ℝ)) ≤
              ({r : ℝ | r ∈ Icc (dyadicScale n) ((dyadicScale n) ^ (3 / 4 : ℝ)) ∧
                (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
                IsGoodAnnulus (μ ω) (s i*r) z a b ∧
                IsGoodAnnulus (μ ω) (s i*r) w a b}.ncard : ℝ)) := by
  obtain ⟨c₀, a₀, a₁, δ, hc₀, ha₀, ha₁, hδ, c, hc, ht⟩ :=
    exists_ae_singular_mass_prescribed_grid_and_common_radii
      hball h hμ hE₀ hAff hCC hγ hγ2 hα hb β hβ s hs
  let K : ℝ := ((1001 : ℝ) ^ |-(γ*α)|) ^ 2
  have hK : 0 < K := by dsimp [K]; positivity
  let a : ℝ := min a₀ ((a₁/8)/K)
  have ha : 0 < a := lt_min ha₀.1 (div_pos (div_pos ha₁.1 (by norm_num)) hK)
  have ha₀' : a ≤ a₀ := min_le_left _ _
  have ha₁' : a ≤ (a₁/8)/K := min_le_right _ _
  have ha₁'' : a ≤ a₁/K := ha₁'.trans
    (div_le_div_of_nonneg_right (by linarith [ha₁.1]) hK.le)
  refine ⟨c₀, a, δ, hc₀, ⟨ha, lt_of_le_of_lt ha₀' ha₀.2⟩, hδ, c, hc, ?_⟩
  filter_upwards [ht] with ω hω
  filter_upwards [hω] with w hw
  constructor
  · filter_upwards [hw.1] with n hn y hy
    have hmono := sevenAdic_goodAnnulus_count_mono (μ ω) y 1 (dyadicScale n)
      (Real.sqrt (dyadicScale n)) a₀ a b (dyadicScale_pos n) ha₀'
    simp only [one_mul] at hmono
    exact (hn y hy).trans hmono
  · intro i
    filter_upwards [hw.2 i] with n hn
    obtain ⟨z, hz, hdist, hcount⟩ := hn
    refine ⟨z, hz, hdist, hcount.trans ?_⟩
    norm_cast
    apply Set.ncard_le_ncard ?_ ?_
    · intro r hr
      refine ⟨hr.1, hr.2.1, ?_, ?_⟩
      · exact isGoodAnnulus_mono_avoidance
          (isGoodAnnulus_mono_mass hr.2.2.1 ha₁'') (by linarith [hb.1])
      · exact isGoodAnnulus_mono_mass hr.2.2.2 ha₁'
    · apply finite_of_geometric (q := (7 : ℝ)⁻¹) (A := 1) (lo := dyadicScale n)
        (by norm_num) (by norm_num) (dyadicScale_pos n)
      intro r hr
      obtain ⟨k, hk⟩ := hr.2.1
      exact ⟨hr.1.1, k, by simpa using hk⟩

end HarmonicBalls.Section6
