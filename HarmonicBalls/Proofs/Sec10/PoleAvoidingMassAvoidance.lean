import HarmonicBalls.Proofs.Sec10.PoleAvoidingHarnackInduction

/-! # Component mass-or-avoidance from good-annulus decay -/

namespace HarmonicBalls

open MeasureTheory Metric Set Section6
open scoped ENNReal

/-- The componentwise mass-or-avoidance estimate follows from one-annulus
odometer decay. The universal constants come from the annular mass and
Harnack bounds; the pole may lie in the containing disc. -/
theorem exists_pole_avoiding_component_mass_or_avoid_of_goodAnnulus_decay :
    ∃ C₄ c : ℝ, 0 < C₄ ∧ 0 < c ∧
    ∀ {μ : Measure ℂ}, IsLocallyFiniteMeasure μ →
    ∀ {β βplus : ℝ}, 0 < β → VolumeGrowth μ 1 β βplus →
    ∀ {z : ℂ}, z ∈ ball (0 : ℂ) 1 → ∀ {t : ℝ}, 0 < t →
    ∀ {ρ : ℝ}, 0 < ρ → ∀ {x₀ : ℂ}, closedBall x₀ ρ ⊆ ball (0 : ℂ) 1 →
    ∀ {Λ : Set ℂ}, Λ ∈ connectedComponentsIn (cluster μ 1 z t ∩ ball x₀ ρ) → z ∉ Λ →
    ∀ {N₀ : ℕ}, 200 ≤ N₀ → ∀ {a b C₁m C₁p C₂m C₂p C₃ α : ℝ},
    0 < a → b ∈ Ioo (0 : ℝ) 1 → 0 < C₁m → 0 < C₂p → 0 < C₃ → 0 ≤ α →
    annulusBallMassSize μ β ρ x₀ / μ (annulus x₀ (ρ / 4) (2 * ρ)) ∈
      Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p) →
    annulusGreenPotentialSup μ x₀ (ρ / 4) (2 * ρ) / μ (annulus x₀ (ρ / 4) (2 * ρ)) ∈
      Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p) →
    μ (Λ ∩ annulus x₀ (ρ / 2) ρ) ≤ ENNReal.ofReal α * μ (annulus x₀ (ρ / 2) ρ) →
    α ≤ a * (2 : ℝ) ^ (-((N₀ : ℝ) * β)) * C₁m → α < C₁m * (8 : ℝ) ^ (-β) →
    (∀ j : ℕ, b ^ (Real.log 2 / (2 * Real.log 7) * C₃ * ((N₀ : ℝ) + j)) =
      (2 : ℝ) ^ (-(2 * β * ((N₀ : ℝ) + j)))) →
    max C₄ 1 * (2 : ℝ) ^ (-(2 * β * N₀)) * c * C₂p / C₁m ≤
      a * (2 : ℝ) ^ (-(((N₀ : ℝ) + 1) * β)) →
    VeryGoodCriterionThree μ ρ x₀ N₀ a b C₃ →
    (∀ r : ℝ, 0 < r → ∀ w : ℂ, closedBall w (5 * r) ⊆ ball x₀ ρ →
      IsGoodAnnulus μ r w a b →
      μ (Λ ∩ annulus w (3 * r) (5 * r)) ≤ ENNReal.ofReal a * μ (annulus w (3 * r) (5 * r)) →
      (⨆ x ∈ Λ ∩ ball w (4 * r), odometerExt μ z t x) ≤
        ENNReal.ofReal b * ⨆ x ∈ Λ ∩ annulus w (3 * r) (5 * r), odometerExt μ z t x) →
    Λ ∩ closedBall x₀ (ρ / 2) = ∅ := by
  obtain ⟨C₄, hC₄, h68⟩ := component_annulus_mass_le_odometer_of_pole_not_mem
    (s₁ := 1) (s₂ := 3) (s₃ := 5) (s₄ := 7)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨c, hc, h610⟩ := exists_component_middle_annulus_odometer_bound_of_outer_mass
  refine ⟨C₄, c, hC₄, hc, ?_⟩
  intro μ hμ β βplus hβ hV z hz t ht ρ hρ x₀ hball Λ hΛ hzΛ N₀ hN₀
    a b C₁m C₁p C₂m C₂p C₃ α ha hb h1m h2p hC₃ hα0 hv1 hv2 hmass hα1 hα2 hbpow hN hVG3 hdec
  have hUsub : ball x₀ ρ ⊆ ball (0 : ℂ) 1 := ball_subset_closedBall.trans hball
  have hΛ' : Λ ∈ connectedComponentsIn (ball x₀ ρ ∩ cluster μ 1 z t) := by
    simpa only [inter_comm] using hΛ
  apply pole_avoiding_component_harnack_core hβ hρ hΛ hzΛ ha h1m hC₄ hc h2p hv1 hv2 hmass hα1 hbpow hb.1.le hN
  · intro r hr w hA
    have h := h68 hμ hV hz ht hUsub hΛ' hzΛ (w := w) hr (by simpa only [one_mul] using hA)
    simpa only [one_mul] using h
  · exact h610 hμ hV hz ht hUsub hΛ' hzΛ hρ sdiff_subset h1m hα0 hv1 hmass hα2
  · exact greenPotentialSupMonoStep_proved μ x₀ (ρ / 4) ρ (2 * ρ) (by positivity) (by linarith) (by linarith)
  · intro j hj
    exact pole_avoiding_component_lowMass_smallOdometer hμ hV hz ht hb hN₀ hC₃ hρ hball hVG3 hΛ hzΛ hdec j hj
  · intro d hd hempty
    exact pole_avoiding_component_inter_closedBall_eq_empty hμ hV hz ht hΛ hzΛ hd hempty

end HarmonicBalls
