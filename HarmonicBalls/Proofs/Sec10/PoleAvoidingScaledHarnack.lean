import HarmonicBalls.Proofs.Sec10.PoleAvoidingHarnackAnchor
import HarmonicBalls.Proofs.Sec6.HarnackChainScaling

/-! # Scale-invariant Harnack bounds for pole-avoiding components -/

namespace HarmonicBalls

open MeasureTheory Metric Set Section6
open scoped ENNReal

/-- Unit-scale Harnack chains give a uniform middle-annulus odometer bound
for every scale and every pole-avoiding local cluster component. -/
theorem component_middle_annulus_odometer_le_of_unit_harnack_chains
    {r : ℝ} (hr : 0 < r) (N : ℕ)
    (hchains : ∀ x ∈ annulus (0 : ℂ) (1 / 2) (7 / 8),
      ∀ y ∈ annulus (0 : ℂ) (1 / 2) (7 / 8), ∃ p : ℕ → ℂ,
        p 0 = y ∧ p N = x ∧
        (∀ i < N, closedBall (p i) r ⊆ annulus (0 : ℂ) (1 / 4) 1) ∧
        (∀ i < N, p (i + 1) ∈ closedBall (p i) (r / 2))) :
    ∃ C : ℝ, 0 < C ∧ ∀ {μ : Measure ℂ}, IsLocallyFiniteMeasure μ →
      ∀ {βminus βplus : ℝ}, VolumeGrowth μ 1 βminus βplus →
      ∀ {z : ℂ}, z ∈ ball (0 : ℂ) 1 → ∀ {t : ℝ}, 0 < t →
      ∀ {U D : Set ℂ}, U ⊆ ball (0 : ℂ) 1 →
      D ∈ connectedComponentsIn (U ∩ cluster μ 1 z t) → z ∉ D →
      ∀ {ρ : ℝ}, 0 < ρ → ∀ {x₀ : ℂ}, annulus x₀ (ρ / 4) ρ ⊆ U →
      ∀ {C₁m C₁p α : ℝ}, 0 < C₁m → 0 ≤ α →
      annulusBallMassSize μ βminus ρ x₀ / μ (annulus x₀ (ρ / 4) (2 * ρ)) ∈
        Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p) →
      μ (D ∩ annulus x₀ (ρ / 2) ρ) ≤
        ENNReal.ofReal α * μ (annulus x₀ (ρ / 2) ρ) →
      α < C₁m * (8 : ℝ) ^ (-βminus) →
      ⨆ x ∈ annulus x₀ (ρ / 2) (7 / 8 * ρ) ∩ D, odometerExt μ z t x ≤
        ENNReal.ofReal C * annulusGreenPotentialSup μ x₀ (ρ / 4) ρ := by
  refine ⟨(4 : ℝ) ^ N, by positivity, ?_⟩
  intro μ hμ βminus βplus hV z hz t ht U D hUsub hD hzD ρ hρ x₀ hA
    C₁m C₁p α h1m hα0 hv1 hmass hα
  have hscaled := harnack_chains_scale N hchains x₀ hρ
  apply component_middle_annulus_odometer_le_of_outer_mass_of_chains
    hμ hV hz ht hUsub hD hzD hρ hA h1m hα0 hv1 hmass hα (mul_pos hρ hr) N
  intro y hy x hx
  have hy' : y ∈ annulus x₀ ((1 / 2) * ρ) ((7 / 8) * ρ) := by
    simpa [div_eq_mul_inv, mul_comm] using hy
  have hx' : x ∈ annulus x₀ ((1 / 2) * ρ) ((7 / 8) * ρ) := by
    simpa [div_eq_mul_inv, mul_comm] using hx.1
  obtain ⟨p, hp0, hpN, hpdisc, hpstep⟩ := hscaled x hx' y hy'
  refine ⟨p, hp0, hpN, ?_, hpstep⟩
  intro i hi
  simpa [div_eq_mul_inv, mul_comm] using hpdisc i hi

end HarmonicBalls
