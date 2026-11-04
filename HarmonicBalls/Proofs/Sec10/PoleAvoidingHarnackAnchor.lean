import HarmonicBalls.Proofs.Sec10.PoleAvoidingHarnackChain
import HarmonicBalls.Proofs.Sec6.HarnackIteration

/-! # A middle-annulus anchor for pole-avoiding components -/

namespace HarmonicBalls

open MeasureTheory Metric Set Section6
open scoped ENNReal

/-- A small outer-annulus mass and the lower ball-mass ratio force a point in
the middle annulus outside the selected set. No pole separation is needed. -/
theorem exists_middle_annulus_not_mem_of_outer_mass
    {μ : Measure ℂ} {β ρ : ℝ} {x₀ : ℂ} (hρ : 0 < ρ)
    {C₁m C₁p α : ℝ} (h1m : 0 < C₁m) (hα0 : 0 ≤ α)
    (hv1 : annulusBallMassSize μ β ρ x₀ / μ (annulus x₀ (ρ / 4) (2 * ρ)) ∈
      Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p))
    {D : Set ℂ} (hmass : μ (D ∩ annulus x₀ (ρ / 2) ρ) ≤
      ENNReal.ofReal α * μ (annulus x₀ (ρ / 2) ρ))
    (hα : α < C₁m * (8 : ℝ) ^ (-β)) :
    (annulus x₀ (ρ / 2) (7 / 8 * ρ) \ D).Nonempty := by
  set M := annulusBallMassSize μ β ρ x₀ with hMdef
  set A := annulus x₀ (ρ / 2) ρ with hAdef
  set A' := annulus x₀ (ρ / 4) (2 * ρ) with hA'def
  set K := annulus x₀ (ρ / 2) (7 / 8 * ρ) with hKdef
  obtain ⟨hY0, hYt, hM0, hMt, hMlo, -⟩ := ratio_facts h1m hv1
  have hAA : A ⊆ A' := annulus_subset_annulus (by linarith) (by linarith)
  have hKA : K ⊆ A := annulus_subset_annulus le_rfl (by linarith)
  set y : ℂ := x₀ + ((11 / 16 * ρ : ℝ) : ℂ) with hydef
  have hyd : dist y x₀ = 11 / 16 * ρ := by
    rw [hydef, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  have hBy : ball y (ρ / 8) ⊆ K := by
    intro w hw
    have h1 := mem_ball.1 hw
    have t1 := dist_triangle w y x₀
    have t2 := dist_triangle y w x₀
    rw [dist_comm y w] at t2
    refine ⟨mem_ball.2 (by linarith), fun hc => ?_⟩
    have := mem_closedBall.1 hc
    linarith
  have hyA : y ∈ A :=
    ⟨mem_ball.2 (by linarith), fun hc => by have := mem_closedBall.1 hc; linarith⟩
  have hMy : M ≤ μ (ball y (ρ / 8)) / ENNReal.ofReal ((ρ / 8 / ρ) ^ β) :=
    iInf₂_le_of_le y hyA (iInf₂_le (ρ / 8) ⟨by positivity, by linarith⟩)
  have hpow : (ρ / 8 / ρ) ^ β = (8 : ℝ) ^ (-β) := by
    rw [show ρ / 8 / ρ = (8 : ℝ)⁻¹ by field_simp [hρ.ne'],
      Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num)]
  rw [hpow] at hMy
  have h8 : ENNReal.ofReal ((8 : ℝ) ^ (-β)) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hMy' : M * ENNReal.ofReal ((8 : ℝ) ^ (-β)) ≤ μ (ball y (ρ / 8)) :=
    (ENNReal.le_div_iff_mul_le (Or.inl h8) (Or.inl ENNReal.ofReal_ne_top)).1 hMy
  have hlow : ENNReal.ofReal (C₁m * (8 : ℝ) ^ (-β)) * μ A ≤ μ K := by
    calc
      ENNReal.ofReal (C₁m * (8 : ℝ) ^ (-β)) * μ A ≤
          ENNReal.ofReal (C₁m * (8 : ℝ) ^ (-β)) * μ A' :=
            mul_le_mul_right (measure_mono hAA) _
      _ = ENNReal.ofReal C₁m * μ A' * ENNReal.ofReal ((8 : ℝ) ^ (-β)) := by
        rw [ENNReal.ofReal_mul h1m.le]
        ring
      _ ≤ M * ENNReal.ofReal ((8 : ℝ) ^ (-β)) := mul_le_mul_left hMlo _
      _ ≤ μ (ball y (ρ / 8)) := hMy'
      _ ≤ μ K := measure_mono hBy
  have hA0 : μ A ≠ 0 := by
    intro h0
    have hball0 : μ (ball y (ρ / 8)) = 0 :=
      le_zero_iff.1 ((measure_mono (hBy.trans hKA)).trans h0.le)
    rw [hball0] at hMy'
    exact (mul_ne_zero hM0 h8) (le_zero_iff.1 hMy')
  have hAt : μ A ≠ ∞ := ne_top_of_le_ne_top hYt (measure_mono hAA)
  have hcoeff : ENNReal.ofReal α < ENNReal.ofReal (C₁m * (8 : ℝ) ^ (-β)) :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hα0).2 hα
  have hless : ENNReal.ofReal α * μ A < μ K := by
    have h := ENNReal.mul_lt_mul_left hA0 hAt hcoeff
    exact h.trans_le hlow
  exact exists_mem_sdiff_of_outer_mass_bound μ hKA hmass hless

/-- The middle-annulus odometer of a pole-avoiding local component is bounded
by the Green-potential supremum when the component has small outer mass and
uniform Harnack chains are available. -/
theorem component_middle_annulus_odometer_le_of_outer_mass_of_chains
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {βminus βplus : ℝ} (hV : VolumeGrowth μ 1 βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) {t : ℝ} (ht : 0 < t)
    {U D : Set ℂ} (hUsub : U ⊆ ball (0 : ℂ) 1)
    (hD : D ∈ connectedComponentsIn (U ∩ cluster μ 1 z t)) (hzD : z ∉ D)
    {ρ : ℝ} (hρ : 0 < ρ) {x₀ : ℂ}
    (hA : annulus x₀ (ρ / 4) ρ ⊆ U) {C₁m C₁p α : ℝ}
    (h1m : 0 < C₁m) (hα0 : 0 ≤ α)
    (hv1 : annulusBallMassSize μ βminus ρ x₀ / μ (annulus x₀ (ρ / 4) (2 * ρ)) ∈
      Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p))
    (hmass : μ (D ∩ annulus x₀ (ρ / 2) ρ) ≤
      ENNReal.ofReal α * μ (annulus x₀ (ρ / 2) ρ))
    (hα : α < C₁m * (8 : ℝ) ^ (-βminus)) {r : ℝ} (hr : 0 < r) (N : ℕ)
    (hchains : ∀ y ∈ annulus x₀ (ρ / 2) (7 / 8 * ρ),
      ∀ x ∈ annulus x₀ (ρ / 2) (7 / 8 * ρ) ∩ D, ∃ p : ℕ → ℂ,
        p 0 = y ∧ p N = x ∧
        (∀ i < N, closedBall (p i) r ⊆ annulus x₀ (ρ / 4) ρ) ∧
        (∀ i < N, p (i + 1) ∈ closedBall (p i) (r / 2))) :
    ⨆ x ∈ annulus x₀ (ρ / 2) (7 / 8 * ρ) ∩ D, odometerExt μ z t x ≤
      ENNReal.ofReal ((4 : ℝ) ^ N) * annulusGreenPotentialSup μ x₀ (ρ / 4) ρ := by
  obtain ⟨y, hy, hyD⟩ := exists_middle_annulus_not_mem_of_outer_mass
    hρ h1m hα0 hv1 hmass hα
  have hKA : annulus x₀ (ρ / 2) (7 / 8 * ρ) ⊆ annulus x₀ (ρ / 4) ρ :=
    annulus_subset_annulus (by linarith) (by linarith)
  exact component_odometer_iSup_le_greenPotentialSup_of_harnack_chains
    hμ hV hz ht hUsub hD hzD (by linarith) hρ hA (hKA hy) hyD hKA hr N (hchains y hy)

end HarmonicBalls
