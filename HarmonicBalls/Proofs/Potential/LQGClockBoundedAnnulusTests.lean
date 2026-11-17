import HarmonicBalls.Proofs.Potential.LQGClockCountableOccupationTests
import HarmonicBalls.Proofs.Potential.LQGClockAnnularAnnealedIncrement

/-! # Inserted occupation tests on bounded annuli

Dyadic inserted field occupations converge for countable families of Brownian
occupation submeasures on a bounded annulus of arbitrary radius.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped NNReal ENNReal
namespace HarmonicBalls

private theorem bounded_annulus_weight_bounded {δ r γ α : ℝ} (hδ : 0 < δ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ,
      |({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ r}.indicator
        (fun z => Real.exp (-γ*α*Real.log (max δ ‖z‖))) z)| ≤ M := by
  let f : ℂ → ℝ := fun z => Real.exp (-γ*α*Real.log (max δ ‖z‖))
  have hf : Continuous f := by
    exact Real.continuous_exp.comp (continuous_const.mul
      ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left hδ).ne')))
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : ℂ) r).bddAbove_image hf.continuousOn
  refine ⟨max K 0, le_max_right _ _, ?_⟩
  intro z
  by_cases hz : z ∈ {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ r}
  · have hzk : z ∈ Metric.closedBall (0 : ℂ) r := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz.2
    have hle : f z ≤ K := hK ⟨z, hzk, rfl⟩
    rw [Set.indicator_of_mem hz, abs_of_pos (Real.exp_pos _)]
    exact hle.trans (le_max_left K 0)
  · rw [Set.indicator_of_notMem hz, abs_zero]
    exact le_max_right K 0

/-- For a fixed positive annular cutoff, inserted dyadic occupations converge
simultaneously for any specified countable family of unit-time Brownian
occupation submeasures. -/
theorem ae_brownian_field_tendsto_countable_bounded_annulus_inserted_tests
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) (x : ℂ) {δ : ℝ} (hδ : 0 < δ) {r : ℝ} (hr : 0 < r) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    ∀ᵐ b ∂(planarBrownianMotion x), ∀ μ : ι → Measure ℂ,
      (∀ i, μ i ≤ Measure.map (fun t => b t) ν) → ∀ᵐ ω ∂P,
      ∀ i, ∃ L : ℝ, Tendsto (fun n : ℕ =>
        let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
        ∫ z, {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ r}.indicator (fun z =>
          ε^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) z ∂(μ i))
          atTop (𝓝 L) := by
  let A : Set ℂ := {z | δ ≤ ‖z‖ ∧ ‖z‖ ≤ r}
  let g : ℂ → ℝ := A.indicator (fun z => Real.exp (-γ*α*Real.log (max δ ‖z‖)))
  have hA : MeasurableSet A := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  have hgm : Measurable g := by
    apply Measurable.indicator _ hA
    exact (Real.continuous_exp.comp (continuous_const.mul
      ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left hδ).ne')))).measurable
  obtain ⟨M, hM, hgM⟩ := bounded_annulus_weight_bounded (r := r) (γ := γ) (α := α) hδ
  have hgs : ∀ z, g z ≠ 0 → ‖z‖ ≤ (r + 1) - 1/2 := by
    intro z hz
    have hzA : z ∈ A := by
      by_contra h
      exact hz (Set.indicator_of_notMem h _)
    linarith [hzA.2]
  have hs := ae_brownian_field_tendsto_countable_occupation_tests (ι := ι) hh hγ0 hγ2 x
    (R := r + 1) (by linarith) hgm hM hgM hgs
  have hsmall : ∀ᶠ n : ℕ in atTop, (2 : ℝ)⁻¹ ^ (n+1) < δ := by
    have ht : Tendsto (fun n : ℕ => (2 : ℝ)⁻¹ ^ (n+1)) atTop (𝓝 0) := by
      exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
        (tendsto_add_atTop_nat 1)
    exact ht.eventually (Iio_mem_nhds hδ)
  filter_upwards [hs] with b hb
  intro μ hμ
  filter_upwards [hb μ hμ, ae_recentered_inserted_circle_average hh α] with ω hω hrec i
  obtain ⟨L, hL⟩ := hω i
  refine ⟨L, hL.congr' ?_⟩
  filter_upwards [hsmall] with n hn
  apply integral_congr_ae
  filter_upwards with z
  by_cases hz : z ∈ A
  · have he : 0 < (2 : ℝ)⁻¹ ^ (n+1) := by positivity
    have hm : max ((2 : ℝ)⁻¹ ^ (n+1)) ‖z‖ = ‖z‖ := max_eq_right (le_trans hn.le hz.1)
    have hm' : max δ ‖z‖ = ‖z‖ := max_eq_right hz.1
    rw [Set.indicator_of_mem hz, ← hrec _ z he, hm]
    dsimp only [g]
    rw [Set.indicator_of_mem hz, hm']
    rw [show Real.exp (-γ * α * Real.log ‖z‖) *
      ((2⁻¹ ^ (n + 1)) ^ (γ ^ 2 / 2) *
        Real.exp (γ * (hcirc ω (2⁻¹ ^ (n + 1)) z - hcirc ω 1 0))) =
      (2⁻¹ ^ (n + 1)) ^ (γ ^ 2 / 2) *
        (Real.exp (-γ * α * Real.log ‖z‖) *
          Real.exp (γ * (hcirc ω (2⁻¹ ^ (n + 1)) z - hcirc ω 1 0))) by ring]
    rw [← Real.exp_add]
    congr 2
    ring
  · change g z * _ = A.indicator _ z
    rw [show g z = 0 from Set.indicator_of_notMem hz _, Set.indicator_of_notMem hz, zero_mul]

end HarmonicBalls
