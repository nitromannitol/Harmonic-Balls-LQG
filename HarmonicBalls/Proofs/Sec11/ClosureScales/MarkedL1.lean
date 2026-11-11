import Mathlib
import HarmonicBalls.Defs.LQG
import HarmonicBalls.Defs.GFF
import HarmonicBalls.Proposed.DuplantierMillerSheffield
import HarmonicBalls.Proofs.Sec11.ClosureScales.MarkedFirstMoment
import HarmonicBalls.Proofs.Sec11.ClosureScales.MarkedFatou
import HarmonicBalls.Proofs.Sec11.ClosureScales.MarkedComparison
import HarmonicBalls.Proofs.Sec11.ClosureScales.CodeLimitTools

/-! # Route (A), Palm identity: the L¹ convergence of the marked LQG masses

For `0 ≤ η ∈ C_c(B_1)`, the marked masses `X_k = μ_{2^(-k)}(η)` (density `ε^(γ²/2) exp(γ h_ε)`, `ε = 2^(-k)`) converge to
`Y = μ_g(η)` in `L¹`: `E|X_k - Y| → 0`. The proof: the a.s. vague convergence, the first moment of
`X_k` for small scales (`integral_marked_mass_eps_eq`), `E Y = ∫ η` (`integral_lqgMeasure_eq_of_nonneg`), and the
min-trick `tendsto_integral_abs_sub_of_ae_tendsto` (CodeLimitTools.lean).
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric

namespace HarmonicBalls

/-- The almost sure vague convergence of the marked masses along the dyadic scales to `μ_ω(η)`. -/
theorem ae_tendsto_marked_mass (γ : ℝ) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {η : ℂ → ℝ} (hη : Continuous η) (hηs : HasCompactSupport η) :
    ∀ᵐ ω ∂P, Tendsto (fun k : ℕ => ∫ z, η z * (dyadicScale k ^ (γ ^ 2 / 2) *
      Real.exp (γ * hcirc ω (dyadicScale k) z)) ∂(volume : Measure ℂ)) atTop
      (𝓝 (∫ z, η z ∂(μ ω))) := by
  have hμ' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage 0 (hcirc ω)) (μ ω) := hμ
  filter_upwards [hμ', hG.ae_continuousOn_circle] with ω hω hcont
  have hT := hω.tendsto_integral η hη hηs
  have hcontk : ∀ k : ℕ, Continuous (fun z => fieldCircleAverage 0 (hcirc ω) (dyadicScale k) z) := by
    intro k
    simp only [fieldCircleAverage_zero_eq]
    exact hcont.comp_continuous (continuous_const.prodMk continuous_id)
      (fun z => ⟨dyadicScale_pos k, Set.mem_univ z⟩)
  refine Tendsto.congr (fun k => ?_) hT
  rw [integral_lqgApprox_of_continuous (dyadicScale_pos k) (hcontk k) η]
  simp only [fieldCircleAverage_zero_eq]

/-- **L¹ convergence of the marked LQG masses**: for `0 ≤ η ∈ C_c(B_1)`,
`E|μ_{2^(-k)}(η) - μ_g(η)| → 0`. -/
theorem tendsto_integral_abs_marked_sub (γ : ℝ) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hU : DMSLemmaA10WholePlaneUnnormalized P γ hC hcirc μ)
    {η : ℂ → ℝ} (hη : Continuous η) (hηs : HasCompactSupport η) (hη0 : ∀ z, 0 ≤ η z)
    (htsupp : tsupport η ⊆ ball (0 : ℂ) 1) :
    Tendsto (fun k : ℕ => ∫ ω, |(∫ z, η z * (dyadicScale k ^ (γ ^ 2 / 2) *
      Real.exp (γ * hcirc ω (dyadicScale k) z)) ∂(volume : Measure ℂ)) - ∫ z, η z ∂(μ ω)| ∂P)
      atTop (𝓝 0) := by
  obtain ⟨M, hM1, hMsup⟩ := exists_margin_of_tsupport_subset_ball hηs htsupp
  have hev : ∀ᶠ k : ℕ in atTop, dyadicScale k < 1 - M := by
    have h0 : Tendsto dyadicScale atTop (𝓝 0) := by
      unfold dyadicScale
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    exact (tendsto_order.1 h0).2 (1 - M) (by linarith)
  have hdisk_ev : ∀ᶠ k : ℕ in atTop, ∀ z ∈ tsupport η, ∀ x ∈ Metric.sphere z (dyadicScale k),
      ‖x‖ ≤ 1 := by
    filter_upwards [hev] with k hk z hz x hx
    have hxz : ‖x - z‖ = dyadicScale k := by
      rw [← dist_eq_norm]
      exact mem_sphere.1 hx
    have h1 : ‖x‖ ≤ ‖z‖ + ‖x - z‖ := by
      simpa using norm_add_le z (x - z)
    have h2 := hMsup z hz
    linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 hdisk_ev
  have hY : Integrable (fun ω => ∫ z, η z ∂(μ ω)) P :=
    integrable_lqgMeasure_test_of_nonneg γ hG hμ hη hηs hη0 htsupp
  have hYmean : ∫ ω, ∫ z, η z ∂(μ ω) ∂P = ∫ z, η z ∂(volume : Measure ℂ) :=
    integral_lqgMeasure_eq_of_nonneg γ hG hμ hU hη hηs hη0 htsupp
  have hXi : ∀ k : ℕ, Integrable (fun ω => ∫ z, η z * (dyadicScale (k + N) ^ (γ ^ 2 / 2) *
      Real.exp (γ * hcirc ω (dyadicScale (k + N)) z)) ∂(volume : Measure ℂ)) P := fun k =>
    (integral_marked_mass_eps_eq hG (dyadicScale_pos (k + N)) γ hη hηs
      (hN (k + N) (Nat.le_add_left N k))).1
  have hXmean : ∀ k : ℕ, ∫ ω, ∫ z, η z * (dyadicScale (k + N) ^ (γ ^ 2 / 2) *
      Real.exp (γ * hcirc ω (dyadicScale (k + N)) z)) ∂(volume : Measure ℂ) ∂P
      = ∫ z, η z ∂(volume : Measure ℂ) := fun k =>
    (integral_marked_mass_eps_eq hG (dyadicScale_pos (k + N)) γ hη hηs
      (hN (k + N) (Nat.le_add_left N k))).2
  have hX0 : ∀ k : ℕ, 0 ≤ᵐ[P] (fun ω => ∫ z, η z * (dyadicScale (k + N) ^ (γ ^ 2 / 2) *
      Real.exp (γ * hcirc ω (dyadicScale (k + N)) z)) ∂(volume : Measure ℂ)) := fun k =>
    ae_of_all _ fun ω => integral_nonneg fun z => mul_nonneg (hη0 z)
      (mul_nonneg (Real.rpow_nonneg (dyadicScale_pos (k + N)).le _) (Real.exp_pos _).le)
  have hY0 : 0 ≤ᵐ[P] (fun ω => ∫ z, η z ∂(μ ω)) :=
    ae_of_all _ fun ω => integral_nonneg hη0
  have hconv : ∀ᵐ ω ∂P, Tendsto (fun k : ℕ => ∫ z, η z * (dyadicScale (k + N) ^ (γ ^ 2 / 2) *
      Real.exp (γ * hcirc ω (dyadicScale (k + N)) z)) ∂(volume : Measure ℂ)) atTop
      (𝓝 (∫ z, η z ∂(μ ω))) := by
    filter_upwards [ae_tendsto_marked_mass γ hG hμ hη hηs] with ω hω
    exact (tendsto_add_atTop_iff_nat N).2 hω
  have hmean : ∀ᶠ k : ℕ in atTop, ∫ ω, ∫ z, η z * (dyadicScale (k + N) ^ (γ ^ 2 / 2) *
      Real.exp (γ * hcirc ω (dyadicScale (k + N)) z)) ∂(volume : Measure ℂ) ∂P
      = ∫ ω, ∫ z, η z ∂(μ ω) ∂P :=
    Eventually.of_forall fun k => by rw [hXmean k, hYmean]
  have hmain := tendsto_integral_abs_sub_of_ae_tendsto hXi hY hX0 hY0 hmean hconv
  exact (tendsto_add_atTop_iff_nat N).1 hmain

end HarmonicBalls

end
