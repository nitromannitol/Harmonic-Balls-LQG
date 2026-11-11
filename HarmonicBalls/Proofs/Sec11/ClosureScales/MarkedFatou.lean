import Mathlib
import HarmonicBalls.Defs.LQG
import HarmonicBalls.Defs.GFF
import HarmonicBalls.Proofs.Sec11.ClosureScales.MarkedFirstMoment
import HarmonicBalls.Proofs.Sec11.ClosureScales.CircleAverageJointMeasurable

/-! # Route (A), Palm identity: the Fatou bound for the marked LQG mass

For the γ-LQG measure `μ_g` of the whole-plane GFF with `α₀ = 0` and `0 ≤ η ∈ C_c(B_1)`, the expectation of
`μ_g(η)` is at most `∫ η`: "Fatou consequently implies `E μ_g(η) ≤ ∫ η dz`". The proof: the vague limit along the dyadic scales `2^(-k)` (`IsLQGLimit`), the first
moment `E μ_ε(η) = ∫ η` for small `ε` (`integral_marked_mass_eps_eq`), and Fatou's lemma.
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric

namespace HarmonicBalls

/-- The circle-average field at `α₀ = 0` is the circle-average process itself. -/
theorem fieldCircleAverage_zero_eq (h : ℝ → ℂ → ℝ) (r : ℝ) (z : ℂ) :
    fieldCircleAverage 0 h r z = h r z := by
  simp [fieldCircleAverage]

/-- Integrals against the approximating measure `lqgApprox` (density `ε^(γ²/2) exp(γ h_ε)`) are integrals against
the density, when the density is continuous. -/
theorem integral_lqgApprox_of_continuous {γ : ℝ} {hε : ℝ → ℂ → ℝ} {r : ℝ} (hr : 0 < r)
    (hcont : Continuous (fun z => hε r z)) (f : ℂ → ℝ) :
    ∫ z, f z ∂(lqgApprox γ hε r) = ∫ z, f z * (r ^ (γ ^ 2 / 2) * Real.exp (γ * hε r z)) := by
  unfold lqgApprox
  have hdens : Continuous fun z => r ^ (γ ^ 2 / 2) * Real.exp (γ * hε r z) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hcont))
  have hnn : ∀ z, 0 ≤ r ^ (γ ^ 2 / 2) * Real.exp (γ * hε r z) := fun z =>
    mul_nonneg (Real.rpow_nonneg hr.le _) (Real.exp_pos _).le
  rw [integral_withDensity_eq_integral_toReal_smul hdens.measurable.ennreal_ofReal
    (ae_of_all _ fun z => ENNReal.ofReal_lt_top)]
  congr 1
  funext z
  rw [ENNReal.toReal_ofReal (hnn z), smul_eq_mul, mul_comm]

/-- A compact subset of the open unit ball lies in a closed ball of radius `M < 1`. -/
theorem exists_margin_of_tsupport_subset_ball {η : ℂ → ℝ} (hηs : HasCompactSupport η)
    (htsupp : tsupport η ⊆ Metric.ball 0 1) : ∃ M < 1, ∀ z ∈ tsupport η, ‖z‖ ≤ M := by
  rcases (tsupport η).eq_empty_or_nonempty with h | hne
  · exact ⟨0, by norm_num, fun z hz => by simp [h] at hz⟩
  · obtain ⟨z0, hz0, hmax⟩ := (show IsCompact (tsupport η) from hηs).exists_isMaxOn hne
      continuous_norm.continuousOn
    refine ⟨‖z0‖, ?_, fun z hz => isMaxOn_iff.1 hmax z hz⟩
    simpa using htsupp hz0

/-- **Fatou bound for the marked LQG mass**: `E μ_g(η) ≤ ∫ η` for `0 ≤ η ∈ C_c(B_1)`. -/
theorem lintegral_lqgMeasure_le (γ : ℝ) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {η : ℂ → ℝ} (hη : Continuous η) (hηs : HasCompactSupport η) (hη0 : ∀ z, 0 ≤ η z)
    (htsupp : tsupport η ⊆ Metric.ball 0 1) :
    ∫⁻ ω, ENNReal.ofReal (∫ z, η z ∂(μ ω)) ∂P ≤ ENNReal.ofReal (∫ z, η z) := by
  obtain ⟨M, hM1, hMsup⟩ := exists_margin_of_tsupport_subset_ball hηs htsupp
  -- for large `k` the circles of radius `2^(-k)` about `tsupport η` lie in the closed unit disk
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
  -- jointly measurable versions of the circle averages at every dyadic scale
  have hver : ∀ k : ℕ, ∃ g : Ω → ℂ → ℝ, Measurable (fun p : Ω × ℂ => g p.1 p.2) ∧
      ∃ N : Set Ω, P N = 0 ∧ ∀ ω, ω ∉ N → ∀ z, g ω z = hcirc ω (dyadicScale k) z := fun k => by
    obtain ⟨g, hgm, _, N, _, hN0, hgN⟩ :=
      exists_measurable_circleAverage_version hG (dyadicScale_pos k)
    exact ⟨g, hgm, N, hN0, hgN⟩
  choose g hgm N hN0 hgN using hver
  have hAm : ∀ k : ℕ, AEMeasurable (fun ω => ∫ z, η z * (dyadicScale k ^ (γ ^ 2 / 2) *
      Real.exp (γ * hcirc ω (dyadicScale k) z)) ∂(volume : Measure ℂ)) P := by
    intro k
    have hF : Measurable (fun p : Ω × ℂ =>
        η p.2 * (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * g k p.1 p.2))) :=
      (hη.measurable.comp measurable_snd).mul
        (measurable_const.mul (Real.continuous_exp.measurable.comp (measurable_const.mul (hgm k))))
    have hS := hF.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℂ))
    refine (hS.aestronglyMeasurable.congr ?_).aemeasurable
    filter_upwards [(ae_iff (p := fun ω => ω ∉ N k)).2 (by simpa using hN0 k)] with ω hω
    simp only [hgN k ω hω]
  -- a.s. convergence of the marked masses to `μ ω η` along the dyadic scales
  have hμ' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage 0 (hcirc ω)) (μ ω) := hμ
  have hconv : ∀ᵐ ω ∂P, Tendsto (fun k : ℕ => ∫ z, η z * (dyadicScale k ^ (γ ^ 2 / 2) *
      Real.exp (γ * hcirc ω (dyadicScale k) z)) ∂(volume : Measure ℂ)) atTop
      (𝓝 (∫ z, η z ∂(μ ω))) := by
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
  -- the lower integrals are eventually `ofReal ∫ η` (first moment, `integral_marked_mass_eps_eq`)
  have hint_eq : ∀ᶠ k : ℕ in atTop, ∫⁻ ω, ENNReal.ofReal (∫ z, η z * (dyadicScale k ^ (γ ^ 2 / 2) *
      Real.exp (γ * hcirc ω (dyadicScale k) z)) ∂(volume : Measure ℂ)) ∂P
      = ENNReal.ofReal (∫ z, η z) := by
    filter_upwards [hdisk_ev] with k hk
    obtain ⟨h1, h2⟩ := integral_marked_mass_eps_eq hG (dyadicScale_pos k) γ hη hηs hk
    rw [← ofReal_integral_eq_lintegral_ofReal h1 (ae_of_all _ fun ω => integral_nonneg fun z =>
      mul_nonneg (hη0 z) (mul_nonneg (Real.rpow_nonneg (dyadicScale_pos k).le _)
        (Real.exp_pos _).le)), h2]
  have hliminf : liminf (fun k : ℕ => ∫⁻ ω, ENNReal.ofReal (∫ z, η z * (dyadicScale k ^ (γ ^ 2 / 2) *
      Real.exp (γ * hcirc ω (dyadicScale k) z)) ∂(volume : Measure ℂ)) ∂P) atTop
      = ENNReal.ofReal (∫ z, η z) :=
    Tendsto.liminf_eq (Tendsto.congr' (hint_eq.mono fun k hk => hk.symm) tendsto_const_nhds)
  -- pointwise: the liminf of the masses is the mass of the limit measure
  have hae_lim : ∀ᵐ ω ∂P, liminf (fun k : ℕ => ENNReal.ofReal (∫ z, η z * (dyadicScale k ^ (γ ^ 2 / 2) *
      Real.exp (γ * hcirc ω (dyadicScale k) z)) ∂(volume : Measure ℂ))) atTop
      = ENNReal.ofReal (∫ z, η z ∂(μ ω)) := by
    filter_upwards [hconv] with ω hω
    exact (ENNReal.tendsto_ofReal hω).liminf_eq
  calc ∫⁻ ω, ENNReal.ofReal (∫ z, η z ∂(μ ω)) ∂P
      = ∫⁻ ω, liminf (fun k : ℕ => ENNReal.ofReal (∫ z, η z * (dyadicScale k ^ (γ ^ 2 / 2) *
          Real.exp (γ * hcirc ω (dyadicScale k) z)) ∂(volume : Measure ℂ))) atTop ∂P :=
        lintegral_congr_ae (hae_lim.mono fun ω hω => hω.symm)
    _ ≤ liminf (fun k : ℕ => ∫⁻ ω, ENNReal.ofReal (∫ z, η z * (dyadicScale k ^ (γ ^ 2 / 2) *
          Real.exp (γ * hcirc ω (dyadicScale k) z)) ∂(volume : Measure ℂ)) ∂P) atTop :=
        lintegral_liminf_le' fun k => (hAm k).ennreal_ofReal
    _ = ENNReal.ofReal (∫ z, η z) := hliminf

end HarmonicBalls

end
