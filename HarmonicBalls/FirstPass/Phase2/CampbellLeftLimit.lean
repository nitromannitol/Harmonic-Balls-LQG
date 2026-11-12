import HarmonicBalls.FirstPass.Phase2.CampbellRegularized
import HarmonicBalls.FirstPass.Phase2.MassFunctionalDerived
import HarmonicBalls.FirstPass.LPBridge.M1
import HarmonicBalls.FirstPass.LPBridge.M4
import HarmonicBalls.Proofs.Sec2.AffineField
import HarmonicBalls.Proofs.Sec5.CircleAverageMeasurability
import LatticeProb.LQG.GMCL1Convergence

/-!
# The rooted side of the Campbell identity in the limit (Duplantier-Miller-Sheffield Lemma A.10)

For a whole-plane GFF `h`, `0 < γ < 2`, its `γ`-LQG measure `μ` (insertion `α = 0`), a continuous `g ≥ 0` with compact
support in the open unit disc and a random weight `0 ≤ Θ ≤ 1`,
`E[Θ ∫ g d(ε_k^{γ²/2} e^{γ h_{ε_k}} dz)] → E[Θ ∫ g dμ]` along the dyadic scales `ε_k = 2^{-k}`.

The proof: at the scales with `‖z‖ + ε_k ≤ 1` on the support of `g`, the expected approximating mass is
`E ∫ g dμ_k = ∫ g dz` (regularized Campbell identity with a test independent of the field,
`IsWholePlaneGFF.lintegral_lintegral_circleWeight_mul_eq`); Fatou along the almost sure vague convergence gives
`E ∫ g dμ ≤ ∫ g dz`, so all these masses are integrable; and the `L¹` convergence
`E |∫ g dμ_k - ∫ g dμ| → 0` (`LatticeProb.Gauss.IsWholePlaneGFF.tendsto_integral_abs_integral_lqgApprox_sub`) bounds
`|E[Θ ∫ g dμ_k] - E[Θ ∫ g dμ]|`.
-/

open MeasureTheory ProbabilityTheory Metric Set Filter Topology
open scoped ENNReal NNReal

namespace HarmonicBalls

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- Almost surely, the circle average process is continuous at every dyadic scale. -/
theorem IsWholePlaneGFF.ae_continuous_dyadic_circle (hh : IsWholePlaneGFF P hC hcirc) :
    ∀ᵐ ω ∂P, ∀ k : ℕ, Continuous (hcirc ω (dyadicScale k)) := by
  refine ae_all_iff.2 fun k => ?_
  obtain ⟨H, -, -, hHc, hH⟩ := hh.exists_measurable_circle_version (dyadicScale_pos k)
  filter_upwards [hH] with ω hω
  rw [← hω]
  exact hHc ω

/-- Almost surely, at every dyadic scale, the approximating mass of a continuous compactly supported `g ≥ 0` is
the real integral: `∫⁻ g dμ_k = ofReal (∫ g dμ_k)`. -/
theorem IsWholePlaneGFF.ae_lintegral_lqgApprox_eq_ofReal (hh : IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    {g : ℂ → ℝ} (hgc : Continuous g) (hgs : HasCompactSupport g) (hg0 : ∀ z, 0 ≤ g z) :
    ∀ᵐ ω ∂P, ∀ k : ℕ, ∫⁻ z, ENNReal.ofReal (g z) ∂(lqgApprox γ (hcirc ω) (dyadicScale k))
      = ENNReal.ofReal (∫ z, g z ∂(lqgApprox γ (hcirc ω) (dyadicScale k))) := by
  filter_upwards [hh.ae_continuous_dyadic_circle] with ω hω k
  have := MassFunctionalDerived.isLocallyFiniteMeasure_lqgApprox γ (hω k)
  exact MassFunctionalDerived.lintegral_ofReal_eq_ofReal_integral hgc hgs hg0

/-- The approximating mass `ω ↦ ∫⁻ g dμ_k` is almost everywhere measurable. -/
theorem IsWholePlaneGFF.aemeasurable_lintegral_lqgApprox (hh : IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    {g : ℂ → ℝ} (hgm : Measurable g) (k : ℕ) :
    AEMeasurable (fun ω => ∫⁻ z, ENNReal.ofReal (g z) ∂(lqgApprox γ (hcirc ω) (dyadicScale k))) P := by
  have h := hh.aemeasurable_lqgApprox γ 0 k
  simp only [fieldCircleAverage_zero] at h
  exact (Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp hgm)).comp_aemeasurable h

/-- **Expected approximating mass.** If `‖z‖ + ε ≤ 1` on the support of `g`, then at the scale `ε = 2^{-k}` the
expected approximating mass of `g ≥ 0` is `∫ g dz` (regularized Campbell identity with a test independent of the
field). -/
theorem IsWholePlaneGFF.lintegral_lintegral_lqgApprox_eq (hh : IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    {g : ℂ → ℝ} (hgc : Continuous g) {k : ℕ} (hk : ∀ z ∈ tsupport g, ‖z‖ + dyadicScale k ≤ 1) :
    ∫⁻ ω, ∫⁻ z, ENNReal.ofReal (g z) ∂(lqgApprox γ (hcirc ω) (dyadicScale k)) ∂P
      = ∫⁻ z in tsupport g, ENNReal.ofReal (g z) := by
  have hP : IsProbabilityMeasure P := hh.isGaussianProcess.isProbabilityMeasure
  have hε := dyadicScale_pos k
  have hU : MeasurableSet (tsupport g) := (isClosed_tsupport g).measurableSet
  have hΦ : Measurable fun p : ({φ : ℂ → ℝ // IsTestFunction univ φ} → ℝ) × ℂ => ENNReal.ofReal (g p.2) :=
    ENNReal.measurable_ofReal.comp (hgc.measurable.comp measurable_snd)
  have h5 := hh.lintegral_lintegral_circleWeight_mul_eq hε γ hU hk hΦ
  simp only [lintegral_const, measure_univ, mul_one] at h5
  rw [← h5]
  obtain ⟨H, hHm, -, -, hH⟩ := hh.exists_measurable_circle_version hε
  refine lintegral_congr_ae ?_
  filter_upwards [hH] with ω hω
  have hdm : Measurable fun z => ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω (dyadicScale k) z)) := by
    rw [← hω]
    exact ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.measurable_exp.comp
      (measurable_const.mul (hHm.comp measurable_prodMk_left))))
  rw [lqgApprox, lintegral_withDensity_eq_lintegral_mul _ hdm hgc.measurable.ennreal_ofReal]
  refine (setLIntegral_eq_of_support_subset ?_).symm
  intro z hz
  refine subset_tsupport g ?_
  intro hgz
  apply hz
  simp [hgz]

/-- **The rooted side in the limit.** For a whole-plane GFF, `0 < γ < 2`, the `α = 0` LQG measure `μ`, a continuous
`g ≥ 0` with compact support in the open unit disc and an almost everywhere measurable weight `0 ≤ Θ ≤ 1`,
`E[Θ ∫ g d(ε_k^{γ²/2} e^{γ h_{ε_k}} dz)] → E[Θ ∫ g dμ]` along `ε_k = 2^{-k}`. -/
theorem IsWholePlaneGFF.tendsto_lintegral_mul_lintegral_lqgApprox (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ 0 hcirc μ) {g : ℂ → ℝ}
    (hgc : Continuous g) (hgs : HasCompactSupport g) (hg1 : tsupport g ⊆ ball (0 : ℂ) 1) (hg0 : ∀ z, 0 ≤ g z)
    {Θ : Ω → ℝ} (hΘ : AEMeasurable Θ P) (hΘ0 : ∀ ω, 0 ≤ Θ ω) (hΘ1 : ∀ ω, Θ ω ≤ 1) :
    Tendsto (fun k : ℕ => ∫⁻ ω, ENNReal.ofReal (Θ ω) *
        ∫⁻ z, ENNReal.ofReal (g z) ∂(lqgApprox γ (hcirc ω) (dyadicScale k)) ∂P) atTop
      (𝓝 (∫⁻ ω, ENNReal.ofReal (Θ ω) * ∫⁻ z, ENNReal.ofReal (g z) ∂(μ ω) ∂P)) := by
  have hP : IsProbabilityMeasure P := hh.isGaussianProcess.isProbabilityMeasure
  have hμ' : ∀ᵐ ω ∂P, IsLQGLimit γ (hcirc ω) (μ ω) := by
    have h : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage 0 (hcirc ω)) (μ ω) := hμ
    filter_upwards [h] with ω hω
    rwa [fieldCircleAverage_zero] at hω
  have hL1 : Tendsto (fun k : ℕ => ∫ ω, |∫ z, g z ∂(lqgApprox γ (hcirc ω) (dyadicScale k)) -
      ∫ z, g z ∂(μ ω)| ∂P) atTop (𝓝 0) :=
    LatticeProb.Gauss.IsWholePlaneGFF.tendsto_integral_abs_integral_lqgApprox_sub
      ((LPBridge.isWholePlaneGFF_iff P hC hcirc).1 hh) hγ0 hγ2
      ((LPBridge.isLQGMeasure_iff P γ hcirc μ).1 hμ') hgc hgs hg1
  obtain ⟨k₀, hk₀⟩ := LatticeProb.Gauss.exists_norm_add_dyadicScale_le_one hgs.isCompact hg1
  have hk : ∀ k, k₀ ≤ k → ∀ z ∈ tsupport g, ‖z‖ + dyadicScale k ≤ 1 := fun k hk z hz => by
    have := hk₀ z hz (k - k₀)
    rwa [Nat.sub_add_cancel hk] at this
  -- the masses
  have hJm := fun k => hh.aemeasurable_lintegral_lqgApprox γ hgc.measurable k
  have hJI := hh.ae_lintegral_lqgApprox_eq_ofReal γ hgc hgs hg0
  have hJinfI : ∀ᵐ ω ∂P, ∫⁻ z, ENNReal.ofReal (g z) ∂(μ ω) = ENNReal.ofReal (∫ z, g z ∂(μ ω)) := by
    filter_upwards [hμ'] with ω hω
    have := hω.isLocallyFiniteMeasure
    exact MassFunctionalDerived.lintegral_ofReal_eq_ofReal_integral hgc hgs hg0
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun k => ∫⁻ z, ENNReal.ofReal (g z) ∂(lqgApprox γ (hcirc ω) (dyadicScale k)))
      atTop (𝓝 (∫⁻ z, ENNReal.ofReal (g z) ∂(μ ω))) := by
    filter_upwards [hμ', hJI, hJinfI] with ω hω h1 h2
    simp only [h1, h2]
    exact ENNReal.tendsto_ofReal (hω.tendsto_integral g hgc hgs)
  have hc : ∫⁻ z in tsupport g, ENNReal.ofReal (g z) < ∞ :=
    (hgc.integrable_of_hasCompactSupport hgs).integrableOn.lintegral_lt_top
  have hEJ : ∀ k, k₀ ≤ k → ∫⁻ ω, ∫⁻ z, ENNReal.ofReal (g z) ∂(lqgApprox γ (hcirc ω) (dyadicScale k)) ∂P
      = ∫⁻ z in tsupport g, ENNReal.ofReal (g z) := fun k hkk =>
    hh.lintegral_lintegral_lqgApprox_eq γ hgc (hk k hkk)
  have hJinfm : AEMeasurable (fun ω => ∫⁻ z, ENNReal.ofReal (g z) ∂(μ ω)) P :=
    aemeasurable_of_tendsto_metrizable_ae' hJm hlim
  have hEJinf : ∫⁻ ω, ∫⁻ z, ENNReal.ofReal (g z) ∂(μ ω) ∂P ≤ ∫⁻ z in tsupport g, ENNReal.ofReal (g z) := by
    calc ∫⁻ ω, ∫⁻ z, ENNReal.ofReal (g z) ∂(μ ω) ∂P
        = ∫⁻ ω, liminf (fun k => ∫⁻ z, ENNReal.ofReal (g z) ∂(lqgApprox γ (hcirc ω) (dyadicScale k))) atTop ∂P :=
          lintegral_congr_ae (hlim.mono fun ω h => h.liminf_eq.symm)
      _ ≤ liminf (fun k => ∫⁻ ω, ∫⁻ z, ENNReal.ofReal (g z) ∂(lqgApprox γ (hcirc ω) (dyadicScale k)) ∂P) atTop :=
          lintegral_liminf_le' hJm
      _ = ∫⁻ z in tsupport g, ENNReal.ofReal (g z) :=
          (tendsto_const_nhds.congr' ((eventually_ge_atTop k₀).mono fun k hkk => (hEJ k hkk).symm)).liminf_eq
  -- integrability of the real masses
  have hIint : ∀ k, k₀ ≤ k → Integrable (fun ω => ∫ z, g z ∂(lqgApprox γ (hcirc ω) (dyadicScale k))) P := by
    intro k hkk
    refine (integrable_toReal_of_lintegral_ne_top (hJm k) (by rw [hEJ k hkk]; exact hc.ne)).congr ?_
    filter_upwards [hJI] with ω hω
    rw [hω k, ENNReal.toReal_ofReal (integral_nonneg fun z => hg0 z)]
  have hIinfint : Integrable (fun ω => ∫ z, g z ∂(μ ω)) P := by
    refine (integrable_toReal_of_lintegral_ne_top hJinfm (lt_of_le_of_lt hEJinf hc).ne).congr ?_
    filter_upwards [hJinfI] with ω hω
    rw [hω, ENNReal.toReal_ofReal (integral_nonneg fun z => hg0 z)]
  have hΘs : AEStronglyMeasurable Θ P := hΘ.aestronglyMeasurable
  have hΘb : ∀ᵐ ω ∂P, ‖Θ ω‖ ≤ 1 := ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hΘ0 ω)]; exact hΘ1 ω
  have hΘIint : ∀ k, k₀ ≤ k →
      Integrable (fun ω => Θ ω * ∫ z, g z ∂(lqgApprox γ (hcirc ω) (dyadicScale k))) P := fun k hkk =>
    (hIint k hkk).bdd_mul hΘs hΘb
  have hΘIinfint : Integrable (fun ω => Θ ω * ∫ z, g z ∂(μ ω)) P := hIinfint.bdd_mul hΘs hΘb
  -- the real limit
  have hR : Tendsto (fun k : ℕ => ∫ ω, Θ ω * ∫ z, g z ∂(lqgApprox γ (hcirc ω) (dyadicScale k)) ∂P) atTop
      (𝓝 (∫ ω, Θ ω * ∫ z, g z ∂(μ ω) ∂P)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hL1
    filter_upwards [eventually_ge_atTop k₀] with k hkk
    rw [← integral_sub (hΘIint k hkk) hΘIinfint]
    refine norm_integral_le_of_norm_le ((hIint k hkk).sub hIinfint).abs (ae_of_all _ fun ω => ?_)
    rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hΘ0 ω)]
    exact mul_le_of_le_one_left (abs_nonneg _) (hΘ1 ω)
  -- back to `ℝ≥0∞`
  have hconv : ∀ {ν : Ω → Measure ℂ}, (∀ᵐ ω ∂P, ∫⁻ z, ENNReal.ofReal (g z) ∂(ν ω) = ENNReal.ofReal (∫ z, g z ∂(ν ω))) →
      Integrable (fun ω => Θ ω * ∫ z, g z ∂(ν ω)) P →
      ∫⁻ ω, ENNReal.ofReal (Θ ω) * ∫⁻ z, ENNReal.ofReal (g z) ∂(ν ω) ∂P
        = ENNReal.ofReal (∫ ω, Θ ω * ∫ z, g z ∂(ν ω) ∂P) := by
    intro ν hν hint
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ fun ω => mul_nonneg (hΘ0 ω) (integral_nonneg fun z => hg0 z))]
    refine lintegral_congr_ae ?_
    filter_upwards [hν] with ω hω
    rw [hω, ENNReal.ofReal_mul (hΘ0 ω)]
  rw [hconv hJinfI hΘIinfint]
  refine (ENNReal.tendsto_ofReal hR).congr' ?_
  filter_upwards [eventually_ge_atTop k₀] with k hkk
  exact (hconv (ν := fun ω => lqgApprox γ (hcirc ω) (dyadicScale k))
    (hJI.mono fun ω hω => hω k) (hΘIint k hkk)).symm

end HarmonicBalls
