import Mathlib
import HarmonicBalls.Defs.GFF
import HarmonicBalls.Defs.LQG
import HarmonicBalls.Proofs.Sec2.AffineField
import HarmonicBalls.Proofs.Sec11.ClosureScales.CircleAverageJointMeasurable

/-! # Route (A), Step M: measurability of the random LQG measure

The γ-LQG measure `μ ω` is, for almost every `ω`, the vague limit of the dyadic approximations
`ε^{γ²/2} e^{γ h_ε(z)} dz` (`IsLQGLimit`), but the definition of `IsLQGMeasure` does not record that `ω ↦ μ ω` is a
random measure. The lintegral identity of `StepM` needs this. We prove it on a full-measure set `G` on which a jointly
measurable version of every dyadic circle average agrees with the field: for `f` continuous with compact support,
`ω ↦ ∫ f dμ_ω` is a pointwise limit on `G` of measurable functions (`measurable_integral_lqg_test`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Filter Topology
open scoped ENNReal NNReal

namespace HarmonicBalls

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The dyadic scales `2^{-k}` are positive. -/
theorem dyadicScale_pos_aux (k : ℕ) : 0 < dyadicScale k := by
  unfold dyadicScale
  positivity

/-- A full-measure set `G` on which the LQG measure is a vague limit of the dyadic approximations and jointly
measurable versions `g k` of the dyadic circle averages agree with the field (for every `z` at once). -/
theorem exists_lqg_good_set {P : Measure Ω} [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc) {γ : ℝ} {μ : Ω → Measure ℂ}
    (hμ : IsLQGMeasureOfField P γ 0 hcirc μ) :
    ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ (∀ ω ∈ G, IsLQGLimit γ (hcirc ω) (μ ω)) ∧
      ∃ g : ℕ → Ω → ℂ → ℝ, (∀ k, Measurable (fun p : Ω × ℂ => g k p.1 p.2)) ∧
        (∀ k ω, Continuous (g k ω)) ∧
        ∀ k, ∀ ω ∈ G, ∀ z, g k ω z = hcirc ω (dyadicScale k) z := by
  have hμ' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage 0 (hcirc ω)) (μ ω) := hμ
  have hbad : ∀ᵐ ω ∂P, IsLQGLimit γ (hcirc ω) (μ ω) := by
    filter_upwards [hμ'] with ω hω
    rwa [fieldCircleAverage_zero] at hω
  obtain ⟨Nb, hNb_sub, hNbm, hNb0⟩ := exists_measurable_superset_of_null (ae_iff.1 hbad)
  have hk : ∀ k : ℕ, ∃ g : Ω → ℂ → ℝ, Measurable (fun p : Ω × ℂ => g p.1 p.2) ∧
      (∀ ω, Continuous (g ω)) ∧ ∃ N : Set Ω, MeasurableSet N ∧ P N = 0 ∧
        ∀ ω, ω ∉ N → ∀ z, g ω z = hcirc ω (dyadicScale k) z := fun k => by
    obtain ⟨g, hgm, hgc, N, hNm, hN0, hgN⟩ :=
      exists_measurable_circleAverage_version hG (dyadicScale_pos_aux k)
    exact ⟨g, hgm, hgc, N, hNm, hN0, hgN⟩
  choose g hgm hgc N hNm hN0 hgN using hk
  refine ⟨(Nb ∪ ⋃ k, N k)ᶜ, (MeasurableSet.union hNbm (MeasurableSet.iUnion hNm)).compl, ?_, ?_,
    g, hgm, hgc, ?_⟩
  · rw [compl_compl]
    exact measure_union_null hNb0 (measure_iUnion_null fun k => hN0 k)
  · intro ω hω
    by_contra h
    exact hω (Or.inl (hNb_sub h))
  · intro k ω hω z
    exact hgN k ω (fun h => hω (Or.inr (Set.mem_iUnion.2 ⟨k, h⟩))) z

/-- Pathwise identity for one dyadic approximation: the integral of `f` against the dyadic approximation of the LQG
measure is the integral of `f(z) ε^{γ²/2} e^{γ g(z)} ` for any version `g` of the circle averages. -/
theorem integral_lqgApprox_eq (γ : ℝ) {ε : ℝ} (hε : 0 < ε) (h : ℝ → ℂ → ℝ) (gk : ℂ → ℝ)
    (hgk : ∀ z, gk z = h ε z) (hm : Measurable gk) (f : ℂ → ℝ) :
    ∫ z, f z ∂(lqgApprox γ h ε) =
      ∫ z, f z * (ε ^ (γ ^ 2 / 2) * Real.exp (γ * gk z)) ∂(volume : Measure ℂ) := by
  have hfun : (fun z => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * h ε z))) =
      fun z => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * gk z)) := by
    funext z
    rw [hgk z]
  have hmeas : Measurable (fun z => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * gk z))) :=
    ENNReal.measurable_ofReal.comp
      (measurable_const.mul (Real.continuous_exp.measurable.comp (measurable_const.mul hm)))
  unfold lqgApprox
  rw [hfun, integral_withDensity_eq_integral_toReal_smul₀ hmeas.aemeasurable]
  · congr 1
    funext z
    rw [ENNReal.toReal_ofReal (mul_nonneg (Real.rpow_nonneg hε.le _) (Real.exp_pos _).le), smul_eq_mul]
    ring
  · exact ae_of_all _ fun z => ENNReal.ofReal_lt_top

/-- For a continuous compactly supported test function `f`, the map `ω ↦ ∫ f dμ_ω` is measurable on the good set `G`
(the indicator of `G` makes it measurable everywhere): it is a pointwise limit of the measurable functions
`ω ↦ ∫ f(z) ε_k^{γ²/2} e^{γ g_k(ω,z)} dz`. -/
theorem measurable_integral_lqg_test {hcirc : Ω → ℝ → ℂ → ℝ}
    {γ : ℝ} {μ : Ω → Measure ℂ} {G : Set Ω} (hGm : MeasurableSet G)
    {g : ℕ → Ω → ℂ → ℝ} (hgm : ∀ k, Measurable (fun p : Ω × ℂ => g k p.1 p.2))
    (hgN : ∀ k, ∀ ω ∈ G, ∀ z, g k ω z = hcirc ω (dyadicScale k) z)
    (hGgood : ∀ ω ∈ G, IsLQGLimit γ (hcirc ω) (μ ω))
    {f : ℂ → ℝ} (hf : Continuous f) (hfs : HasCompactSupport f) :
    Measurable (G.indicator fun ω => ∫ z, f z ∂(μ ω)) := by
  have hA : ∀ k, Measurable (fun ω => ∫ z, f z * (dyadicScale k ^ (γ ^ 2 / 2) *
      Real.exp (γ * g k ω z)) ∂(volume : Measure ℂ)) := by
    intro k
    have hH : Measurable (fun p : Ω × ℂ => f p.2 * (dyadicScale k ^ (γ ^ 2 / 2) *
        Real.exp (γ * g k p.1 p.2))) :=
      (hf.measurable.comp measurable_snd).mul
        (measurable_const.mul (Real.continuous_exp.measurable.comp (measurable_const.mul (hgm k))))
    exact (hH.stronglyMeasurable.integral_prod_right').measurable
  have hlim : ∀ ω ∈ G, Tendsto (fun k => ∫ z, f z * (dyadicScale k ^ (γ ^ 2 / 2) *
      Real.exp (γ * g k ω z)) ∂(volume : Measure ℂ)) atTop (𝓝 (∫ z, f z ∂(μ ω))) := by
    intro ω hω
    have hI := (hGgood ω hω).tendsto_integral f hf hfs
    refine Tendsto.congr (fun k => ?_) hI
    exact (integral_lqgApprox_eq γ (dyadicScale_pos_aux k) (hcirc ω) (g k ω) (fun z => hgN k ω hω z)
      ((hgm k).comp (measurable_const.prodMk measurable_id)) f)
  refine measurable_of_tendsto_metrizable (fun k => (hA k).indicator hGm) ?_
  refine tendsto_pi_nhds.2 fun ω => ?_
  by_cases hω : ω ∈ G
  · simpa [hω] using hlim ω hω
  · simp [hω]

end HarmonicBalls

end
