import HarmonicBalls.Proofs.Potential.LQGActualContinuousGreenConvergence
import HarmonicBalls.Proofs.Potential.LQGClockOfLocallyUniformLimit

/-!
# Green integrals of smooth bounded domains against the approximating measures

For a smooth bounded domain `O` and a pole `x ∈ O`, the Green function `y ↦ G_O(x, y)` is
continuous on the whole plane away from the pole: it vanishes outside `O` and tends to zero at
the boundary of `O`. A pole cutoff times it is therefore a continuous test with compact support,
and the uniform local Green bound near the pole gives, on one field event, the convergence of
`∫ G_O(x, y) ν_s(dy)` to `∫ G_O(x, y) μ_h(dy)` for every smooth bounded domain `O` and every
pole `x`, where `ν_s` are the approximating measures of the LQG measure `μ_h`. Along the dyadic
scales this is the convergence of the Green integrals `∫ 2 G_O(x, y) ε^{γ²/2} e^{γ h_ε(y)} dy`
to `2 ∫ G_O(x, y) μ_h(dy)`.
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
open LatticeProb.LQG LatticeProb.Gauss

namespace HarmonicBalls

/-- Away from its pole, the Green function of a smooth bounded domain is continuous on the whole
plane in its second variable. -/
theorem continuousAt_greenFunction_right_of_isSmoothBoundedOpen {O : Set ℂ}
    (hO : IsSmoothBoundedOpen O) {x y : ℂ} (hx : x ∈ O) (hxy : x ≠ y) :
    ContinuousAt (greenFunction O x) y := by
  have hOo := GreenGeneral.isOpen_of_isSmoothBoundedOpen hO
  have hOb : Bornology.IsBounded O := hO.1
  by_cases hyO : y ∈ O
  · exact (continuousAt_greenFunction_uncurry hOo hOb hx hyO hxy).comp
      ((continuous_const.prodMk continuous_id).continuousAt)
  have hval : greenFunction O x y = 0 := greenFunction_of_notMem_right hyO x
  have hout : Tendsto (greenFunction O x) (𝓝[(closure O)ᶜ] y) (𝓝 (greenFunction O x y)) := by
    rw [hval]
    refine tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)
    exact (greenFunction_of_notMem_right (fun h => hz (subset_closure h)) x).symm
  by_cases hyc : y ∈ closure O
  · have hsymm : greenFunction O x = fun z => greenFunction O z x :=
      funext fun z => greenFunction_bounded_open_comm hOo hOb x z
    have hin : Tendsto (greenFunction O x) (𝓝[closure O] y) (𝓝 (greenFunction O x y)) := by
      have h := GreenGeneral.tendsto_greenFunction_nhdsWithin_closure hO hyc hx hxy
      rw [greenFunction_of_notMem_left hyO x] at h
      rw [hval, hsymm]
      exact h
    have h := hin.sup hout
    rwa [← nhdsWithin_union, union_compl_self, nhdsWithin_univ] at h
  · have hmem : (closure O)ᶜ ∈ 𝓝 y := isClosed_closure.isOpen_compl.mem_nhds hyc
    rw [ContinuousAt, ← nhdsWithin_eq_nhds.mpr hmem]
    exact hout

/-- A pole cutoff times the Green function of a smooth bounded domain is continuous. -/
theorem continuous_greenPoleCutoff_mul_greenFunction {O : Set ℂ} (hO : IsSmoothBoundedOpen O)
    {x : ℂ} (hx : x ∈ O) {r : ℝ} (hr : 0 < r) :
    Continuous (fun y => greenPoleCutoff x r y * greenFunction O x y) := by
  have hc : Continuous (greenPoleCutoff x r) := by
    unfold greenPoleCutoff
    fun_prop
  apply continuous_iff_continuousAt.mpr
  intro y
  by_cases hyr : dist y x < r
  · have he : (fun z => greenPoleCutoff x r z * greenFunction O x z) =ᶠ[𝓝 y]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [(isOpen_ball.mem_nhds (show y ∈ ball x r from hyr))] with z hz
      have hz' : dist z x / r - 1 ≤ 0 := by
        have := (mem_ball.mp hz).le
        exact sub_nonpos.mpr ((div_le_one hr).2 this)
      simp [greenPoleCutoff, max_eq_left hz']
    exact continuousAt_const.congr he.symm
  · have hne : x ≠ y := by
      intro h; subst y; simp at hyr; linarith
    exact hc.continuousAt.mul (continuousAt_greenFunction_right_of_isSmoothBoundedOpen hO hx hne)

/-- The cutoff Green function of a bounded domain has compact support. -/
theorem hasCompactSupport_greenPoleCutoff_mul_greenFunction {O : Set ℂ}
    (hOb : Bornology.IsBounded O) (x : ℂ) (r : ℝ) :
    HasCompactSupport (fun y => greenPoleCutoff x r y * greenFunction O x y) := by
  refine HasCompactSupport.intro hOb.isCompact_closure fun y hy => ?_
  rw [greenFunction_of_notMem_right (fun h => hy (subset_closure h)) x, mul_zero]

/-- A local Green bound near the pole controls the error of the pole cutoff for the Green
function of a smooth bounded domain. -/
theorem greenPoleCutoff_integral_error_of_isSmoothBoundedOpen {O : Set ℂ}
    (hO : IsSmoothBoundedOpen O) {x : ℂ} (hx : x ∈ O) {r : ℝ} (hr : 0 < r)
    (ν : Measure ℂ) [IsLocallyFiniteMeasure ν]
    (hG : IntegrableOn (greenFunction O x) (ball x (2 * r)) ν) :
    Integrable (greenFunction O x) ν ∧
    ‖(∫ y, greenFunction O x y ∂ν) -
      (∫ y, greenPoleCutoff x r y * greenFunction O x y ∂ν)‖ ≤
      ∫ y in ball x (2 * r), greenFunction O x y ∂ν := by
  have hOo := GreenGeneral.isOpen_of_isSmoothBoundedOpen hO
  have hOb : Bornology.IsBounded O := hO.1
  let g : ℂ → ℝ := greenFunction O x
  let t : ℂ → ℝ := fun y => greenPoleCutoff x r y * greenFunction O x y
  let d : ℂ → ℝ := (ball x (2 * r)).indicator (fun y => greenFunction O x y)
  have htc : Continuous t := continuous_greenPoleCutoff_mul_greenFunction hO hx hr
  have ht : Integrable t ν :=
    htc.integrable_of_hasCompactSupport (hasCompactSupport_greenPoleCutoff_mul_greenFunction hOb x r)
  have hd : Integrable d ν := (integrable_indicator_iff measurableSet_ball).2 hG
  have hm : AEStronglyMeasurable (fun y => g y - t y) ν :=
    ((measurable_greenFunction hOo x).sub htc.measurable).aestronglyMeasurable
  have hpoint : ∀ y, ‖g y - t y‖ ≤ d y := by
    intro y
    have hgreen : 0 ≤ greenFunction O x y := greenFunction_nonneg hOb x y
    have hcut := greenPoleCutoff_mem_Icc x r y
    by_cases hy : y ∈ ball x (2 * r)
    · have heq : g y - t y = (1 - greenPoleCutoff x r y) * greenFunction O x y := by
        dsimp [g, t]; ring
      rw [heq]
      dsimp [d]
      rw [Set.indicator_of_mem hy, abs_mul,
        abs_of_nonneg (sub_nonneg.mpr hcut.2), abs_of_nonneg hgreen]
      nlinarith [mul_nonneg hcut.1 hgreen]
    · have hy' : 2 * r ≤ dist y x := le_of_not_gt (by simpa [mem_ball] using hy)
      dsimp [d]
      rw [Set.indicator_of_notMem hy]
      have hc := greenPoleCutoff_eq_one hr hy'
      simp [g, t, hc]
  have he : Integrable (fun y => g y - t y) ν := hd.mono' hm (ae_of_all _ hpoint)
  have hg : Integrable g ν := by
    convert he.add ht using 1
    ext y
    simp
  refine ⟨hg, ?_⟩
  have hb := norm_integral_le_of_norm_le hd (ae_of_all _ hpoint)
  rw [integral_sub hg ht] at hb
  have hdint : (∫ y, d y ∂ν) = ∫ y in ball x (2 * r), greenFunction O x y ∂ν :=
    integral_indicator measurableSet_ball
  rwa [hdint] at hb

/-- Uniform local Green control near the pole and vague convergence imply the convergence of
the Green integrals of a smooth bounded domain. -/
theorem tendsto_green_integral_of_isSmoothBoundedOpen_of_uniform_local_bound {O : Set ℂ}
    (hO : IsSmoothBoundedOpen O) {x : ℂ} (hx : x ∈ O) {ν : ℝ → Measure ℂ} {μ : Measure ℂ}
    [IsLocallyFiniteMeasure μ]
    (hν : ∀ s, 0 < s → IsLocallyFiniteMeasure (ν s))
    (hv : ∀ g : ℂ → ℝ, Continuous g → HasCompactSupport g →
      Tendsto (fun s => ∫ y, g y ∂(ν s)) (𝓝[>] 0) (𝓝 (∫ y, g y ∂μ)))
    {K a r₀ : ℝ} (hK : 0 < K) (ha : 0 < a) (hr₀ : 0 < r₀)
    (hG : ∀ r, 0 < r → r ≤ r₀ →
      (IntegrableOn (greenFunction O x) (ball x r) μ ∧
        (∫ y in ball x r, greenFunction O x y ∂μ) ≤ K * r ^ a) ∧
      ∀ s, 0 < s → s ≤ 1 →
        IntegrableOn (greenFunction O x) (ball x r) (ν s) ∧
        (∫ y in ball x r, greenFunction O x y ∂(ν s)) ≤ K * r ^ a) :
    Tendsto (fun s => ∫ y, greenFunction O x y ∂(ν s))
      (𝓝[>] 0) (𝓝 (∫ y, greenFunction O x y ∂μ)) := by
  have hpow : ContinuousAt (fun t : ℝ => K * t ^ a) 0 :=
    continuousAt_const.mul (Real.continuousAt_rpow_const 0 a (Or.inr ha.le))
  have hzero : K * (0 : ℝ) ^ a = 0 := by simp [Real.zero_rpow (ne_of_gt ha)]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hδsmall⟩ := Metric.continuousAt_iff.mp hpow (ε / 3) (by positivity)
  let r := min δ r₀ / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hrδ : 2 * r < δ := by dsimp [r]; have := min_le_left δ r₀; linarith
  have hrr₀ : 2 * r ≤ r₀ := by dsimp [r]; have := min_le_right δ r₀; linarith
  have hsmall : K * (2 * r) ^ a < ε / 3 := by
    have hh := hδsmall (x := 2 * r) (by
      rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity : 0 < 2 * r)]
      exact hrδ)
    rw [Real.dist_eq, hzero, sub_zero, abs_of_nonneg (by positivity)] at hh
    exact hh
  obtain ⟨⟨hμG, hμbound⟩, hsG⟩ := hG (2 * r) (by positivity) hrr₀
  have hμerr := greenPoleCutoff_integral_error_of_isSmoothBoundedOpen hO hx hr μ hμG
  have hμsmall : ‖(∫ y, greenFunction O x y ∂μ) -
      (∫ y, greenPoleCutoff x r y * greenFunction O x y ∂μ)‖ < ε / 3 :=
    lt_of_le_of_lt (hμerr.2.trans hμbound) hsmall
  have hcv := hv _ (continuous_greenPoleCutoff_mul_greenFunction hO hx hr)
    (hasCompactSupport_greenPoleCutoff_mul_greenFunction hO.1 x r)
  have hev := (Metric.tendsto_nhds.mp hcv) (ε / 3) (by positivity)
  filter_upwards [hev, self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with s hs hspos hsone
  have := hν s hspos
  obtain ⟨hsGi, hsbound⟩ := hsG s hspos hsone.le
  have hserr := greenPoleCutoff_integral_error_of_isSmoothBoundedOpen hO hx hr (ν s) hsGi
  have hssmall : ‖(∫ y, greenFunction O x y ∂(ν s)) -
      (∫ y, greenPoleCutoff x r y * greenFunction O x y ∂(ν s))‖ < ε / 3 :=
    lt_of_le_of_lt (hserr.2.trans hsbound) hsmall
  rw [Real.dist_eq] at hs ⊢
  rw [Real.norm_eq_abs] at hssmall hμsmall
  have htri := abs_sub_le (∫ y, greenFunction O x y ∂(ν s))
    (∫ y, greenPoleCutoff x r y * greenFunction O x y ∂(ν s))
    (∫ y, greenFunction O x y ∂μ)
  have htri' := abs_sub_le (∫ y, greenPoleCutoff x r y * greenFunction O x y ∂(ν s))
    (∫ y, greenPoleCutoff x r y * greenFunction O x y ∂μ)
    (∫ y, greenFunction O x y ∂μ)
  rw [abs_sub_comm] at hμsmall
  linarith

/-- On one field event, the Green integrals of every smooth bounded domain, for every pole,
against the approximating measures of the LQG measure converge to the Green integrals against
the LQG measure. -/
theorem IsWholePlaneGFF.ae_tendsto_singular_green_integral_smooth
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ) :
    ∀ᵐ ω ∂P, ∀ O : Set ℂ, IsSmoothBoundedOpen O → ∀ x : ℂ,
      Tendsto (fun s : ℝ => ∫ y, greenFunction O x y ∂
        (lqgApprox γ (fieldCircleAverage α (hcirc ω)) s)) (𝓝[>] 0)
        (𝓝 (∫ y, greenFunction O x y ∂(μ ω))) := by
  have hlp : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc :=
    (LPBridge.isWholePlaneGFF_iff P hC hcirc).mp hh
  have hlpμ : LatticeProb.LQG.IsLQGMeasureOfField P γ α hcirc μ :=
    (LPBridge.isLQGMeasureOfField_iff P γ α hcirc μ).mp hμ
  filter_upwards [hh.ae_singular_green_integral_ball_bound hγ hγ2 hαQ hμ,
    ae_tendsto_integral_singular_lqgApprox_continuum_all hlp hγ hγ2 hαQ hlpμ,
    hlp.ae_continuousOn_circle, hμ] with ω htail hv hc hm O hO x
  have hOo := GreenGeneral.isOpen_of_isSmoothBoundedOpen hO
  by_cases hx : x ∈ O
  · have : IsLocallyFiniteMeasure (μ ω) := hm.isLocallyFiniteMeasure
    have hν : ∀ s, 0 < s → IsLocallyFiniteMeasure
        (lqgApprox γ (fieldCircleAverage α (hcirc ω)) s) := by
      intro s hs
      apply LatticeProb.LQG.isLocallyFiniteMeasure_lqgApprox_of_continuous γ
      exact LQGMeasureExistenceSingular.continuous_fieldCircleAverage_of_continuous hs
        (GMCRatioLimit.continuous_slice hc hs)
    obtain ⟨R, hR⟩ := hO.1.subset_ball (0 : ℂ)
    let R' := max R 1
    have hR' : 0 < R' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    have hOR : O ⊆ ball (0 : ℂ) R' := hR.trans (ball_subset_ball (le_max_left _ _))
    have hxR : ‖x‖ ≤ R' := by
      have := mem_ball.mp (hOR hx)
      simpa [dist_zero_right] using this.le
    obtain ⟨K, a, r₀, hK, ha, hr₀, hbound⟩ := htail R' hR'
    exact tendsto_green_integral_of_isSmoothBoundedOpen_of_uniform_local_bound hO hx hν hv
      hK ha hr₀ (hbound O hOo hOR x hxR)
  · have hz : ∀ y, greenFunction O x y = 0 := fun y => greenFunction_of_notMem_left hx y
    simp only [hz, integral_zero]
    exact tendsto_const_nhds

/-- The Green integral of a bounded domain against a continuous nonnegative density, in
extended nonnegative form: `∫ 2 G_O(x, y) d(y) dy = 2 ∫ G_O(x, y) (d(y) dy)`. -/
theorem lintegral_two_greenFunction_mul_density_eq {O : Set ℂ} (hO : IsOpen O)
    (hOb : Bornology.IsBounded O) (x : ℂ) {d : ℂ → ℝ} (hd : Continuous d)
    (hd0 : ∀ y, 0 ≤ d y) :
    (∫⁻ y, ENNReal.ofReal (2 * greenFunction O x y) * ENNReal.ofReal (d y)) =
      ENNReal.ofReal (2 * ∫ y, greenFunction O x y ∂(volume.withDensity
        fun y => ENNReal.ofReal (d y))) := by
  let ν : Measure ℂ := volume.withDensity fun y => ENNReal.ofReal (d y)
  have hG0 : ∀ y, 0 ≤ greenFunction O x y := greenFunction_nonneg hOb x
  have hGm : Measurable (greenFunction O x) := measurable_greenFunction hO x
  have hlin : (∫⁻ y, ENNReal.ofReal (greenFunction O x y) ∂ν) =
      ∫⁻ y, ENNReal.ofReal (d y) * ENNReal.ofReal (greenFunction O x y) :=
    lintegral_withDensity_eq_lintegral_mul _ hd.measurable.ennreal_ofReal hGm.ennreal_ofReal
  obtain ⟨M, hM⟩ := hOb.isCompact_closure.exists_bound_of_continuousOn hd.continuousOn
  have hGi : Integrable (greenFunction O x) := integrable_greenFunction_pole hO hOb x
  have hpt (y : ℂ) : ENNReal.ofReal (d y) * ENNReal.ofReal (greenFunction O x y) ≤
      ENNReal.ofReal (max M 0) * ENNReal.ofReal (greenFunction O x y) := by
    by_cases hy : y ∈ O
    · gcongr
      have := hM y (subset_closure hy)
      rw [Real.norm_eq_abs, abs_of_nonneg (hd0 y)] at this
      exact this.trans (le_max_left _ _)
    · rw [greenFunction_of_notMem_right hy x, ENNReal.ofReal_zero, mul_zero, mul_zero]
  have hfin : (∫⁻ y, ENNReal.ofReal (greenFunction O x y) ∂ν) ≠ ⊤ := by
    rw [hlin]
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hpt)
    rw [lintegral_const_mul _ hGm.ennreal_ofReal]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
    rw [← ofReal_integral_eq_lintegral_ofReal hGi (Filter.Eventually.of_forall hG0)]
    exact ENNReal.ofReal_ne_top
  have hint : Integrable (greenFunction O x) ν := by
    refine ⟨hGm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hG0)]
    exact lt_top_iff_ne_top.mpr hfin
  rw [ENNReal.ofReal_mul (by norm_num), ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall hG0), hlin, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext y
  rw [ENNReal.ofReal_mul (by norm_num)]
  ring

/-- On one field event, for every smooth bounded domain `O` and every pole `x`, the Green
integrals `∫ 2 G_O(x, y) ε^{γ²/2} e^{γ h_ε(y)} dy` along the dyadic scales converge to
`2 ∫ G_O(x, y) μ_h(dy)`. -/
theorem IsWholePlaneGFF.ae_tendsto_green_lintegral_smooth
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ) :
    ∀ᵐ ω ∂P, ∀ O : Set ℂ, IsSmoothBoundedOpen O → ∀ x : ℂ,
      Tendsto (fun k : ℕ => ∫⁻ y, ENNReal.ofReal (2 * greenFunction O x y) *
        ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) *
          Real.exp (γ * fieldCircleAverage α (hcirc ω) (dyadicScale k) y))) atTop
        (𝓝 (ENNReal.ofReal (2 * ∫ y, greenFunction O x y ∂(μ ω)))) := by
  have hlp : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc :=
    (LPBridge.isWholePlaneGFF_iff P hC hcirc).mp hh
  filter_upwards [hh.ae_tendsto_singular_green_integral_smooth hγ hγ2 hαQ hμ,
    HarmonicBalls.ae_continuous_fieldCircleAverage hlp α] with ω hlim hcω O hO x
  have hOo := GreenGeneral.isOpen_of_isSmoothBoundedOpen hO
  have hseq : Tendsto (fun k : ℕ => dyadicScale k) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Filter.Eventually.of_forall fun k => dyadicScale_pos k⟩
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hI := (hlim O hO x).comp hseq
  have hconv : Tendsto (fun k : ℕ => ENNReal.ofReal (2 * ∫ y, greenFunction O x y ∂
      (lqgApprox γ (fieldCircleAverage α (hcirc ω)) (dyadicScale k)))) atTop
      (𝓝 (ENNReal.ofReal (2 * ∫ y, greenFunction O x y ∂(μ ω)))) :=
    ENNReal.tendsto_ofReal (hI.const_mul 2)
  refine hconv.congr fun k => ?_
  have hdc : Continuous (fun y => dyadicScale k ^ (γ ^ 2 / 2) *
      Real.exp (γ * fieldCircleAverage α (hcirc ω) (dyadicScale k) y)) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
      (hcω _ (dyadicScale_pos k))))
  have hd0 (y : ℂ) : 0 ≤ dyadicScale k ^ (γ ^ 2 / 2) *
      Real.exp (γ * fieldCircleAverage α (hcirc ω) (dyadicScale k) y) :=
    mul_nonneg (Real.rpow_nonneg (dyadicScale_pos k).le _) (Real.exp_pos _).le
  exact (lintegral_two_greenFunction_mul_density_eq hOo hO.1 x hdc hd0).symm

end HarmonicBalls
