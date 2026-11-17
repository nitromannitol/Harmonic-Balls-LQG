import HarmonicBalls.Proofs.Potential.LQGUniformGreenTail
import HarmonicBalls.Proofs.GFF.LQGMeasureContinuumConvergence
import HarmonicBalls.FirstPass.LPBridge.M4

/-!
# Green integrals against continuous tests

Compactly supported continuous tests can be combined with a cutoff at the Green pole.
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
open LatticeProb.LQG LatticeProb.Gauss

namespace HarmonicBalls

/-- A continuous cutoff for the Green pole. -/
noncomputable def greenPoleCutoff (x : ℂ) (r : ℝ) (y : ℂ) : ℝ :=
  min 1 (max 0 (dist y x / r - 1))

/-- A pole cutoff times a test supported inside the domain is continuous. -/
theorem continuous_greenPoleCutoff_mul {O : Set ℂ} (hO : IsOpen O)
    (hOb : Bornology.IsBounded O) {x : ℂ} (hx : x ∈ O) {r : ℝ} (hr : 0 < r)
    {f : ℂ → ℝ} (hf : Continuous f) (hfs : tsupport f ⊆ O) :
    Continuous (fun y => greenPoleCutoff x r y * greenFunction O x y * f y) := by
  have hc : Continuous (greenPoleCutoff x r) := by
    unfold greenPoleCutoff
    fun_prop
  apply continuous_iff_continuousAt.mpr
  intro y
  by_cases hyf : y ∈ tsupport f
  · have hyO : y ∈ O := hfs hyf
    by_cases hyr : dist y x < r
    · have he : (fun z => greenPoleCutoff x r z * greenFunction O x z * f z) =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
        filter_upwards [(isOpen_ball.mem_nhds (show y ∈ ball x r from hyr))] with z hz
        have hz' : dist z x / r - 1 ≤ 0 := by
          have := (mem_ball.mp hz).le
          exact sub_nonpos.mpr ((div_le_one hr).2 this)
        simp [greenPoleCutoff, max_eq_left hz']
      exact continuousAt_const.congr he.symm
    · have hne : x ≠ y := by
        intro h; subst y; simp at hyr; linarith
      have hg : ContinuousAt (fun z => greenFunction O x z) y :=
        (continuousAt_greenFunction_uncurry hO hOb hx hyO hne).comp
          ((continuous_const.prodMk continuous_id).continuousAt)
      exact (hc.continuousAt.mul hg).mul hf.continuousAt
  · have he : (fun z => greenPoleCutoff x r z * greenFunction O x z * f z) =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
      filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hyf] with z hz
      have hz' : f z = 0 := by
        by_contra hn
        exact (show z ∉ tsupport f from hz) (subset_closure hn)
      rw [hz', mul_zero]
    exact continuousAt_const.congr he.symm

/-- The cutoff Green test has compact support. -/
theorem hasCompactSupport_greenPoleCutoff_mul {O : Set ℂ} (x : ℂ) (r : ℝ)
    {f : ℂ → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (fun y => greenPoleCutoff x r y * greenFunction O x y * f y) :=
  hf.mul_left

/-- The pole cutoff lies between zero and one. -/
theorem greenPoleCutoff_mem_Icc (x : ℂ) (r : ℝ) (y : ℂ) :
    greenPoleCutoff x r y ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact le_min (by norm_num) (le_max_left _ _)
  · exact min_le_left _ _

/-- The pole cutoff equals one beyond twice its radius. -/
theorem greenPoleCutoff_eq_one {x y : ℂ} {r : ℝ} (hr : 0 < r)
    (hy : 2 * r ≤ dist y x) : greenPoleCutoff x r y = 1 := by
  have h : 1 ≤ dist y x / r - 1 := by
    have hd : 2 ≤ dist y x / r := (le_div_iff₀ hr).2 (by linarith)
    linarith
  exact min_eq_left (le_trans h (le_max_right _ _))

/-- A local Green bound controls the cutoff error in absolute value. -/
theorem greenPoleCutoff_integral_error {O : Set ℂ} (hO : IsOpen O)
    (hOb : Bornology.IsBounded O) {x : ℂ} (hx : x ∈ O) {r C : ℝ}
    (hr : 0 < r) (hC : 0 ≤ C) {f : ℂ → ℝ} (hf : Continuous f)
    (hfs : HasCompactSupport f) (hfO : tsupport f ⊆ O)
    (hfC : ∀ y, ‖f y‖ ≤ C) (ν : Measure ℂ) [IsLocallyFiniteMeasure ν]
    (hG : IntegrableOn (greenFunction O x) (ball x (2 * r)) ν) :
    Integrable (fun y => greenFunction O x y * f y) ν ∧
    ‖(∫ y, greenFunction O x y * f y ∂ν) -
      (∫ y, greenPoleCutoff x r y * greenFunction O x y * f y ∂ν)‖ ≤
      C * ∫ y in ball x (2 * r), greenFunction O x y ∂ν := by
  let g : ℂ → ℝ := fun y => greenFunction O x y * f y
  let t : ℂ → ℝ := fun y => greenPoleCutoff x r y * greenFunction O x y * f y
  let d : ℂ → ℝ := (ball x (2 * r)).indicator (fun y => C * greenFunction O x y)
  have ht : Integrable t ν :=
    (continuous_greenPoleCutoff_mul hO hOb hx hr hf hfO).integrable_of_hasCompactSupport
      (hasCompactSupport_greenPoleCutoff_mul x r hfs)
  have hd : Integrable d ν := (integrable_indicator_iff measurableSet_ball).2 (hG.const_mul C)
  have hm : AEStronglyMeasurable (fun y => g y - t y) ν := by
    have hg : Measurable g := (measurable_greenFunction hO x).mul hf.measurable
    exact (hg.sub (continuous_greenPoleCutoff_mul hO hOb hx hr hf hfO).measurable).aestronglyMeasurable
  have hpoint : ∀ y, ‖g y - t y‖ ≤ d y := by
    intro y
    have hgreen : 0 ≤ greenFunction O x y := greenFunction_nonneg hOb x y
    have hcut := greenPoleCutoff_mem_Icc x r y
    by_cases hy : y ∈ ball x (2 * r)
    · have heq : g y - t y = (1 - greenPoleCutoff x r y) * greenFunction O x y * f y := by
        dsimp [g, t]; ring
      rw [heq]
      dsimp [d]
      rw [Set.indicator_of_mem hy]
      rw [abs_mul, abs_mul,
        abs_of_nonneg (sub_nonneg.mpr hcut.2), abs_of_nonneg hgreen, ← Real.norm_eq_abs]
      have hprod := mul_le_mul_of_nonneg_left (hfC y)
        (mul_nonneg (sub_nonneg.mpr hcut.2) hgreen)
      calc
        (1 - greenPoleCutoff x r y) * greenFunction O x y * ‖f y‖ ≤
            ((1 - greenPoleCutoff x r y) * greenFunction O x y) * C := hprod
        _ ≤ C * greenFunction O x y := by nlinarith [mul_nonneg hcut.1 hgreen]
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
  have hdint : (∫ y, d y ∂ν) = C * ∫ y in ball x (2 * r), greenFunction O x y ∂ν := by
    rw [show d = (ball x (2 * r)).indicator (fun y => C * greenFunction O x y) from rfl,
      integral_indicator measurableSet_ball, integral_const_mul]
  rwa [hdint] at hb

/-- Uniform local Green control and vague convergence imply convergence of
Green integrals against a continuous test supported in the domain. -/
theorem tendsto_green_integral_of_uniform_local_bound {O : Set ℂ}
    (hO : IsOpen O) (hOb : Bornology.IsBounded O) {x : ℂ} (hx : x ∈ O)
    {f : ℂ → ℝ} (hf : Continuous f) (hfs : HasCompactSupport f)
    (hfO : tsupport f ⊆ O) {ν : ℝ → Measure ℂ} {μ : Measure ℂ}
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
    Tendsto (fun s => ∫ y, greenFunction O x y * f y ∂(ν s))
      (𝓝[>] 0) (𝓝 (∫ y, greenFunction O x y * f y ∂μ)) := by
  obtain ⟨B, hB⟩ := hfs.exists_bound_of_continuousOn hf.continuousOn
  let C := max B 0
  have hC : 0 ≤ C := le_max_right _ _
  have hfC : ∀ y, ‖f y‖ ≤ C := by
    intro y
    by_cases hy : y ∈ tsupport f
    · exact (hB y hy).trans (le_max_left _ _)
    · have : f y = 0 := by
        by_contra hn
        exact hy (subset_closure hn)
      simp [this, hC]
  have hpow : ContinuousAt (fun t : ℝ => C * K * t ^ a) 0 :=
    continuousAt_const.mul (Real.continuousAt_rpow_const 0 a (Or.inr ha.le))
  have hzero : C * K * (0 : ℝ) ^ a = 0 := by simp [Real.zero_rpow (ne_of_gt ha)]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hδsmall⟩ := Metric.continuousAt_iff.mp hpow (ε / 3) (by positivity)
  let r := min δ r₀ / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hrδ : 2 * r < δ := by dsimp [r]; have := min_le_left δ r₀; linarith
  have hrr₀ : 2 * r ≤ r₀ := by dsimp [r]; have := min_le_right δ r₀; linarith
  have hsmall : C * (K * (2 * r) ^ a) < ε / 3 := by
    have hh := hδsmall (x := 2 * r) (by
      rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity : 0 < 2 * r)]
      exact hrδ)
    rw [Real.dist_eq, hzero, sub_zero, abs_of_nonneg (by positivity)] at hh
    nlinarith
  obtain ⟨⟨hμG, hμbound⟩, hsG⟩ := hG (2 * r) (by positivity) hrr₀
  have hμerr := greenPoleCutoff_integral_error hO hOb hx hr hC hf hfs hfO hfC μ hμG
  have hμsmall : ‖(∫ y, greenFunction O x y * f y ∂μ) -
      (∫ y, greenPoleCutoff x r y * greenFunction O x y * f y ∂μ)‖ < ε / 3 :=
    lt_of_le_of_lt (hμerr.2.trans (mul_le_mul_of_nonneg_left hμbound hC)) hsmall
  have hcv := hv _ (continuous_greenPoleCutoff_mul hO hOb hx hr hf hfO)
    (hasCompactSupport_greenPoleCutoff_mul x r hfs)
  have hev := (Metric.tendsto_nhds.mp hcv) (ε / 3) (by positivity)
  filter_upwards [hev, self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with s hs hspos hsone
  have := hν s hspos
  obtain ⟨hsGi, hsbound⟩ := hsG s hspos hsone.le
  have hserr := greenPoleCutoff_integral_error hO hOb hx hr hC hf hfs hfO hfC (ν s) hsGi
  have hssmall : ‖(∫ y, greenFunction O x y * f y ∂(ν s)) -
      (∫ y, greenPoleCutoff x r y * greenFunction O x y * f y ∂(ν s))‖ < ε / 3 :=
    lt_of_le_of_lt (hserr.2.trans (mul_le_mul_of_nonneg_left hsbound hC)) hsmall
  rw [Real.dist_eq] at hs ⊢
  rw [Real.norm_eq_abs] at hssmall hμsmall
  have htri := abs_sub_le (∫ y, greenFunction O x y * f y ∂(ν s))
    (∫ y, greenPoleCutoff x r y * greenFunction O x y * f y ∂(ν s))
    (∫ y, greenFunction O x y * f y ∂μ)
  have htri' := abs_sub_le (∫ y, greenPoleCutoff x r y * greenFunction O x y * f y ∂(ν s))
    (∫ y, greenPoleCutoff x r y * greenFunction O x y * f y ∂μ)
    (∫ y, greenFunction O x y * f y ∂μ)
  rw [abs_sub_comm] at hμsmall
  linarith

/-- On one field event, singular approximations converge against every continuous
compactly supported test inside every bounded open domain, for every center. -/
theorem IsWholePlaneGFF.ae_tendsto_singular_green_integral_continuous
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ) :
    ∀ᵐ ω ∂P, ∀ O : Set ℂ, IsOpen O → Bornology.IsBounded O →
      ∀ x : ℂ, ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ O →
      Tendsto (fun s : ℝ => ∫ y, greenFunction O x y * f y ∂
        (lqgApprox γ (fieldCircleAverage α (hcirc ω)) s)) (𝓝[>] 0)
        (𝓝 (∫ y, greenFunction O x y * f y ∂(μ ω))) := by
  have hlp : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc :=
    (LPBridge.isWholePlaneGFF_iff P hC hcirc).mp hh
  have hlpμ : LatticeProb.LQG.IsLQGMeasureOfField P γ α hcirc μ :=
    (LPBridge.isLQGMeasureOfField_iff P γ α hcirc μ).mp hμ
  filter_upwards [hh.ae_singular_green_integral_ball_bound hγ hγ2 hαQ hμ,
    ae_tendsto_integral_singular_lqgApprox_continuum_all hlp hγ hγ2 hαQ hlpμ,
    hlp.ae_continuousOn_circle, hμ] with ω htail hv hc hm O hO hOb x f hf hfs hfO
  by_cases hx : x ∈ O
  · have : IsLocallyFiniteMeasure (μ ω) := hm.isLocallyFiniteMeasure
    have hν : ∀ s, 0 < s → IsLocallyFiniteMeasure
        (lqgApprox γ (fieldCircleAverage α (hcirc ω)) s) := by
      intro s hs
      apply LatticeProb.LQG.isLocallyFiniteMeasure_lqgApprox_of_continuous γ
      exact LQGMeasureExistenceSingular.continuous_fieldCircleAverage_of_continuous hs
        (GMCRatioLimit.continuous_slice hc hs)
    obtain ⟨R, hR⟩ := hOb.subset_ball (0 : ℂ)
    let R' := max R 1
    have hR' : 0 < R' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    have hOR : O ⊆ ball (0 : ℂ) R' := hR.trans (ball_subset_ball (le_max_left _ _))
    have hxR : ‖x‖ ≤ R' := by
      have := mem_ball.mp (hOR hx)
      simpa [dist_zero_right] using this.le
    obtain ⟨K, a, r₀, hK, ha, hr₀, hbound⟩ := htail R' hR'
    exact tendsto_green_integral_of_uniform_local_bound hO hOb hx hf hfs hfO hν hv
      hK ha hr₀ (hbound O hO hOR x hxR)
  · have hz : ∀ y, greenFunction O x y = 0 := by intro y; simp [greenFunction, hx]
    simp only [hz, zero_mul, integral_zero]
    exact tendsto_const_nhds

end HarmonicBalls
