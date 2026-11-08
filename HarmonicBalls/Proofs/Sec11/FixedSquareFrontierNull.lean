import HarmonicBalls.Proofs.Sec5.CircleAverageMeasurability
import HarmonicBalls.Proofs.Sec8.ConcentricCircleCovariance
import HarmonicBalls.Proofs.Sec8.CircleLogPotential
import HarmonicBalls.Proofs.Sec11.SquareFrontierLines
import HarmonicBalls.Defs.LBM
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Topology.UrysohnsLemma
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Zero-charge LQG measures do not charge deterministic Lebesgue-null compact sets

Let `h` be a whole-plane Gaussian free field (`IsWholePlaneGFF`) and let `μ` be its zero-charge γ-LQG measure
(`IsLQGMeasureOfField P γ 0 hcirc μ`, Duplantier–Sheffield 2011, Prop. 1.1; the scope `0 < γ < 2` of the paper is kept
in the statements). For every deterministic compact Lebesgue-null set `K`, almost surely `μ ω K = 0`. The quantifier
order is the one of the task: `K` is fixed before `ω`, and no samplewise absolute continuity `μ ω ≪ volume` is used.

Argument (first moment). For `0 < ε ≤ 1` and `‖z‖ ≤ R`, the circle average `h_ε(z)` has variance `2 A_ε(z) - log ε`,
where `A_ε(z)` is the circle average of `log (max |·| 1)` over `∂B_ε(z)`, and `A_ε(z) ≤ log (R + 1)`. The Gaussian
exponential moment gives `E[ε^{γ²/2} exp(γ h_ε(z))] ≤ (R + 1)^{γ²}`. Tonelli, Fatou and the dyadic vague convergence
of the LQG measure then bound `E μ(K)` by `(R + 1)^{γ²} ∫ f`, for every continuous `0 ≤ f ≤ 1` equal to `1` on `K` and
vanishing outside `B_R`. Urysohn cutoffs of `cthickening δ K` and `δ → 0` (with `Leb K = 0`) give `E μ(K) = 0`.

The square frontier `frontier (closedSquare a L)` is compact and Lebesgue-null (it lies on four lines), hence it is
zero-charge LQG-null almost surely.

Credit: the import closure of this module contains code by Leonardo Bonanno. It reaches the external LatticeProb
module `LatticeProb.Prob.Birkhoff` (his LatticeProb formalization of the ergodic theorem) through
`HarmonicBalls/Proofs/Sec8/BirkhoffPort.lean`; this module does not cite that code directly. The closure check is
recorded in `docs/campaign/audits/FixedSquareFrontierNull.md`.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Set Filter Metric Topology
open scoped ENNReal NNReal

/-- At zero charge `α₀ = 0` the field circle average is the circle average of the whole-plane field itself. -/
@[simp] theorem fieldCircleAverage_zero_charge (hc : ℝ → ℂ → ℝ) (r : ℝ) (z : ℂ) :
    fieldCircleAverage 0 hc r z = hc r z := by
  simp [fieldCircleAverage]

/-- For `0 < r ≤ 1` and `‖z‖ ≤ R`, the circle average of `log (max |·| 1)` over `∂B_r(z)` is at most `log (R + 1)`. -/
theorem circleAverage_wholePlaneNormalization_le {R : ℝ} (hR : 0 ≤ R) {z : ℂ} (hz : ‖z‖ ≤ R)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    Real.circleAverage wholePlaneNormalization z r ≤ Real.log (R + 1) := by
  rw [← Real.circleAverage_const (Real.log (R + 1)) z r]
  have hI₁ : CircleIntegrable wholePlaneNormalization z r :=
    continuous_wholePlaneNormalization.continuousOn.circleIntegrable hr.le
  have hI₂ : CircleIntegrable (fun _ : ℂ => Real.log (R + 1)) z r :=
    continuous_const.continuousOn.circleIntegrable hr.le
  refine Real.circleAverage_mono hI₁ hI₂ ?_
  intro x hx
  rw [Metric.mem_sphere, dist_eq_norm, abs_of_pos hr] at hx
  have hxn : ‖x‖ ≤ R + 1 := by
    have h := norm_add_le z (x - z)
    rw [show z + (x - z) = x by ring, hx] at h
    linarith
  show Real.log (max ‖x‖ 1) ≤ Real.log (R + 1)
  exact Real.log_le_log (lt_max_of_lt_right one_pos) (max_le hxn (by linarith))

/-- The variance of a circle average of the whole-plane GFF: `Var h_r(z) = 2 A_r(z) - log r`, where `A_r(z)` is the
circle average of `log (max |·| 1)` over `∂B_r(z)`, from the concentric covariance
`wholePlaneGFFCov_concentric_circles_general`. -/
theorem IsWholePlaneGFF.variance_circleAverage_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hgff : IsWholePlaneGFF P hC hcirc)
    {r : ℝ} (hr : 0 < r) (z : ℂ) :
    Var[fun ω => hcirc ω r z; P] = 2 * Real.circleAverage wholePlaneNormalization z r - Real.log r := by
  rw [← covariance_self (hgff.hasGaussianLaw_circle hr z).aemeasurable]
  refine (hgff.covariance_eq (.circle r z) (.circle r z) hr hr).trans ?_
  rw [wholePlaneGFFCov_concentric_circles_general hr hr z, max_self]
  ring

/-- Gaussian exponential moment of a circle average: `E exp(γ h_r(z)) = exp(γ² Var h_r(z) / 2)`. -/
theorem IsWholePlaneGFF.lintegral_exp_circleAverage_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hgff : IsWholePlaneGFF P hC hcirc)
    (γ : ℝ) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (γ * hcirc ω r z)) ∂P =
      ENNReal.ofReal (Real.exp (γ ^ 2 * Var[fun ω => hcirc ω r z; P] / 2)) := by
  have hG := hgff.hasGaussianLaw_circle hr z
  have hm : ∫ ω, hcirc ω r z ∂P = 0 := hgff.integral_eq_zero (.circle r z) hr
  have hv : 0 ≤ Var[fun ω => hcirc ω r z; P] := variance_nonneg _ _
  have hf : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (γ * x)) :=
    (Real.measurable_exp.comp (measurable_id.const_mul γ)).ennreal_ofReal
  have hmap : ∫⁻ ω, ENNReal.ofReal (Real.exp (γ * hcirc ω r z)) ∂P =
      ∫⁻ x, ENNReal.ofReal (Real.exp (γ * x)) ∂(P.map fun ω => hcirc ω r z) :=
    (lintegral_map' hf.aemeasurable hG.aemeasurable).symm
  rw [hmap, hG.map_eq_gaussianReal, hm]
  have hint : Integrable (fun x : ℝ => Real.exp (γ * x))
      (gaussianReal 0 (Var[fun ω => hcirc ω r z; P]).toNNReal) := integrable_exp_mul_gaussianReal γ
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x => (Real.exp_pos _).le)]
  congr 1
  have hmgf := congrFun (mgf_id_gaussianReal (μ := 0) (v := (Var[fun ω => hcirc ω r z; P]).toNNReal)) γ
  have hmgf' : ∫ x, Real.exp (γ * x) ∂(gaussianReal 0 (Var[fun ω => hcirc ω r z; P]).toNNReal) =
      Real.exp (0 * γ + ((Var[fun ω => hcirc ω r z; P]).toNNReal : ℝ) * γ ^ 2 / 2) := hmgf
  rw [hmgf', Real.coe_toNNReal _ hv]
  congr 1
  ring

/-- First-moment bound for one dyadic density: for `0 < ε ≤ 1` and `‖z‖ ≤ R`,
`E[ε^{γ²/2} exp(γ h_ε(z))] ≤ (R + 1)^{γ²}`. -/
theorem IsWholePlaneGFF.lintegral_density_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hgff : IsWholePlaneGFF P hC hcirc)
    (γ : ℝ) {R : ℝ} (hR : 0 ≤ R) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ∫⁻ ω, ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω ε z)) ∂P ≤
      ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log (R + 1))) := by
  have hc : 0 ≤ ε ^ (γ ^ 2 / 2) := Real.rpow_nonneg hε.le _
  simp_rw [ENNReal.ofReal_mul hc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hgff.lintegral_exp_circleAverage_eq γ hε z,
    ← ENNReal.ofReal_mul hc]
  refine ENNReal.ofReal_le_ofReal ?_
  have hA := circleAverage_wholePlaneNormalization_le hR hz hε hε1
  have hV := hgff.variance_circleAverage_eq hε z
  have hVle : Var[fun ω => hcirc ω ε z; P] ≤ 2 * Real.log (R + 1) - Real.log ε := by
    rw [hV]
    linarith
  rw [Real.rpow_def_of_pos hε, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have h2 := mul_le_mul_of_nonneg_left hVle (sq_nonneg γ)
  nlinarith [h2]

/-- Vague lower semicontinuity along the dyadic scales, with equality: for a locally finite limit `m` and a
sequence `ν k` of measures with `∫⁻ f dν k < ∞`, if `∫ f dν k → ∫ f dm` for a continuous compactly supported `f ≥ 0`,
then `∫⁻ f dm = liminf_k ∫⁻ f dν k`. -/
theorem lintegral_eq_liminf_of_tendsto {m : Measure ℂ} [IsLocallyFiniteMeasure m] {ν : ℕ → Measure ℂ}
    {f : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) (hf0 : ∀ z, 0 ≤ f z)
    (hfin : ∀ k, ∫⁻ z, ENNReal.ofReal (f z) ∂(ν k) ≠ ∞)
    (hlim : Tendsto (fun k : ℕ => ∫ z, f z ∂(ν k)) atTop (𝓝 (∫ z, f z ∂m))) :
    ∫⁻ z, ENNReal.ofReal (f z) ∂m = liminf (fun k : ℕ => ∫⁻ z, ENNReal.ofReal (f z) ∂(ν k)) atTop := by
  have hint : Integrable f m := hf.integrable_of_hasCompactSupport hfc
  have hm : ∫⁻ z, ENNReal.ofReal (f z) ∂m = ENNReal.ofReal (∫ z, f z ∂m) :=
    (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hf0)).symm
  have hk : ∀ k, ENNReal.ofReal (∫ z, f z ∂(ν k)) = ∫⁻ z, ENNReal.ofReal (f z) ∂(ν k) := by
    intro k
    have hintk : Integrable f (ν k) := by
      refine ⟨hf.aestronglyMeasurable, ?_⟩
      have h1 : ∫⁻ z, ‖f z‖ₑ ∂(ν k) = ∫⁻ z, ENNReal.ofReal (f z) ∂(ν k) :=
        lintegral_congr fun z => by rw [Real.enorm_eq_ofReal (hf0 z)]
      rw [HasFiniteIntegral, h1]
      exact lt_top_iff_ne_top.2 (hfin k)
    exact ofReal_integral_eq_lintegral_ofReal hintk (Eventually.of_forall hf0)
  have hlim' : Tendsto (fun k : ℕ => ∫⁻ z, ENNReal.ofReal (f z) ∂(ν k)) atTop
      (𝓝 (∫⁻ z, ENNReal.ofReal (f z) ∂m)) := by
    rw [hm]
    simp_rw [← hk]
    exact (ENNReal.continuous_ofReal.tendsto _).comp hlim
  exact hlim'.liminf_eq.symm

/-- Urysohn cutoffs of a compact set: for `δ > 0` there is a continuous `0 ≤ f ≤ 1` equal to `1` on `K`, vanishing
off `cthickening δ K`, with `∫⁻ f ≤ Leb (cthickening δ K)`. -/
theorem exists_cutoff_of_isCompact {K : Set ℂ} (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ f : ℂ → ℝ, Continuous f ∧ HasCompactSupport f ∧ (∀ z, 0 ≤ f z ∧ f z ≤ 1) ∧
      (∀ z ∈ K, f z = 1) ∧ (∀ z, z ∉ cthickening δ K → f z = 0) ∧
      ∫⁻ z, ENNReal.ofReal (f z) ≤ volume (cthickening δ K) := by
  have hdisj : Disjoint K (thickening δ K)ᶜ :=
    disjoint_compl_right_iff_subset.2 (self_subset_thickening hδ K)
  -- Urysohn: `g = 0` on `K` and `g = 1` off `thickening δ K`; the cutoff is `f = 1 - g`.
  obtain ⟨g, hg0, hg1, hg01⟩ := exists_continuous_zero_one_of_isCompact hK
    (isOpen_thickening.isClosed_compl) hdisj
  have hcpt : IsCompact (cthickening δ K) := hK.cthickening
  have hone : ∀ z, z ∉ cthickening δ K → g z = 1 := fun z hz =>
    hg1 (fun h => hz (thickening_subset_cthickening δ K h))
  have hint : ∫⁻ z, ENNReal.ofReal (1 - g z) ≤ volume (cthickening δ K) := by
    have hle : ∀ z, ENNReal.ofReal (1 - g z) ≤ (cthickening δ K).indicator 1 z := by
      intro z
      by_cases hz : z ∈ cthickening δ K
      · rw [indicator_of_mem hz, Pi.one_apply]
        exact ENNReal.ofReal_le_one.2 (by linarith [(hg01 z).1])
      · rw [indicator_of_notMem hz, hone z hz, sub_self, ENNReal.ofReal_zero]
    calc ∫⁻ z, ENNReal.ofReal (1 - g z) ≤ ∫⁻ z, (cthickening δ K).indicator 1 z := lintegral_mono hle
      _ = volume (cthickening δ K) := lintegral_indicator_one isClosed_cthickening.measurableSet
  refine ⟨fun z => 1 - g z, continuous_const.sub g.continuous, ?_, fun z => ⟨by linarith [(hg01 z).2],
    by linarith [(hg01 z).1]⟩, fun z hz => by simp [hg0 hz], fun z hz => by simp [hone z hz], hint⟩
  exact HasCompactSupport.intro hcpt fun z hz => by simp [hone z hz]

/-- Upper bound for the zero-charge LQG measure of a compact set through a cutoff `f` supported in `B_R`:
`E μ(K) ≤ (R + 1)^{γ²} ∫ f dLeb`. -/
theorem IsWholePlaneGFF.lintegral_lqgMeasure_le_of_cutoff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hgff : IsWholePlaneGFF P hC hcirc)
    {γ : ℝ} {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {K : Set ℂ} (hKm : MeasurableSet K) {f : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hf01 : ∀ z, 0 ≤ f z ∧ f z ≤ 1) (hK1 : ∀ z ∈ K, f z = 1) {R : ℝ} (hR : 0 ≤ R)
    (hfR : ∀ z, R < ‖z‖ → f z = 0) :
    ∫⁻ ω, μ ω K ∂P ≤
      ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log (R + 1))) * ∫⁻ z, ENNReal.ofReal (f z) := by
  have := hgff.isProbabilityMeasure
  obtain ⟨H, hHcont, hHmeas, hHae⟩ := hgff.exists_jointlyMeasurable_circleAverage
  have hμ' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage 0 (hcirc ω)) (μ ω) := hμ
  have hfeM : Measurable fun z => ENNReal.ofReal (f z) := hf.measurable.ennreal_ofReal
  -- the total mass of the cutoff is finite (it vanishes off `B_R` and is at most `1`)
  have hfint : ∫⁻ z, ENNReal.ofReal (f z) ≠ ∞ := by
    have hpt : ∀ z, ENNReal.ofReal (f z) ≤ (closedBall (0 : ℂ) R).indicator 1 z := by
      intro z
      by_cases hz : ‖z‖ ≤ R
      · rw [indicator_of_mem (mem_closedBall_zero_iff.2 hz), Pi.one_apply]
        exact ENNReal.ofReal_le_one.2 (hf01 z).2
      · rw [hfR z (lt_of_not_ge hz), ENNReal.ofReal_zero]
        exact zero_le
    have hle : ∫⁻ z, ENNReal.ofReal (f z) ≤ volume (closedBall (0 : ℂ) R) :=
      calc ∫⁻ z, ENNReal.ofReal (f z) ≤ ∫⁻ z, (closedBall (0 : ℂ) R).indicator 1 z := lintegral_mono hpt
        _ = volume (closedBall (0 : ℂ) R) := lintegral_indicator_one measurableSet_closedBall
    exact ne_top_of_le_ne_top measure_closedBall_lt_top.ne hle
  -- the dyadic approximations evaluated on `f`
  set A : ℕ → Ω → ℝ≥0∞ := fun k ω =>
    ∫⁻ z, ENNReal.ofReal (f z) ∂(lqgApprox γ (fieldCircleAverage 0 (hcirc ω)) (dyadicScale k)) with hAdef
  have hAmeas : ∀ k, AEMeasurable (A k) P := fun k =>
    (Measure.measurable_lintegral hfeM).comp_aemeasurable (hgff.aemeasurable_lqgApprox γ 0 k)
  -- the integrand of the dyadic approximation, written with the jointly measurable version `H`
  set F : ℕ → Ω → ℂ → ℝ≥0∞ := fun k ω z =>
    ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * H ω (dyadicScale k) z)) *
      ENNReal.ofReal (f z) with hFdef
  have hdens : ∀ k, ∀ᵐ ω ∂P, A k ω = ∫⁻ z, F k ω z := by
    intro k
    filter_upwards [hHae] with ω hω
    have hε := dyadicScale_pos k
    have hcont : Continuous fun z =>
        ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * H ω (dyadicScale k) z)) :=
      ENNReal.continuous_ofReal.comp
        (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul (hHcont ω _ hε))))
    simp only [hAdef, lqgApprox, fieldCircleAverage_zero_charge, ← hω, hFdef]
    exact lintegral_withDensity_eq_lintegral_mul _ hcont.measurable hfeM
  have hbound : ∀ k, ∫⁻ ω, A k ω ∂P ≤
      ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log (R + 1))) * ∫⁻ z, ENNReal.ofReal (f z) := by
    intro k
    have hε := dyadicScale_pos k
    have hε1 : dyadicScale k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hHk : Measurable fun p : Ω × ℂ => H p.1 (dyadicScale k) p.2 :=
      (hHmeas _ hε).comp measurable_swap
    have hFm : Measurable fun p : Ω × ℂ => F k p.1 p.2 := by
      simp only [hFdef]
      exact ((measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul hHk))).ennreal_ofReal).mul
        ((hf.measurable.comp measurable_snd).ennreal_ofReal)
    have hpt : ∀ z, ∫⁻ ω, F k ω z ∂P ≤
        ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log (R + 1))) * ENNReal.ofReal (f z) := by
      intro z
      by_cases hz : ‖z‖ ≤ R
      · have hGle : ∫⁻ ω, ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * H ω (dyadicScale k) z)) ∂P
            ≤ ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log (R + 1))) := by
          have hae : (fun ω => ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * H ω (dyadicScale k) z)))
              =ᵐ[P] (fun ω => ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω (dyadicScale k) z))) :=
            hHae.mono fun ω hω => by simp only [hω]
          rw [lintegral_congr_ae hae]
          exact hgff.lintegral_density_le γ hR hε hε1 hz
        simp only [hFdef]
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
        exact mul_le_mul_of_nonneg_right hGle zero_le
      · have hf0 : f z = 0 := hfR z (lt_of_not_ge hz)
        simp [hFdef, hf0]
    calc ∫⁻ ω, A k ω ∂P = ∫⁻ ω, ∫⁻ z, F k ω z ∂volume ∂P := lintegral_congr_ae (hdens k)
      _ = ∫⁻ z, ∫⁻ ω, F k ω z ∂P ∂volume := lintegral_lintegral_swap hFm.aemeasurable
      _ ≤ ∫⁻ z, ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log (R + 1))) * ENNReal.ofReal (f z) ∂volume :=
          lintegral_mono hpt
      _ = ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log (R + 1))) * ∫⁻ z, ENNReal.ofReal (f z) ∂volume :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hfinA : ∀ k, ∀ᵐ ω ∂P, A k ω < ∞ := fun k =>
    ae_lt_top' (hAmeas k)
      (ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfint) (hbound k))
  have hpt : ∀ᵐ ω ∂P, μ ω K ≤ liminf (fun k => A k ω) atTop := by
    filter_upwards [hμ', ae_all_iff.2 hfinA] with ω hω hωfin
    have := hω.isLocallyFiniteMeasure
    have hle : ∀ z, K.indicator 1 z ≤ ENNReal.ofReal (f z) := by
      intro z
      by_cases hz : z ∈ K
      · rw [indicator_of_mem hz, Pi.one_apply, hK1 z hz, ENNReal.ofReal_one]
      · rw [indicator_of_notMem hz]
        exact zero_le
    have key := lintegral_eq_liminf_of_tendsto (m := μ ω)
      (ν := fun k => lqgApprox γ (fieldCircleAverage 0 (hcirc ω)) (dyadicScale k)) hf hfc
      (fun z => (hf01 z).1) (fun k => (hωfin k).ne) (hω.tendsto_integral f hf hfc)
    calc μ ω K = ∫⁻ z, K.indicator 1 z ∂(μ ω) := (lintegral_indicator_one hKm).symm
      _ ≤ ∫⁻ z, ENNReal.ofReal (f z) ∂(μ ω) := lintegral_mono hle
      _ = liminf (fun k => A k ω) atTop := key
  have hfat : ∫⁻ ω, liminf (fun k => A k ω) atTop ∂P ≤ liminf (fun k => ∫⁻ ω, A k ω ∂P) atTop :=
    lintegral_liminf_le' hAmeas
  have hlim : liminf (fun k => ∫⁻ ω, A k ω ∂P) atTop ≤
      ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log (R + 1))) * ∫⁻ z, ENNReal.ofReal (f z) :=
    liminf_le_of_frequently_le' (Eventually.frequently (Eventually.of_forall hbound))
  exact (lintegral_mono_ae hpt).trans (hfat.trans hlim)

/-- **Zero-charge LQG measures do not charge deterministic Lebesgue-null compact sets.** If `h` is a whole-plane GFF
and `μ` is its zero-charge γ-LQG measure, then for every compact `K ⊆ ℂ` with `Leb K = 0`, almost surely `μ ω K = 0`.
The statement keeps the paper's range `0 < γ < 2`. -/
theorem IsWholePlaneGFF.ae_lqgMeasure_eq_zero_of_isCompact_volume_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hgff : IsWholePlaneGFF P hC hcirc)
    {γ : ℝ} (_hγ : 0 < γ) (_hγ2 : γ < 2) {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {K : Set ℂ} (hK : IsCompact K) (hKv : volume K = 0) :
    ∀ᵐ ω ∂P, μ ω K = 0 := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hc1 : IsCompact (cthickening (1 : ℝ) K) := hK.cthickening
  obtain ⟨R₀, hR₀⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1 hc1.isBounded
  set R : ℝ := max R₀ 0 with hRdef
  have hR : 0 ≤ R := le_max_right _ _
  have hRK : ∀ z ∈ cthickening (1 : ℝ) K, ‖z‖ ≤ R := fun z hz =>
    le_trans (mem_closedBall_zero_iff.1 (hR₀ hz)) (le_max_left _ _)
  have hkey : ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∫⁻ ω, μ ω K ∂P ≤ ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log (R + 1))) * volume (cthickening δ K) := by
    intro δ hδ hδ1
    obtain ⟨f, hf, hfc, hf01, hK1, hfδ, hfint⟩ := exists_cutoff_of_isCompact hK hδ
    have hfR : ∀ z, R < ‖z‖ → f z = 0 := by
      intro z hz
      refine hfδ z fun hzc => ?_
      have h1 : cthickening δ K ⊆ cthickening (1 : ℝ) K := cthickening_mono hδ1 K
      exact absurd (hRK z (h1 hzc)) (not_le.2 hz)
    refine (hgff.lintegral_lqgMeasure_le_of_cutoff hμ hKm hf hfc hf01 hK1 hR hfR).trans ?_
    gcongr
  have hlim : Tendsto (fun δ : ℝ => ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log (R + 1))) *
      volume (cthickening δ K)) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun δ : ℝ => volume (cthickening δ K)) (𝓝[>] 0) (𝓝 (volume K)) :=
      (tendsto_measure_cthickening_of_isCompact hK (μ := volume)).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    rw [hKv] at h
    have h2 : Tendsto (fun δ : ℝ => ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log (R + 1))) *
        volume (cthickening δ K)) (𝓝[>] 0)
        (𝓝 (ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log (R + 1))) * 0)) :=
      ENNReal.Tendsto.const_mul h (Or.inr ENNReal.ofReal_ne_top)
    rwa [mul_zero] at h2
  have hzero : ∫⁻ ω, μ ω K ∂P = 0 := by
    refine le_antisymm (ge_of_tendsto hlim ?_) zero_le
    filter_upwards [Ioo_mem_nhdsGT one_pos] with δ hδ
    exact hkey δ hδ.1 hδ.2.le
  have hAE : AEMeasurable (fun ω => μ ω K) P :=
    (Measure.measurable_coe hKm).comp_aemeasurable (hgff.aemeasurable_lqgMeasure hμ)
  exact (lintegral_eq_zero_iff' hAE).1 hzero

/-- The Lebesgue measure of a vertical line `{x | x.re = c}` in `ℂ` is zero. -/
theorem volume_setOf_re_eq_const (c : ℝ) : volume {x : ℂ | x.re = c} = 0 := by
  have h : {x : ℂ | x.re = c} = Complex.measurableEquivRealProd ⁻¹' ({c} ×ˢ (univ : Set ℝ)) := by
    ext x
    simp [Complex.measurableEquivRealProd]
  rw [h, Complex.volume_preserving_equiv_real_prod.measure_preimage
    ((measurableSet_singleton c).prod MeasurableSet.univ).nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]

/-- The Lebesgue measure of a horizontal line `{x | x.im = c}` in `ℂ` is zero. -/
theorem volume_setOf_im_eq_const (c : ℝ) : volume {x : ℂ | x.im = c} = 0 := by
  have h : {x : ℂ | x.im = c} = Complex.measurableEquivRealProd ⁻¹' ((univ : Set ℝ) ×ˢ {c}) := by
    ext x
    simp [Complex.measurableEquivRealProd]
  rw [h, Complex.volume_preserving_equiv_real_prod.measure_preimage
    (MeasurableSet.univ.prod (measurableSet_singleton c)).nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]

/-- **The fixed square frontier is zero-charge LQG-null.** For every deterministic square `frontier (closedSquare a L)`
(corner `a`, side `L ≥ 0`), almost surely `μ ω (frontier (closedSquare a L)) = 0`. The square is fixed before `ω`;
this is not a choice of good squares (compare `SquareContinuitySelection`). -/
theorem IsWholePlaneGFF.ae_lqgMeasure_frontier_closedSquare_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hgff : IsWholePlaneGFF P hC hcirc)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (a : ℂ) {L : ℝ} (hL : 0 ≤ L) :
    ∀ᵐ ω ∂P, μ ω (frontier (closedSquare a L)) = 0 := by
  have hcpt : IsCompact (closedSquare a L) := IsCompact.reProdIm isCompact_Icc isCompact_Icc
  have hfr_sub : frontier (closedSquare a L) ⊆ closedSquare a L := by
    rw [hcpt.isClosed.frontier_eq]
    exact sdiff_subset
  have hfr_cpt : IsCompact (frontier (closedSquare a L)) :=
    hcpt.of_isClosed_subset isClosed_frontier hfr_sub
  have hfr_vol : volume (frontier (closedSquare a L)) = 0 :=
    measure_mono_null (frontier_closedSquare_subset_lines a hL)
      (measure_union_null (measure_union_null (measure_union_null (volume_setOf_re_eq_const _)
        (volume_setOf_re_eq_const _)) (volume_setOf_im_eq_const _)) (volume_setOf_im_eq_const _))
  exact hgff.ae_lqgMeasure_eq_zero_of_isCompact_volume_eq_zero hγ hγ2 hμ hfr_cpt hfr_vol

end HarmonicBalls
