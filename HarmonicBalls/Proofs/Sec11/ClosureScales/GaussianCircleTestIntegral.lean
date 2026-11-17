import Mathlib
import HarmonicBalls.Defs.GFF
import HarmonicBalls.Proofs.Sec11.ClosureScales.CircleTestFubiniLimit
import HarmonicBalls.Proofs.Sec11.ClosureScales.MollifiedCircleGaussianL2
import HarmonicBalls.Proofs.Sec11.ClosureScales.CircleAverageJointMeasurable
import HarmonicBalls.Proofs.Sec11.ClosureScales.MollifiedLogCircleLimit
import HarmonicBalls.Proofs.Sec11.ClosureScales.RootedShiftProfile
import HarmonicBalls.Proofs.Sec11.ClosureScales.RouteAKernel
import HarmonicBalls.Proofs.Potential.Fundamental

/-!
# Fixed-test Gaussian circle identity (first `L²` / Fubini reconstruction ingredient)

For the whole-plane Gaussian free field `h^ℂ` of `IsWholePlaneGFF`, a smooth compactly supported test function `φ`
and a fixed radius `0 < r ≤ 1`, the circle-average integral `∫ h^ℂ_r(w) φ(w) dw` equals the pairing of `h^ℂ` with the
circle-averaged test `φ_r(v) = ⨍_{∂B_r(v)} φ`, almost surely. The argument is the written reconstruction step: the
identity first holds in `L²`, from the joint Gaussian covariance `wholePlaneGFFCov`, and then almost surely. The
deterministic input is the circle-average adjointness `CircleTestFubini.integral_circleAverage_mul_eq`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped Topology

namespace HarmonicBalls

namespace GaussianCircleTestIntegral

/-! ## Deterministic kernels -/

lemma logMaxOne_nonneg (v : ℂ) : 0 ≤ logMaxOne v :=
  Real.log_nonneg (le_max_left _ _)

/-- Absolute bound of the whole-plane covariance kernel by the two logarithmic weights and the log singularity. -/
lemma abs_wholePlaneCov_le (x y : ℂ) :
    |wholePlaneCov x y| ≤ logMaxOne x + logMaxOne y + |Real.log ‖x - y‖| := by
  unfold wholePlaneCov
  by_cases hxy : ‖x - y‖ = 0
  · rw [hxy, div_zero, Real.log_zero, abs_zero]
    linarith [logMaxOne_nonneg x, logMaxOne_nonneg y, abs_nonneg (Real.log ‖x - y‖)]
  · have hx : max ‖x‖ 1 ≠ 0 := (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'
    have hy : max ‖y‖ 1 ≠ 0 := (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'
    rw [Real.log_div (mul_ne_zero hx hy) hxy, Real.log_mul hx hy]
    have hx' : Real.log (max ‖x‖ 1) = logMaxOne x := by unfold logMaxOne; rw [max_comm]
    have hy' : Real.log (max ‖y‖ 1) = logMaxOne y := by unfold logMaxOne; rw [max_comm]
    rw [hx', hy', abs_le]
    constructor <;>
      linarith [le_abs_self (Real.log ‖x - y‖), neg_le_abs (Real.log ‖x - y‖),
        abs_nonneg (Real.log ‖x - y‖), logMaxOne_nonneg x, logMaxOne_nonneg y]

lemma measurable_wholePlaneCov : Measurable fun p : ℂ × ℂ => wholePlaneCov p.1 p.2 := by
  unfold wholePlaneCov
  fun_prop

/-- The logarithmic singularity `y ↦ |log ‖x - y‖|` is locally integrable (Fundamental, `integrableOn_ball_log_norm`). -/
lemma locallyIntegrable_abs_log_sub (x : ℂ) :
    LocallyIntegrable fun y : ℂ => |Real.log ‖x - y‖| := by
  have h := locallyIntegrable_comp_sub_of_integrableOn_ball
    (f := fun z : ℂ => |Real.log ‖z‖|) (fun R => integrableOn_abs_log_norm_ball R) x
  have he : (fun y : ℂ => |Real.log ‖x - y‖|) = fun y : ℂ => |Real.log ‖y - x‖| := by
    funext y
    rw [norm_sub_rev]
  rw [he]
  exact h

/-- For each fixed `x`, the covariance kernel is locally integrable in its second variable. -/
lemma locallyIntegrable_wholePlaneCov_right (x : ℂ) :
    LocallyIntegrable fun y : ℂ => wholePlaneCov x y := by
  have hB : LocallyIntegrable fun y : ℂ => logMaxOne x + logMaxOne y + |Real.log ‖x - y‖| :=
    ((locallyIntegrable_const _).add continuous_logMaxOne.locallyIntegrable).add
      (locallyIntegrable_abs_log_sub x)
  intro y0
  obtain ⟨s, hs, hsi⟩ := hB y0
  refine ⟨s, hs, Integrable.mono' hsi ?_ (ae_of_all _ fun y => ?_)⟩
  · exact (measurable_wholePlaneCov.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · exact (Real.norm_eq_abs _).trans_le (abs_wholePlaneCov_le x y)

/-- The circle-averaged kernel `circleKernelMean` is jointly continuous in its centre and its point. -/
lemma continuous_circleKernelMean_joint {r : ℝ} (hr : 0 < r) :
    Continuous fun p : ℂ × ℂ => circleKernelMean p.1 r p.2 := by
  have h1 : Continuous fun p : ℂ × ℂ => logMaxOne p.2 := continuous_logMaxOne.comp continuous_snd
  have h2 : Continuous fun p : ℂ × ℂ => Real.circleAverage logMaxOne p.1 r :=
    continuous_circleAverage_logMaxOne.comp (continuous_fst.prodMk continuous_const)
  have h3 : Continuous fun p : ℂ × ℂ => circlePot p.1 r p.2 := by
    unfold circlePot
    refine Continuous.log (continuous_const.max (continuous_snd.sub continuous_fst).norm) fun p => ?_
    exact (lt_of_lt_of_le hr (le_max_left _ _)).ne'
  unfold circleKernelMean
  exact (h1.add h2).sub h3

/-- The Gaussian covariance of two circle averages at radius `r`, written as the circle average of
`circleKernelMean`: `circleCovKernel r w w' = wholePlaneGFFCov (circle r w) (circle r w')`. -/
def circleCovKernel (r : ℝ) (w w' : ℂ) : ℝ :=
  Real.circleAverage (circleKernelMean w' r) w r

lemma continuous_circleCovKernel {r : ℝ} (hr : 0 < r) :
    Continuous fun p : ℂ × ℂ => circleCovKernel r p.1 p.2 := by
  have hcm : Continuous fun q : ℂ × ℝ => circleMap q.1 r q.2 := by
    unfold circleMap
    fun_prop
  have hF : Continuous fun q : (ℂ × ℂ) × ℝ => circleKernelMean q.1.2 r (circleMap q.1.1 r q.2) :=
    (continuous_circleKernelMean_joint hr).comp
      ((continuous_snd.comp continuous_fst).prodMk
        (hcm.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)))
  have hint := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (p : ℂ × ℂ) (t : ℝ) => circleKernelMean p.2 r (circleMap p.1 r t)) (μ := volume) hF 0
    (2 * Real.pi)
  unfold circleCovKernel Real.circleAverage
  simp only [smul_eq_mul]
  exact continuous_const.mul hint

/-- The kernel pairing `x ↦ ∫ ψ(y) wholePlaneCov x y dy` (the smearing of a pairing observable). -/
def kernelPairing (ψ : ℂ → ℝ) (x : ℂ) : ℝ :=
  ∫ y, ψ y * wholePlaneCov x y

/-- Integrability of a product `a(p.1) b(p.2) c(p)` of compactly supported continuous data on `ℂ × ℂ`. -/
lemma integrable_pair_mul {a b : ℂ → ℝ} (ha : Continuous a) (hb : Continuous b)
    (has : HasCompactSupport a) (hbs : HasCompactSupport b) {c : ℂ × ℂ → ℝ} (hc : Continuous c) :
    Integrable (fun p : ℂ × ℂ => a p.1 * b p.2 * c p) (volume.prod volume) := by
  refine Continuous.integrable_of_hasCompactSupport
    (((ha.comp continuous_fst).mul (hb.comp continuous_snd)).mul hc) ?_
  refine HasCompactSupport.intro (has.isCompact.prod hbs.isCompact) fun p hp => ?_
  by_cases h1 : p.1 ∈ tsupport a
  · have h2 : p.2 ∉ tsupport b := fun h2 => hp ⟨h1, h2⟩
    simp [image_eq_zero_of_notMem_tsupport h2]
  · simp [image_eq_zero_of_notMem_tsupport h1]

/-- The averaged-kernel identity: `∫ w', circleKernelMean w' r x φ(w') = kernelPairing φ_r x`, by circle-average
adjointness (`CircleTestFubini.integral_circleAverage_mul_eq`) applied to `y ↦ wholePlaneCov x y`. -/
lemma integral_circleKernelMean_mul_eq_kernelPairing {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (x : ℂ) :
    ∫ w, circleKernelMean w r x * φ w =
      kernelPairing (fun v => Real.circleAverage φ v r) x := by
  have hr1' : |r| ≤ 1 := by rw [abs_of_pos hr]; exact hr1
  have h := (CircleTestFubini.integral_circleAverage_mul_eq
    (g := fun y => wholePlaneCov x y) (locallyIntegrable_wholePlaneCov_right x) hφ hr1').2.2
  have hm : ∀ w : ℂ, Real.circleAverage (fun y => wholePlaneCov x y) w r = circleKernelMean w r x :=
    fun w => circleAverage_wholePlaneCov_eq_circleKernelMean w hr x
  simp only [hm] at h
  unfold kernelPairing
  rw [h]
  congr 1
  funext y
  ring

/-- `x ↦ kernelPairing φ_r x` is continuous (a parametric integral of a jointly continuous, compactly supported
integrand). -/
lemma continuous_kernelPairing {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    Continuous (kernelPairing fun v => Real.circleAverage φ v r) := by
  have hfun : kernelPairing (fun v => Real.circleAverage φ v r) =
      fun x => ∫ w in tsupport φ, circleKernelMean w r x * φ w := by
    funext x
    rw [← integral_circleKernelMean_mul_eq_kernelPairing hφ hr hr1 x]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw => ?_).symm
    rw [image_eq_zero_of_notMem_tsupport hw, mul_zero]
  rw [hfun]
  have hcont : Continuous fun q : ℂ × ℂ => circleKernelMean q.2 r q.1 * φ q.2 :=
    ((continuous_circleKernelMean_joint hr).comp (continuous_snd.prodMk continuous_fst)).mul
      (hφ.1.continuous.comp continuous_snd)
  exact continuous_parametric_integral_of_continuous (f := fun (x w : ℂ) => circleKernelMean w r x * φ w)
    hcont hφ.2.1.isCompact

/-- The covariance-kernel identity with the averaged test: the double circle average of the kernel integrates against
`φ ⊗ φ` to the kernel pairing of `φ_r` (two Fubini swaps and two circle-average adjointness steps). -/
lemma integral_prod_circleCovKernel {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) {r : ℝ} (hr : 0 < r)
    (hr1 : r ≤ 1) :
    ∫ p : ℂ × ℂ, φ p.1 * φ p.2 * circleCovKernel r p.1 p.2 =
      ∫ x, Real.circleAverage φ x r * kernelPairing (fun v => Real.circleAverage φ v r) x := by
  have hr1' : |r| ≤ 1 := by rw [abs_of_pos hr]; exact hr1
  have hφc : Continuous φ := hφ.1.continuous
  have hφs : HasCompactSupport φ := hφ.2.1
  have hφr := CircleTestFubini.isTestFunction_univ_circleAverage hφ hr1'
  have hφrc : Continuous fun v => Real.circleAverage φ v r := hφr.1.continuous
  have hφrs : HasCompactSupport fun v => Real.circleAverage φ v r := hφr.2.1
  have hint1 : Integrable (fun p : ℂ × ℂ => φ p.1 * φ p.2 * circleCovKernel r p.1 p.2) (volume.prod volume) :=
    integrable_pair_mul hφc hφc hφs hφs (continuous_circleCovKernel hr)
  -- inner integral in `w` for fixed `w'`: circle-average adjointness in the centre variable
  have hstep1 : ∀ w' : ℂ, ∫ w, φ w * φ w' * circleCovKernel r w w' =
      φ w' * ∫ x, circleKernelMean w' r x * Real.circleAverage φ x r := by
    intro w'
    have hgl : LocallyIntegrable (circleKernelMean w' r) :=
      (continuous_circleKernelMean_joint hr |>.comp (continuous_const.prodMk continuous_id)).locallyIntegrable
    rw [← (CircleTestFubini.integral_circleAverage_mul_eq hgl hφ hr1').2.2, ← integral_const_mul]
    congr 1
    funext w
    unfold circleCovKernel
    ring
  have hint2 : Integrable (fun p : ℂ × ℂ => φ p.1 * (circleKernelMean p.1 r p.2 * Real.circleAverage φ p.2 r))
      (volume.prod volume) :=
    (integrable_pair_mul hφc hφrc hφs hφrs (c := fun p : ℂ × ℂ => circleKernelMean p.1 r p.2)
      (continuous_circleKernelMean_joint hr)).congr (ae_of_all _ fun p => by dsimp only; ring)
  calc ∫ p : ℂ × ℂ, φ p.1 * φ p.2 * circleCovKernel r p.1 p.2
      = ∫ w, ∫ w', φ w * φ w' * circleCovKernel r w w' := integral_prod _ hint1
    _ = ∫ w', ∫ w, φ w * φ w' * circleCovKernel r w w' :=
        integral_integral_swap (f := fun w w' : ℂ => φ w * φ w' * circleCovKernel r w w') hint1
    _ = ∫ w', φ w' * ∫ x, circleKernelMean w' r x * Real.circleAverage φ x r :=
        integral_congr_ae (ae_of_all _ hstep1)
    _ = ∫ w', ∫ x, φ w' * (circleKernelMean w' r x * Real.circleAverage φ x r) := by
        congr 1
        funext w'
        rw [integral_const_mul]
    _ = ∫ x, ∫ w', φ w' * (circleKernelMean w' r x * Real.circleAverage φ x r) :=
        integral_integral_swap (f := fun w' x : ℂ => φ w' * (circleKernelMean w' r x * Real.circleAverage φ x r))
          hint2
    _ = ∫ x, Real.circleAverage φ x r * kernelPairing (fun v => Real.circleAverage φ v r) x := by
        congr 1
        funext x
        rw [← integral_circleKernelMean_mul_eq_kernelPairing hφ hr hr1 x, ← integral_const_mul]
        congr 1
        funext w'
        ring

/-! ## Probabilistic Fubini lemmas (for a jointly measurable version `g` of the circle averages) -/

/-- The weighted square integral `ω ↦ ∫ |φ(w)| g(ω,w)² dw` is integrable on the probability space: its expectation
is `∫ |φ(w)| K(w,w) dw` with the (continuous, compactly supported) diagonal kernel `K(w,w) = E[h_r(w)²]`. -/
lemma integrable_weighted_sq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {g : Ω → ℂ → ℝ} (hgm : Measurable fun p : Ω × ℂ => g p.1 p.2) (hgc : ∀ ω, Continuous (g ω))
    (hL2 : ∀ w, Integrable (fun ω => g ω w ^ 2) P)
    {r : ℝ} (hr : 0 < r) (hsq : ∀ w, ∫ ω, g ω w ^ 2 ∂P = circleCovKernel r w w)
    {φ : ℂ → ℝ} (hφc : Continuous φ) (hφs : HasCompactSupport φ) :
    Integrable (fun ω => ∫ w, |φ w| * g ω w ^ 2) P := by
  have hdiag : Continuous fun w : ℂ => (w, w) := by fun_prop
  have hK : Continuous fun w : ℂ => circleCovKernel r w w :=
    Continuous.comp (g := fun p : ℂ × ℂ => circleCovKernel r p.1 p.2) (f := fun w : ℂ => (w, w))
      (continuous_circleCovKernel hr) hdiag
  have hnn : ∀ w, 0 ≤ circleCovKernel r w w := fun w => by
    rw [← hsq w]
    exact integral_nonneg fun ω => sq_nonneg _
  have hu_cont : Continuous fun w : ℂ => |φ w| * circleCovKernel r w w :=
    ((continuous_abs.comp hφc)).mul hK
  have hu_cpt : HasCompactSupport fun w : ℂ => |φ w| * circleCovKernel r w w :=
    HasCompactSupport.intro hφs.isCompact fun w hw => by simp [image_eq_zero_of_notMem_tsupport hw]
  have hu_int : Integrable (fun w : ℂ => |φ w| * circleCovKernel r w w) volume :=
    hu_cont.integrable_of_hasCompactSupport hu_cpt
  have hu_nn : ∀ w, 0 ≤ |φ w| * circleCovKernel r w w := fun w => mul_nonneg (abs_nonneg _) (hnn w)
  have hF_int : ∀ ω, Integrable (fun w => |φ w| * g ω w ^ 2) volume := fun ω => by
    refine Continuous.integrable_of_hasCompactSupport ((continuous_abs.comp hφc).mul ((hgc ω).pow 2)) ?_
    exact HasCompactSupport.intro hφs.isCompact fun w hw => by simp [image_eq_zero_of_notMem_tsupport hw]
  have hF_nn : ∀ ω w, 0 ≤ |φ w| * g ω w ^ 2 := fun ω w => mul_nonneg (abs_nonneg _) (sq_nonneg _)
  have hm : Measurable fun p : Ω × ℂ => |φ p.2| * g p.1 p.2 ^ 2 :=
    ((continuous_abs.comp hφc).measurable.comp measurable_snd).mul (hgm.pow_const 2)
  have hQm : AEStronglyMeasurable (fun ω => ∫ w, |φ w| * g ω w ^ 2) P :=
    (hm.stronglyMeasurable.integral_prod_right' (ν := volume)).aestronglyMeasurable
  refine ⟨hQm, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω => integral_nonneg fun w => hF_nn ω w)]
  have hstep : ∀ ω, ENNReal.ofReal (∫ w, |φ w| * g ω w ^ 2) =
      ∫⁻ w, ENNReal.ofReal (|φ w| * g ω w ^ 2) :=
    fun ω => ofReal_integral_eq_lintegral_ofReal (hF_int ω) (ae_of_all _ fun w => hF_nn ω w)
  have hmeas : AEMeasurable (Function.uncurry fun ω w => ENNReal.ofReal (|φ w| * g ω w ^ 2))
      (P.prod volume) :=
    (ENNReal.measurable_ofReal.comp hm).aemeasurable
  have hinner : ∀ w, ∫⁻ ω, ENNReal.ofReal (|φ w| * g ω w ^ 2) ∂P =
      ENNReal.ofReal (|φ w| * circleCovKernel r w w) := by
    intro w
    have h1 : ∀ ω, ENNReal.ofReal (|φ w| * g ω w ^ 2) =
        ENNReal.ofReal |φ w| * ENNReal.ofReal (g ω w ^ 2) :=
      fun ω => ENNReal.ofReal_mul (abs_nonneg _)
    simp_rw [h1]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← ofReal_integral_eq_lintegral_ofReal (hL2 w) (ae_of_all _ fun ω => sq_nonneg _), hsq w,
      ← ENNReal.ofReal_mul (abs_nonneg (φ w))]
  calc ∫⁻ ω, ENNReal.ofReal (∫ w, |φ w| * g ω w ^ 2) ∂P
      = ∫⁻ ω, ∫⁻ w, ENNReal.ofReal (|φ w| * g ω w ^ 2) ∂volume ∂P := lintegral_congr fun ω => hstep ω
    _ = ∫⁻ w, ∫⁻ ω, ENNReal.ofReal (|φ w| * g ω w ^ 2) ∂P ∂volume := lintegral_lintegral_swap hmeas
    _ = ∫⁻ w, ENNReal.ofReal (|φ w| * circleCovKernel r w w) ∂volume := lintegral_congr fun w => hinner w
    _ = ENNReal.ofReal (∫ w, |φ w| * circleCovKernel r w w) :=
        (ofReal_integral_eq_lintegral_ofReal hu_int (ae_of_all _ hu_nn)).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- Fubini for the weighted pairing: `E[(∫ g(·,w) φ(w) dw) Z] = ∫ φ(w) E[g(·,w) Z] dw`, justified by the weighted
`L²` bound `hQ` and `Z ∈ L²`. -/
lemma integral_pairing_mul_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {g : Ω → ℂ → ℝ} (hgm : Measurable fun p : Ω × ℂ => g p.1 p.2) (hgc : ∀ ω, Continuous (g ω))
    {φ : ℂ → ℝ} (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (hQ : Integrable (fun ω => ∫ w, |φ w| * g ω w ^ 2) P)
    {Z : Ω → ℝ} (hZm : Measurable Z) (hZ2 : Integrable (fun ω => Z ω ^ 2) P) :
    Integrable (fun ω => (∫ w, g ω w * φ w) * Z ω) P ∧
      ∫ ω, (∫ w, g ω w * φ w) * Z ω ∂P = ∫ w, φ w * ∫ ω, g ω w * Z ω ∂P := by
  have hcpt_abs : HasCompactSupport fun w : ℂ => |φ w| :=
    HasCompactSupport.intro hφs.isCompact fun w hw => by simp [image_eq_zero_of_notMem_tsupport hw]
  have hφabs : Integrable (fun w : ℂ => |φ w|) volume :=
    hφc.abs.integrable_of_hasCompactSupport hcpt_abs
  have hfb : ∀ ω, Integrable (fun w => g ω w * φ w * Z ω) volume := fun ω => by
    refine Continuous.integrable_of_hasCompactSupport (((hgc ω).mul hφc).mul continuous_const) ?_
    exact HasCompactSupport.intro hφs.isCompact fun w hw => by simp [image_eq_zero_of_notMem_tsupport hw]
  have hbd : ∀ ω, ∫ w, ‖g ω w * φ w * Z ω‖ ∂volume ≤
      (1 / 2) * ((∫ w, |φ w| * g ω w ^ 2) + (∫ w, |φ w|) * Z ω ^ 2) := by
    intro ω
    have h1 : Integrable (fun w => |φ w| * g ω w ^ 2) volume :=
      (hφc.abs.mul ((hgc ω).pow 2)).integrable_of_hasCompactSupport
        (HasCompactSupport.intro hφs.isCompact fun w hw => by simp [image_eq_zero_of_notMem_tsupport hw])
    have h2 : Integrable (fun w => |φ w| * Z ω ^ 2) volume := hφabs.mul_const (Z ω ^ 2)
    calc ∫ w, ‖g ω w * φ w * Z ω‖ ∂volume
        ≤ ∫ w, (1 / 2) * (|φ w| * g ω w ^ 2 + |φ w| * Z ω ^ 2) ∂volume := by
          refine integral_mono (hfb ω).norm ((h1.add h2).const_mul (1 / 2)) fun w => ?_
          have hgZ : |g ω w| * |Z ω| ≤ (g ω w ^ 2 + Z ω ^ 2) / 2 := by
            nlinarith [sq_nonneg (|g ω w| - |Z ω|), sq_abs (g ω w), sq_abs (Z ω)]
          rw [Real.norm_eq_abs, abs_mul, abs_mul]
          calc |g ω w| * |φ w| * |Z ω| = |φ w| * (|g ω w| * |Z ω|) := by ring
            _ ≤ |φ w| * ((g ω w ^ 2 + Z ω ^ 2) / 2) :=
                mul_le_mul_of_nonneg_left hgZ (abs_nonneg _)
            _ = (1 / 2) * (|φ w| * g ω w ^ 2 + |φ w| * Z ω ^ 2) := by ring
      _ = (1 / 2) * ((∫ w, |φ w| * g ω w ^ 2) + (∫ w, |φ w|) * Z ω ^ 2) := by
          rw [integral_const_mul, integral_add h1 h2, integral_mul_const]
  have hG : Integrable (fun ω => (1 / 2) * ((∫ w, |φ w| * g ω w ^ 2) + (∫ w, |φ w|) * Z ω ^ 2)) P :=
    (hQ.add (hZ2.const_mul (∫ w, |φ w|))).const_mul (1 / 2)
  have hfm : Measurable fun p : Ω × ℂ => g p.1 p.2 * φ p.2 * Z p.1 :=
    (hgm.mul ((hφc.measurable).comp measurable_snd)).mul (hZm.comp measurable_fst)
  have hint : Integrable (fun p : Ω × ℂ => g p.1 p.2 * φ p.2 * Z p.1) (P.prod volume) :=
    integrable_prod_of_bound hfm hG hfb hbd
  have hswap : ∫ ω, ∫ w, g ω w * φ w * Z ω ∂volume ∂P = ∫ w, ∫ ω, g ω w * φ w * Z ω ∂P ∂volume :=
    integral_integral_swap hint
  have hint1 : Integrable (fun ω => (∫ w, g ω w * φ w) * Z ω) P := by
    refine (hint.integral_prod_left).congr (ae_of_all _ fun ω => ?_)
    simp only [integral_mul_const]
  refine ⟨hint1, ?_⟩
  have hLHS : ∫ ω, (∫ w, g ω w * φ w) * Z ω ∂P = ∫ ω, ∫ w, g ω w * φ w * Z ω ∂volume ∂P := by
    congr 1
    funext ω
    rw [integral_mul_const]
  have hRHS : ∀ w, ∫ ω, g ω w * φ w * Z ω ∂P = φ w * ∫ ω, g ω w * Z ω ∂P := fun w => by
    rw [← integral_const_mul]
    congr 1
    funext ω
    ring
  rw [hLHS, hswap]
  congr 1
  funext w
  exact hRHS w

/-- The square of the pairing: `E[(∫ g(·,w) φ(w) dw)²] = ∫∫ φ(w) φ(w') E[g(·,w) g(·,w')] dw dw'`, with the
integrability of the square justified by the weighted `L²` bound `hQ`. -/
lemma integrable_and_integral_sq_pairing {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {g : Ω → ℂ → ℝ} (hgm : Measurable fun p : Ω × ℂ => g p.1 p.2) (hgc : ∀ ω, Continuous (g ω))
    {φ : ℂ → ℝ} (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (hQ : Integrable (fun ω => ∫ w, |φ w| * g ω w ^ 2) P) :
    Integrable (fun ω => (∫ w, g ω w * φ w) ^ 2) P ∧
      ∫ ω, (∫ w, g ω w * φ w) ^ 2 ∂P =
        ∫ p : ℂ × ℂ, φ p.1 * φ p.2 * ∫ ω, g ω p.1 * g ω p.2 ∂P := by
  have hcpt_abs : HasCompactSupport fun w : ℂ => |φ w| :=
    HasCompactSupport.intro hφs.isCompact fun w hw => by simp [image_eq_zero_of_notMem_tsupport hw]
  have hφabs : Integrable (fun w : ℂ => |φ w|) volume :=
    hφc.abs.integrable_of_hasCompactSupport hcpt_abs
  have hfacts : ∀ ω, Integrable (fun w => g ω w * φ w) volume := fun ω => by
    refine Continuous.integrable_of_hasCompactSupport ((hgc ω).mul hφc) ?_
    exact HasCompactSupport.intro hφs.isCompact fun w hw => by simp [image_eq_zero_of_notMem_tsupport hw]
  have hu : ∀ ω, Integrable (fun w => |φ w| * g ω w ^ 2) volume := fun ω => by
    refine (hφc.abs.mul ((hgc ω).pow 2)).integrable_of_hasCompactSupport ?_
    exact HasCompactSupport.intro hφs.isCompact fun w hw => by simp [image_eq_zero_of_notMem_tsupport hw]
  have hG : Integrable (fun ω => (∫ w, |φ w|) * ∫ w, |φ w| * g ω w ^ 2) P := hQ.const_mul _
  have hfb : ∀ ω, Integrable (fun p : ℂ × ℂ => (g ω p.1 * φ p.1) * (g ω p.2 * φ p.2))
      (volume.prod volume) := fun ω => (hfacts ω).mul_prod (hfacts ω)
  have hFm : Measurable fun q : Ω × (ℂ × ℂ) => (g q.1 q.2.1 * φ q.2.1) * (g q.1 q.2.2 * φ q.2.2) := by
    have hm1 : Measurable fun q : Ω × (ℂ × ℂ) => g q.1 q.2.1 :=
      Measurable.comp (g := fun p : Ω × ℂ => g p.1 p.2)
        (f := fun q : Ω × (ℂ × ℂ) => (q.1, q.2.1)) hgm (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    have hm2 : Measurable fun q : Ω × (ℂ × ℂ) => g q.1 q.2.2 :=
      Measurable.comp (g := fun p : Ω × ℂ => g p.1 p.2)
        (f := fun q : Ω × (ℂ × ℂ) => (q.1, q.2.2)) hgm (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
    have hp1 : Measurable fun q : Ω × (ℂ × ℂ) => φ q.2.1 :=
      Measurable.comp (g := φ) (f := fun q : Ω × (ℂ × ℂ) => q.2.1) hφc.measurable
        (measurable_fst.comp measurable_snd)
    have hp2 : Measurable fun q : Ω × (ℂ × ℂ) => φ q.2.2 :=
      Measurable.comp (g := φ) (f := fun q : Ω × (ℂ × ℂ) => q.2.2) hφc.measurable
        (measurable_snd.comp measurable_snd)
    exact (hm1.mul hp1).mul (hm2.mul hp2)
  -- pointwise domination: `|g_1 φ_1 g_2 φ_2| ≤ (1/2)(u_1 v_2 + v_1 u_2)`, with `u = |φ| g²`, `v = |φ|`
  have hbd : ∀ ω, ∫ p : ℂ × ℂ, ‖(g ω p.1 * φ p.1) * (g ω p.2 * φ p.2)‖ ∂(volume.prod volume) ≤
      (∫ w, |φ w|) * ∫ w, |φ w| * g ω w ^ 2 := by
    intro ω
    have hI1 : Integrable (fun p : ℂ × ℂ => (|φ p.1| * g ω p.1 ^ 2) * |φ p.2|) (volume.prod volume) :=
      (hu ω).mul_prod hφabs
    have hI2 : Integrable (fun p : ℂ × ℂ => |φ p.1| * (|φ p.2| * g ω p.2 ^ 2)) (volume.prod volume) :=
      hφabs.mul_prod (hu ω)
    have e1 : ∫ p : ℂ × ℂ, (|φ p.1| * g ω p.1 ^ 2) * |φ p.2| ∂(volume.prod volume) =
        (∫ w, |φ w| * g ω w ^ 2) * ∫ w, |φ w| :=
      integral_prod_mul (fun w => |φ w| * g ω w ^ 2) (fun w => |φ w|)
    have e2 : ∫ p : ℂ × ℂ, |φ p.1| * (|φ p.2| * g ω p.2 ^ 2) ∂(volume.prod volume) =
        (∫ w, |φ w|) * ∫ w, |φ w| * g ω w ^ 2 :=
      integral_prod_mul (fun w => |φ w|) (fun w => |φ w| * g ω w ^ 2)
    have hbound : ∀ p : ℂ × ℂ, ‖(g ω p.1 * φ p.1) * (g ω p.2 * φ p.2)‖ ≤
        (1 / 2) * ((|φ p.1| * g ω p.1 ^ 2) * |φ p.2| + |φ p.1| * (|φ p.2| * g ω p.2 ^ 2)) := by
      intro p
      have hgg : |g ω p.1| * |g ω p.2| ≤ (g ω p.1 ^ 2 + g ω p.2 ^ 2) / 2 := by
        nlinarith [sq_nonneg (|g ω p.1| - |g ω p.2|), sq_abs (g ω p.1), sq_abs (g ω p.2)]
      rw [Real.norm_eq_abs]
      calc |(g ω p.1 * φ p.1) * (g ω p.2 * φ p.2)|
          = (|φ p.1| * |φ p.2|) * (|g ω p.1| * |g ω p.2|) := by
            rw [abs_mul, abs_mul, abs_mul]
            ring
        _ ≤ (|φ p.1| * |φ p.2|) * ((g ω p.1 ^ 2 + g ω p.2 ^ 2) / 2) :=
            mul_le_mul_of_nonneg_left hgg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        _ = (1 / 2) * ((|φ p.1| * g ω p.1 ^ 2) * |φ p.2| + |φ p.1| * (|φ p.2| * g ω p.2 ^ 2)) := by
            ring
    calc ∫ p : ℂ × ℂ, ‖(g ω p.1 * φ p.1) * (g ω p.2 * φ p.2)‖ ∂(volume.prod volume)
        ≤ ∫ p : ℂ × ℂ, (1 / 2) * ((|φ p.1| * g ω p.1 ^ 2) * |φ p.2| + |φ p.1| * (|φ p.2| * g ω p.2 ^ 2))
            ∂(volume.prod volume) :=
          integral_mono (hfb ω).norm ((hI1.add hI2).const_mul _) hbound
      _ = (∫ w, |φ w| * g ω w ^ 2) * ∫ w, |φ w| := by
          rw [integral_const_mul, integral_add hI1 hI2, e1, e2]
          ring
      _ = (∫ w, |φ w|) * ∫ w, |φ w| * g ω w ^ 2 := by ring
  have hint : Integrable (fun q : Ω × (ℂ × ℂ) => (g q.1 q.2.1 * φ q.2.1) * (g q.1 q.2.2 * φ q.2.2))
      (P.prod (volume.prod volume)) :=
    integrable_prod_of_bound hFm hG hfb hbd
  have hsq : ∀ ω, (∫ w, g ω w * φ w) ^ 2 =
      ∫ p : ℂ × ℂ, (g ω p.1 * φ p.1) * (g ω p.2 * φ p.2) ∂(volume.prod volume) := fun ω => by
    rw [sq]
    exact (integral_prod_mul (fun w => g ω w * φ w) (fun w => g ω w * φ w)).symm
  have hY2 : Integrable (fun ω => (∫ w, g ω w * φ w) ^ 2) P := by
    refine (hint.integral_prod_left).congr (ae_of_all _ fun ω => ?_)
    exact (hsq ω).symm
  refine ⟨hY2, ?_⟩
  have hswap : ∫ ω, ∫ p : ℂ × ℂ, (g ω p.1 * φ p.1) * (g ω p.2 * φ p.2) ∂(volume.prod volume) ∂P =
      ∫ p : ℂ × ℂ, ∫ ω, (g ω p.1 * φ p.1) * (g ω p.2 * φ p.2) ∂P ∂(volume.prod volume) :=
    integral_integral_swap hint
  calc ∫ ω, (∫ w, g ω w * φ w) ^ 2 ∂P
      = ∫ ω, ∫ p : ℂ × ℂ, (g ω p.1 * φ p.1) * (g ω p.2 * φ p.2) ∂(volume.prod volume) ∂P :=
        integral_congr_ae (ae_of_all _ hsq)
    _ = ∫ p : ℂ × ℂ, ∫ ω, (g ω p.1 * φ p.1) * (g ω p.2 * φ p.2) ∂P ∂(volume.prod volume) := hswap
    _ = ∫ p : ℂ × ℂ, φ p.1 * φ p.2 * ∫ ω, g ω p.1 * g ω p.2 ∂P := by
        congr 1
        funext p
        rw [← integral_const_mul]
        congr 1
        funext ω
        ring

/-! ## Gaussian covariance identities -/

/-- For centred observables, the covariance is the expectation of the product. -/
lemma covariance_eq_integral_mul {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X Y : Ω → ℝ}
    (hX0 : ∫ ω, X ω ∂P = 0) (hY0 : ∫ ω, Y ω ∂P = 0) :
    ProbabilityTheory.covariance X Y P = ∫ ω, X ω * Y ω ∂P := by
  unfold ProbabilityTheory.covariance
  rw [hX0, hY0]
  simp

/-- A circle average of positive radius is square integrable (Gaussian law). -/
lemma memLp_circle {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hgff : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r) (w : ℂ) :
    MemLp (fun ω => hcirc ω r w) 2 P :=
  (hgff.hasGaussianLaw_circle hr w).memLp_two

/-- A pairing with a test function is square integrable (Gaussian law). -/
lemma memLp_pairing {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hgff : IsWholePlaneGFF P hC hcirc) {ψ : ℂ → ℝ}
    (hψ : IsTestFunction Set.univ ψ) : MemLp (fun ω => hC ω ψ) 2 P :=
  (hgff.isGaussianProcess.hasGaussianLaw_eval (⟨.pairing ψ, hψ⟩ : GFFObservable.Admissible)).memLp_two

/-- The circle-average covariance kernel: `E[h_r(w) h_r(w')] = circleCovKernel r w w'`. -/
lemma integral_circle_mul_circle {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hgff : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r) (w w' : ℂ) :
    ∫ ω, hcirc ω r w * hcirc ω r w' ∂P = circleCovKernel r w w' := by
  have h0 : ∀ z, ∫ ω, hcirc ω r z ∂P = 0 := fun z => hgff.integral_eq_zero (GFFObservable.circle r z) hr
  have hcov : ProbabilityTheory.covariance (fun ω => hcirc ω r w) (fun ω => hcirc ω r w') P =
      wholePlaneGFFCov (GFFObservable.circle r w) (GFFObservable.circle r w') :=
    hgff.covariance_eq (GFFObservable.circle r w) (GFFObservable.circle r w') hr hr
  rw [← covariance_eq_integral_mul (h0 w) (h0 w'), hcov]
  unfold wholePlaneGFFCov circleCovKernel
  simp only [GFFObservable.smear]
  congr 1
  funext x
  exact circleAverage_wholePlaneCov_eq_circleKernelMean w' hr x

/-- The circle-average/pairing covariance: `E[h_r(w) h(ψ)] = ⨍_{∂B_r(w)} kernelPairing ψ`. -/
lemma integral_circle_mul_pairing {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hgff : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r) (w : ℂ)
    {ψ : ℂ → ℝ} (hψ : IsTestFunction Set.univ ψ) :
    ∫ ω, hcirc ω r w * hC ω ψ ∂P = Real.circleAverage (kernelPairing ψ) w r := by
  have h0c : ∫ ω, hcirc ω r w ∂P = 0 := hgff.integral_eq_zero (GFFObservable.circle r w) hr
  have h0p : ∫ ω, hC ω ψ ∂P = 0 := hgff.integral_eq_zero (GFFObservable.pairing ψ) hψ
  have hcov : ProbabilityTheory.covariance (fun ω => hcirc ω r w) (fun ω => hC ω ψ) P =
      wholePlaneGFFCov (GFFObservable.circle r w) (GFFObservable.pairing ψ) :=
    hgff.covariance_eq (GFFObservable.circle r w) (GFFObservable.pairing ψ) hr hψ
  rw [← covariance_eq_integral_mul h0c h0p, hcov]
  unfold wholePlaneGFFCov
  simp only [GFFObservable.smear]
  rfl

/-- The pairing covariance: `E[h(ψ)²] = ∫ ψ(x) kernelPairing ψ x dx`. -/
lemma integral_pairing_mul_pairing {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hgff : IsWholePlaneGFF P hC hcirc) {ψ : ℂ → ℝ}
    (hψ : IsTestFunction Set.univ ψ) :
    ∫ ω, hC ω ψ * hC ω ψ ∂P = ∫ x, ψ x * kernelPairing ψ x := by
  have h0 : ∫ ω, hC ω ψ ∂P = 0 := hgff.integral_eq_zero (GFFObservable.pairing ψ) hψ
  have hcov : ProbabilityTheory.covariance (fun ω => hC ω ψ) (fun ω => hC ω ψ) P =
      wholePlaneGFFCov (GFFObservable.pairing ψ) (GFFObservable.pairing ψ) :=
    hgff.covariance_eq (GFFObservable.pairing ψ) (GFFObservable.pairing ψ) hψ hψ
  rw [← covariance_eq_integral_mul h0 h0, hcov]
  rfl

end GaussianCircleTestIntegral

open GaussianCircleTestIntegral

/-- **Fixed-test Gaussian circle identity** (first `L²` / Fubini reconstruction ingredient).

For the whole-plane GFF `h^ℂ` of `IsWholePlaneGFF` with pairings `hC` and circle averages `hcirc`, a test function
`φ` (`IsTestFunction Set.univ φ`) and a radius `0 < r ≤ 1`: almost surely the circle-average integral
`w ↦ h^ℂ_r(w) φ(w)` is integrable and its integral equals the pairing of `h^ℂ` with the circle-averaged test
`φ_r(v) = ⨍_{∂B_r(v)} φ`. The probability space is arbitrary; no linearity of `hC` in the sample is assumed. The
identity holds for this single test and radius only almost surely (see the countable corollary below). -/
theorem IsWholePlaneGFF.ae_integral_circle_mul_eq_pairing_circleAverage
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc) {φ : ℂ → ℝ} (hphi : IsTestFunction Set.univ φ)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∀ᵐ ω ∂P, Integrable (fun w : ℂ => hcirc ω r w * φ w) ∧
      ∫ w, hcirc ω r w * φ w = hC ω (fun v : ℂ => Real.circleAverage φ v r) := by
  have : IsProbabilityMeasure P := hgff.isProbabilityMeasure
  obtain ⟨g, hgm, hgc, N, hNm, hN0, hgN⟩ := exists_measurable_circleAverage_version hgff hr
  have hr1' : |r| ≤ 1 := by rw [abs_of_pos hr]; exact hr1
  have hφr : IsTestFunction Set.univ (fun v : ℂ => Real.circleAverage φ v r) :=
    CircleTestFubini.isTestFunction_univ_circleAverage hphi hr1'
  have hae : ∀ᵐ ω ∂P, ω ∉ N := by
    rw [ae_iff]
    simpa using hN0
  -- `g` is a jointly measurable version of the circle averages, equal to `hcirc ω r ·` for every `ω ∉ N`
  have hL2c : ∀ w, Integrable (fun ω => g ω w ^ 2) P := by
    intro w
    refine (memLp_circle hgff hr w).integrable_sq.congr ?_
    filter_upwards [hae] with ω hω
    rw [hgN ω hω w]
  have hsq : ∀ w, ∫ ω, g ω w ^ 2 ∂P = circleCovKernel r w w := by
    intro w
    rw [← integral_circle_mul_circle hgff hr w w]
    refine integral_congr_ae ?_
    filter_upwards [hae] with ω hω
    rw [hgN ω hω w, sq]
  have hgg : ∀ p : ℂ × ℂ, ∫ ω, g ω p.1 * g ω p.2 ∂P = circleCovKernel r p.1 p.2 := by
    intro p
    rw [← integral_circle_mul_circle hgff hr p.1 p.2]
    refine integral_congr_ae ?_
    filter_upwards [hae] with ω hω
    rw [hgN ω hω p.1, hgN ω hω p.2]
  have hQ := integrable_weighted_sq hgm hgc hL2c hr hsq hphi.1.continuous hphi.2.1
  obtain ⟨hY2, hY2eq⟩ := integrable_and_integral_sq_pairing hgm hgc hphi.1.continuous hphi.2.1 hQ
  have hHL2 : MemLp (fun ω => hC ω (fun v : ℂ => Real.circleAverage φ v r)) 2 P :=
    memLp_pairing hgff hφr
  have hHm : Measurable fun ω => hC ω (fun v : ℂ => Real.circleAverage φ v r) :=
    hgff.measurable_pairing _ hφr
  obtain ⟨hYH, hYHeq⟩ :=
    integral_pairing_mul_eq hgm hgc hphi.1.continuous hphi.2.1 hQ hHm hHL2.integrable_sq
  have hHint : Integrable (fun ω => hC ω (fun v : ℂ => Real.circleAverage φ v r) *
      hC ω (fun v : ℂ => Real.circleAverage φ v r)) P :=
    hHL2.integrable_sq.congr (ae_of_all _ fun ω => (sq _))
  -- cross term: `∫ g(·,w) h(φ_r) = ⨍_{∂B_r(w)} kernelPairing φ_r` and the averaging adjointness
  have hcross : ∀ w, ∫ ω, g ω w * hC ω (fun v : ℂ => Real.circleAverage φ v r) ∂P =
      Real.circleAverage (kernelPairing fun v => Real.circleAverage φ v r) w r := by
    intro w
    rw [← integral_circle_mul_pairing hgff hr w hφr]
    refine integral_congr_ae ?_
    filter_upwards [hae] with ω hω
    rw [hgN ω hω w]
  have hKc : Continuous (kernelPairing fun v => Real.circleAverage φ v r) :=
    continuous_kernelPairing hphi hr hr1
  have hCTFL := (CircleTestFubini.integral_circleAverage_mul_eq hKc.locallyIntegrable hphi hr1').2.2
  have hYH_val : ∫ ω, (∫ w, g ω w * φ w) * hC ω (fun v : ℂ => Real.circleAverage φ v r) ∂P =
      ∫ x, Real.circleAverage φ x r * kernelPairing (fun v => Real.circleAverage φ v r) x := by
    rw [hYHeq]
    simp_rw [hcross]
    calc ∫ w, φ w * Real.circleAverage (kernelPairing fun v => Real.circleAverage φ v r) w r
        = ∫ w, Real.circleAverage (kernelPairing fun v => Real.circleAverage φ v r) w r * φ w := by
          congr 1
          funext w
          ring
      _ = ∫ v, kernelPairing (fun v => Real.circleAverage φ v r) v * Real.circleAverage φ v r := hCTFL
      _ = ∫ x, Real.circleAverage φ x r * kernelPairing (fun v => Real.circleAverage φ v r) x := by
          congr 1
          funext x
          ring
  have hY2_val : ∫ ω, (∫ w, g ω w * φ w) ^ 2 ∂P =
      ∫ x, Real.circleAverage φ x r * kernelPairing (fun v => Real.circleAverage φ v r) x := by
    rw [hY2eq]
    simp_rw [hgg]
    exact integral_prod_circleCovKernel hphi hr hr1
  have hHH : ∫ ω, hC ω (fun v : ℂ => Real.circleAverage φ v r) *
      hC ω (fun v : ℂ => Real.circleAverage φ v r) ∂P =
      ∫ x, Real.circleAverage φ x r * kernelPairing (fun v => Real.circleAverage φ v r) x :=
    integral_pairing_mul_pairing hgff hφr
  -- second moment of the difference `Y - H`
  have e : ∀ ω, ((∫ w, g ω w * φ w) - hC ω (fun v : ℂ => Real.circleAverage φ v r)) ^ 2 =
      (∫ w, g ω w * φ w) ^ 2 - 2 * ((∫ w, g ω w * φ w) *
        hC ω (fun v : ℂ => Real.circleAverage φ v r)) +
        hC ω (fun v : ℂ => Real.circleAverage φ v r) * hC ω (fun v : ℂ => Real.circleAverage φ v r) := by
    intro ω
    ring
  have hI1 : Integrable (fun ω => (∫ w, g ω w * φ w) ^ 2 -
      2 * ((∫ w, g ω w * φ w) * hC ω (fun v : ℂ => Real.circleAverage φ v r))) P :=
    hY2.sub (hYH.const_mul 2)
  have hdiff_int : Integrable (fun ω => ((∫ w, g ω w * φ w) -
      hC ω (fun v : ℂ => Real.circleAverage φ v r)) ^ 2) P :=
    (hI1.add hHint).congr (ae_of_all _ fun ω => (e ω).symm)
  have hsum : ∫ ω, ((∫ w, g ω w * φ w) - hC ω (fun v : ℂ => Real.circleAverage φ v r)) ^ 2 ∂P = 0 := by
    rw [integral_congr_ae (ae_of_all _ e), integral_add hI1 hHint,
      integral_sub hY2 (hYH.const_mul 2), integral_const_mul, hY2_val, hYH_val, hHH]
    ring
  have hzero := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg _) hdiff_int).1 hsum
  have hYH_ae : ∀ᵐ ω ∂P, (∫ w, g ω w * φ w) = hC ω (fun v : ℂ => Real.circleAverage φ v r) := by
    filter_upwards [hzero] with ω hω
    have h1 : (∫ w, g ω w * φ w) - hC ω (fun v : ℂ => Real.circleAverage φ v r) = 0 :=
      (pow_eq_zero_iff two_ne_zero).1 hω
    exact sub_eq_zero.1 h1
  filter_upwards [hYH_ae, hae] with ω hω hωN
  have hfun : (fun w : ℂ => hcirc ω r w * φ w) = fun w => g ω w * φ w := by
    funext w
    rw [hgN ω hωN w]
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact ((hgc ω).mul hphi.1.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.intro hphi.2.1.isCompact fun w hw => by simp [image_eq_zero_of_notMem_tsupport hw])
  · rw [hfun, hω]

/-- **Countable corollary.** For arbitrary countable families of tests and of radii in `(0, 1]`, fixed before the
sample, the fixed-test identities hold simultaneously on one measurable event of full measure. -/
theorem IsWholePlaneGFF.exists_measurable_conull_ae_integral_circle_mul_eq_pairing_circleAverage
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc) {ι κ : Type*} [Countable ι] [Countable κ]
    (φ : ι → ℂ → ℝ) (hφ : ∀ i, IsTestFunction Set.univ (φ i))
    (r : κ → ℝ) (hr : ∀ k, 0 < r k) (hr1 : ∀ k, r k ≤ 1) :
    ∃ S : Set Ω, MeasurableSet S ∧ P Sᶜ = 0 ∧ ∀ ω ∈ S, ∀ i k,
      Integrable (fun w : ℂ => hcirc ω (r k) w * φ i w) ∧
        ∫ w, hcirc ω (r k) w * φ i w = hC ω (fun v : ℂ => Real.circleAverage (φ i) v (r k)) := by
  have h : ∀ᵐ ω ∂P, ∀ i k,
      Integrable (fun w : ℂ => hcirc ω (r k) w * φ i w) ∧
        ∫ w, hcirc ω (r k) w * φ i w = hC ω (fun v : ℂ => Real.circleAverage (φ i) v (r k)) := by
    refine ae_all_iff.2 fun i => ae_all_iff.2 fun k => ?_
    exact IsWholePlaneGFF.ae_integral_circle_mul_eq_pairing_circleAverage hgff (hφ i) (hr k) (hr1 k)
  obtain ⟨t, hsub, htm, ht0⟩ := exists_measurable_superset_of_null (ae_iff.1 h)
  refine ⟨tᶜ, htm.compl, by rw [compl_compl]; exact ht0, fun ω hω i k => ?_⟩
  by_contra hn
  exact hω (hsub fun hall => hn (hall i k))

end HarmonicBalls

