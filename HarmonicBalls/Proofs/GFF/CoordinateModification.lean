import HarmonicBalls.Defs.GFF
import LatticeProb.Bonanno.LQGMetric.Field.MarkovNorm
import LatticeProb.Bonanno.LQGMetric.Field.MarkovGermVerPot
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgGP
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgKolm
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgBridge

/-! # Coordinatewise modifications of the whole-plane GFF

The related distribution-valued construction is due to Leonardo Bonanno.
Coordinatewise agreement alone does not assert a common samplewise representation. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace
namespace HarmonicBalls

/-- Away from the diagonal, the normalized whole-plane covariance kernel has
the additive logarithmic form used for GFF circle averages. -/
theorem wholePlaneCov_eq_additive_of_ne {z w : ℂ} (hzw : z ≠ w) :
    wholePlaneCov z w = -Real.log ‖z - w‖ + Real.log (max ‖z‖ 1) +
      Real.log (max ‖w‖ 1) := by
  rw [wholePlaneCov, Real.log_div (by positivity) (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hzw)),
    Real.log_mul (by positivity) (by positivity)]
  ring

#print axioms wholePlaneCov_eq_additive_of_ne

/-- Circle smearing removes the diagonal discrepancy between the project
kernel and Leonardo Bonanno's additive logarithmic covariance kernel. -/
theorem wholePlaneGFFCov_circle_eq_gffCircleCov {r s : ℝ} (hs : 0 < s) (z w : ℂ) :
    wholePlaneGFFCov (.circle r z) (.circle s w) =
      LQGDimension.gffCircleCov r z s w := by
  rw [LQGDimension.Osc37.gffCircleCov_eq_circleAverage]
  change Real.circleAverage (fun x => Real.circleAverage (wholePlaneCov x) w s) z r = _
  apply Real.circleAverage_congr_sphere
  intro x hx
  apply Real.circleAverage_congr_codiscreteWithin ?_ (ne_of_gt hs)
  filter_upwards [compl_singleton_mem_codiscreteWithin x] with y hy
  exact (wholePlaneCov_eq_additive_of_ne (by simpa [eq_comm] using hy) :
    wholePlaneCov x y = LQGDimension.gffGreen x y)

#print axioms wholePlaneGFFCov_circle_eq_gffCircleCov

/-- All pairings of Leonardo Bonanno's normalized distribution-valued GFF
are jointly Gaussian and centered, including tests with nonzero integral. -/
theorem normalizedGFF_allPairings_gaussian
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistC} (hh : LQGMetric.IsNormalizedWPGFF h P) :
    IsGaussianProcess (fun (φ : LQGMetric.TestC) ω => h ω φ) P ∧
      ∀ φ : LQGMetric.TestC, ∫ ω, h ω φ ∂P = 0 := by
  have hgauss := LQGMetric.MarkovGauss.isGaussianProcess_of_mem_gaussSpace
    (LQGMetric.gaussian_pairProc hh.1) (LQGMetric.centered_pairProc hh.1)
    (LQGMetric.MarkovZB.memLp_pair hh.1) (LQGMetric.MarkovNorm.pairVec hh)
    (LQGMetric.MarkovNorm.pairVec_mem_gaussSpace hh)
  refine ⟨hgauss.congr (LQGMetric.MarkovNorm.pairVec_ae hh), ?_⟩
  intro φ
  have hc := LQGMetric.MarkovGauss.isCGauss_of_mem_gaussSpace
    (LQGMetric.gaussian_pairProc hh.1) (LQGMetric.centered_pairProc hh.1)
    (LQGMetric.MarkovZB.memLp_pair hh.1) (LQGMetric.MarkovNorm.pairVec_mem_gaussSpace hh φ)
  rw [← integral_congr_ae (LQGMetric.MarkovNorm.pairVec_ae hh φ)]
  exact hc.2

#print axioms normalizedGFF_allPairings_gaussian

/-- The covariance of two test pairings of Leonardo Bonanno's normalized GFF
is the limit of their mean-zero approximations' logarithmic covariances. -/
theorem normalizedGFF_pairing_covariance_tendsto
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistC} (hh : LQGMetric.IsNormalizedWPGFF h P)
    (φ ψ : LQGMetric.TestC) :
    Tendsto (fun n => LQGMetric.logCov
      (LQGMetric.MarkovGerm.meanZeroApprox φ n).1
      (LQGMetric.MarkovGerm.meanZeroApprox ψ n).1) atTop
      (𝓝 (cov[fun ω => h ω φ, fun ω => h ω ψ; P])) := by
  let U := LQGMetric.MarkovNorm.pairVec hh φ
  let V := LQGMetric.MarkovNorm.pairVec hh ψ
  have hcenter : ∫ ω, (U : Ω → ℝ) ω ∂P = 0 := by
    rw [integral_congr_ae (LQGMetric.MarkovNorm.pairVec_ae hh φ)]
    exact (normalizedGFF_allPairings_gaussian hh).2 φ
  have hc : ⟪U, V⟫ = cov[fun ω => h ω φ, fun ω => h ω ψ; P] := by
    calc
      ⟪U, V⟫ = cov[(U : Ω → ℝ), (V : Ω → ℝ); P] := by
        have hu := Lp.memLp U
        have hv := Lp.memLp V
        simpa only [Lp.toLp_coeFn] using LQGMetric.MarkovZB.inner_toLp_eq_cov hu hv hcenter
      _ = _ := LQGMetric.MarkovNorm.cov_congr_ae
        (LQGMetric.MarkovNorm.pairVec_ae hh φ) (LQGMetric.MarkovNorm.pairVec_ae hh ψ)
  have ht := (LQGMetric.MarkovNorm.tendsto_pairVec hh φ).inner (𝕜 := ℝ)
    (LQGMetric.MarkovNorm.tendsto_pairVec hh ψ)
  rw [hc] at ht
  refine ht.congr fun n => ?_
  dsimp only [LQGMetric.MarkovNorm.apxVec]
  rw [LQGMetric.MarkovZB.inner_toLp_eq_cov _ _
    (LQGMetric.centered_pairProc hh.1 _)]
  exact hh.1.covariance_eq _ _

#print axioms normalizedGFF_pairing_covariance_tendsto

/-- The unit-circle mollifier's logarithmic potential converges uniformly,
with the geometric rate in Leonardo Bonanno's circle-average construction. -/
theorem abs_logPot_unitCircleBump_add_le (n : ℕ) (x : ℂ) :
    |LQGMetric.CircleAvg.logPot (LQGMetric.CircleAvg.circBump n 0 1) x +
      LQGMetric.CircleAvg.circLog 0 1 x| ≤ (2 : ℝ)⁻¹ ^ n := by
  rw [LQGMetric.CircleAvg.logPot_circBump]
  have h := LQGMetric.CircleAvg.abs_integral_bump_circLog_sub_le one_pos n 0 x
  rw [div_one] at h
  rw [show -(∫ t, LQGMetric.bumpTest n 0 t *
      LQGMetric.CircleAvg.circLog 0 1 (x - t)) + LQGMetric.CircleAvg.circLog 0 1 x =
      -((∫ t, LQGMetric.bumpTest n 0 t * LQGMetric.CircleAvg.circLog 0 1 (x - t)) -
        LQGMetric.CircleAvg.circLog 0 1 x) by ring, abs_neg]
  exact h

#print axioms abs_logPot_unitCircleBump_add_le

/-- The mean-zero approximation has the normalized logarithmic potential,
up to a uniform geometric error. -/
theorem abs_logPot_meanZeroApprox_sub_le (φ : LQGMetric.TestC) (n : ℕ) (x : ℂ) :
    |LQGMetric.CircleAvg.logPot (LQGMetric.MarkovGerm.meanZeroApprox φ n).1 x -
      (LQGMetric.CircleAvg.logPot φ x + (∫ y, φ y) *
        LQGMetric.CircleAvg.circLog 0 1 x)| ≤ |∫ y, φ y| * (2 : ℝ)⁻¹ ^ n := by
  have hsmul : LQGMetric.CircleAvg.logPot
      ((∫ y, φ y) • LQGMetric.CircleAvg.circBump n 0 1 : LQGMetric.TestC) x =
      (∫ y, φ y) * LQGMetric.CircleAvg.logPot
        (LQGMetric.CircleAvg.circBump n 0 1) x := by
    unfold LQGMetric.CircleAvg.logPot
    rw [← integral_const_mul]
    congr 1
    funext y
    change (-Real.log ‖x - y‖) * ((∫ y, φ y) *
      LQGMetric.CircleAvg.circBump n 0 1 y) = _
    ring
  change |LQGMetric.CircleAvg.logPot
      (⇑(φ - (∫ y, φ y) • LQGMetric.CircleAvg.circBump n 0 1)) x - _| ≤ _
  rw [LQGMetric.CircleAvg.logPot_sub, hsmul]
  have heq : LQGMetric.CircleAvg.logPot φ x -
      (∫ y, φ y) * LQGMetric.CircleAvg.logPot (LQGMetric.CircleAvg.circBump n 0 1) x -
      (LQGMetric.CircleAvg.logPot φ x + (∫ y, φ y) * LQGMetric.CircleAvg.circLog 0 1 x) =
      -(∫ y, φ y) * (LQGMetric.CircleAvg.logPot (LQGMetric.CircleAvg.circBump n 0 1) x +
        LQGMetric.CircleAvg.circLog 0 1 x) := by ring
  rw [heq, abs_mul, abs_neg]
  exact mul_le_mul_of_nonneg_left (abs_logPot_unitCircleBump_add_le n x) (abs_nonneg _)

#print axioms abs_logPot_meanZeroApprox_sub_le

/-- Integrating the normalized potential approximation against a fixed test
function preserves its geometric convergence, in Leonardo Bonanno's construction. -/
theorem tendsto_integral_test_mul_meanZeroApprox_error (ρ φ : LQGMetric.TestC) :
    Tendsto (fun n => ∫ x, ρ x *
      (LQGMetric.CircleAvg.logPot (LQGMetric.MarkovGerm.meanZeroApprox φ n).1 x -
        (LQGMetric.CircleAvg.logPot φ x + (∫ y, φ y) *
          LQGMetric.CircleAvg.circLog 0 1 x))) atTop (𝓝 0) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
    (by norm_num : (2 : ℝ)⁻¹ < 1)
  have he : Tendsto (fun n : ℕ => (∫ x, ‖ρ x‖) * |∫ y, φ y| * (2 : ℝ)⁻¹ ^ n)
      atTop (𝓝 0) := by
    simpa using hp.const_mul ((∫ x, ‖ρ x‖) * |∫ y, φ y|)
  refine squeeze_zero_norm (fun n => ?_) he
  have hb : ∀ x : ℂ, ‖ρ x *
      (LQGMetric.CircleAvg.logPot (LQGMetric.MarkovGerm.meanZeroApprox φ n).1 x -
        (LQGMetric.CircleAvg.logPot φ x + (∫ y, φ y) *
          LQGMetric.CircleAvg.circLog 0 1 x))‖ ≤
      ‖ρ x‖ * (|∫ y, φ y| * (2 : ℝ)⁻¹ ^ n) := by
    intro x
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (abs_logPot_meanZeroApprox_sub_le φ n x) (abs_nonneg _)
  have hi : Integrable (fun x : ℂ => ‖ρ x‖ * (|∫ y, φ y| * (2 : ℝ)⁻¹ ^ n)) :=
    (LQGMetric.CircleAvg.integrable_testC ρ).norm.mul_const _
  refine (norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall hb)).trans (le_of_eq ?_)
  rw [integral_mul_const]
  ring

#print axioms tendsto_integral_test_mul_meanZeroApprox_error

/-- The potential error also vanishes against the changing mean-zero test
approximations, whose absolute masses are uniformly bounded. -/
theorem tendsto_integral_meanZeroApprox_mul_error (ρ φ : LQGMetric.TestC) :
    Tendsto (fun n => ∫ x, (LQGMetric.MarkovGerm.meanZeroApprox ρ n).1 x *
      (LQGMetric.CircleAvg.logPot (LQGMetric.MarkovGerm.meanZeroApprox φ n).1 x -
        (LQGMetric.CircleAvg.logPot φ x + (∫ y, φ y) *
          LQGMetric.CircleAvg.circLog 0 1 x))) atTop (𝓝 0) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
    (by norm_num : (2 : ℝ)⁻¹ < 1)
  have he : Tendsto (fun n : ℕ => ((∫ x, ‖ρ x‖) + |∫ y, ρ y|) *
      |∫ y, φ y| * (2 : ℝ)⁻¹ ^ n) atTop (𝓝 0) := by
    simpa using hp.const_mul (((∫ x, ‖ρ x‖) + |∫ y, ρ y|) * |∫ y, φ y|)
  refine squeeze_zero_norm (fun n => ?_) he
  let g : ℂ → ℝ := fun x => ‖ρ x‖ + |∫ y, ρ y| * LQGMetric.CircleAvg.circBump n 0 1 x
  have hg : Integrable g := (LQGMetric.CircleAvg.integrable_testC ρ).norm.add
    ((LQGMetric.CircleAvg.integrable_testC _).const_mul _)
  have hgn : ∀ x, 0 ≤ g x := fun x => add_nonneg (norm_nonneg _)
    (mul_nonneg (abs_nonneg _) (LQGMetric.CircleAvg.circBump_nonneg _ _ _ _))
  have hbound : ∀ x, ‖(LQGMetric.MarkovGerm.meanZeroApprox ρ n).1 x‖ ≤ g x := by
    intro x
    change ‖ρ x - (∫ y, ρ y) * LQGMetric.CircleAvg.circBump n 0 1 x‖ ≤ _
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (LQGMetric.CircleAvg.circBump_nonneg _ _ _ _)]
    exact le_rfl
  have hb : ∀ x : ℂ, ‖(LQGMetric.MarkovGerm.meanZeroApprox ρ n).1 x *
      (LQGMetric.CircleAvg.logPot (LQGMetric.MarkovGerm.meanZeroApprox φ n).1 x -
        (LQGMetric.CircleAvg.logPot φ x + (∫ y, φ y) *
          LQGMetric.CircleAvg.circLog 0 1 x))‖ ≤
      g x * (|∫ y, φ y| * (2 : ℝ)⁻¹ ^ n) := by
    intro x
    rw [norm_mul]
    exact mul_le_mul (hbound x) (by simpa only [Real.norm_eq_abs] using
      abs_logPot_meanZeroApprox_sub_le φ n x) (norm_nonneg _) (hgn x)
  refine (norm_integral_le_of_norm_le (hg.mul_const _) (Filter.Eventually.of_forall hb)).trans
    (le_of_eq ?_)
  rw [integral_mul_const, show ∫ x, g x = (∫ x, ‖ρ x‖) + |∫ y, ρ y| by
    dsimp [g]
    have hρ : Integrable (fun x => |ρ x|) := by
      simpa only [Real.norm_eq_abs] using (LQGMetric.CircleAvg.integrable_testC ρ).norm
    rw [integral_add hρ
      ((LQGMetric.CircleAvg.integrable_testC _).const_mul _), integral_const_mul,
      LQGMetric.CircleAvg.integral_circBump, mul_one]]
  ring

#print axioms tendsto_integral_meanZeroApprox_mul_error

/-- A mean-zero approximation integrates a continuous function against the
original test and subtracts its unit-circle average, as in Leonardo Bonanno's
normalized GFF construction. -/
theorem tendsto_integral_meanZeroApprox_mul_continuous
    (ρ : LQGMetric.TestC) (f : C(ℂ, ℝ)) :
    Tendsto (fun n => ∫ x, (LQGMetric.MarkovGerm.meanZeroApprox ρ n).1 x * f x)
      atTop (𝓝 ((∫ x, ρ x * f x) -
        (∫ x, ρ x) * Real.circleAverage f 0 1)) := by
  have heq : ∀ n, (∫ x, (LQGMetric.MarkovGerm.meanZeroApprox ρ n).1 x * f x) =
      (∫ x, ρ x * f x) - (∫ x, ρ x) *
        LQGMetric.CircleAvg.mollAvg (LQGMetric.ofCont f) n 0 1 := by
    intro n
    change (∫ x, (ρ x - (∫ y, ρ y) * LQGMetric.CircleAvg.circBump n 0 1 x) * f x) = _
    simp_rw [sub_mul, mul_assoc]
    rw [integral_sub (LQGMetric.CircleAvg.integrable_test_mul ρ f)
      ((LQGMetric.CircleAvg.integrable_test_mul _ f).const_mul _), integral_const_mul,
      LQGMetric.CircleAvg.integral_circBump_mul]
  simp_rw [heq]
  exact tendsto_const_nhds.sub ((LQGMetric.CircleAvg.tendsto_mollAvg_ofCont f 1 0).const_mul _)

#print axioms tendsto_integral_meanZeroApprox_mul_continuous

/-- The logarithmic covariances of Leonardo Bonanno's mean-zero approximations
converge to the normalized potential expression. -/
theorem tendsto_logCov_meanZeroApprox (ρ φ : LQGMetric.TestC) :
    Tendsto (fun n => LQGMetric.logCov (LQGMetric.MarkovGerm.meanZeroApprox ρ n).1
      (LQGMetric.MarkovGerm.meanZeroApprox φ n).1) atTop
      (𝓝 ((∫ x, ρ x * (LQGMetric.CircleAvg.logPot φ x + (∫ y, φ y) *
          LQGMetric.CircleAvg.circLog 0 1 x)) - (∫ x, ρ x) *
        Real.circleAverage (fun x => LQGMetric.CircleAvg.logPot φ x +
          (∫ y, φ y) * LQGMetric.CircleAvg.circLog 0 1 x) 0 1)) := by
  let f : C(ℂ, ℝ) := ⟨fun x => LQGMetric.CircleAvg.logPot φ x +
      (∫ y, φ y) * LQGMetric.CircleAvg.circLog 0 1 x,
    (LQGMetric.MarkovGermVer.contDiff_logPot φ).continuous.add
      (continuous_const.mul (LQGMetric.CircleAvg.continuous_circLog one_ne_zero 0))⟩
  have hlim := (tendsto_integral_meanZeroApprox_mul_continuous ρ f).add
    (tendsto_integral_meanZeroApprox_mul_error ρ φ)
  simp only [add_zero] at hlim
  refine hlim.congr fun n => ?_
  let D := (LQGMetric.MarkovGerm.meanZeroApprox ρ n).1
  let E := (LQGMetric.MarkovGerm.meanZeroApprox φ n).1
  let p : C(ℂ, ℝ) := ⟨LQGMetric.CircleAvg.logPot E,
    (LQGMetric.MarkovGermVer.contDiff_logPot E).continuous⟩
  have h1 := LQGMetric.CircleAvg.integrable_test_mul D f
  have h2 := LQGMetric.CircleAvg.integrable_test_mul D p
  have herror : Integrable (fun x => D x * (p x - f x)) := by
    have heq : (fun x => D x * (p x - f x)) =
        (fun x => D x * p x) - (fun x => D x * f x) := by
      funext x
      simp only [Pi.sub_apply]
      ring
    rw [heq]
    exact h2.sub h1
  rw [LQGMetric.CircleAvg.logCov_eq_integral_logPot]
  change (∫ x, D x * f x) + (∫ x, D x * (p x - f x)) = ∫ x, D x * p x
  rw [← integral_add h1 herror]
  congr 1
  funext x
  change D x * f x + D x * (p x - f x) = D x * p x
  ring

#print axioms tendsto_logCov_meanZeroApprox

/-- Test-pairing covariance in Leonardo Bonanno's normalized GFF, expressed
using a logarithmic potential and the normalizing unit-circle average. -/
theorem normalizedGFF_pairing_covariance_eq_potential
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistC} (hh : LQGMetric.IsNormalizedWPGFF h P)
    (ρ φ : LQGMetric.TestC) :
    cov[fun ω => h ω ρ, fun ω => h ω φ; P] =
      (∫ x, ρ x * (LQGMetric.CircleAvg.logPot φ x + (∫ y, φ y) *
          LQGMetric.CircleAvg.circLog 0 1 x)) - (∫ x, ρ x) *
        Real.circleAverage (fun x => LQGMetric.CircleAvg.logPot φ x +
          (∫ y, φ y) * LQGMetric.CircleAvg.circLog 0 1 x) 0 1 :=
  tendsto_nhds_unique (normalizedGFF_pairing_covariance_tendsto hh ρ φ)
    (tendsto_logCov_meanZeroApprox ρ φ)

#print axioms normalizedGFF_pairing_covariance_eq_potential

/-- Integrating the project kernel against a test removes its diagonal junk
value and yields Leonardo Bonanno's logarithmic potential plus both
normalization terms. -/
theorem integral_test_mul_wholePlaneCov (φ : LQGMetric.TestC) (x : ℂ) :
    (∫ y, φ y * wholePlaneCov x y) =
      LQGMetric.CircleAvg.logPot φ x + (∫ y, φ y) *
        LQGMetric.CircleAvg.circLog 0 1 x +
        ∫ y, φ y * LQGMetric.CircleAvg.circLog 0 1 y := by
  let f : C(ℂ, ℝ) := ⟨LQGMetric.CircleAvg.circLog 0 1,
    LQGMetric.CircleAvg.continuous_circLog one_ne_zero 0⟩
  have hlog := LQGMetric.CircleAvg.integrable_log_mul_test φ x
  have hconst : Integrable (fun y => LQGMetric.CircleAvg.circLog 0 1 x * φ y) :=
    (LQGMetric.CircleAvg.integrable_testC φ).const_mul _
  have hnorm : Integrable (fun y => φ y * f y) :=
    LQGMetric.CircleAvg.integrable_test_mul φ f
  have heq : (∫ y, φ y * wholePlaneCov x y) = ∫ y,
      ((-Real.log ‖x - y‖ * φ y + LQGMetric.CircleAvg.circLog 0 1 x * φ y) +
        φ y * LQGMetric.CircleAvg.circLog 0 1 y) := by
    apply integral_congr_ae
    filter_upwards [Measure.ae_ne volume x] with y hy
    rw [wholePlaneCov_eq_additive_of_ne (Ne.symm hy),
      ← LQGMetric.CircleAvg.circLog_zero_one x,
      ← LQGMetric.CircleAvg.circLog_zero_one y]
    ring
  rw [heq]
  change (∫ y, ((-Real.log ‖x - y‖ * φ y + LQGMetric.CircleAvg.circLog 0 1 x * φ y) +
    φ y * f y)) = _
  have hsum : Integrable (fun y => -Real.log ‖x - y‖ * φ y +
      LQGMetric.CircleAvg.circLog 0 1 x * φ y) := hlog.add hconst
  rw [integral_add hsum hnorm, integral_add hlog hconst, integral_const_mul]
  dsimp only [f, LQGMetric.CircleAvg.logPot, ContinuousMap.coe_mk]
  ring

#print axioms integral_test_mul_wholePlaneCov

/-- Test-test covariance of the project kernel in terms of Leonardo Bonanno's
logarithmic potential and the two unit-circle normalization terms. -/
theorem wholePlaneGFFCov_pairings_eq_potential (ρ φ : LQGMetric.TestC) :
    wholePlaneGFFCov (.pairing ρ) (.pairing φ) =
      (∫ x, ρ x * (LQGMetric.CircleAvg.logPot φ x + (∫ y, φ y) *
        LQGMetric.CircleAvg.circLog 0 1 x)) + (∫ x, ρ x) *
          (∫ y, φ y * LQGMetric.CircleAvg.circLog 0 1 y) := by
  let f : C(ℂ, ℝ) := ⟨fun x => LQGMetric.CircleAvg.logPot φ x +
      (∫ y, φ y) * LQGMetric.CircleAvg.circLog 0 1 x,
    (LQGMetric.MarkovGermVer.contDiff_logPot φ).continuous.add
      (continuous_const.mul (LQGMetric.CircleAvg.continuous_circLog one_ne_zero 0))⟩
  change (∫ x, ρ x * (∫ y, φ y * wholePlaneCov x y)) = _
  simp_rw [integral_test_mul_wholePlaneCov]
  change (∫ x, ρ x * (f x + (∫ y, φ y * LQGMetric.CircleAvg.circLog 0 1 y))) = _
  simp_rw [mul_add]
  rw [integral_add (LQGMetric.CircleAvg.integrable_test_mul ρ f)
    ((LQGMetric.CircleAvg.integrable_testC ρ).mul_const _), integral_mul_const]
  change (∫ x, ρ x * (LQGMetric.CircleAvg.logPot φ x + (∫ y, φ y) *
    LQGMetric.CircleAvg.circLog 0 1 x)) + _ = _
  simp_rw [mul_add]

#print axioms wholePlaneGFFCov_pairings_eq_potential

/-- The logarithmic kernel times a test is integrable against Lebesgue measure
and the unit-circle measure; this justifies exchanging these integrals. -/
theorem integrable_test_log_unitCircle_prod (φ : LQGMetric.TestC) :
    Integrable (fun p : ℂ × ℂ => φ p.1 * (-Real.log ‖p.2 - p.1‖))
      (volume.prod (LQGDimension.Coupling.circMeas 0 1)) := by
  let μ := LQGDimension.Coupling.circMeas 0 1
  let g : ℂ × ℂ → ℝ := fun p => φ p.1 * (-Real.log ‖p.2 - p.1‖)
  have hm : AEStronglyMeasurable g (volume.prod μ) := by
    apply Measurable.aestronglyMeasurable
    exact (φ.continuous.measurable.comp measurable_fst).mul
      (((Real.measurable_log.comp (measurable_snd.sub measurable_fst).norm)).neg)
  change Integrable g (volume.prod μ)
  rw [integrable_prod_iff hm]
  constructor
  · filter_upwards with y
    exact ((LQGDimension.Coupling.integrable_log_norm_sub_circ y 0 1).neg.const_mul
      (φ y)).congr (Filter.Eventually.of_forall fun x => by simp only [g, Pi.neg_apply, norm_sub_rev])
  · let b : ℂ → ℝ := fun y => ‖φ y‖ * (2 * (‖y‖ + 1))
    have hbi : Integrable b := by
      have hc : Continuous b := by
        dsimp [b]
        fun_prop
      exact hc.integrable_of_hasCompactSupport φ.hasCompactSupport.norm.mul_right
    refine hbi.mono' hm.norm.integral_prod_right' (Filter.Eventually.of_forall fun y => ?_)
    have hbound := LQGDimension.Coupling.integral_abs_log_le y 0 (r := 1) one_pos
    have hn : 0 ≤ 2 * (‖y‖ + 1) := by positivity
    have heq : (∫ x, ‖g (y, x)‖ ∂μ) = ‖φ y‖ *
        (∫ x, |Real.log ‖y - x‖| ∂μ) := by
      simp only [g, norm_mul, norm_neg, Real.norm_eq_abs, norm_sub_rev, integral_const_mul]
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _), heq]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    simpa only [norm_zero, add_zero, Real.log_one, sub_zero] using hbound

#print axioms integrable_test_log_unitCircle_prod

/-- The unit-circle average of Leonardo Bonanno's logarithmic potential is
the negative test integral of the circle logarithmic potential. -/
theorem circleAverage_logPot_unitCircle (φ : LQGMetric.TestC) :
    Real.circleAverage (LQGMetric.CircleAvg.logPot φ) 0 1 =
      -∫ y, φ y * LQGMetric.CircleAvg.circLog 0 1 y := by
  let μ := LQGDimension.Coupling.circMeas 0 1
  rw [← LQGDimension.Coupling.integral_circMeas_eq_circleAverage
    (LQGMetric.CircleAvg.measurable_logPot φ).aestronglyMeasurable]
  have hs := integral_integral_swap (μ := volume) (ν := μ)
    (f := fun y x : ℂ => φ y * (-Real.log ‖x - y‖))
    (integrable_test_log_unitCircle_prod φ)
  change (∫ x, LQGMetric.CircleAvg.logPot φ x ∂μ) = _
  calc
    (∫ x, LQGMetric.CircleAvg.logPot φ x ∂μ) =
        ∫ x, (∫ y, φ y * (-Real.log ‖x - y‖)) ∂μ := by
          apply integral_congr_ae
          filter_upwards with x
          unfold LQGMetric.CircleAvg.logPot
          apply integral_congr_ae
          filter_upwards with y
          ring
    _ = ∫ y, (∫ x, φ y * (-Real.log ‖x - y‖) ∂μ) := hs.symm
    _ = -∫ y, φ y * LQGMetric.CircleAvg.circLog 0 1 y := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards with y
      rw [integral_const_mul, integral_neg]
      change φ y * -(∫ x, Real.log ‖x - y‖ ∂LQGDimension.Coupling.circMeas 0 1) = _
      have hm : AEStronglyMeasurable (fun x : ℂ => Real.log ‖x - y‖)
          (LQGDimension.Coupling.circMeas 0 1) :=
        (show Measurable (fun x : ℂ => Real.log ‖x - y‖) from
          Real.measurable_log.comp (measurable_id.sub measurable_const).norm).aestronglyMeasurable
      rw [LQGDimension.Coupling.integral_circMeas_eq_circleAverage hm]
      change φ y * -LQGMetric.CircleAvg.circLog 0 1 y = _
      ring

#print axioms circleAverage_logPot_unitCircle

/-- The logarithmic kernel times a test is integrable against Lebesgue measure
and the circle measure; this justifies exchanging these integrals. -/
theorem integrable_test_log_circle_prod (φ : LQGMetric.TestC) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    Integrable (fun p : ℂ × ℂ => φ p.1 * (-Real.log ‖p.2 - p.1‖))
      (volume.prod (LQGDimension.Coupling.circMeas z r)) := by
  let μ := LQGDimension.Coupling.circMeas z r
  let g : ℂ × ℂ → ℝ := fun p => φ p.1 * (-Real.log ‖p.2 - p.1‖)
  have hm : AEStronglyMeasurable g (volume.prod μ) := by
    apply Measurable.aestronglyMeasurable
    exact (φ.continuous.measurable.comp measurable_fst).mul
      (((Real.measurable_log.comp (measurable_snd.sub measurable_fst).norm)).neg)
  change Integrable g (volume.prod μ)
  rw [integrable_prod_iff hm]
  constructor
  · filter_upwards with y
    exact ((LQGDimension.Coupling.integrable_log_norm_sub_circ y z r).neg.const_mul
      (φ y)).congr (Filter.Eventually.of_forall fun x => by simp only [g, Pi.neg_apply, norm_sub_rev])
  · let b : ℂ → ℝ := fun y => ‖φ y‖ * (2 * (‖y‖ + ‖z‖ + r) + |Real.log r|)
    have hbi : Integrable b := by
      have hc : Continuous b := by
        dsimp [b]
        fun_prop
      exact hc.integrable_of_hasCompactSupport φ.hasCompactSupport.norm.mul_right
    refine hbi.mono' hm.norm.integral_prod_right' (Filter.Eventually.of_forall fun y => ?_)
    have hbound := LQGDimension.Coupling.integral_abs_log_le y z hr
    have hn : 0 ≤ 2 * (‖y‖ + ‖z‖ + r) + |Real.log r| := by positivity
    have heq : (∫ x, ‖g (y, x)‖ ∂μ) = ‖φ y‖ *
        (∫ x, |Real.log ‖y - x‖| ∂μ) := by
      simp only [g, norm_mul, norm_neg, Real.norm_eq_abs, norm_sub_rev, integral_const_mul]
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _), heq]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    linarith [neg_abs_le (Real.log r)]

#print axioms integrable_test_log_circle_prod

/-- The circle average of Leonardo Bonanno's logarithmic potential is
the negative test integral of the circle logarithmic potential. -/
theorem circleAverage_logPot_circle (φ : LQGMetric.TestC) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    Real.circleAverage (LQGMetric.CircleAvg.logPot φ) z r =
      -∫ y, φ y * LQGMetric.CircleAvg.circLog z r y := by
  let μ := LQGDimension.Coupling.circMeas z r
  rw [← LQGDimension.Coupling.integral_circMeas_eq_circleAverage
    (LQGMetric.CircleAvg.measurable_logPot φ).aestronglyMeasurable]
  have hs := integral_integral_swap (μ := volume) (ν := μ)
    (f := fun y x : ℂ => φ y * (-Real.log ‖x - y‖))
    (integrable_test_log_circle_prod φ z hr)
  change (∫ x, LQGMetric.CircleAvg.logPot φ x ∂μ) = _
  calc
    (∫ x, LQGMetric.CircleAvg.logPot φ x ∂μ) =
        ∫ x, (∫ y, φ y * (-Real.log ‖x - y‖)) ∂μ := by
          apply integral_congr_ae
          filter_upwards with x
          unfold LQGMetric.CircleAvg.logPot
          apply integral_congr_ae
          filter_upwards with y
          ring
    _ = ∫ y, (∫ x, φ y * (-Real.log ‖x - y‖) ∂μ) := hs.symm
    _ = -∫ y, φ y * LQGMetric.CircleAvg.circLog z r y := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards with y
      rw [integral_const_mul, integral_neg]
      change φ y * -(∫ x, Real.log ‖x - y‖ ∂LQGDimension.Coupling.circMeas z r) = _
      have hm : AEStronglyMeasurable (fun x : ℂ => Real.log ‖x - y‖)
          (LQGDimension.Coupling.circMeas z r) :=
        (show Measurable (fun x : ℂ => Real.log ‖x - y‖) from
          Real.measurable_log.comp (measurable_id.sub measurable_const).norm).aestronglyMeasurable
      rw [LQGDimension.Coupling.integral_circMeas_eq_circleAverage hm]
      change φ y * -LQGMetric.CircleAvg.circLog z r y = _
      ring

#print axioms circleAverage_logPot_circle

/-- The mixed project kernel in terms of the normalized logarithmic potential
of Leonardo Bonanno's test pairing. -/
theorem wholePlaneGFFCov_circle_pairing_eq_potential (φ : LQGMetric.TestC)
    (z : ℂ) (r : ℝ) :
    wholePlaneGFFCov (.circle r z) (.pairing φ) =
      Real.circleAverage (fun x => LQGMetric.CircleAvg.logPot φ x +
        (∫ y, φ y) * LQGMetric.CircleAvg.circLog 0 1 x) z r +
      ∫ y, φ y * LQGMetric.CircleAvg.circLog 0 1 y := by
  change Real.circleAverage (fun x => ∫ y, φ y * wholePlaneCov x y) z r = _
  simp_rw [integral_test_mul_wholePlaneCov]
  let f : ℂ → ℝ := fun x => LQGMetric.CircleAvg.logPot φ x +
    (∫ y, φ y) * LQGMetric.CircleAvg.circLog 0 1 x
  have hf : Continuous f := (LQGMetric.MarkovGermVer.contDiff_logPot φ).continuous.add
    (continuous_const.mul (LQGMetric.CircleAvg.continuous_circLog one_ne_zero 0))
  change Real.circleAverage (fun x => f x +
    (∫ y, φ y * LQGMetric.CircleAvg.circLog 0 1 y)) z r = _
  rw [Real.circleAverage_fun_add hf.continuousOn.circleIntegrable'
    (continuousOn_const.circleIntegrable'), Real.circleAverage_const]

#print axioms wholePlaneGFFCov_circle_pairing_eq_potential

/-- The mixed whole-plane kernel is integrable against a test function and a
circle measure. The diagonal convention is immaterial for this product. -/
theorem integrable_test_wholePlaneCov_circle_prod (φ : LQGMetric.TestC)
    (z : ℂ) {r : ℝ} (hr : 0 < r) :
    Integrable (fun p : ℂ × ℂ => φ p.1 * wholePlaneCov p.1 p.2)
      (volume.prod (LQGDimension.Coupling.circMeas z r)) := by
  let μ := LQGDimension.Coupling.circMeas z r
  let f : C(ℂ, ℝ) := ⟨LQGMetric.CircleAvg.circLog 0 1,
    LQGMetric.CircleAvg.continuous_circLog one_ne_zero 0⟩
  have hφ := LQGMetric.CircleAvg.integrable_testC φ
  have hf : Integrable f μ := by
    convert LQGDimension.Coupling.integrable_posLog_norm_circ z r using 1
    funext x
    change LQGMetric.CircleAvg.circLog 0 1 x = _
    rw [LQGMetric.CircleAvg.circLog_zero_one, Real.posLog_eq_log_max_one (norm_nonneg _), max_comm]
  have h1 := integrable_test_log_circle_prod φ z hr
  have h2 := (LQGMetric.CircleAvg.integrable_test_mul φ f).mul_prod
    (integrable_const (1 : ℝ) : Integrable (fun _ : ℂ => (1 : ℝ)) μ)
  have h3 := hφ.mul_prod hf
  have hi : Integrable (fun p : ℂ × ℂ =>
      φ p.1 * (-Real.log ‖p.2 - p.1‖) + (φ p.1 * f p.1) * 1 + φ p.1 * f p.2)
      (volume.prod μ) := (h1.add h2).add h3
  apply hi.congr
  have hne : ∀ᵐ p : ℂ × ℂ ∂volume.prod μ, p.1 ≠ p.2 := by
    have hm : MeasurableSet {p : ℂ × ℂ | p.1 ≠ p.2} :=
      (isClosed_eq continuous_fst continuous_snd).isOpen_compl.measurableSet
    apply (Measure.ae_prod_iff_ae_ae hm).2
    apply (Measure.ae_ae_comm hm).2
    filter_upwards with x
    exact Measure.ae_ne volume x
  filter_upwards [hne] with p hp
  rw [wholePlaneCov_eq_additive_of_ne hp, ← LQGMetric.CircleAvg.circLog_zero_one p.1,
    ← LQGMetric.CircleAvg.circLog_zero_one p.2, norm_sub_rev]
  dsimp [f]
  ring

#print axioms integrable_test_wholePlaneCov_circle_prod

/-- Exchanging a test pairing and a positive-radius circle average preserves
the covariance kernel, by Fubini's theorem. -/
theorem wholePlaneGFFCov_pairing_circle_symm (φ : LQGMetric.TestC)
    (z : ℂ) {r : ℝ} (hr : 0 < r) :
    wholePlaneGFFCov (.pairing φ) (.circle r z) =
      wholePlaneGFFCov (.circle r z) (.pairing φ) := by
  let μ := LQGDimension.Coupling.circMeas z r
  have hi := integrable_test_wholePlaneCov_circle_prod φ z hr
  change (∫ x, φ x * Real.circleAverage (wholePlaneCov x) z r) =
    Real.circleAverage (fun x => ∫ y, φ y * wholePlaneCov x y) z r
  have hm (x : ℂ) : AEStronglyMeasurable (wholePlaneCov x) μ := by
    apply Measurable.aestronglyMeasurable
    unfold wholePlaneCov
    fun_prop
  simp_rw [← LQGDimension.Coupling.integral_circMeas_eq_circleAverage (hm _),
    ← integral_const_mul]
  have hs := integral_integral_swap (μ := volume) (ν := μ)
    (f := fun x y : ℂ => φ x * wholePlaneCov x y) hi
  rw [hs]
  have hmeas : AEStronglyMeasurable (fun x => ∫ y, φ y * wholePlaneCov x y) μ := by
    have h := hi.swap.aestronglyMeasurable.integral_prod_right'
    convert h using 1
    ext x
    congr 1
    funext y
    unfold wholePlaneCov
    simp only [Function.comp_apply, Prod.swap_prod_mk]
    rw [norm_sub_rev, mul_comm (max ‖x‖ 1) (max ‖y‖ 1)]
  rw [← LQGDimension.Coupling.integral_circMeas_eq_circleAverage hmeas]
  apply integral_congr_ae
  filter_upwards with x
  apply integral_congr_ae
  filter_upwards with y
  unfold wholePlaneCov
  rw [norm_sub_rev, mul_comm (max ‖y‖ 1) (max ‖x‖ 1)]

#print axioms wholePlaneGFFCov_pairing_circle_symm

/-- Uniform potential convergence can be integrated against Leonardo Bonanno's
mollified circle increments. -/
theorem tendsto_integral_circDiff_mul_meanZeroApprox_error
    (φ : LQGMetric.TestC) (z w : ℂ) (r s : ℝ) :
    Tendsto (fun n => ∫ x, (LQGMetric.CircleAvg.circDiff n z r n w s).1 x *
      (LQGMetric.CircleAvg.logPot (LQGMetric.MarkovGerm.meanZeroApprox φ n).1 x -
        (LQGMetric.CircleAvg.logPot φ x + (∫ y, φ y) *
          LQGMetric.CircleAvg.circLog 0 1 x))) atTop (𝓝 0) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
    (by norm_num : (2 : ℝ)⁻¹ < 1)
  have he : Tendsto (fun n : ℕ => 2 * |∫ y, φ y| * (2 : ℝ)⁻¹ ^ n)
      atTop (𝓝 0) := by simpa using hp.const_mul (2 * |∫ y, φ y|)
  refine squeeze_zero_norm (fun n => ?_) he
  let g : ℂ → ℝ := fun x => LQGMetric.CircleAvg.circBump n z r x +
    LQGMetric.CircleAvg.circBump n w s x
  have hg : Integrable g := (LQGMetric.CircleAvg.integrable_testC _).add
    (LQGMetric.CircleAvg.integrable_testC _)
  have hgn : ∀ x, 0 ≤ g x := fun x => add_nonneg
    (LQGMetric.CircleAvg.circBump_nonneg _ _ _ _)
    (LQGMetric.CircleAvg.circBump_nonneg _ _ _ _)
  have hb : ∀ x, ‖(LQGMetric.CircleAvg.circDiff n z r n w s).1 x *
      (LQGMetric.CircleAvg.logPot (LQGMetric.MarkovGerm.meanZeroApprox φ n).1 x -
        (LQGMetric.CircleAvg.logPot φ x + (∫ y, φ y) *
          LQGMetric.CircleAvg.circLog 0 1 x))‖ ≤
      g x * (|∫ y, φ y| * (2 : ℝ)⁻¹ ^ n) := by
    intro x
    rw [norm_mul]
    apply mul_le_mul _ (by simpa only [Real.norm_eq_abs] using
      abs_logPot_meanZeroApprox_sub_le φ n x) (norm_nonneg _) (hgn x)
    change |LQGMetric.CircleAvg.circBump n z r x -
      LQGMetric.CircleAvg.circBump n w s x| ≤ _
    refine (abs_sub _ _).trans (le_of_eq ?_)
    rw [abs_of_nonneg (LQGMetric.CircleAvg.circBump_nonneg _ _ _ _),
      abs_of_nonneg (LQGMetric.CircleAvg.circBump_nonneg _ _ _ _)]
  refine (norm_integral_le_of_norm_le (hg.mul_const _) (Eventually.of_forall hb)).trans
    (le_of_eq ?_)
  rw [integral_mul_const, show ∫ x, g x = 2 by
    dsimp [g]
    rw [integral_add (LQGMetric.CircleAvg.integrable_testC _)
      (LQGMetric.CircleAvg.integrable_testC _), LQGMetric.CircleAvg.integral_circBump,
      LQGMetric.CircleAvg.integral_circBump]; norm_num]
  ring

#print axioms tendsto_integral_circDiff_mul_meanZeroApprox_error

/-- The mixed logarithmic covariances of Leonardo Bonanno's mollified circle
increments and normalized test approximations converge to the potential formula. -/
theorem tendsto_logCov_circDiff_meanZeroApprox (φ : LQGMetric.TestC)
    (z w : ℂ) (r s : ℝ) :
    Tendsto (fun n => LQGMetric.logCov (LQGMetric.CircleAvg.circDiff n z r n w s).1
      (LQGMetric.MarkovGerm.meanZeroApprox φ n).1) atTop
      (𝓝 (Real.circleAverage (fun x => LQGMetric.CircleAvg.logPot φ x +
        (∫ y, φ y) * LQGMetric.CircleAvg.circLog 0 1 x) z r -
        Real.circleAverage (fun x => LQGMetric.CircleAvg.logPot φ x +
        (∫ y, φ y) * LQGMetric.CircleAvg.circLog 0 1 x) w s)) := by
  let f : C(ℂ, ℝ) := ⟨fun x => LQGMetric.CircleAvg.logPot φ x +
      (∫ y, φ y) * LQGMetric.CircleAvg.circLog 0 1 x,
    (LQGMetric.MarkovGermVer.contDiff_logPot φ).continuous.add
      (continuous_const.mul (LQGMetric.CircleAvg.continuous_circLog one_ne_zero 0))⟩
  have hlim := ((LQGMetric.CircleAvg.tendsto_mollAvg_ofCont f r z).sub
    (LQGMetric.CircleAvg.tendsto_mollAvg_ofCont f s w)).add
      (tendsto_integral_circDiff_mul_meanZeroApprox_error φ z w r s)
  simp only [add_zero] at hlim
  refine hlim.congr fun n => ?_
  let D := (LQGMetric.CircleAvg.circDiff n z r n w s).1
  let E := (LQGMetric.MarkovGerm.meanZeroApprox φ n).1
  let p : C(ℂ, ℝ) := ⟨LQGMetric.CircleAvg.logPot E,
    (LQGMetric.MarkovGermVer.contDiff_logPot E).continuous⟩
  have h1 := LQGMetric.CircleAvg.integrable_test_mul D f
  have h2 := LQGMetric.CircleAvg.integrable_test_mul D p
  have herr : Integrable (fun x => D x * (p x - f x)) := by
    have heq : (fun x => D x * (p x - f x)) =
        (fun x => D x * p x) - (fun x => D x * f x) := by
      funext x; simp only [Pi.sub_apply]; ring
    rw [heq]
    exact h2.sub h1
  rw [LQGMetric.CircleAvg.logCov_eq_integral_logPot]
  have hD : (∫ x, D x * f x) =
      LQGMetric.CircleAvg.mollAvg (LQGMetric.ofCont f) n z r -
        LQGMetric.CircleAvg.mollAvg (LQGMetric.ofCont f) n w s := by
    change (∫ x, (LQGMetric.CircleAvg.circBump n z r x -
      LQGMetric.CircleAvg.circBump n w s x) * f x) = _
    simp_rw [sub_mul]
    rw [integral_sub (LQGMetric.CircleAvg.integrable_test_mul _ f)
      (LQGMetric.CircleAvg.integrable_test_mul _ f),
      LQGMetric.CircleAvg.integral_circBump_mul, LQGMetric.CircleAvg.integral_circBump_mul]
  rw [← hD]
  change (∫ x, D x * f x) + (∫ x, D x * (p x - f x)) = ∫ x, D x * p x
  rw [← integral_add h1 herr]
  congr 1
  funext x
  change D x * f x + D x * (p x - f x) = D x * p x
  ring

#print axioms tendsto_logCov_circDiff_meanZeroApprox

/-- The unit-circle normalization term averages to zero in Leonardo Bonanno's
potential formula. -/
theorem circleAverage_normalized_logPot_unitCircle (φ : LQGMetric.TestC) :
    Real.circleAverage (fun x => LQGMetric.CircleAvg.logPot φ x +
      (∫ y, φ y) * LQGMetric.CircleAvg.circLog 0 1 x) 0 1 =
      -∫ y, φ y * LQGMetric.CircleAvg.circLog 0 1 y := by
  have hzero : Real.circleAverage (LQGMetric.CircleAvg.circLog 0 1) 0 1 = 0 := by
    change LQGMetric.CircleAvg.circCov 0 1 0 1 = 0
    rw [LQGMetric.CircleAvg.circCov_center 0 one_pos 1 one_pos]
    simp [Real.posLog_apply]
  have h1 : CircleIntegrable (LQGMetric.CircleAvg.logPot φ) 0 1 :=
    (LQGMetric.MarkovGermVer.contDiff_logPot φ).continuous.continuousOn.circleIntegrable'
  have h2 : CircleIntegrable (fun x => (∫ y, φ y) * LQGMetric.CircleAvg.circLog 0 1 x) 0 1 :=
    (continuous_const.mul (LQGMetric.CircleAvg.continuous_circLog one_ne_zero 0)).continuousOn.circleIntegrable'
  rw [Real.circleAverage_fun_add h1 h2, circleAverage_logPot_unitCircle]
  change -_ + Real.circleAverage (fun x => (∫ y, φ y) •
    LQGMetric.CircleAvg.circLog 0 1 x) 0 1 = _
  rw [Real.circleAverage_fun_smul, hzero, smul_eq_mul, mul_zero, add_zero]

#print axioms circleAverage_normalized_logPot_unitCircle

/-- Leonardo Bonanno's normalized GFF has exactly the project's test-test
covariance, including the project's diagonal convention. -/
theorem normalizedGFF_pairing_covariance_eq_project
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistC} (hh : LQGMetric.IsNormalizedWPGFF h P)
    (ρ φ : LQGMetric.TestC) :
    cov[fun ω => h ω ρ, fun ω => h ω φ; P] =
      wholePlaneGFFCov (.pairing ρ) (.pairing φ) := by
  rw [normalizedGFF_pairing_covariance_eq_potential hh,
    wholePlaneGFFCov_pairings_eq_potential, circleAverage_normalized_logPot_unitCircle]
  ring

#print axioms normalizedGFF_pairing_covariance_eq_project

/-- The L² norm of one successive mollified circle increment has geometric
rate, using Leonardo Bonanno's variance estimate. -/
theorem norm_circleAvg_succ_toLp_le
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistC} (hh : LQGMetric.IsWholePlaneGFF h P)
    (z : ℂ) {r : ℝ} (hr : 0 < r) (n : ℕ) :
    ‖(LQGMetric.MarkovZB.memLp_pair hh
      (LQGMetric.CircleAvg.circDiff (n + 1) z r n z r)).toLp _‖ ≤
      Real.sqrt (4 / r) * Real.sqrt 2⁻¹ ^ n := by
  let D := LQGMetric.CircleAvg.circDiff (n + 1) z r n z r
  have hm := LQGMetric.MarkovZB.memLp_pair hh D
  have hsq : ‖hm.toLp (LQGMetric.pairProc h D)‖ ^ 2 ≤
      (Real.sqrt (4 / r) * Real.sqrt 2⁻¹ ^ n) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, LQGMetric.MarkovZB.inner_toLp_eq_cov _ _
      (LQGMetric.centered_pairProc hh _)]
    refine ((hh.covariance_eq _ _).trans_le
      (LQGMetric.CircleAvg.logCov_circDiff_succ_le hr z n)).trans_eq ?_
    rw [mul_pow, ← pow_mul, mul_comm n 2, pow_mul,
      Real.sq_sqrt (by positivity : 0 ≤ 4 / r), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

#print axioms norm_circleAvg_succ_toLp_le

/-- The L² representative of a mollified circle-average increment in
Leonardo Bonanno's GFF construction. -/
noncomputable def circleIncrementApproxVec
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistC} (hh : LQGMetric.IsWholePlaneGFF h P)
    (r : ℝ) (z : ℂ) (s : ℝ) (w : ℂ) (n : ℕ) : Lp ℝ 2 P :=
  (LQGMetric.MarkovZB.memLp_pair hh (LQGMetric.CircleAvg.circDiff n z r n w s)).toLp _

/-- The successive L² differences of mollified circle increments have a
summable geometric bound. -/
theorem norm_circleIncrementApproxVec_succ_sub_le
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistC} (hh : LQGMetric.IsWholePlaneGFF h P)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (z w : ℂ) (n : ℕ) :
    ‖circleIncrementApproxVec hh r z s w (n + 1) -
      circleIncrementApproxVec hh r z s w n‖ ≤
        (Real.sqrt (4 / r) + Real.sqrt (4 / s)) * Real.sqrt 2⁻¹ ^ n := by
  let A := LQGMetric.CircleAvg.circDiff (n + 1) z r n z r
  let B := LQGMetric.CircleAvg.circDiff (n + 1) w s n w s
  have ha := LQGMetric.MarkovZB.memLp_pair hh A
  have hb := LQGMetric.MarkovZB.memLp_pair hh B
  have heq : circleIncrementApproxVec hh r z s w (n + 1) -
      circleIncrementApproxVec hh r z s w n =
        ha.toLp (LQGMetric.pairProc h A) - hb.toLp (LQGMetric.pairProc h B) := by
    unfold circleIncrementApproxVec
    rw [← MemLp.toLp_sub, ← MemLp.toLp_sub]
    apply MemLp.toLp_congr
    filter_upwards with ω
    simp only [Pi.sub_apply, LQGMetric.pairProc]
    rw [← LQGMetric.CircleAvg.mollAvg_sub_eq, ← LQGMetric.CircleAvg.mollAvg_sub_eq,
      ← LQGMetric.CircleAvg.mollAvg_sub_eq, ← LQGMetric.CircleAvg.mollAvg_sub_eq]
    ring
  rw [heq]
  calc
    ‖ha.toLp (LQGMetric.pairProc h A) - hb.toLp (LQGMetric.pairProc h B)‖ ≤
        ‖ha.toLp (LQGMetric.pairProc h A)‖ + ‖hb.toLp (LQGMetric.pairProc h B)‖ :=
          norm_sub_le _ _
    _ ≤ Real.sqrt (4 / r) * Real.sqrt 2⁻¹ ^ n +
        Real.sqrt (4 / s) * Real.sqrt 2⁻¹ ^ n :=
      add_le_add (norm_circleAvg_succ_toLp_le hh z hr n)
        (norm_circleAvg_succ_toLp_le hh w hs n)
    _ = _ := by ring

#print axioms norm_circleIncrementApproxVec_succ_sub_le

/-- Leonardo Bonanno's mollified circle increments converge in L² to a
representative of the circle-average increment. -/
theorem exists_tendsto_circleIncrementApproxVec
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistC} (hh : LQGMetric.IsWholePlaneGFF h P)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (z w : ℂ) :
    ∃ Y : Lp ℝ 2 P, Tendsto (circleIncrementApproxVec hh r z s w) atTop (𝓝 Y) ∧
      (Y : Ω → ℝ) =ᵐ[P] LQGMetric.CircleAvg.cInc h r z s w := by
  have hq : Real.sqrt 2⁻¹ < 1 := (Real.sqrt_lt' one_pos).2 (by norm_num)
  have hc : CauchySeq (circleIncrementApproxVec hh r z s w) :=
    cauchySeq_of_le_geometric _ _ hq fun n => by
      rw [dist_comm, dist_eq_norm]
      exact norm_circleIncrementApproxVec_succ_sub_le hh hr hs z w n
  obtain ⟨Y, hY⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨Y, hY, ?_⟩
  let X : ℕ → Ω → ℝ := fun n =>
    LQGMetric.pairProc h (LQGMetric.CircleAvg.circDiff n z r n w s)
  have h1 : TendstoInMeasure P X atTop Y :=
    (tendstoInMeasure_of_tendsto_Lp hY).congr_left fun n =>
      (LQGMetric.MarkovZB.memLp_pair hh _).coeFn_toLp
  have h2 : TendstoInMeasure P X atTop (LQGMetric.CircleAvg.cInc h r z s w) := by
    refine tendstoInMeasure_of_tendsto_ae (fun n => ?_) ?_
    · exact (LQGMetric.MarkovGerm.measurable_eval hh _).aestronglyMeasurable
    · filter_upwards [LQGMetric.CircleAvg.ae_tendsto_mInc hh hr hs z w] with ω hω
      convert hω using 1
      funext n
      exact (LQGMetric.CircleAvg.mollAvg_sub_eq (h ω) n z r n w s).symm
  exact tendstoInMeasure_ae_unique h1 h2

#print axioms exists_tendsto_circleIncrementApproxVec

/-- Mixed covariance of Leonardo Bonanno's circle increment and test pairing,
obtained as the L² limit of their mean-zero approximations. -/
theorem normalizedGFF_circleIncrement_pairing_covariance_tendsto
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistC} (hh : LQGMetric.IsNormalizedWPGFF h P)
    (φ : LQGMetric.TestC) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (z w : ℂ) :
    Tendsto (fun n => LQGMetric.logCov (LQGMetric.CircleAvg.circDiff n z r n w s).1
      (LQGMetric.MarkovGerm.meanZeroApprox φ n).1) atTop
      (𝓝 (cov[LQGMetric.CircleAvg.cInc h r z s w, fun ω => h ω φ; P])) := by
  obtain ⟨U, hU, hUae⟩ := exists_tendsto_circleIncrementApproxVec hh.1 hr hs z w
  let V := LQGMetric.MarkovNorm.pairVec hh φ
  have hcenter : ∫ ω, (U : Ω → ℝ) ω ∂P = 0 := by
    rw [integral_congr_ae hUae]
    exact LQGMetric.CircleAvg.integral_cInc hh.1 hr hs z w
  have hc : ⟪U, V⟫ =
      cov[LQGMetric.CircleAvg.cInc h r z s w, fun ω => h ω φ; P] := by
    calc
      ⟪U, V⟫ = cov[(U : Ω → ℝ), (V : Ω → ℝ); P] := by
        simpa only [Lp.toLp_coeFn] using
          LQGMetric.MarkovZB.inner_toLp_eq_cov (Lp.memLp U) (Lp.memLp V) hcenter
      _ = _ := LQGMetric.MarkovNorm.cov_congr_ae hUae
        (LQGMetric.MarkovNorm.pairVec_ae hh φ)
  have ht := hU.inner (𝕜 := ℝ) (LQGMetric.MarkovNorm.tendsto_pairVec hh φ)
  rw [hc] at ht
  refine ht.congr fun n => ?_
  dsimp only [circleIncrementApproxVec, LQGMetric.MarkovNorm.apxVec]
  rw [LQGMetric.MarkovZB.inner_toLp_eq_cov _ _ (LQGMetric.centered_pairProc hh.1 _)]
  exact hh.1.covariance_eq _ _

#print axioms normalizedGFF_circleIncrement_pairing_covariance_tendsto

/-- The mixed covariance of a normalized circle average and a test pairing
is the project whole-plane covariance kernel. -/
theorem normalizedGFF_circleIncrement_pairing_covariance_eq_project
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistC} (hh : LQGMetric.IsNormalizedWPGFF h P)
    (φ : LQGMetric.TestC) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    cov[LQGMetric.CircleAvg.cInc h r z 1 0, fun ω => h ω φ; P] =
      wholePlaneGFFCov (.circle r z) (.pairing φ) := by
  have heq := tendsto_nhds_unique
    (normalizedGFF_circleIncrement_pairing_covariance_tendsto hh φ hr one_pos z 0)
    (tendsto_logCov_circDiff_meanZeroApprox φ z 0 r 1)
  rw [circleAverage_normalized_logPot_unitCircle] at heq
  rw [wholePlaneGFFCov_circle_pairing_eq_potential]
  linarith

#print axioms normalizedGFF_circleIncrement_pairing_covariance_eq_project

/-- The mollified circle-average increments of Leonardo Bonanno's normalized
GFF are jointly Gaussian with all of its test-function pairings. -/
theorem normalizedGFF_pairings_mollifiedIncrements_gaussian
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistC} (hh : LQGMetric.IsNormalizedWPGFF h P) (n : ℕ) :
    IsGaussianProcess (Sum.elim (fun (φ : LQGMetric.TestC) ω => h ω φ)
      (LQGMetric.CircleAvg.incProcN h n)) P := by
  let f : LQGMetric.TestC ⊕ LQGMetric.CircleAvg.IncIdx → LQGMetric.TestC :=
    Sum.elim id (fun p => (LQGMetric.CircleAvg.circDiff n p.1.2 p.1.1 n p.2.2 p.2.1).1)
  have hg := (normalizedGFF_allPairings_gaussian hh).1.comp_right f
  refine hg.congr fun p => ?_
  cases p with
  | inl φ => exact Filter.Eventually.of_forall fun _ => rfl
  | inr p =>
    exact Filter.Eventually.of_forall fun ω =>
      (LQGMetric.CircleAvg.mollAvg_sub_eq (h ω) n p.1.2 p.1.1 n p.2.2 p.2.1).symm

#print axioms normalizedGFF_pairings_mollifiedIncrements_gaussian

/-- The pairings and circle-average increments of Leonardo Bonanno's normalized
GFF form one jointly Gaussian process. -/
theorem normalizedGFF_pairings_increments_gaussian
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistC} (hh : LQGMetric.IsNormalizedWPGFF h P) :
    IsGaussianProcess (Sum.elim (fun (φ : LQGMetric.TestC) ω => h ω φ)
      (LQGMetric.CircleAvg.incProc h)) P := by
  classical
  let X := Sum.elim (fun (φ : LQGMetric.TestC) ω => h ω φ) (LQGMetric.CircleAvg.incProc h)
  let Xn := fun n => Sum.elim (fun (φ : LQGMetric.TestC) ω => h ω φ)
    (LQGMetric.CircleAvg.incProcN h n)
  have hg : ∀ n, IsGaussianProcess (Xn n) P :=
    normalizedGFF_pairings_mollifiedIncrements_gaussian hh
  have hm : ∀ i, Measurable (X i) := by
    intro i
    cases i with
    | inl φ => exact LQGMetric.MarkovGerm.measurable_eval hh.1 φ
    | inr p => exact LQGMetric.CircleAvg.measurable_cInc hh.1 _ _ _ _
  have hmean : ∀ n i, ∫ ω, Xn n i ω ∂P = 0 := by
    intro n i
    cases i with
    | inl φ => exact (normalizedGFF_allPairings_gaussian hh).2 φ
    | inr p => exact LQGMetric.CircleAvg.integral_incProcN hh.1 n p
  have hlim : ∀ i, ∀ᵐ ω ∂P, Tendsto (fun n => Xn n i ω) atTop (𝓝 (X i ω)) := by
    intro i
    cases i with
    | inl φ => exact Eventually.of_forall fun _ => tendsto_const_nhds
    | inr p => exact LQGMetric.CircleAvg.ae_tendsto_mInc hh.1 p.1.1.2 p.2.1.2 _ _
  refine ⟨fun I => ?_⟩
  let Y : Ω → (I → ℝ) := fun ω => I.restrict (X · ω)
  have hY : Measurable Y := measurable_pi_iff.mpr fun i => hm i.1
  refine ⟨hY.aemeasurable, isGaussian_of_map_eq_gaussianReal fun L => ?_⟩
  rw [AEMeasurable.map_map_of_aemeasurable L.continuous.measurable.aemeasurable hY.aemeasurable]
  let Yn : ℕ → Ω → (I → ℝ) := fun n ω => I.restrict (Xn n · ω)
  have hG : ∀ n, HasGaussianLaw (fun ω => L (Yn n ω)) P := fun n =>
    ((hg n).hasGaussianLaw I).map_fun L
  have hzero : ∀ n, P[fun ω => L (Yn n ω)] = 0 := by
    intro n
    have e : ∀ ω, L (Yn n ω) = ∑ i : I, Yn n ω i * L (fun j => if i = j then 1 else 0) := by
      intro ω
      have := LinearMap.pi_apply_eq_sum_univ L.toLinearMap (Yn n ω)
      simpa [smul_eq_mul] using this
    simp_rw [e]
    rw [integral_finsetSum _ fun i _ =>
      ((((hg n).hasGaussianLaw_eval i.1).integrable).mul_const _)]
    refine Finset.sum_eq_zero fun i _ => ?_
    simp [Yn, Finset.restrict, hmean, integral_mul_const]
  have hmap : ∀ n, P.map (fun ω => L (Yn n ω)) =
      gaussianReal 0 (Var[fun ω => L (Yn n ω); P]).toNNReal := by
    intro n
    rw [(hG n).map_eq_gaussianReal, hzero]
  have ht : ∀ᵐ ω ∂P, Tendsto (fun n => L (Yn n ω)) atTop (𝓝 (L (Y ω))) := by
    have hall : ∀ᵐ ω ∂P, ∀ i : I, Tendsto (fun n => Xn n i.1 ω) atTop
        (𝓝 (X i.1 ω)) := by
      rw [ae_all_iff]
      intro i
      exact hlim i.1
    filter_upwards [hall] with ω hω
    exact (L.continuous.tendsto _).comp (tendsto_pi_nhds.mpr hω)
  obtain ⟨V, -, hV⟩ := LQGMetric.exists_gaussianReal_of_ae_tendsto
    (fun n => (hG n).aemeasurable) (L.continuous.measurable.comp hY).aemeasurable hmap ht
  exact ⟨0, V, hV⟩

#print axioms normalizedGFF_pairings_increments_gaussian

/-- Leonardo Bonanno's normalized GFF admits a continuous circle-average
version that is jointly Gaussian with all test-function pairings. -/
theorem normalizedGFF_exists_joint_circle_version
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistC} (hh : LQGMetric.IsNormalizedWPGFF h P) :
    ∃ H : ℝ → ℂ → Ω → ℝ,
      (∀ ω, ContinuousOn (fun p : ℝ × ℂ => H p.1 p.2 ω) (Set.Ioi 0 ×ˢ Set.univ)) ∧
      (∀ r, 0 < r → ∀ z, (fun ω => H r z ω) =ᵐ[P]
        fun ω => LQGMetric.circleAvg (h ω) r z) ∧
      IsGaussianProcess (Sum.elim (fun (φ : LQGMetric.TestC) ω => h ω φ)
        (fun (p : Set.Ioi (0 : ℝ) × ℂ) ω => H p.1 p.2 ω)) P ∧
      ∀ r s, 0 < r → 0 < s → ∀ z w,
        cov[H r z, H s w; P] = wholePlaneGFFCov (.circle r z) (.circle s w) := by
  obtain ⟨H, hcont, hae⟩ := LQGMetric.CircleAvg.exists_continuous_version_circleAvg hh.1
  refine ⟨H, hcont, ?_, ?_, ?_⟩
  · intro r hr z
    filter_upwards [hae r hr z, hh.2] with ω hω h0
    rw [hω, h0, sub_zero]
  · let f : LQGMetric.TestC ⊕ (Set.Ioi (0 : ℝ) × ℂ) →
        LQGMetric.TestC ⊕ LQGMetric.CircleAvg.IncIdx :=
      Sum.elim Sum.inl (fun p => Sum.inr (p, (⟨1, Set.mem_Ioi.mpr one_pos⟩, 0)))
    have hg := (normalizedGFF_pairings_increments_gaussian hh).comp_right f
    refine hg.congr fun p => ?_
    cases p with
    | inl φ => exact Eventually.of_forall fun _ => rfl
    | inr p => exact (hae p.1 p.1.2 p.2).symm
  · intro r s hr hs z w
    rw [LQGMetric.CircleAvg.covariance_congr_ae (hae r hr z) (hae s hs w),
      wholePlaneGFFCov_circle_eq_gffCircleCov hs,
      LQGMetric.CircleAvg.gffCircleCov_eq_incCov hr hs]
    exact LQGMetric.CircleAvg.covariance_cInc hh.1 hr one_pos hs one_pos z 0 w 0

#print axioms normalizedGFF_exists_joint_circle_version

/-- A measurable coordinatewise modification preserves all six fields of the
whole-plane GFF specification, with circle averages unchanged. -/
theorem IsWholePlaneGFF.coordinateModification
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC hC' : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc)
    (hm : ∀ φ, IsTestFunction Set.univ φ → Measurable fun ω => hC' ω φ)
    (he : ∀ φ, IsTestFunction Set.univ φ → (fun ω => hC ω φ) =ᵐ[P] (fun ω => hC' ω φ)) :
    IsWholePlaneGFF P hC' hcirc := by
  have heval (o : GFFObservable) (ho : o.IsAdmissible) :
      (fun ω => o.eval (hC ω) (hcirc ω)) =ᵐ[P]
        (fun ω => o.eval (hC' ω) (hcirc ω)) := by
    cases o with
    | pairing φ => exact he φ ho
    | circle r z => exact Filter.Eventually.of_forall (fun _ => rfl)
  refine ⟨hm, hh.measurable_circle, hh.isGaussianProcess.congr (fun o => heval o.1 o.2), ?_, ?_, hh.ae_continuousOn_circle⟩
  · intro o ho
    rw [← integral_congr_ae (heval o ho)]
    exact hh.integral_eq_zero o ho
  · intro o o' ho ho'
    have h₁ := heval o ho
    have h₂ := heval o' ho'
    have hi₁ := integral_congr_ae h₁
    have hi₂ := integral_congr_ae h₂
    calc
      cov[fun ω => o.eval (hC' ω) (hcirc ω), fun ω => o'.eval (hC' ω) (hcirc ω); P] =
          cov[fun ω => o.eval (hC ω) (hcirc ω), fun ω => o'.eval (hC ω) (hcirc ω); P] := by
            unfold ProbabilityTheory.covariance
            apply integral_congr_ae
            filter_upwards [h₁, h₂] with ω hω hω'
            rw [← hω, ← hω', ← hi₁, ← hi₂]
      _ = wholePlaneGFFCov o o' := hh.covariance_eq o o' ho ho'

/-- Pulling back a whole-plane GFF through a measure-preserving map preserves
its complete joint specification. -/
theorem IsWholePlaneGFF.comp_measurePreserving
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {f : Ω' → Ω}
    (hf : MeasurePreserving f P' P) :
    IsWholePlaneGFF P' (fun ω => hC (f ω)) (fun ω => hcirc (f ω)) := by
  have hm (o : GFFObservable) (ho : o.IsAdmissible) :
      Measurable (fun ω => o.eval (hC ω) (hcirc ω)) := by
    cases o with
    | pairing φ => exact hh.measurable_pairing φ ho
    | circle r z => exact hh.measurable_circle r z ho
  refine ⟨fun φ hφ => (hh.measurable_pairing φ hφ).comp hf.measurable,
    fun r z hr => (hh.measurable_circle r z hr).comp hf.measurable, ?_, ?_, ?_, ?_⟩
  · constructor
    intro I
    let X := fun ω (i : I) => i.1.1.eval (hC ω) (hcirc ω)
    have hX : Measurable X := measurable_pi_iff.mpr (fun i => hm i.1.1 i.1.2)
    have hG := hh.isGaussianProcess.hasGaussianLaw I
    have hmap : P'.map (X ∘ f) = P.map X := by
      rw [← Measure.map_map hX hf.measurable, hf.map_eq]
    exact ⟨(hX.comp hf.measurable).aemeasurable, hmap ▸ hG.isGaussian_map⟩
  · intro o ho
    have hi := integral_map hf.measurable.aemeasurable (f := fun ω => o.eval (hC ω) (hcirc ω))
      (by rw [hf.map_eq]; exact (hm o ho).aestronglyMeasurable)
    rw [hf.map_eq] at hi
    exact hi.symm.trans (hh.integral_eq_zero o ho)
  · intro o o' ho ho'
    have hc := covariance_map_fun (μ := P') (Z := f)
      (by rw [hf.map_eq]; exact (hm o ho).aestronglyMeasurable)
      (by rw [hf.map_eq]; exact (hm o' ho').aestronglyMeasurable)
      hf.measurable.aemeasurable
    rw [hf.map_eq] at hc
    exact hc.symm.trans (hh.covariance_eq o o' ho ho')
  · exact hf.quasiMeasurePreserving.ae hh.ae_continuousOn_circle

/-- A diagonal spike has measurable sections and vanishes almost surely at
    each fixed index when its parameter has no atoms. -/
theorem diagonalSpike_sections
    {Ω I : Type*} [MeasurableSpace Ω] [DecidableEq I] {P : Measure Ω}
    (t : Ω → ℝ) (ht : Measurable t)
    (hnull : ∀ r, ∀ᵐ ω ∂P, t ω ≠ r)
    (a : ℝ → I) (ha : Function.Injective a) :
    (∀ i, Measurable (fun ω => if i = a (t ω) then (1 : ℝ) else 0)) ∧
    (∀ i, ∀ᵐ ω ∂P, (if i = a (t ω) then (1 : ℝ) else 0) = 0) := by
  classical
  have hsection (i : I) : MeasurableSet {ω | i = a (t ω)} := by
    by_cases hi : ∃ r, i = a r
    · obtain ⟨r, rfl⟩ := hi
      have heq : {ω | a r = a (t ω)} = {ω | t ω = r} := by
        ext ω
        simp only [Set.mem_ofPred_eq]
        constructor
        · intro h
          exact (ha h).symm
        · intro h
          rw [h]
      rw [heq]
      exact measurableSet_eq_fun ht measurable_const
    · have hempty : {ω | i = a (t ω)} = ∅ := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hi ⟨t ω, h⟩
      rw [hempty]
      exact MeasurableSet.empty
  constructor
  · intro i
    exact Measurable.ite (hsection i) measurable_const measurable_const
  · intro i
    by_cases hi : ∃ r, i = a r
    · obtain ⟨r, rfl⟩ := hi
      filter_upwards [hnull r] with ω hω
      have hne : a r ≠ a (t ω) := fun h => hω (ha h).symm
      simp only [hne, ↓reduceIte]
    · filter_upwards with ω
      have hne : i ≠ a (t ω) := fun h => hi ⟨t ω, h⟩
      simp only [hne, ↓reduceIte]

/-- On any GFF probability space carrying a diffuse parameter, the diagonal
modification retains the full GFF specification. If the original pairings
obey the indicated scalar relation, the modified pairings violate it almost
surely. Instantiating this conditional result requires a suitable joint GFF. -/
theorem IsWholePlaneGFF.exists_diagonal_modification
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc)
    (t : Ω → ℝ) (ht : Measurable t)
    (hnull : ∀ r, ∀ᵐ ω ∂P, t ω ≠ r)
    (a : ℝ → (ℂ → ℝ)) (ha : Function.Injective a)
    (hlinear : ∀ᵐ ω ∂P, hC ω (a (2 * t ω)) = 2 * hC ω (a (t ω))) :
    ∃ hC' : Ω → (ℂ → ℝ) → ℝ, IsWholePlaneGFF P hC' hcirc ∧
      (∀ φ, (fun ω => hC ω φ) =ᵐ[P] (fun ω => hC' ω φ)) ∧
      ∀ᵐ ω ∂P, hC' ω (a (2 * t ω)) ≠ 2 * hC' ω (a (t ω)) := by
  classical
  let D : Ω → (ℂ → ℝ) → ℝ := fun ω φ => if φ = a (t ω) then 1 else 0
  have hd := diagonalSpike_sections t ht hnull a ha
  let hC' := fun ω φ => hC ω φ + D ω φ
  have he (φ : ℂ → ℝ) : (fun ω => hC ω φ) =ᵐ[P] (fun ω => hC' ω φ) := by
    filter_upwards [hd.2 φ] with ω hω
    simp only [hC', D, hω, add_zero]
  refine ⟨hC', hh.coordinateModification (fun φ hφ => (hh.measurable_pairing φ hφ).add (hd.1 φ))
    (fun φ _ => he φ), he, ?_⟩
  filter_upwards [hlinear, hnull 0] with ω hl hn
  have hne : a (2 * t ω) ≠ a (t ω) := by
    intro h
    have hhzero : t ω = 0 := by
      have hhcoef := ha h
      linarith
    exact hn hhzero
  change hC ω (a (2 * t ω)) + D ω (a (2 * t ω)) ≠
    2 * (hC ω (a (t ω)) + D ω (a (t ω)))
  simp only [D, hne, ↓reduceIte, add_zero]
  linarith

/-- A diagonal modification can be chosen to violate scalar linearity at
    almost every sample, without any regularity assumption on the starting
    pairings. The curve must consist of admissible test functions. -/
theorem IsWholePlaneGFF.exists_ae_non_linear_modification
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc)
    (t : Ω → ℝ) (ht : Measurable t)
    (hnull : ∀ r, ∀ᵐ ω ∂P, t ω ≠ r)
    (a : ℝ → (ℂ → ℝ)) (ha : Function.Injective a)
    (hat : ∀ r, IsTestFunction Set.univ (a r)) :
    ∃ hC' : Ω → (ℂ → ℝ) → ℝ, IsWholePlaneGFF P hC' hcirc ∧
      (∀ φ, (fun ω => hC ω φ) =ᵐ[P] (fun ω => hC' ω φ)) ∧
      ∀ᵐ ω ∂P, hC' ω (a (2 * t ω)) ≠ 2 * hC' ω (a (t ω)) := by
  classical
  let D : Ω → (ℂ → ℝ) → ℝ := fun ω φ =>
    if φ = a (t ω) then
      if hC ω (a (2 * t ω)) = 2 * hC ω φ + 2 then 2 else 1
    else 0
  have hd := diagonalSpike_sections t ht hnull a ha
  have hm (φ : ℂ → ℝ) : Measurable (fun ω => D ω φ) := by
    by_cases hφ : ∃ r, φ = a r
    · obtain ⟨r, rfl⟩ := hφ
      have heq : (fun ω => D ω (a r)) = fun ω =>
          if t ω = r then
            if hC ω (a (2 * r)) = 2 * hC ω (a r) + 2 then 2 else 1
          else 0 := by
        funext ω
        by_cases htr : t ω = r
        · subst r
          simp only [D, ↓reduceIte]
        · have hne : a r ≠ a (t ω) := fun h => htr (ha h).symm
          simp only [D, hne, htr, ↓reduceIte]
      rw [heq]
      apply Measurable.ite (measurableSet_eq_fun ht measurable_const)
      · exact Measurable.ite (measurableSet_eq_fun (hh.measurable_pairing _ (hat (2 * r)))
          (((hh.measurable_pairing _ (hat r)).const_mul 2).add_const 2)) measurable_const measurable_const
      · exact measurable_const
    · have heq : (fun ω => D ω φ) = fun _ => 0 := by
        funext ω
        have hne : φ ≠ a (t ω) := fun h => hφ ⟨t ω, h⟩
        simp only [D, hne, ↓reduceIte]
      rw [heq]
      exact measurable_const
  let hC' := fun ω φ => hC ω φ + D ω φ
  have he (φ : ℂ → ℝ) : (fun ω => hC ω φ) =ᵐ[P] (fun ω => hC' ω φ) := by
    filter_upwards [hd.2 φ] with ω hω
    have hne : φ ≠ a (t ω) := by
      intro h
      simp only [h, ↓reduceIte, one_ne_zero] at hω
    simp only [hC', D, hne, ↓reduceIte, add_zero]
  refine ⟨hC', hh.coordinateModification (fun φ hφ => (hh.measurable_pairing φ hφ).add (hm φ))
    (fun φ _ => he φ), he, ?_⟩
  filter_upwards [hnull 0] with ω hn
  have hne : a (2 * t ω) ≠ a (t ω) := by
    intro h
    have hhzero : t ω = 0 := by
      have hhcoef := ha h
      linarith
    exact hn hhzero
  change hC ω (a (2 * t ω)) + D ω (a (2 * t ω)) ≠
    2 * (hC ω (a (t ω)) + D ω (a (t ω)))
  simp only [D, hne, ↓reduceIte, add_zero]
  split_ifs with h
  · linarith
  · intro heq
    apply h
    linarith

/-- Given a diffuse parameter on a GFF probability space, some coordinatewise
modification has no common event of linearity along the specified curve. This
requires no samplewise regularity of the original pairings. -/
theorem IsWholePlaneGFF.exists_modification_not_ae_linear
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc)
    (t : Ω → ℝ) (ht : Measurable t)
    (hnull : ∀ r, ∀ᵐ ω ∂P, t ω ≠ r)
    (a : ℝ → (ℂ → ℝ)) (ha : Function.Injective a) :
    ∃ hC' : Ω → (ℂ → ℝ) → ℝ, IsWholePlaneGFF P hC' hcirc ∧
      (∀ φ, (fun ω => hC ω φ) =ᵐ[P] (fun ω => hC' ω φ)) ∧
      ¬ (∀ᵐ ω ∂P, ∀ r, hC' ω (a (2 * r)) = 2 * hC' ω (a r)) := by
  classical
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  by_cases hl : ∀ᵐ ω ∂P, ∀ r, hC ω (a (2 * r)) = 2 * hC ω (a r)
  · have hl' : ∀ᵐ ω ∂P, hC ω (a (2 * t ω)) = 2 * hC ω (a (t ω)) := by
      filter_upwards [hl] with ω hω
      exact hω (t ω)
    obtain ⟨hC', hG, he, hn⟩ := hh.exists_diagonal_modification t ht hnull a ha hl'
    refine ⟨hC', hG, he, ?_⟩
    intro hc
    have hf : ∀ᵐ ω ∂P, False := by
      filter_upwards [hc, hn] with ω hω hne
      exact hne (hω (t ω))
    obtain ⟨_, hfalse⟩ := Filter.Eventually.exists hf
    exact hfalse
  · exact ⟨hC, hh, fun _ => Filter.Eventually.of_forall (fun _ => rfl), hl⟩

/-- Every whole-plane GFF admits a product extension with an equal-in-law
coordinatewise modification whose test-function pairings lack a common
samplewise scalar-linearity event. -/
theorem IsWholePlaneGFF.product_has_non_linear_modification
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) :
    ∃ hC' : Ω × ℝ → (ℂ → ℝ) → ℝ,
      IsWholePlaneGFF (P.prod (gaussianReal 0 1)) hC' (fun p => hcirc p.1) ∧
      (∀ φ, (fun p : Ω × ℝ => hC p.1 φ) =ᵐ[P.prod (gaussianReal 0 1)] (fun p => hC' p φ)) ∧
      ¬ (∀ᵐ p ∂P.prod (gaussianReal 0 1), ∀ φ, IsTestFunction Set.univ φ → ∀ c : ℝ,
          hC' p (fun z => c * φ z) = c * hC' p φ) := by
  classical
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  let Q := P.prod (gaussianReal 0 1)
  have hp : IsWholePlaneGFF Q (fun p => hC p.1) (fun p => hcirc p.1) :=
    hh.comp_measurePreserving measurePreserving_fst
  have ht : ∀ r : ℝ, ∀ᵐ p ∂Q, p.2 ≠ r := by
    intro r
    have hr : ∀ᵐ x ∂(gaussianReal 0 1), x ≠ r := by
      apply ae_iff.mpr
      simpa only [not_not, Set.ofPred_eq_eq_singleton] using (measure_singleton r : gaussianReal 0 1 {r} = 0)
    exact measurePreserving_snd.quasiMeasurePreserving.ae hr
  let b : ContDiffBump (0 : ℂ) := ⟨1, 2, by norm_num, by norm_num⟩
  have hb : b (0 : ℂ) = 1 := b.one_of_mem_closedBall (by simp [b])
  let a : ℝ → (ℂ → ℝ) := fun r z => r * b z
  have ha : Function.Injective a := by
    intro r s h
    have hz := congrFun h 0
    simpa only [a, hb, mul_one] using hz
  have htest (r : ℝ) : IsTestFunction Set.univ (a r) :=
    ⟨contDiff_const.mul b.contDiff, b.hasCompactSupport.mul_left, Set.subset_univ _⟩
  obtain ⟨hC', hG, he, hn⟩ := hp.exists_modification_not_ae_linear Prod.snd measurable_snd ht a ha
  refine ⟨hC', hG, he, ?_⟩
  intro hl
  apply hn
  filter_upwards [hl] with p hlin r
  have h := hlin (a r) (htest r) 2
  have heq : (fun z => (2 : ℝ) * a r z) = a (2 * r) := by
    funext z
    simp only [a]
    ring
  rw [heq] at h
  exact h

/-- Every whole-plane GFF admits a product extension and a coordinatewise
modification whose test pairings fail scalar linearity at almost every sample. -/
theorem IsWholePlaneGFF.product_has_ae_non_linear_modification
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) :
    ∃ hC' : Ω × ℝ → (ℂ → ℝ) → ℝ,
      IsWholePlaneGFF (P.prod (gaussianReal 0 1)) hC' (fun p => hcirc p.1) ∧
      (∀ φ, (fun p : Ω × ℝ => hC p.1 φ) =ᵐ[P.prod (gaussianReal 0 1)] (fun p => hC' p φ)) ∧
      ∀ᵐ p ∂P.prod (gaussianReal 0 1), ∃ φ, IsTestFunction Set.univ φ ∧
          hC' p (fun z => 2 * φ z) ≠ 2 * hC' p φ := by
  classical
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  let Q := P.prod (gaussianReal 0 1)
  have hp : IsWholePlaneGFF Q (fun p => hC p.1) (fun p => hcirc p.1) :=
    hh.comp_measurePreserving measurePreserving_fst
  have ht : ∀ r : ℝ, ∀ᵐ p ∂Q, p.2 ≠ r := by
    intro r
    have hr : ∀ᵐ x ∂(gaussianReal 0 1), x ≠ r := by
      apply ae_iff.mpr
      simpa only [not_not, Set.ofPred_eq_eq_singleton] using (measure_singleton r : gaussianReal 0 1 {r} = 0)
    exact measurePreserving_snd.quasiMeasurePreserving.ae hr
  let b : ContDiffBump (0 : ℂ) := ⟨1, 2, by norm_num, by norm_num⟩
  have hb : b (0 : ℂ) = 1 := b.one_of_mem_closedBall (by simp [b])
  let a : ℝ → (ℂ → ℝ) := fun r z => r * b z
  have ha : Function.Injective a := by
    intro r s h
    have hz := congrFun h 0
    simpa only [a, hb, mul_one] using hz
  have htest (r : ℝ) : IsTestFunction Set.univ (a r) :=
    ⟨contDiff_const.mul b.contDiff, b.hasCompactSupport.mul_left, Set.subset_univ _⟩
  obtain ⟨hC', hG, he, hn⟩ :=
    hp.exists_ae_non_linear_modification Prod.snd measurable_snd ht a ha htest
  refine ⟨hC', hG, he, ?_⟩
  filter_upwards [hn] with p hp
  refine ⟨a p.2, htest p.2, ?_⟩
  have heq : (fun z => (2 : ℝ) * a p.2 z) = a (2 * p.2) := by
    funext z
    simp only [a]
    ring
  rw [heq]
  exact hp

#print axioms IsWholePlaneGFF.product_has_ae_non_linear_modification
#print axioms IsWholePlaneGFF.exists_ae_non_linear_modification
#print axioms IsWholePlaneGFF.product_has_non_linear_modification
#print axioms IsWholePlaneGFF.comp_measurePreserving
#print axioms IsWholePlaneGFF.exists_modification_not_ae_linear
#print axioms IsWholePlaneGFF.exists_diagonal_modification
#print axioms IsWholePlaneGFF.coordinateModification
#print axioms diagonalSpike_sections
end HarmonicBalls
