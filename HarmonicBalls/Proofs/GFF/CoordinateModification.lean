import HarmonicBalls.Defs.GFF
import LatticeProb.Bonanno.LQGMetric.Field.MarkovNorm
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
