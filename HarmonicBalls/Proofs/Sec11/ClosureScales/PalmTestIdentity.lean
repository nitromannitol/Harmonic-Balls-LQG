import Mathlib
import HarmonicBalls.Proofs.Sec11.ClosureScales.GaussianExpTilt
import HarmonicBalls.Proofs.Sec11.ClosureScales.GaussianFamilyLaw
import HarmonicBalls.Proofs.Sec11.ClosureScales.CircleGaussianMoment
import HarmonicBalls.Proofs.Sec11.ClosureScales.CircleAverageJointMeasurable
import HarmonicBalls.Proofs.Sec11.ClosureScales.GammaCovarianceShift
import HarmonicBalls.Proofs.Sec11.ClosureScales.MarkedFirstMoment
import HarmonicBalls.Proofs.Sec11.ClosureScales.MarkedComparison
import HarmonicBalls.Proofs.Sec11.ClosureScales.MarkedL1
import HarmonicBalls.Proofs.Sec11.ClosureScales.MarkedFatou
import HarmonicBalls.Proposed.DuplantierMillerSheffield

/-! # Route (A), Palm identity: the product-test case of Step M (r10 `l:r9-marked`)

For a bounded continuous `ψ : ℝ^k → ℝ`, test functions `φ_1, …, φ_k`, and a nonnegative continuous `η` supported in
the open unit disk, the marked identity
`E[ψ(hC φ) μ_g(η)] = ∫ η(z) E[ψ(hC φ + ∫ dmsShift_z φ)] d²z`
holds (`palm_test_identity`). The left-hand limit is the `L¹` convergence of the marked circle masses (`MarkedL1`),
the right-hand side is the exponential tilt (`tilt_circleAverage`) combined with the covariance shift
(`tendsto_gamma_cov_shift`); Fubini (`integral_fubini_marked`) exchanges `ω` and `z`, and dominated convergence in
`z` and in `ω` passes to the limit. The only literature input is the staged unnormalized DMS identity
`DMSLemmaA10WholePlaneUnnormalized`, used through `MarkedL1`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Filter Topology
open scoped NNReal

namespace HarmonicBalls

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The circle average `h_r(z)` of a whole-plane GFF in the closed unit disk is a centred Gaussian of variance
`-log r`. -/
theorem hasLaw_circleAverage {P : Measure Ω} [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r) (z : ℂ)
    (hdisk : ∀ x ∈ Metric.sphere z r, ‖x‖ ≤ 1) :
    HasLaw (fun ω => hcirc ω r z) (gaussianReal 0 (-Real.log r).toNNReal) P := by
  have hadm : (GFFObservable.circle r z).IsAdmissible := hr
  set X : Ω → ℝ := fun ω => hcirc ω r z with hX_def
  have hGL : HasGaussianLaw X P :=
    hG.isGaussianProcess.hasGaussianLaw_eval ⟨GFFObservable.circle r z, hadm⟩
  have hmeas : AEMeasurable X P := (hG.measurable_circle r z hr).aemeasurable
  have hmean : ∫ ω, X ω ∂P = 0 := hG.integral_eq_zero (GFFObservable.circle r z) hadm
  have hvar : variance X P = -Real.log r := by
    rw [← covariance_self hmeas]
    exact (hG.covariance_eq (GFFObservable.circle r z) (GFFObservable.circle r z) hadm hadm).trans
      (wholePlaneGFFCov_circle_self_eq hr z hdisk)
  refine ⟨hmeas, ?_⟩
  rw [hGL.map_eq_gaussianReal, hmean, hvar]

/-- The exponential tilt of a circle average: for `ε ∈ (0,1)` and `z` with the circle of radius `ε` about `z` in the
closed unit disk, `E[ψ(hC φ) ε^{γ²/2} e^{γ h_ε(z)}] = E[ψ(hC φ + γ Cov(hC φ, h_ε(z)))]`. -/
theorem tilt_circleAverage {P : Measure Ω} [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc) {k : ℕ} (φ : Fin k → ℂ → ℝ)
    (hφ : ∀ j, IsTestFunction Set.univ (φ j)) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (z : ℂ)
    (hdisk : ∀ x ∈ Metric.sphere z ε, ‖x‖ ≤ 1) (γ : ℝ) (ψ : (Fin k → ℝ) → ℝ) (hψ : Continuous ψ)
    (C : ℝ) (hψC : ∀ x, |ψ x| ≤ C) :
    ∫ ω, ψ (fun j => hC ω (φ j)) * (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω ε z)) ∂P =
      ∫ ω, ψ (fun j => hC ω (φ j) + γ * covariance (fun ω => hC ω (φ j)) (fun ω => hcirc ω ε z) P) ∂P := by
  have hlog : Real.log ε < 0 := Real.log_neg hε0 hε1
  set v : ℝ≥0 := (-Real.log ε).toNNReal with hv_def
  have hvR : (v : ℝ) = -Real.log ε := Real.coe_toNNReal _ (by linarith)
  have hv0 : v ≠ 0 := by
    intro h
    have h' : (v : ℝ) = 0 := by simp [h]
    linarith
  let t : Option (Fin k) → GFFObservable.Admissible := fun o =>
    Option.elim o ⟨GFFObservable.circle ε z, hε0⟩ (fun j => ⟨GFFObservable.pairing (φ j), hφ j⟩)
  have hG2 : HasGaussianLaw (fun ω => ((fun j : Fin k => hC ω (φ j)), hcirc ω ε z)) P :=
    hasGaussianLaw_pair_family hG.isGaussianProcess t
  have hX : ∀ j, Measurable (fun ω => hC ω (φ j)) := fun j => hG.measurable_pairing (φ j) (hφ j)
  have hYm : Measurable (fun ω => hcirc ω ε z) := hG.measurable_circle ε z hε0
  have hY : HasLaw (fun ω => hcirc ω ε z) (gaussianReal 0 v) P :=
    hasLaw_circleAverage hG hε0 z hdisk
  have key := integral_gaussian_exp_tilt (fun j ω => hC ω (φ j)) (fun ω => hcirc ω ε z) hX hYm v hv0 hY hG2
    (fun j => covariance (fun ω => hC ω (φ j)) (fun ω => hcirc ω ε z) P) (fun j => rfl) γ ψ hψ C hψC
  have hpt : ∀ ω, Real.exp (γ * hcirc ω ε z - γ ^ 2 * v / 2) =
      ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω ε z) := by
    intro ω
    rw [Real.rpow_def_of_pos hε0, ← Real.exp_add, hvR]
    congr 1
    ring
  have hLHS : ∫ ω, ψ (fun j => hC ω (φ j)) * (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω ε z)) ∂P =
      ∫ ω, ψ (fun j => hC ω (φ j)) * Real.exp (γ * hcirc ω ε z - γ ^ 2 * v / 2) ∂P := by
    congr 1
    funext ω
    rw [hpt ω]
  rw [hLHS]
  exact key

/-- Every test function is bounded. -/
theorem exists_abs_bound_of_isTestFunction {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) :
    ∃ C, ∀ x, |φ x| ≤ C := by
  obtain ⟨C, hC⟩ := hφ.1.continuous.bounded_above_of_compact_support hφ.2.1
  exact ⟨C, fun x => by simpa [Real.norm_eq_abs] using hC x⟩

/-- Covariance shift along a sequence of radii tending to `0` (from `gamma_covariance_sub_dmsShift_bound`):
`γ Cov(hC φ, h_{ε_n}(z)) → ∫ dmsShift_z φ`. -/
theorem tendsto_gamma_cov_shift {P : Measure Ω} [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc) (γ : ℝ) {φ : ℂ → ℝ}
    (hφ : IsTestFunction Set.univ φ) {C : ℝ} (hC0 : ∀ x, |φ x| ≤ C) (z : ℂ) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0)) (hε0 : ∀ n, 0 < ε n)
    (hdisk : ∀ᶠ n in atTop, ∀ x ∈ Metric.sphere z (ε n), ‖x‖ ≤ 1) :
    Tendsto (fun n => γ * covariance (fun ω => hC ω φ) (fun ω => hcirc ω (ε n) z) P) atTop
      (𝓝 (∫ x, dmsShift γ z x * φ x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun n => |γ| * C * (2 * Real.pi) * ε n ^ 2) atTop (𝓝 0) := by
    have h2 : Tendsto (fun n => ε n ^ 2) atTop (𝓝 0) := by
      simpa using hε.pow 2
    simpa using (tendsto_const_nhds (x := |γ| * C * (2 * Real.pi))).mul h2
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hlim
  filter_upwards [hdisk] with n hn
  rw [Real.norm_eq_abs]
  exact le_of_le_of_eq (gamma_covariance_sub_dmsShift_bound hG (hε0 n) z hn γ hφ hC0) (by ring)

/-- Dominated convergence in `ω` for a shifted bounded continuous functional of finitely many pairings. -/
theorem tendsto_shift_integral {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ} (X : Fin k → Ω → ℝ)
    (hX : ∀ j, Measurable (X j)) (ψ : (Fin k → ℝ) → ℝ) (hψ : Continuous ψ) (C : ℝ)
    (hψC : ∀ x, |ψ x| ≤ C) (v : ℕ → Fin k → ℝ) (w : Fin k → ℝ) (hv : Tendsto v atTop (𝓝 w)) :
    Tendsto (fun n => ∫ ω, ψ (fun j => X j ω + v n j) ∂P) atTop
      (𝓝 (∫ ω, ψ (fun j => X j ω + w j) ∂P)) := by
  refine tendsto_integral_of_dominated_convergence (fun _ => C) (fun n => ?_) (integrable_const C)
    (fun n => ae_of_all _ fun ω => ?_) (ae_of_all _ fun ω => ?_)
  · exact (hψ.measurable.comp (Measurable.of_eval fun j => (hX j).add_const (v n j))).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    exact hψC _
  · have hcont : Tendsto (fun n => fun j => X j ω + v n j) atTop (𝓝 (fun j => X j ω + w j)) :=
      tendsto_pi_nhds.2 fun j => tendsto_const_nhds.add ((tendsto_pi_nhds.1 hv) j)
    exact (hψ.tendsto _).comp hcont

/-- A bounded function times an integrable function is integrable. -/
theorem integrable_bdd_mul {P : Measure Ω} [IsProbabilityMeasure P] {F f : Ω → ℝ} (hF : Measurable F) {C : ℝ}
    (hFC : ∀ ω, |F ω| ≤ C) (hf : Integrable f P) : Integrable (fun ω => F ω * f ω) P := by
  refine (hf.abs.const_mul C).mono' (hF.aestronglyMeasurable.mul hf.aestronglyMeasurable)
    (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hFC ω) (abs_nonneg _)

/-- The difference of two bounded-weighted integrals is controlled by the `L¹` distance of the integrands. -/
theorem abs_integral_bdd_mul_sub_le {P : Measure Ω} [IsProbabilityMeasure P] {F f g : Ω → ℝ} (hF : Measurable F)
    {C : ℝ} (hFC : ∀ ω, |F ω| ≤ C) (hf : Integrable f P) (hg : Integrable g P) :
    |∫ ω, F ω * f ω ∂P - ∫ ω, F ω * g ω ∂P| ≤ C * ∫ ω, |f ω - g ω| ∂P := by
  have hfi := integrable_bdd_mul hF hFC hf
  have hgi := integrable_bdd_mul hF hFC hg
  have hdi : Integrable (fun ω => |f ω - g ω|) P := (hf.sub hg).abs
  rw [← integral_sub hfi hgi]
  calc |∫ ω, (F ω * f ω - F ω * g ω) ∂P| ≤ ∫ ω, |F ω * f ω - F ω * g ω| ∂P :=
        abs_integral_le_integral_abs
    _ ≤ ∫ ω, C * |f ω - g ω| ∂P := by
        refine integral_mono (hfi.sub hgi).abs (hdi.const_mul C) fun ω => ?_
        rw [← mul_sub, abs_mul]
        exact mul_le_mul_of_nonneg_right (hFC ω) (abs_nonneg _)
    _ = C * ∫ ω, |f ω - g ω| ∂P := integral_const_mul _ _

/-- The circle-average integral `z ↦ E[F(ω) ε^{γ²/2} e^{γ h_ε(z)}]` is measurable (Fubini on a jointly measurable
version of the circle averages). -/
theorem measurable_integral_circleAverage {P : Measure Ω} [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc) {ε : ℝ} (hε : 0 < ε) (γ : ℝ)
    {F : Ω → ℝ} (hF : Measurable F) :
    Measurable (fun z : ℂ => ∫ ω, F ω * (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω ε z)) ∂P) := by
  obtain ⟨g, hgm, _, N, _, hN0, hgN⟩ := exists_measurable_circleAverage_version hG hε
  have hae : ∀ᵐ ω ∂P, ω ∉ N := ae_iff.2 (by simpa using hN0)
  have heq : (fun z : ℂ => ∫ ω, F ω * (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω ε z)) ∂P) =
      fun z => ∫ ω, F ω * (ε ^ (γ ^ 2 / 2) * Real.exp (γ * g ω z)) ∂P := by
    funext z
    refine integral_congr_ae ?_
    filter_upwards [hae] with ω hω
    rw [hgN ω hω z]
  rw [heq]
  have hH : Measurable (fun p : ℂ × Ω => F p.2 * (ε ^ (γ ^ 2 / 2) * Real.exp (γ * g p.2 p.1))) :=
    (hF.comp measurable_snd).mul (measurable_const.mul
      (Real.continuous_exp.measurable.comp (measurable_const.mul (hgm.comp measurable_swap))))
  exact (hH.stronglyMeasurable.integral_prod_right').measurable

/-- Fubini for the marked circle masses tested against a bounded measurable `F`: the exchange of `ω` and `z`
(r10 `l:r9-marked`). The jointly measurable version `g` of the circle averages agrees with `hcirc` off a null set,
for all `z` at once. -/
theorem integral_fubini_marked {P : Measure Ω} [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc) {ε : ℝ} (hε : 0 < ε) (γ : ℝ)
    {η : ℂ → ℝ} (hη : Continuous η) (hηs : HasCompactSupport η) (hη0 : ∀ z, 0 ≤ η z)
    (hdisk : ∀ z ∈ tsupport η, ∀ x ∈ Metric.sphere z ε, ‖x‖ ≤ 1)
    {F : Ω → ℝ} (hF : Measurable F) {C : ℝ} (hC0 : 0 ≤ C) (hFC : ∀ ω, |F ω| ≤ C) :
    ∫ ω, F ω * ∫ z, η z * (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω ε z)) ∂(volume : Measure ℂ) ∂P =
      ∫ z, η z * ∫ ω, F ω * (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω ε z)) ∂P ∂(volume : Measure ℂ) := by
  have hcpos : 0 < ε ^ (γ ^ 2 / 2) := Real.rpow_pos_of_pos hε _
  obtain ⟨g, hgm, hgc, N, _, hN0, hgN⟩ := exists_measurable_circleAverage_version hG hε
  have hae : ∀ᵐ ω ∂P, ω ∉ N := ae_iff.2 (by simpa using hN0)
  have hmass := (integral_marked_mass_eps_eq hG hε γ hη hηs hdisk).1
  have hEm : Measurable (fun p : Ω × ℂ => η p.2 * (ε ^ (γ ^ 2 / 2) * Real.exp (γ * g p.1 p.2))) :=
    (hη.measurable.comp measurable_snd).mul (measurable_const.mul
      (Real.continuous_exp.measurable.comp (measurable_const.mul hgm)))
  have hGm : Measurable (fun p : Ω × ℂ => F p.1 * (η p.2 * (ε ^ (γ ^ 2 / 2) * Real.exp (γ * g p.1 p.2)))) :=
    (hF.comp measurable_fst).mul hEm
  have hBm : Measurable (fun p : Ω × ℂ => C * (η p.2 * (ε ^ (γ ^ 2 / 2) * Real.exp (γ * g p.1 p.2)))) :=
    measurable_const.mul hEm
  have hX0 : ∀ p : Ω × ℂ, 0 ≤ η p.2 * (ε ^ (γ ^ 2 / 2) * Real.exp (γ * g p.1 p.2)) := fun p =>
    mul_nonneg (hη0 _) (mul_nonneg hcpos.le (Real.exp_pos _).le)
  have hGB : ∀ p : Ω × ℂ, ‖F p.1 * (η p.2 * (ε ^ (γ ^ 2 / 2) * Real.exp (γ * g p.1 p.2)))‖ ≤
      C * (η p.2 * (ε ^ (γ ^ 2 / 2) * Real.exp (γ * g p.1 p.2))) := by
    intro p
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hX0 p)]
    exact mul_le_mul_of_nonneg_right (hFC p.1) (hX0 p)
  have hB_int : Integrable (fun p : Ω × ℂ => C * (η p.2 * (ε ^ (γ ^ 2 / 2) * Real.exp (γ * g p.1 p.2))))
      (P.prod (volume : Measure ℂ)) := by
    rw [integrable_prod_iff hBm.aestronglyMeasurable]
    refine ⟨ae_of_all _ fun ω => ?_, ?_⟩
    · have hcs : HasCompactSupport (fun z : ℂ => C * (η z * (ε ^ (γ ^ 2 / 2) * Real.exp (γ * g ω z)))) :=
        (hηs.mul_right).mul_left
      have hct : Continuous (fun z : ℂ => C * (η z * (ε ^ (γ ^ 2 / 2) * Real.exp (γ * g ω z)))) := by
        have := hgc ω
        fun_prop
      exact hct.integrable_of_hasCompactSupport hcs
    · have hmass' := hmass.const_mul C
      refine hmass'.congr ?_
      filter_upwards [hae] with ω hω
      have hnorm : ∀ z : ℂ, ‖C * (η z * (ε ^ (γ ^ 2 / 2) * Real.exp (γ * g ω z)))‖ =
          C * (η z * (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω ε z))) := by
        intro z
        rw [hgN ω hω z]
        exact Real.norm_of_nonneg (mul_nonneg hC0 (mul_nonneg (hη0 z) (mul_nonneg hcpos.le (Real.exp_pos _).le)))
      simp only [hnorm, integral_const_mul]
  have hG_int : Integrable (fun p : Ω × ℂ => F p.1 * (η p.2 * (ε ^ (γ ^ 2 / 2) * Real.exp (γ * g p.1 p.2))))
      (P.prod (volume : Measure ℂ)) :=
    hB_int.mono' hGm.aestronglyMeasurable (ae_of_all _ hGB)
  have hL : ∫ ω, F ω * ∫ z, η z * (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω ε z)) ∂(volume : Measure ℂ) ∂P =
      ∫ ω, ∫ z, F ω * (η z * (ε ^ (γ ^ 2 / 2) * Real.exp (γ * g ω z))) ∂(volume : Measure ℂ) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with ω hω
    rw [← integral_const_mul]
    congr 1
    funext z
    rw [hgN ω hω z]
  have hR : ∫ z, η z * ∫ ω, F ω * (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω ε z)) ∂P ∂(volume : Measure ℂ) =
      ∫ z, ∫ ω, F ω * (η z * (ε ^ (γ ^ 2 / 2) * Real.exp (γ * g ω z))) ∂P ∂(volume : Measure ℂ) := by
    congr 1
    funext z
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hae] with ω hω
    rw [hgN ω hω z]
    ring
  rw [hL, hR]
  exact integral_integral_swap hG_int

/-- **Palm test identity** (product-test case of Step M; r10 `l:r9-marked`). For a bounded continuous `ψ` on `ℝ^k`,
test functions `φ_j`, and a nonnegative continuous `η` supported in the open unit disk,
`E[ψ(hC φ) μ_g(η)] = ∫ η(z) E[ψ(hC φ + ∫ dmsShift_z φ)] d²z`. The constant term of `dmsShiftedPairing` is not
present: it vanishes almost surely on the unit disk (a separate step). -/
theorem palm_test_identity {P : Measure Ω} [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc) (γ : ℝ) {μ : Ω → Measure ℂ}
    (hμ : IsLQGMeasureOfField P γ 0 hcirc μ) (hU : DMSLemmaA10WholePlaneUnnormalized P γ hC hcirc μ)
    {η : ℂ → ℝ} (hη : Continuous η) (hηs : HasCompactSupport η) (hη0 : ∀ z, 0 ≤ η z)
    (htsupp : tsupport η ⊆ Metric.ball (0 : ℂ) 1) {k : ℕ} (φ : Fin k → ℂ → ℝ)
    (hφ : ∀ j, IsTestFunction Set.univ (φ j)) (ψ : (Fin k → ℝ) → ℝ) (hψ : Continuous ψ) (C : ℝ)
    (hψC : ∀ x, |ψ x| ≤ C) :
    ∫ ω, ψ (fun j => hC ω (φ j)) * (∫ z, η z ∂(μ ω)) ∂P =
      ∫ z, η z * ∫ ω, ψ (fun j => hC ω (φ j) + ∫ x, dmsShift γ z x * φ j x) ∂P ∂(volume : Measure ℂ) := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hψC 0)
  obtain ⟨M, hM1, hMsup⟩ := exists_margin_of_tsupport_subset_ball hηs htsupp
  choose Cφ hCφ using fun j => exists_abs_bound_of_isTestFunction (hφ j)
  have hXm : ∀ j, Measurable (fun ω => hC ω (φ j)) := fun j => hG.measurable_pairing (φ j) (hφ j)
  have hFm : Measurable (fun ω => ψ (fun j => hC ω (φ j))) :=
    hψ.measurable.comp (Measurable.of_eval fun j => hXm j)
  have hFC : ∀ ω, |ψ (fun j => hC ω (φ j))| ≤ C := fun ω => hψC _
  -- the eventual margin for the dyadic radii
  set δ : ℝ := min 1 (1 - M) with hδ_def
  have hδpos : 0 < δ := lt_min one_pos (by linarith)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδM : δ ≤ 1 - M := min_le_right _ _
  have hpos : ∀ n : ℕ, 0 < dyadicScale n := fun n => by unfold dyadicScale; positivity
  have hdyad : Tendsto (fun n : ℕ => dyadicScale n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hev : ∀ᶠ n : ℕ in atTop, dyadicScale n < δ :=
    hdyad.eventually (gt_mem_nhds hδpos)
  -- on the support, the circles of the dyadic radii lie in the closed unit disk
  have hdiskn : ∀ n : ℕ, dyadicScale n < δ → ∀ z ∈ tsupport η,
      ∀ x ∈ Metric.sphere z (dyadicScale n), ‖x‖ ≤ 1 := by
    intro n hn z hz x hx
    have h1 := hMsup z hz
    have h5 : ‖x‖ ≤ ‖x - z‖ + ‖z‖ := by
      have := norm_add_le (x - z) z
      rwa [sub_add_cancel] at this
    have h6 : ‖x - z‖ = dyadicScale n := by
      rw [← dist_eq_norm]
      exact mem_sphere.1 hx
    linarith
  have hlt1 : ∀ n : ℕ, dyadicScale n < δ → dyadicScale n < 1 := fun n hn => lt_of_lt_of_le hn hδ1
  -- the tilt identity at each radius on the support
  have hGF : ∀ n : ℕ, dyadicScale n < δ → ∀ z ∈ tsupport η,
      ∫ ω, ψ (fun j => hC ω (φ j)) * (dyadicScale n ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω (dyadicScale n) z)) ∂P =
        ∫ ω, ψ (fun j => hC ω (φ j) + γ * covariance (fun ω => hC ω (φ j))
          (fun ω => hcirc ω (dyadicScale n) z) P) ∂P :=
    fun n hn z hz => tilt_circleAverage hG φ hφ (hpos n) (hlt1 n hn) z (hdiskn n hn z hz) γ ψ hψ C hψC
  -- the covariance shifts converge on the support
  have hFs : ∀ z ∈ tsupport η,
      Tendsto (fun n : ℕ => ∫ ω, ψ (fun j => hC ω (φ j) + γ * covariance (fun ω => hC ω (φ j))
        (fun ω => hcirc ω (dyadicScale n) z) P) ∂P) atTop
        (𝓝 (∫ ω, ψ (fun j => hC ω (φ j) + ∫ x, dmsShift γ z x * φ j x) ∂P)) := by
    intro z hz
    have hvec : Tendsto (fun n : ℕ => fun j : Fin k =>
        γ * covariance (fun ω => hC ω (φ j)) (fun ω => hcirc ω (dyadicScale n) z) P) atTop
        (𝓝 (fun j : Fin k => ∫ x, dmsShift γ z x * φ j x)) :=
      tendsto_pi_nhds.2 fun j => tendsto_gamma_cov_shift hG γ (hφ j) (hCφ j) z (fun n => dyadicScale n)
        hdyad (fun n => hpos n) (hev.mono fun n hn => hdiskn n hn z hz)
    exact tendsto_shift_integral (fun j ω => hC ω (φ j)) (fun j => hXm j) ψ hψ C hψC _ _ hvec
  -- the bound on the averages `|E[ψ(...)]| ≤ C`
  have hnorm_le : ∀ f : Ω → ℝ, (∀ ω, ‖f ω‖ ≤ C) → ‖∫ ω, f ω ∂P‖ ≤ C := fun f hf =>
    le_of_le_of_eq (norm_integral_le_of_norm_le_const (ae_of_all _ hf)) (by simp)
  -- right-hand side: dominated convergence in `z`
  have hDCT : Tendsto (fun n : ℕ => ∫ z, η z * ∫ ω, ψ (fun j => hC ω (φ j)) *
      (dyadicScale n ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω (dyadicScale n) z)) ∂P ∂(volume : Measure ℂ))
      atTop (𝓝 (∫ z, η z * ∫ ω, ψ (fun j => hC ω (φ j) + ∫ x, dmsShift γ z x * φ j x) ∂P
        ∂(volume : Measure ℂ))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun z => C * η z) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun n =>
        (hη.measurable.mul (measurable_integral_circleAverage hG (hpos n) γ hFm)).aestronglyMeasurable
    · filter_upwards [hev] with n hn
      refine ae_of_all _ fun z => ?_
      by_cases hz : z ∈ tsupport η
      · have hbd := hnorm_le (fun ω => ψ (fun j => hC ω (φ j) + γ * covariance (fun ω => hC ω (φ j))
          (fun ω => hcirc ω (dyadicScale n) z) P)) (fun ω => by rw [Real.norm_eq_abs]; exact hψC _)
        have heq := hGF n hn z hz
        show ‖η z * ∫ ω, ψ (fun j => hC ω (φ j)) * (dyadicScale n ^ (γ ^ 2 / 2) *
          Real.exp (γ * hcirc ω (dyadicScale n) z)) ∂P‖ ≤ C * η z
        rw [heq, norm_mul, Real.norm_of_nonneg (hη0 z), mul_comm C]
        exact mul_le_mul_of_nonneg_left hbd (hη0 z)
      · have h0 : η z = 0 := image_eq_zero_of_notMem_tsupport hz
        simp [h0]
    · exact (hη.integrable_of_hasCompactSupport hηs).const_mul C
    · refine ae_of_all _ fun z => ?_
      by_cases hz : z ∈ tsupport η
      · have hEv : (fun n : ℕ => η z * ∫ ω, ψ (fun j => hC ω (φ j) + γ * covariance (fun ω => hC ω (φ j))
            (fun ω => hcirc ω (dyadicScale n) z) P) ∂P) =ᶠ[atTop]
            (fun n : ℕ => η z * ∫ ω, ψ (fun j => hC ω (φ j)) *
              (dyadicScale n ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω (dyadicScale n) z)) ∂P) :=
          hev.mono fun n hn => congrArg (fun x => η z * x) (hGF n hn z hz).symm
        exact Tendsto.congr' hEv ((hFs z hz).const_mul (η z))
      · have h0 : η z = 0 := image_eq_zero_of_notMem_tsupport hz
        simp [h0]
  -- left-hand side: the marked masses converge in L¹ (MarkedL1) and the identities hold eventually
  have hL1 := tendsto_integral_abs_marked_sub γ hG hμ hU hη hηs hη0 htsupp
  have hμinf : Integrable (fun ω => ∫ z, η z ∂(μ ω)) P :=
    integrable_lqgMeasure_test_of_nonneg γ hG hμ hη hηs hη0 htsupp
  have hMk : ∀ n : ℕ, dyadicScale n < δ →
      ∫ ω, ψ (fun j => hC ω (φ j)) * ∫ z, η z * (dyadicScale n ^ (γ ^ 2 / 2) *
        Real.exp (γ * hcirc ω (dyadicScale n) z)) ∂(volume : Measure ℂ) ∂P =
      ∫ z, η z * ∫ ω, ψ (fun j => hC ω (φ j)) * (dyadicScale n ^ (γ ^ 2 / 2) *
        Real.exp (γ * hcirc ω (dyadicScale n) z)) ∂P ∂(volume : Measure ℂ) :=
    fun n hn => integral_fubini_marked hG (hpos n) γ hη hηs hη0 (hdiskn n hn) hFm hC0 hFC
  have hdiffk : ∀ n : ℕ, dyadicScale n < δ →
      |∫ ω, ψ (fun j => hC ω (φ j)) * (∫ z, η z * (dyadicScale n ^ (γ ^ 2 / 2) *
          Real.exp (γ * hcirc ω (dyadicScale n) z)) ∂(volume : Measure ℂ)) ∂P -
        ∫ ω, ψ (fun j => hC ω (φ j)) * (∫ z, η z ∂(μ ω)) ∂P| ≤
      C * ∫ ω, |(∫ z, η z * (dyadicScale n ^ (γ ^ 2 / 2) *
          Real.exp (γ * hcirc ω (dyadicScale n) z)) ∂(volume : Measure ℂ)) - ∫ z, η z ∂(μ ω)| ∂P :=
    fun n hn => abs_integral_bdd_mul_sub_le hFm hFC
      (integral_marked_mass_eps_eq hG (hpos n) γ hη hηs (hdiskn n hn)).1 hμinf
  have hLim : Tendsto (fun n : ℕ => ∫ ω, ψ (fun j => hC ω (φ j)) * ∫ z, η z * (dyadicScale n ^ (γ ^ 2 / 2) *
      Real.exp (γ * hcirc ω (dyadicScale n) z)) ∂(volume : Measure ℂ) ∂P) atTop
      (𝓝 (∫ ω, ψ (fun j => hC ω (φ j)) * (∫ z, η z ∂(μ ω)) ∂P)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim0 : Tendsto (fun n : ℕ => C * ∫ ω, |(∫ z, η z * (dyadicScale n ^ (γ ^ 2 / 2) *
        Real.exp (γ * hcirc ω (dyadicScale n) z)) ∂(volume : Measure ℂ)) - ∫ z, η z ∂(μ ω)| ∂P)
        atTop (𝓝 0) := by
      simpa using hL1.const_mul C
    refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hlim0
    filter_upwards [hev] with n hn
    rw [Real.norm_eq_abs]
    exact hdiffk n hn
  -- identify the limits: the marked masses equal the right-hand sequence eventually
  have hDCT' : Tendsto (fun n : ℕ => ∫ ω, ψ (fun j => hC ω (φ j)) * ∫ z, η z * (dyadicScale n ^ (γ ^ 2 / 2) *
      Real.exp (γ * hcirc ω (dyadicScale n) z)) ∂(volume : Measure ℂ) ∂P) atTop
      (𝓝 (∫ z, η z * ∫ ω, ψ (fun j => hC ω (φ j) + ∫ x, dmsShift γ z x * φ j x) ∂P ∂(volume : Measure ℂ))) :=
    hDCT.congr' (hev.mono fun n hn => (hMk n hn).symm)
  exact tendsto_nhds_unique hLim hDCT'

end HarmonicBalls

end
