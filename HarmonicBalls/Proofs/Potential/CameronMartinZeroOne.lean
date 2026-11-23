import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.CameronMartin

/-! # A zero-one law for events invariant under Cameron-Martin shifts

Let `X : I → Ω → ℝ` be a centred Gaussian process. For `σ : I →₀ ℝ` the Cameron-Martin shift
along `X_σ = ∑ σ i X i` is the deterministic function `K(·, σ) = Cov(X ·, X_σ)`
(`QuantumZipper.CameronMartin.covShift`). If a measurable set `S` of paths, for the product
σ-algebra, is invariant under all these shifts, then `P(X ∈ S)` is `0` or `1` (the zero-one law
for Cameron-Martin invariant sets; Bogachev, *Gaussian measures*, AMS 1998, Section 2.5).

Proof. By the Cameron-Martin formula (`QuantumZipper.CameronMartin.map_tiltMeasure_path`) the event
`A = {X ∈ S}` satisfies `E[1_A exp(X_σ - Var(X_σ)/2)] = P(A)` for every `σ`. If `P(A) > 0`, then
under the conditional law `Q = P(· | A)` every combination `X_σ` has the moment generating
function of its law under `P`, hence the same law; by characteristic functions the
finite-dimensional marginals of `X` under `Q` and under `P` agree, hence so do its laws on the
product σ-algebra, and `1 = Q(A) = P(A)`.
-/

open MeasureTheory ProbabilityTheory Complex
open scoped ENNReal NNReal

namespace HarmonicBalls

open QuantumZipper.CameronMartin

variable {Ω I : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : I → Ω → ℝ}

theorem covShift_neg (σ : I →₀ ℝ) (j : I) : covShift X P (-σ) j = -covShift X P σ j := by
  simp [covShift, Finsupp.support_neg, Finset.sum_neg_distrib]

theorem covShift_smul (t : ℝ) (σ : I →₀ ℝ) (j : I) :
    covShift X P (t • σ) j = t * covShift X P σ j := by
  classical
  by_cases ht : t = 0
  · subst ht
    simp [covShift]
  · simp only [covShift, Finsupp.support_smul_eq ht, Finsupp.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- For a shift-invariant measurable set `S`, the tilted measures give the event `{X ∈ S}` the
same mass as `P`. -/
theorem tiltMeasure_preimage_eq_of_shift_invariant (hX : IsGaussianProcess X P)
    (hmeas : ∀ i, Measurable (X i)) (hcent : ∀ i, P[X i] = 0) {S : Set (I → ℝ)}
    (hS : MeasurableSet S)
    (hinv : ∀ (σ : I →₀ ℝ) (g : I → ℝ), g ∈ S → g + covShift X P σ ∈ S) (σ : I →₀ ℝ) :
    tiltMeasure X P σ ((fun ω j => X j ω) ⁻¹' S) = P ((fun ω j => X j ω) ⁻¹' S) := by
  have hp : Measurable fun ω j ↦ X j ω := measurable_pi_iff.mpr hmeas
  have hp' : Measurable fun ω j ↦ X j ω + covShift X P σ j :=
    measurable_pi_iff.mpr fun j ↦ (hmeas j).add_const _
  have h := congrArg (fun μ : Measure (I → ℝ) => μ S) (map_tiltMeasure_path hX hmeas hcent σ)
  rw [Measure.map_apply hp hS, Measure.map_apply hp' hS] at h
  rw [h]
  congr 1
  ext ω
  simp only [Set.mem_preimage]
  constructor
  · intro hω
    have h2 := hinv (-σ) _ hω
    convert h2 using 1
    funext j
    simp [covShift_neg]
  · intro hω
    exact hinv σ _ hω

/-- The tilted mass of `{X ∈ S}` as an integral of the density over the event. -/
theorem tiltMeasure_apply_eq_lintegral (σ : I →₀ ℝ)
    {A : Set Ω} (hA : MeasurableSet A) :
    tiltMeasure X P σ A = ∫⁻ ω in A, ENNReal.ofReal (tiltDensity X P σ ω) ∂P := by
  rw [tiltMeasure, withDensity_apply _ hA]
  rfl

section ZeroOne

variable (hX : IsGaussianProcess X P) (hmeas : ∀ i, Measurable (X i)) (hcent : ∀ i, P[X i] = 0)
include hX hmeas hcent

/-- The conditional law given a shift-invariant event of positive probability: every finite
linear combination of the coordinates has the same law under `P(· | A)` as under `P`. -/
theorem map_cond_finsetComb_eq {S : Set (I → ℝ)} (hS : MeasurableSet S)
    (hinv : ∀ (σ : I →₀ ℝ) (g : I → ℝ), g ∈ S → g + covShift X P σ ∈ S)
    (hpos : P ((fun ω j => X j ω) ⁻¹' S) ≠ 0) (J : Finset I) (c : I → ℝ) :
    (P[|(fun ω j => X j ω) ⁻¹' S]).map (fun ω ↦ ∑ j ∈ J, c j * X j ω) =
      P.map (fun ω ↦ ∑ j ∈ J, c j * X j ω) := by
  classical
  haveI := hX.isProbabilityMeasure
  set A := (fun ω j => X j ω) ⁻¹' S with hAdef
  have hp : Measurable fun ω j ↦ X j ω := measurable_pi_iff.mpr hmeas
  have hA : MeasurableSet A := hp hS
  haveI : IsProbabilityMeasure (P[|A]) := cond_isProbabilityMeasure hpos
  set Y : Ω → ℝ := fun ω ↦ ∑ j ∈ J, c j * X j ω with hYdef
  have hYm : Measurable Y := by rw [hYdef]; fun_prop
  have hYG : HasGaussianLaw Y P := hasGaussianLaw_finsetComb hX J c
  have hY0 : P[Y] = 0 := integral_finsetComb hX hcent J c
  set w : ℝ≥0 := Var[Y; P].toNNReal with hwdef
  have hwv : (w : ℝ) = Var[Y; P] := Real.coe_toNNReal _ (variance_nonneg _ _)
  have hR : P.map Y = gaussianReal 0 w := by
    rw [hYG.map_eq_gaussianReal, hY0]
  rw [hR]
  set σ₀ : I →₀ ℝ := ∑ j ∈ J, Finsupp.single j (c j) with hσ₀
  have hσ₀app : ∀ i, σ₀ i = if i ∈ J then c i else 0 := by
    intro i
    rw [hσ₀, Finsupp.finset_sum_apply]
    simp only [Finsupp.single_apply]
    rw [Finset.sum_ite_eq']
  have hσ₀supp : σ₀.support ⊆ J := by
    intro i hi
    by_contra hiJ
    exact (Finsupp.mem_support_iff.mp hi) (by rw [hσ₀app, if_neg hiJ])
  have hmgf : mgf id (gaussianReal 0 w) = mgf id ((P[|A]).map Y) := by
    funext t
    rw [mgf_id_map hYm.aemeasurable]
    have h1 : mgf id (gaussianReal 0 w) t = Real.exp (0 * t + w * t ^ 2 / 2) :=
      congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := w)) t
    rw [h1]
    -- the tilt along `t σ₀`
    have hsupp : (t • σ₀).support ⊆ J := (Finsupp.support_smul).trans hσ₀supp
    have hcomb : ∀ ω, comb X (t • σ₀) ω = t * Y ω := by
      intro ω
      rw [comb_eq_sum_subset hX (t • σ₀) hsupp, hYdef, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finsupp.smul_apply, smul_eq_mul, hσ₀app, if_pos hj]
      ring
    have hnorm : covNorm X P (t • σ₀) = t ^ 2 * Var[Y; P] := by
      rw [← variance_comb hX (t • σ₀)]
      have : comb X (t • σ₀) = fun ω => t * Y ω := funext hcomb
      rw [this, variance_const_mul]
    have htilt := tiltMeasure_preimage_eq_of_shift_invariant hX hmeas hcent hS hinv (t • σ₀)
    rw [tiltMeasure_apply_eq_lintegral _ hA] at htilt
    -- integrability of `exp (t Y)`
    have hint : Integrable (fun ω => Real.exp (t * Y ω)) P := by
      have hG : HasGaussianLaw (fun ω => t * Y ω) P := by
        have := hasGaussianLaw_finsetComb hX J (fun j => t * c j)
        convert this using 1
        funext ω
        rw [hYdef, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      exact (gauss_exp hX hcent hG (by
        rw [integral_const_mul, hY0, mul_zero])).1
    have hdens : ∀ ω, tiltDensity X P (t • σ₀) ω =
        Real.exp (t * Y ω) * Real.exp (-(t ^ 2 * Var[Y; P]) / 2) := by
      intro ω
      rw [tiltDensity, hcomb, hnorm, ← Real.exp_add]
      congr 1
      ring
    simp_rw [hdens] at htilt
    have hint' : Integrable (fun ω => Real.exp (t * Y ω) * Real.exp (-(t ^ 2 * Var[Y; P]) / 2))
        (P.restrict A) := (hint.mul_const _).restrict
    rw [← ofReal_integral_eq_lintegral_ofReal hint'
      (Filter.Eventually.of_forall fun ω => by positivity)] at htilt
    rw [integral_mul_const] at htilt
    have hPA : P A ≠ ⊤ := measure_ne_top P A
    have hPApos : 0 < (P A).toReal := ENNReal.toReal_pos hpos hPA
    have key : ∫ ω in A, Real.exp (t * Y ω) ∂P =
        (P A).toReal * Real.exp (t ^ 2 * Var[Y; P] / 2) := by
      have h2 := congrArg ENNReal.toReal htilt
      rw [ENNReal.toReal_ofReal (by
        exact mul_nonneg (integral_nonneg fun ω => (Real.exp_pos _).le) (Real.exp_pos _).le)]
        at h2
      have he : Real.exp (-(t ^ 2 * Var[Y; P]) / 2) * Real.exp (t ^ 2 * Var[Y; P] / 2) = 1 := by
        rw [← Real.exp_add]
        simp only [neg_div, neg_add_cancel, Real.exp_zero]
      calc ∫ ω in A, Real.exp (t * Y ω) ∂P
          = (∫ ω in A, Real.exp (t * Y ω) ∂P) * Real.exp (-(t ^ 2 * Var[Y; P]) / 2) *
              Real.exp (t ^ 2 * Var[Y; P] / 2) := by rw [mul_assoc, he, mul_one]
        _ = (P A).toReal * Real.exp (t ^ 2 * Var[Y; P] / 2) := by rw [h2]
    rw [mgf, ProbabilityTheory.cond, integral_smul_measure, key, ENNReal.toReal_inv,
      smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hPApos.ne', one_mul, hwv]
    simp only [id, zero_mul, zero_add]
    congr 1
    ring
  have hc := eqOn_complexMGF_of_mgf hmgf
  refine (Measure.ext_of_complexMGF_id_eq (funext fun z ↦ hc ?_)).symm
  simp [integrableExpSet_id_gaussianReal]

/-- The finite-dimensional marginals of `X` under `P(· | A)` are those under `P`. -/
theorem map_cond_restrict_eq {S : Set (I → ℝ)} (hS : MeasurableSet S)
    (hinv : ∀ (σ : I →₀ ℝ) (g : I → ℝ), g ∈ S → g + covShift X P σ ∈ S)
    (hpos : P ((fun ω j => X j ω) ⁻¹' S) ≠ 0) (J : Finset I) :
    (P[|(fun ω j => X j ω) ⁻¹' S]).map (fun ω ↦ J.restrict (fun j ↦ X j ω)) =
      P.map (fun ω ↦ J.restrict (fun j ↦ X j ω)) := by
  classical
  haveI := hX.isProbabilityMeasure
  set A := (fun ω j => X j ω) ⁻¹' S with hAdef
  haveI : IsProbabilityMeasure (P[|A]) := cond_isProbabilityMeasure hpos
  have hV : Measurable fun ω ↦ J.restrict (fun j ↦ X j ω) :=
    measurable_pi_iff.mpr fun j ↦ hmeas j
  haveI : IsProbabilityMeasure ((P[|A]).map fun ω ↦ J.restrict (fun j ↦ X j ω)) :=
    (Measure.isProbabilityMeasure_map_iff hV.aemeasurable).mpr inferInstance
  haveI : IsProbabilityMeasure (P.map fun ω ↦ J.restrict (fun j ↦ X j ω)) :=
    (Measure.isProbabilityMeasure_map_iff hV.aemeasurable).mpr inferInstance
  refine Measure.ext_of_charFunDual (funext fun L ↦ ?_)
  set c : I → ℝ := fun j ↦
    if h : j ∈ J then L (fun k ↦ if (⟨j, h⟩ : J) = k then 1 else 0) else 0 with hc
  have key := map_cond_finsetComb_eq hX hmeas hcent hS hinv hpos J c
  have hcont : Continuous fun y : ℝ ↦ cexp (y * Complex.I) := by fun_prop
  rw [charFunDual_apply, charFunDual_apply, integral_map hV.aemeasurable (by fun_prop),
    integral_map hV.aemeasurable (by fun_prop)]
  have h1 : ∀ ω, L (J.restrict (fun j ↦ X j ω)) = ∑ j ∈ J, c j * X j ω := fun ω ↦
    strongDual_restrict_eq_sum hX J J (subset_refl J) L _
  simp_rw [h1]
  have hYm : Measurable fun ω ↦ ∑ j ∈ J, c j * X j ω := by fun_prop
  rw [← integral_map (f := fun y : ℝ ↦ cexp (y * Complex.I)) hYm.aemeasurable
      hcont.aestronglyMeasurable, key,
    integral_map hYm.aemeasurable hcont.aestronglyMeasurable]

/-- The law of `X` on the product σ-algebra under `P(· | A)` is its law under `P`. -/
theorem map_cond_eq {S : Set (I → ℝ)} (hS : MeasurableSet S)
    (hinv : ∀ (σ : I →₀ ℝ) (g : I → ℝ), g ∈ S → g + covShift X P σ ∈ S)
    (hpos : P ((fun ω j => X j ω) ⁻¹' S) ≠ 0) :
    (P[|(fun ω j => X j ω) ⁻¹' S]).map (fun ω j ↦ X j ω) = P.map (fun ω j ↦ X j ω) := by
  haveI := hX.isProbabilityMeasure
  set A := (fun ω j => X j ω) ⁻¹' S with hAdef
  haveI : IsProbabilityMeasure (P[|A]) := cond_isProbabilityMeasure hpos
  have hp : Measurable fun ω j ↦ X j ω := measurable_pi_iff.mpr hmeas
  haveI : IsProbabilityMeasure ((P[|A]).map fun ω j ↦ X j ω) :=
    (Measure.isProbabilityMeasure_map_iff hp.aemeasurable).mpr inferInstance
  haveI : IsProbabilityMeasure (P.map fun ω j ↦ X j ω) :=
    (Measure.isProbabilityMeasure_map_iff hp.aemeasurable).mpr inferInstance
  refine ext_of_generate_finite (measurableCylinders fun _ : I ↦ ℝ)
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders (fun s hs ↦ ?_)
    (by simp [measure_univ])
  obtain ⟨J, T, hT, rfl⟩ := (mem_measurableCylinders _).mp hs
  rw [Measure.map_apply hp hT.cylinder, Measure.map_apply hp hT.cylinder]
  have := congrArg (fun μ : Measure (J → ℝ) ↦ μ T)
    (map_cond_restrict_eq hX hmeas hcent hS hinv hpos J)
  have hV : Measurable fun ω ↦ J.restrict (fun j ↦ X j ω) :=
    measurable_pi_iff.mpr fun j ↦ hmeas j
  beta_reduce at this
  rwa [Measure.map_apply hV hT, Measure.map_apply hV hT] at this

/-- **Zero-one law for Cameron-Martin invariant events.** If a measurable set `S` of paths is
invariant under the Cameron-Martin shifts `K(·, σ)` of a centred Gaussian process `X`, then
`P(X ∈ S)` is `0` or `1`. -/
theorem measure_preimage_eq_zero_or_one_of_shift_invariant {S : Set (I → ℝ)}
    (hS : MeasurableSet S)
    (hinv : ∀ (σ : I →₀ ℝ) (g : I → ℝ), g ∈ S → g + covShift X P σ ∈ S) :
    P ((fun ω j => X j ω) ⁻¹' S) = 0 ∨ P ((fun ω j => X j ω) ⁻¹' S) = 1 := by
  haveI := hX.isProbabilityMeasure
  by_cases hpos : P ((fun ω j => X j ω) ⁻¹' S) = 0
  · exact Or.inl hpos
  right
  have hp : Measurable fun ω j ↦ X j ω := measurable_pi_iff.mpr hmeas
  have hA : MeasurableSet ((fun ω j => X j ω) ⁻¹' S) := hp hS
  have h := congrArg (fun μ : Measure (I → ℝ) => μ S) (map_cond_eq hX hmeas hcent hS hinv hpos)
  rw [Measure.map_apply hp hS, Measure.map_apply hp hS, cond_apply hA, Set.inter_self,
    ENNReal.inv_mul_cancel hpos (measure_ne_top _ _)] at h
  exact h.symm

end ZeroOne

end HarmonicBalls
