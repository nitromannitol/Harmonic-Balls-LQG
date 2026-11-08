import HarmonicBalls.Proofs.GFF.DilationPairingCovarianceDecay
import LatticeProb.Prob.Scaling.CramerWold

/-! # Finite-dimensional Gaussian covariance limits

The Cramér–Wold bridge used here is from Leonardo Bonanno's
Lattice-Probability development. This file concerns finite cylinders only.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ProbabilityTheory

noncomputable section
namespace HarmonicBalls

/-- A finite linear combination of a Gaussian process is Gaussian. -/
private theorem gaussian_finset_comb {Ω I : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : I → Ω → ℝ} (hX : IsGaussianProcess X P)
    (T : Finset I) (a : I → ℝ) :
    HasGaussianLaw (fun ω => ∑ i ∈ T, a i * X i ω) P := by
  have h := (hX.hasGaussianLaw T).map_fun
    (∑ i : T, a i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : T => ℝ) i)
  have heq : (fun ω => ∑ i ∈ T, a i * X i ω) =
      fun ω => (∑ i : T, a i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : T => ℝ) i)
        (T.restrict (X · ω)) := by
    funext ω
    rw [sum_apply]
    simp only [smul_apply, ContinuousLinearMap.proj_apply, Finset.restrict, smul_eq_mul]
    exact (Finset.sum_coe_sort T (fun i => a i * X i ω)).symm
  rw [heq]
  exact h

/-- A finite Gaussian process, viewed as a single vector, has Gaussian law. -/
private theorem gaussian_vector {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    {P : Measure Ω} {X : I → Ω → ℝ} (h : IsGaussianProcess X P) :
    HasGaussianLaw (fun ω i => X i ω) P := by
  classical
  let L : (↥(Finset.univ : Finset I) → ℝ) →L[ℝ] (I → ℝ) :=
    { toFun := fun x i => x ⟨i, Finset.mem_univ i⟩
      map_add' := by intros; ext; rfl
      map_smul' := by intros; ext; rfl }
  simpa [L, Finset.restrict] using (h.hasGaussianLaw Finset.univ).map_fun L

/-- Independent finite Gaussian vectors, embedded in a product space, form a
jointly Gaussian finite vector. -/
private theorem gaussian_independent_blocks
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {P : Measure Ω₁} {Q : Measure Ω₂} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {m k : ℕ} {A : Fin m → Ω₁ → ℝ} {B : Fin k → Ω₂ → ℝ}
    (hA : IsGaussianProcess A P) (hB : IsGaussianProcess B Q)
    (hAm : ∀ i, Measurable (A i)) (hBm : ∀ i, Measurable (B i)) :
    IsGaussianProcess (fun (i : Fin (m+k)) (ω : Ω₁ × Ω₂) => Fin.addCases (motive := fun _ : Fin (m+k) => ℝ)
      (fun j => A j ω.1) (fun j => B j ω.2) i) (P.prod Q) := by
  let U : Ω₁ → Fin m → ℝ := fun ω i => A i ω
  let V : Ω₂ → Fin k → ℝ := fun ω i => B i ω
  have hu : Measurable U := Measurable.of_eval hAm
  have hv : Measurable V := Measurable.of_eval hBm
  have hUp : HasGaussianLaw (fun ω : Ω₁ × Ω₂ => U ω.1) (P.prod Q) := by
    refine ⟨(hu.comp measurable_fst).aemeasurable, ?_⟩
    have hg := (gaussian_vector hA).isGaussian_map
    change IsGaussian ((P.prod Q).map (U ∘ Prod.fst))
    rw [← Measure.map_map hu measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]
    exact hg
  have hVp : HasGaussianLaw (fun ω : Ω₁ × Ω₂ => V ω.2) (P.prod Q) := by
    refine ⟨(hv.comp measurable_snd).aemeasurable, ?_⟩
    have hg := (gaussian_vector hB).isGaussian_map
    change IsGaussian ((P.prod Q).map (V ∘ Prod.snd))
    rw [← Measure.map_map hv measurable_snd, Measure.map_snd_prod, measure_univ, one_smul]
    exact hg
  have hp := IndepFun.hasGaussianLaw hUp hVp (indepFun_prod hu hv)
  let L : ((Fin m → ℝ) × (Fin k → ℝ)) →L[ℝ] (Fin (m+k) → ℝ) :=
    { toFun := fun x => Fin.addCases x.1 x.2
      map_add' := by intros; ext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
      map_smul' := by intros; ext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
      cont := by
        apply continuous_pi
        intro i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simpa only [Function.comp_def, Fin.addCases_left, Fin.addCases_right] using (continuous_apply j).comp (continuous_fst : Continuous (Prod.fst :
            ((Fin m → ℝ) × (Fin k → ℝ)) → (Fin m → ℝ)))
        · simpa only [Function.comp_def, Fin.addCases_left, Fin.addCases_right] using (continuous_apply j).comp (continuous_snd : Continuous (Prod.snd :
            ((Fin m → ℝ) × (Fin k → ℝ)) → (Fin k → ℝ))) }
  have hg := hp.map_fun L
  constructor
  intro I
  let R : (Fin (m+k) → ℝ) →L[ℝ] (I → ℝ) :=
    { toFun := fun x i => x i.1
      map_add' := by intros; ext; rfl
      map_smul' := by intros; ext; rfl }
  have heq : (fun ω : Ω₁ × Ω₂ => I.restrict (fun i =>
      Fin.addCases (motive := fun _ : Fin (m+k) => ℝ)
        (fun j => A j ω.1) (fun j => B j ω.2) i)) =
      R ∘ (fun ω => L (U ω.1, V ω.2)) := by
    funext ω i
    rfl
  rw [heq]
  exact hg.map R

/-- Centered finite Gaussian vectors converge in distribution when each entry of
    their covariance matrix converges to the corresponding entry of the limit. -/
theorem tendstoInDistribution_gaussian_of_covariance
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {m : ℕ} {X : ℕ → Fin m → Ω → ℝ} {Y : Fin m → Ω' → ℝ}
    (hX : ∀ n, IsGaussianProcess (X n) P) (hY : IsGaussianProcess Y Q)
    (hXm : ∀ n i, Measurable (X n i)) (hYm : ∀ i, Measurable (Y i))
    (hX0 : ∀ n i, ∫ ω, X n i ω ∂P = 0) (hY0 : ∀ i, ∫ ω, Y i ω ∂Q = 0)
    (hcov : ∀ i j, Tendsto (fun n => cov[X n i, X n j; P]) atTop
      (𝓝 (cov[Y i, Y j; Q]))) :
    TendstoInDistribution (fun n ω i => X n i ω) atTop (fun ω i => Y i ω)
      (fun _ => P) Q := by
  apply LatticeProb.Scaling.CramerWold.tendstoInDistribution_of_tendsto_charFun_linearCombination
  · intro n
    exact Measurable.of_eval (hXm n)
  · exact Measurable.of_eval hYm
  · intro t
    let S : ℕ → Ω → ℝ := fun n ω => ∑ i, t i * X n i ω
    let T : Ω' → ℝ := fun ω => ∑ i, t i * Y i ω
    have hg (n : ℕ) : HasGaussianLaw (S n) P :=
      gaussian_finset_comb (hX n) Finset.univ t
    have hk : HasGaussianLaw T Q :=
      gaussian_finset_comb hY Finset.univ t
    have hm (n : ℕ) : ∫ ω, S n ω ∂P = 0 :=
      by
        dsimp [S]
        rw [integral_finsetSum _ (fun i _ => ((hX n).hasGaussianLaw_eval i).integrable.const_mul _)]
        simp [integral_const_mul, hX0]
    have hm' : ∫ ω, T ω ∂Q = 0 :=
      by
        dsimp [T]
        rw [integral_finsetSum _ (fun i _ => (hY.hasGaussianLaw_eval i).integrable.const_mul _)]
        simp [integral_const_mul, hY0]
    have hv : Tendsto (fun n => Var[S n; P]) atTop (𝓝 (Var[T; Q])) := by
      have he (n : ℕ) : Var[S n; P] =
          ∑ i, t i * ∑ j, t j * cov[X n i, X n j; P] := by
        dsimp [S]
        rw [variance_fun_sum (fun i => ((hX n).hasGaussianLaw_eval i).memLp_two.const_mul _)]
        simp only [covariance_const_mul_left, covariance_const_mul_right]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      have he' : Var[T; Q] = ∑ i, t i * ∑ j, t j * cov[Y i, Y j; Q] := by
        dsimp [T]
        rw [variance_fun_sum (fun i => (hY.hasGaussianLaw_eval i).memLp_two.const_mul _)]
        simp only [covariance_const_mul_left, covariance_const_mul_right]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      simp_rw [he, he']
      exact tendsto_finsetSum _ (fun i _ => tendsto_const_nhds.mul
        (tendsto_finsetSum _ (fun j _ => tendsto_const_nhds.mul (hcov i j))))
    have hc : Tendsto (fun n : ℕ => Complex.exp (-(Var[S n; P] : ℂ) / 2)) atTop
        (𝓝 (Complex.exp (-(Var[T; Q] : ℂ) / 2))) :=
      Complex.continuous_exp.continuousAt.tendsto.comp
        (((Complex.continuous_ofReal.tendsto _).comp hv).neg.div_const 2)
    have hc1 (n : ℕ) : charFun (P.map (S n)) 1 =
        Complex.exp (-(Var[S n; P] : ℂ) / 2) := by
      rw [(hg n).charFun_map_eq]
      simp [hm, neg_div]
    have hc2 : charFun (Q.map T) 1 = Complex.exp (-(Var[T; Q] : ℂ) / 2) := by
      rw [hk.charFun_map_eq]
      simp [hm', neg_div]
    change Tendsto (fun n => charFun (P.map (S n)) 1) atTop (𝓝 (charFun (Q.map T) 1))
    simpa only [hc1, hc2] using hc

/-- Fixed marginal covariances and vanishing cross covariances imply that
centered jointly Gaussian blocks converge in law to independent copies of
their marginal vectors. The limiting copies live on the product space. -/
theorem tendstoInDistribution_gaussian_independent_blocks
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {m k : ℕ} {X : ℕ → Fin (m+k) → Ω → ℝ}
    (hX : ∀ n, IsGaussianProcess (X n) P)
    (hXm : ∀ n i, Measurable (X n i))
    (hX0 : ∀ n i, ∫ ω, X n i ω ∂P = 0)
    (hAA : ∀ n i j, cov[X n (Fin.castAdd k i), X n (Fin.castAdd k j); P] =
      cov[X 0 (Fin.castAdd k i), X 0 (Fin.castAdd k j); P])
    (hBB : ∀ n i j, cov[X n (Fin.natAdd m i), X n (Fin.natAdd m j); P] =
      cov[X 0 (Fin.natAdd m i), X 0 (Fin.natAdd m j); P])
    (hAB : ∀ i j, Tendsto (fun n =>
      cov[X n (Fin.castAdd k i), X n (Fin.natAdd m j); P]) atTop (𝓝 0)) :
    TendstoInDistribution
      (fun n ω => (fun i => X n (Fin.castAdd k i) ω,
        fun j => X n (Fin.natAdd m j) ω)) atTop
      (fun ω : Ω × Ω => (fun i => X 0 (Fin.castAdd k i) ω.1,
        fun j => X 0 (Fin.natAdd m j) ω.2)) (fun _ => P) (P.prod P) := by
  let A : Fin m → Ω → ℝ := fun i => X 0 (Fin.castAdd k i)
  let B : Fin k → Ω → ℝ := fun i => X 0 (Fin.natAdd m i)
  let Y : Fin (m+k) → Ω × Ω → ℝ := fun i ω =>
    Fin.addCases (motive := fun _ : Fin (m+k) => ℝ)
      (fun j => A j ω.1) (fun j => B j ω.2) i
  have hgA : IsGaussianProcess A P := (hX 0).comp_right (Fin.castAdd k)
  have hgB : IsGaussianProcess B P := (hX 0).comp_right (Fin.natAdd m)
  have hmA : ∀ i, Measurable (A i) := fun i => hXm 0 _
  have hmB : ∀ i, Measurable (B i) := fun i => hXm 0 _
  have hY : IsGaussianProcess Y (P.prod P) := gaussian_independent_blocks hgA hgB hmA hmB
  have hYm : ∀ i, Measurable (Y i) := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa [Y, Function.comp_def] using (hmA j).comp measurable_fst
    · simpa [Y, Function.comp_def] using (hmB j).comp measurable_snd
  have hY0 : ∀ i, ∫ ω, Y i ω ∂(P.prod P) = 0 := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Y, Fin.addCases_left]
      rw [← integral_map measurable_fst.aemeasurable (hmA j).aestronglyMeasurable,
        Measure.map_fst_prod, measure_univ, one_smul]
      exact hX0 0 _
    · simp only [Y, Fin.addCases_right]
      rw [← integral_map measurable_snd.aemeasurable (hmB j).aestronglyMeasurable,
        Measure.map_snd_prod, measure_univ, one_smul]
      exact hX0 0 _
  have hcov : ∀ i j, Tendsto (fun n => cov[X n i, X n j; P]) atTop
      (𝓝 (cov[Y i, Y j; P.prod P])) := by
    intro i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · have hc := covariance_map_fun (μ := P.prod P) (Z := Prod.fst)
        (hmA i).aestronglyMeasurable (hmA j).aestronglyMeasurable measurable_fst.aemeasurable
      simp only [Measure.map_fst_prod, measure_univ, one_smul] at hc
      simp only [Y, Fin.addCases_left, ← hc]
      exact tendsto_const_nhds.congr (fun n => (hAA n i j).symm)
    · have hc := covariance_fst_snd_prod (hgA.hasGaussianLaw_eval i).memLp_two
        (hgB.hasGaussianLaw_eval j).memLp_two
      simp only [Y, Fin.addCases_left, Fin.addCases_right, hc]
      exact hAB i j
    · have hc := covariance_fst_snd_prod (hgA.hasGaussianLaw_eval j).memLp_two
        (hgB.hasGaussianLaw_eval i).memLp_two
      simp only [Y, Fin.addCases_left, Fin.addCases_right, covariance_comm, hc]
      simpa only [covariance_comm] using hAB j i
    · have hc := covariance_map_fun (μ := P.prod P) (Z := Prod.snd)
        (hmB i).aestronglyMeasurable (hmB j).aestronglyMeasurable measurable_snd.aemeasurable
      simp only [Measure.map_snd_prod, measure_univ, one_smul] at hc
      simp only [Y, Fin.addCases_right, ← hc]
      exact tendsto_const_nhds.congr (fun n => (hBB n i j).symm)
  have ht := tendstoInDistribution_gaussian_of_covariance hX hY hXm hYm hX0 hY0 hcov
  let split : (Fin (m+k) → ℝ) → (Fin m → ℝ) × (Fin k → ℝ) :=
    fun v => (fun i => v (Fin.castAdd k i), fun j => v (Fin.natAdd m j))
  have hs : Continuous split := by
    apply Continuous.prodMk <;> apply continuous_pi <;> intro i <;> exact continuous_apply _
  have ht' := ht.continuous_comp hs
  simpa [split, Y, A, B, Function.comp_def] using ht'

#print axioms tendstoInDistribution_gaussian_independent_blocks

/-- Finite-dimensional weak convergence implies convergence of every bounded
continuous cylinder expectation. -/
theorem tendsto_integral_gaussian_of_covariance
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {m : ℕ} {X : ℕ → Fin m → Ω → ℝ} {Y : Fin m → Ω' → ℝ}
    (hX : ∀ n, IsGaussianProcess (X n) P) (hY : IsGaussianProcess Y Q)
    (hXm : ∀ n i, Measurable (X n i)) (hYm : ∀ i, Measurable (Y i))
    (hX0 : ∀ n i, ∫ ω, X n i ω ∂P = 0) (hY0 : ∀ i, ∫ ω, Y i ω ∂Q = 0)
    (hcov : ∀ i j, Tendsto (fun n => cov[X n i, X n j; P]) atTop
      (𝓝 (cov[Y i, Y j; Q]))) (F : BoundedContinuousFunction (Fin m → ℝ) ℝ) :
    Tendsto (fun n => ∫ ω, F (fun i => X n i ω) ∂P) atTop
      (𝓝 (∫ ω, F (fun i => Y i ω) ∂Q)) := by
  have h := tendstoInDistribution_gaussian_of_covariance hX hY hXm hYm hX0 hY0 hcov
  have hc := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp h.tendsto) F
  simp only [ProbabilityMeasure.coe_mk] at hc
  simpa only [integral_map (Measurable.of_eval (hXm _) |>.aemeasurable)
      F.continuous.aestronglyMeasurable,
    integral_map (Measurable.of_eval hYm |>.aemeasurable) F.continuous.aestronglyMeasurable] using hc

/-- Weak convergence of a pair to random vectors on a product probability
space gives factorization against bounded continuous cylinder functions. -/
theorem tendsto_cylinder_product_of_tendstoInDistribution
    {Ω Ω₁ Ω₂ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {P : Measure Ω} {Q₁ : Measure Ω₁} {Q₂ : Measure Ω₂}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q₁] [IsProbabilityMeasure Q₂]
    {m k : ℕ} {A : ℕ → Ω → Fin m → ℝ} {B : ℕ → Ω → Fin k → ℝ}
    {U : Ω₁ → Fin m → ℝ} {V : Ω₂ → Fin k → ℝ}
    (h : TendstoInDistribution (fun n ω => (A n ω, B n ω)) atTop
      (fun ω : Ω₁ × Ω₂ => (U ω.1, V ω.2)) (fun _ => P) (Q₁.prod Q₂))
    (f : BoundedContinuousFunction (Fin m → ℝ) ℝ)
    (g : BoundedContinuousFunction (Fin k → ℝ) ℝ) :
    Tendsto (fun n => ∫ ω, f (A n ω) * g (B n ω) ∂P) atTop
      (𝓝 ((∫ ω, f (U ω) ∂Q₁) * (∫ ω, g (V ω) ∂Q₂))) := by
  let F : BoundedContinuousFunction ((Fin m → ℝ) × (Fin k → ℝ)) ℝ :=
    f.compContinuous ⟨Prod.fst, continuous_fst⟩ *
      g.compContinuous ⟨Prod.snd, continuous_snd⟩
  have hc := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp h.tendsto) F
  simp only [ProbabilityMeasure.coe_mk] at hc
  have he₁ (n : ℕ) : (∫ x, F x ∂(P.map (fun ω => (A n ω, B n ω)))) =
      ∫ ω, f (A n ω) * g (B n ω) ∂P := by
    rw [integral_map (h.forall_aemeasurable n) F.continuous.aestronglyMeasurable]
    rfl
  have he₂ : (∫ x, F x ∂((Q₁.prod Q₂).map (fun ω => (U ω.1, V ω.2)))) =
      (∫ ω, f (U ω) ∂Q₁) * (∫ ω, g (V ω) ∂Q₂) := by
    rw [integral_map h.aemeasurable_limit F.continuous.aestronglyMeasurable]
    change (∫ ω : Ω₁ × Ω₂, f (U ω.1) * g (V ω.2) ∂(Q₁.prod Q₂)) = _
    exact integral_prod_mul (fun ω => f (U ω)) (fun ω => g (V ω))
  simpa only [he₁, he₂] using hc

#print axioms tendsto_cylinder_product_of_tendstoInDistribution
/-- Bounded continuous functions of centered Gaussian blocks factor in the
limit when the marginal covariance matrices are fixed and the cross block
converges to zero. -/
theorem tendsto_integral_gaussian_independent_blocks
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {m k : ℕ} {X : ℕ → Fin (m+k) → Ω → ℝ}
    (hX : ∀ n, IsGaussianProcess (X n) P)
    (hXm : ∀ n i, Measurable (X n i))
    (hX0 : ∀ n i, ∫ ω, X n i ω ∂P = 0)
    (hAA : ∀ n i j, cov[X n (Fin.castAdd k i), X n (Fin.castAdd k j); P] =
      cov[X 0 (Fin.castAdd k i), X 0 (Fin.castAdd k j); P])
    (hBB : ∀ n i j, cov[X n (Fin.natAdd m i), X n (Fin.natAdd m j); P] =
      cov[X 0 (Fin.natAdd m i), X 0 (Fin.natAdd m j); P])
    (hAB : ∀ i j, Tendsto (fun n =>
      cov[X n (Fin.castAdd k i), X n (Fin.natAdd m j); P]) atTop (𝓝 0))
    (f : BoundedContinuousFunction (Fin m → ℝ) ℝ)
    (g : BoundedContinuousFunction (Fin k → ℝ) ℝ) :
    Tendsto (fun n => ∫ ω, f (fun i => X n (Fin.castAdd k i) ω) *
      g (fun j => X n (Fin.natAdd m j) ω) ∂P) atTop
      (𝓝 ((∫ ω, f (fun i => X 0 (Fin.castAdd k i) ω) ∂P) *
        (∫ ω, g (fun j => X 0 (Fin.natAdd m j) ω) ∂P))) :=
  tendsto_cylinder_product_of_tendstoInDistribution
    (tendstoInDistribution_gaussian_independent_blocks hX hXm hX0 hAA hBB hAB) f g

#print axioms tendsto_integral_gaussian_independent_blocks

/-- Finite original pairings and normalized dyadic pairings of a whole-plane
GFF converge jointly in law to independent copies of the corresponding
original pairing vectors. The dilated tests have integral zero. -/
theorem IsWholePlaneGFF.tendstoInDistribution_dyadic_pairings
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {m k : ℕ}
    (φ : Fin m → ℂ → ℝ) (ψ : Fin k → ℂ → ℝ)
    (hφ : ∀ i, IsTestFunction Set.univ (φ i))
    (hψ : ∀ j, IsTestFunction Set.univ (ψ j))
    (hψzero : ∀ j, ∫ z, ψ j z = 0) :
    letI := h.isProbabilityMeasure
    TendstoInDistribution
      (fun n ω => (fun i => hC ω (φ i), fun j => affinePairing hC hcirc
        (((((2 : ℝ)⁻¹ ^ n) : ℝ) : ℂ)) 0 ω (ψ j))) atTop
      (fun ω : Ω × Ω => (fun i => hC ω.1 (φ i), fun j => hC ω.2 (ψ j)))
      (fun _ => P) (P.prod P) := by
  let _ := h.isProbabilityMeasure
  let a : ℕ → ℂ := fun n => (((((2 : ℝ)⁻¹ ^ n) : ℝ) : ℂ))
  have ha (n : ℕ) : a n ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity))
  let X : ℕ → Fin (m+k) → Ω → ℝ := fun n i ω =>
    Fin.addCases (motive := fun _ : Fin (m+k) => ℝ)
      (fun j => hC ω (φ j)) (fun j => affinePairing hC hcirc (a n) 0 ω (ψ j)) i
  have hX (n : ℕ) : IsGaussianProcess (X n) P := by
    let q : GFFObservable.Admissible := ⟨.circle ‖a n‖ 0, norm_pos_iff.mpr (ha n)⟩
    let o : Fin (m+k) → GFFObservable.Admissible := Fin.addCases
      (motive := fun _ : Fin (m+k) => GFFObservable.Admissible)
      (fun i => ⟨.pairing (φ i), hφ i⟩)
      (fun j => ⟨.pairing (fun z => ψ j ((z - 0) / a n)),
        (hψ j).comp_inverse_complex_affine (ha n) 0⟩)
    let c : Fin (m+k) → ℝ := Fin.addCases (fun _ => 1) (fun _ => (‖a n‖ ^ 2)⁻¹)
    let d : Fin (m+k) → ℝ := Fin.addCases (fun _ => 0) (fun j => ∫ z, ψ j z)
    have hg := h.isGaussianProcess_weighted_recentered o q c d
    convert hg using 1
    funext i ω
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have ho : o (Fin.castAdd k j) = ⟨.pairing (φ j), hφ j⟩ := by
        exact Fin.addCases_left j
      simp only [X, c, d, Fin.addCases_left, ho, q, GFFObservable.eval, one_mul,
        zero_mul, sub_zero]
    · have ho : o (Fin.natAdd m j) = ⟨.pairing (fun z => ψ j ((z - 0) / a n)),
          (hψ j).comp_inverse_complex_affine (ha n) 0⟩ := by
        exact Fin.addCases_right j
      simp only [X, c, d, Fin.addCases_right, ho, q, affinePairing, GFFObservable.eval,
        mul_comm]
  have hXm (n : ℕ) (i : Fin (m+k)) : Measurable (X n i) := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa [X] using h.measurable_pairing (φ j) (hφ j)
    · simpa [X, affinePairing, affineCircle] using
        (h.complex_affine (ha n) 0).measurable_pairing (ψ j) (hψ j)
  have hX0 (n : ℕ) (i : Fin (m+k)) : ∫ ω, X n i ω ∂P = 0 := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa [X, GFFObservable.eval] using h.integral_eq_zero (.pairing (φ j)) (hφ j)
    · simpa [X, affinePairing, affineCircle, GFFObservable.eval] using
        (h.complex_affine (ha n) 0).integral_eq_zero (.pairing (ψ j)) (hψ j)
  have hAA (n : ℕ) (i j : Fin m) :
      cov[X n (Fin.castAdd k i), X n (Fin.castAdd k j); P] =
        cov[X 0 (Fin.castAdd k i), X 0 (Fin.castAdd k j); P] := by simp [X]
  have hBB (n : ℕ) (i j : Fin k) :
      cov[X n (Fin.natAdd m i), X n (Fin.natAdd m j); P] =
        cov[X 0 (Fin.natAdd m i), X 0 (Fin.natAdd m j); P] := by
    have h1 := h.covariance_complex_affine_pairings (ha n) 0 (hψ i) (hψ j)
    have h2 := h.covariance_complex_affine_pairings (ha 0) 0 (hψ i) (hψ j)
    simpa only [X, Fin.addCases_right, affinePairing] using h1.trans h2.symm
  have hAB (i : Fin m) (j : Fin k) : Tendsto (fun n =>
      cov[X n (Fin.castAdd k i), X n (Fin.natAdd m j); P]) atTop (𝓝 0) := by
    simpa only [X, Fin.addCases_left, Fin.addCases_right, a] using
      h.tendsto_covariance_affinePairing_dyadic (hφ i) (hψ j) (hψzero j)
  have ht := tendstoInDistribution_gaussian_independent_blocks hX hXm hX0 hAA hBB hAB
  simpa [X, a, affinePairing, hψzero] using ht

#print axioms IsWholePlaneGFF.tendstoInDistribution_dyadic_pairings

/-- Bounded continuous cylinder functions of original and normalized dyadic
GFF pairings have asymptotically factorized expectations. -/
theorem IsWholePlaneGFF.tendsto_integral_dyadic_pairings_product
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {m k : ℕ}
    (φ : Fin m → ℂ → ℝ) (ψ : Fin k → ℂ → ℝ)
    (hφ : ∀ i, IsTestFunction Set.univ (φ i))
    (hψ : ∀ j, IsTestFunction Set.univ (ψ j))
    (hψzero : ∀ j, ∫ z, ψ j z = 0)
    (f : BoundedContinuousFunction (Fin m → ℝ) ℝ)
    (g : BoundedContinuousFunction (Fin k → ℝ) ℝ) :
    Tendsto (fun n => ∫ ω, f (fun i => hC ω (φ i)) *
      g (fun j => affinePairing hC hcirc (((((2 : ℝ)⁻¹ ^ n) : ℝ) : ℂ)) 0 ω (ψ j)) ∂P)
      atTop (𝓝 ((∫ ω, f (fun i => hC ω (φ i)) ∂P) *
        (∫ ω, g (fun j => hC ω (ψ j)) ∂P))) := by
  let _ := h.isProbabilityMeasure
  exact tendsto_cylinder_product_of_tendstoInDistribution
    (h.tendstoInDistribution_dyadic_pairings φ ψ hφ hψ hψzero) f g

#print axioms IsWholePlaneGFF.tendsto_integral_dyadic_pairings_product

/-- Every fixed bilinear combination of the mixed covariances of original and
normalized dyadic GFF pairings tends to zero. Only the dilated tests need have
integral zero. -/
theorem IsWholePlaneGFF.tendsto_sum_covariance_affinePairing_dyadic
    {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι] [Fintype κ]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (φ : ι → ℂ → ℝ) (ψ : κ → ℂ → ℝ)
    (hφ : ∀ i, IsTestFunction Set.univ (φ i))
    (hψ : ∀ j, IsTestFunction Set.univ (ψ j))
    (hψzero : ∀ j, ∫ y, ψ j y = 0) (a : ι → ℝ) (b : κ → ℝ) :
    Tendsto (fun n : ℕ => ∑ i, ∑ j, a i * b j *
      cov[fun ω => hC ω (φ i), fun ω => affinePairing hC hcirc
        (((((2 : ℝ)⁻¹ ^ n) : ℝ) : ℂ)) 0 ω (ψ j); P]) atTop (𝓝 0) := by
  have hc : Tendsto (fun n : ℕ => ∑ i, ∑ j, a i * b j *
      cov[fun ω => hC ω (φ i), fun ω => affinePairing hC hcirc
        (((((2 : ℝ)⁻¹ ^ n) : ℝ) : ℂ)) 0 ω (ψ j); P]) atTop
      (𝓝 (∑ _i : ι, ∑ _j : κ, (0 : ℝ))) :=
    tendsto_finsetSum _ (fun i _ => tendsto_finsetSum _ (fun j _ => by
      simpa only [mul_zero] using
        (h.tendsto_covariance_affinePairing_dyadic (hφ i) (hψ j) (hψzero j)).const_mul
          (a i * b j)))
  simpa using hc

#print axioms IsWholePlaneGFF.tendsto_sum_covariance_affinePairing_dyadic
#print axioms tendsto_integral_gaussian_of_covariance
#print axioms tendstoInDistribution_gaussian_of_covariance
end HarmonicBalls
