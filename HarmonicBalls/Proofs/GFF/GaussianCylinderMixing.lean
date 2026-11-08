import HarmonicBalls.Proofs.GFF.DilationPairingCovarianceDecay
import LatticeProb.Prob.Scaling.CramerWold

/-! # Finite-dimensional Gaussian covariance limits

The Cramér–Wold and Cameron–Martin tools used here are from Leonardo Bonanno's
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
