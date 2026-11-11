import Mathlib
import HarmonicBalls.LPStage.GFF

/-!
# Existence of the whole-plane GFF: named ingredients and the elementary moment bound (LP stage)

Owner: worker z6, task fp-phase2-gff-existence-row29. Statement target: `exists_isWholePlaneGFF` (general LP form of
`WholePlaneGFFExistsFrozen`, `HarmonicBalls/FirstPass/S11r/Frozen.lean:39`).

Route (MQ-lh-16 / MQ-lh-17 of `notes/fp-gaps/MATH-ANSWERS.md`):

* B1 (`KolmogorovExtensionStmt`): Kolmogorov extension on an arbitrary index set with the product σ-algebra. Absent from
  pinned Mathlib and from `LatticeProb`; a named hypothesis with its source, not a frozen input.
* B2 (`WholePlaneCovPSDStmt`): positive semidefiniteness of the whole-plane covariance on admissible observables.
  Only a sketch exists (log energy `= (2π)⁻¹ ∫ |∇U|²`, MQ-lh-17 (b)); a named hypothesis, reported as a gap.
* B4: the moment bound. Its elementary real-analysis core is `two_log_max_add_sub_log_le` below (proved). The covariance
  identity `Var(h_r(z) - h_s(w)) = -log r - log s + 2 ∫ log max(|x - w|, s) dρ_{z,r}(x)` is not yet formalized.
* B3: continuity. `LatticeProb.exists_continuous_modification_spaceTime_all`
  (`.lake/packages/lattice-probability/LatticeProb/Prob/ChentsovPiModification.lean:413`) is proved, not Bonanno code;
  the box gluing is not yet formalized.

Nothing here is a frozen input. The named Props below are hypotheses of the statements that use them.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace LatticeProb.Gauss

/-- Kolmogorov extension theorem for an arbitrary index type `ι`, real coordinates, product σ-algebra: a projective
family of probability measures on the finite-dimensional coordinate spaces has a projective limit.
Source: William J. Anderson, *Advanced Probability II Notes*, Theorem 6.0.6, p. 60
(<https://www.math.mcgill.ca/bill/589/589notes.pdf#page=60>); MQ-lh-16 B1 in `notes/fp-gaps/MATH-ANSWERS.md`.
Absent from pinned Mathlib: `Mathlib/MeasureTheory/Constructions/Projective.lean` has uniqueness only (`IsProjectiveLimit`
is defined there, no existence). -/
def KolmogorovExtensionStmt : Prop :=
  ∀ (ι : Type) (P : ∀ J : Finset ι, Measure (∀ _ : J, ℝ)),
    IsProjectiveMeasureFamily (α := fun _ : ι => ℝ) P → (∀ J : Finset ι, IsProbabilityMeasure (P J)) →
      ∃ μ : Measure (ι → ℝ), IsProbabilityMeasure μ ∧ IsProjectiveLimit (α := fun _ : ι => ℝ) μ P

/-- Positive semidefiniteness of the whole-plane covariance on admissible observables: for every finite family of
admissible observables `o_i` and real `c_i`, `∑ c_i c_j wholePlaneGFFCov o_i o_j ≥ 0`.
Sketch (not a written proof): with `σ = ∑ c_i σ_i` (signed smearing measures), `m = σ(ℂ)` and `ν = σ - m ρ` (ρ the uniform
probability on the unit circle), the form equals `-∬ log|x - y| dν dν = (2π)⁻¹ ∫ |∇U|²` with `U = -log|·| * ν`
(MQ-lh-17 (b), `notes/fp-gaps/MATH-ANSWERS.md`). The limit from smooth regularizations is not written out.
Named hypothesis: the operator must source it before any consumer is unconditional. -/
def WholePlaneCovPSDStmt : Prop :=
  ∀ (n : ℕ) (o : Fin n → GFFObservable.Admissible) (c : Fin n → ℝ),
    0 ≤ ∑ i, ∑ j, c i * c j * wholePlaneGFFCov (o i).1 (o j).1

/-- Elementary bound behind the moment estimate (MQ-lh-17 (b), B4): for `0 < a ≤ r`, `a ≤ s`, `0 ≤ d`,
`2 log (max r s + d) - log r - log s ≤ (|r - s| + 2 d) / a`. -/
theorem two_log_max_add_sub_log_le {a r s d : ℝ} (ha : 0 < a) (har : a ≤ r) (has : a ≤ s) (hd : 0 ≤ d) :
    2 * Real.log (max r s + d) - Real.log r - Real.log s ≤ (|r - s| + 2 * d) / a := by
  have hr0 : 0 < r := lt_of_lt_of_le ha har
  have hs0 : 0 < s := lt_of_lt_of_le ha has
  have hMa : a ≤ max r s := le_max_of_le_left har
  have hM0 : 0 < max r s := lt_of_lt_of_le ha hMa
  -- Step 1: `log (M + d) - log M ≤ d / M ≤ d / a` with `M = max r s`.
  have h1 : Real.log (max r s + d) - Real.log (max r s) ≤ d / a := by
    rw [← Real.log_div (by positivity) hM0.ne']
    have hlog := Real.log_le_sub_one_of_pos (show 0 < (max r s + d) / max r s by positivity)
    have h2 : (max r s + d) / max r s - 1 = d / max r s := by
      field_simp
      ring
    have h3 : d / max r s ≤ d / a := div_le_div_of_nonneg_left hd ha hMa
    linarith
  -- Step 2: `2 log M - log r - log s ≤ |r - s| / a`.
  have h4 : 2 * Real.log (max r s) - Real.log r - Real.log s ≤ |r - s| / a := by
    rcases le_total r s with hrs | hrs
    · have hM : max r s = s := max_eq_right hrs
      rw [hM]
      have hlog := Real.log_le_sub_one_of_pos (show 0 < s / r by positivity)
      rw [Real.log_div hs0.ne' hr0.ne'] at hlog
      have h5 : (s / r - 1) = (s - r) / r := by
        field_simp
      have h6 : (s - r) / r ≤ (s - r) / a := div_le_div_of_nonneg_left (by linarith) ha har
      have h7 : |r - s| = s - r := by
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      rw [h7]
      linarith
    · have hM : max r s = r := max_eq_left hrs
      rw [hM]
      have hlog := Real.log_le_sub_one_of_pos (show 0 < r / s by positivity)
      rw [Real.log_div hr0.ne' hs0.ne'] at hlog
      have h5 : (r / s - 1) = (r - s) / s := by
        field_simp
      have h6 : (r - s) / s ≤ (r - s) / a := div_le_div_of_nonneg_left (by linarith) ha has
      have h7 : |r - s| = r - s := abs_of_nonneg (by linarith)
      rw [h7]
      linarith
  -- Combine: `2 log (M + d) - log r - log s = 2 (log (M + d) - log M) + (2 log M - log r - log s)`.
  have h8 : (|r - s| + 2 * d) / a = |r - s| / a + 2 * d / a := by ring
  have h9 : 2 * d / a = 2 * (d / a) := by ring
  linarith

/-! ### Finite-dimensional laws of a centred Gaussian family with a positive semidefinite kernel

Adapted from Mathlib's `ProbabilityTheory.BrownianReal.projectiveFamily` (`Mathlib/Probability/BrownianMotion/
GaussianProjectiveFamily.lean`, Etienne Marion, Apache 2.0 license): the same construction with the covariance
`min s t` replaced by an arbitrary kernel `K` whose finite Gram matrices are positive semidefinite. -/

section KernelFamily

open MeasureTheory ProbabilityTheory NormedSpace Set WithLp

variable {ι : Type} [DecidableEq ι]

/-- The covariance matrix of the kernel `K` on a finite index set `I`. -/
def kernelMatrix (K : ι → ι → ℝ) (I : Finset ι) : Matrix I I ℝ := .of fun s t => K s.1 t.1

/-- The centred Gaussian measure on `I → ℝ` with covariance `K` restricted to `I`. -/
noncomputable def kernelFamily (K : ι → ι → ℝ) (I : Finset ι) : Measure (I → ℝ) :=
  multivariateGaussian 0 (kernelMatrix K I) |>.map (MeasurableEquiv.toLp 2 (I → ℝ)).symm

lemma measurePreserving_ofLp_kernelFamily (K : ι → ι → ℝ) (I : Finset ι) :
    MeasurePreserving ofLp (multivariateGaussian 0 (kernelMatrix K I)) (kernelFamily K I) where
  measurable := by fun_prop
  map_eq := rfl

instance isProbabilityMeasure_kernelFamily (K : ι → ι → ℝ) (I : Finset ι) :
    IsProbabilityMeasure (kernelFamily K I) := by
  unfold kernelFamily
  infer_instance

instance isGaussian_kernelFamily (K : ι → ι → ℝ) (I : Finset ι) : IsGaussian (kernelFamily K I) := by
  rw [kernelFamily, show ⇑(MeasurableEquiv.toLp 2 (I → ℝ)).symm = ⇑(EuclideanSpace.equiv I ℝ) from rfl]
  infer_instance

lemma isProjectiveMeasureFamily_kernelFamily (K : ι → ι → ℝ)
    (hK : ∀ I : Finset ι, (kernelMatrix K I).PosSemidef) :
    IsProjectiveMeasureFamily (α := fun _ : ι ↦ ℝ) (kernelFamily K) := by
  intro I J hJI
  nth_rw 2 [kernelFamily]
  rw [Measure.map_map]
  · have : (Finset.restrict₂ (π := fun _ : ι ↦ ℝ) hJI ∘ (MeasurableEquiv.toLp 2 (I → ℝ)).symm) =
        ofLp ∘ (EuclideanSpace.restrict₂ hJI) := by
      ext; simp
    rw [this, ((measurePreserving_ofLp_kernelFamily K J).comp
        (measurePreserving_restrict₂_multivariateGaussian (hK I) hJI)).map_eq]
  · exact Finset.measurable_restrict₂ _
  · fun_prop

lemma covariance_kernelFamily_fun (K : ι → ι → ℝ) (I : Finset ι) (f g : (I → ℝ) → ℝ) :
    cov[f, g; kernelFamily K I] =
      cov[f ∘ ofLp, g ∘ ofLp; multivariateGaussian 0 (kernelMatrix K I)] := by
  rw [kernelFamily, covariance_map_equiv]
  rfl

lemma covariance_eval_kernelFamily (K : ι → ι → ℝ) (hK : ∀ I : Finset ι, (kernelMatrix K I).PosSemidef)
    (I : Finset ι) (s t : I) :
    cov[fun x : I → ℝ ↦ x s, fun x : I → ℝ ↦ x t; kernelFamily K I] = K s.1 t.1 := by
  rw [covariance_kernelFamily_fun]
  exact covariance_eval_multivariateGaussian (μ := 0) (hK I) s t

lemma integral_kernelFamily {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (K : ι → ι → ℝ)
    (I : Finset ι) (f : (I → ℝ) → E) :
    ∫ x, f x ∂(kernelFamily K I) = ∫ x, f (ofLp x) ∂(multivariateGaussian 0 (kernelMatrix K I)) := by
  simp [kernelFamily, integral_map_equiv]

lemma integral_id_kernelFamily (K : ι → ι → ℝ) (I : Finset ι) :
    ∫ x, x ∂(kernelFamily K I) = 0 := by
  rw [integral_kernelFamily, ← PiLp.coe_continuousLinearEquiv 2 ℝ,
    ContinuousLinearEquiv.integral_comp_id_comm, integral_id_multivariateGaussian, map_zero]

lemma integral_eval_kernelFamily (K : ι → ι → ℝ) (I : Finset ι) (s : I) :
    ∫ x : I → ℝ, x s ∂(kernelFamily K I) = 0 := by
  have h := integral_id_kernelFamily K I
  have hint : Integrable (fun x : I → ℝ ↦ x) (kernelFamily K I) := IsGaussian.integrable_id
  have := (ContinuousLinearMap.proj s : (I → ℝ) →L[ℝ] ℝ).integral_comp_comm hint
  simpa [h] using this

end KernelFamily

/-! ### A centred Gaussian process with a positive semidefinite kernel, from the Kolmogorov extension (B1)

Given `KolmogorovExtensionStmt` (B1) and positive semidefiniteness of every finite Gram matrix of `K` (B2, as a
hypothesis of the finite-dimensional family), the coordinate process of the projective limit is a centred Gaussian
process with covariance `K`. -/

section KernelProcess

open MeasureTheory ProbabilityTheory

variable {ι : Type} [DecidableEq ι]

/-- Kolmogorov extension (B1) applied to the kernel families: there is a probability measure `μ` on `ι → ℝ` under
which the coordinates form a centred Gaussian process with covariance `K`. -/
theorem exists_gaussian_of_kernel (hB1 : KolmogorovExtensionStmt) (K : ι → ι → ℝ)
    (hK : ∀ I : Finset ι, (kernelMatrix K I).PosSemidef) :
    ∃ μ : Measure (ι → ℝ), IsProbabilityMeasure μ ∧
      IsGaussianProcess (fun (i : ι) (ω : ι → ℝ) ↦ ω i) μ ∧
      (∀ i, ∫ ω, ω i ∂μ = 0) ∧
      ∀ i j, cov[fun ω : ι → ℝ ↦ ω i, fun ω : ι → ℝ ↦ ω j; μ] = K i j := by
  obtain ⟨μ, hμ, hlim⟩ := hB1 ι (kernelFamily K) (isProjectiveMeasureFamily_kernelFamily K hK)
    (fun J ↦ inferInstance)
  refine ⟨μ, hμ, ⟨fun I ↦ ?_⟩, ?_, ?_⟩
  · have hm : Measurable (I.restrict : (ι → ℝ) → (I → ℝ)) := Finset.measurable_restrict _
    exact ⟨hm.aemeasurable, by rw [hlim I]; infer_instance⟩
  · intro i
    have hmeas : Measurable (({i} : Finset ι).restrict : (ι → ℝ) → ({i} : Finset ι) → ℝ) :=
      Finset.measurable_restrict _
    have hi : i ∈ ({i} : Finset ι) := Finset.mem_singleton_self i
    have h := integral_map (μ := μ) hmeas.aemeasurable
      (measurable_pi_apply (⟨i, hi⟩ : ({i} : Finset ι))).aestronglyMeasurable
      (f := fun x : ({i} : Finset ι) → ℝ ↦ x ⟨i, hi⟩)
    rw [hlim {i}, integral_eval_kernelFamily] at h
    exact h.symm
  · intro i j
    have hi : i ∈ ({i, j} : Finset ι) := by simp
    have hj : j ∈ ({i, j} : Finset ι) := by simp
    have hmeas : Measurable (({i, j} : Finset ι).restrict : (ι → ℝ) → ({i, j} : Finset ι) → ℝ) :=
      Finset.measurable_restrict _
    have hcov := covariance_map (μ := μ)
      (X := fun x : ({i, j} : Finset ι) → ℝ ↦ x ⟨i, hi⟩)
      (Y := fun x : ({i, j} : Finset ι) → ℝ ↦ x ⟨j, hj⟩) (Z := ({i, j} : Finset ι).restrict)
      (measurable_pi_apply _).aestronglyMeasurable (measurable_pi_apply _).aestronglyMeasurable
      hmeas.aemeasurable
    rw [hlim {i, j}, covariance_eval_kernelFamily K hK {i, j} ⟨i, hi⟩ ⟨j, hj⟩] at hcov
    exact hcov.symm

end KernelProcess

end LatticeProb.Gauss
