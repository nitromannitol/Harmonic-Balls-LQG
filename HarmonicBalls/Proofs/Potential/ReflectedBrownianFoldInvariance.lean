import HarmonicBalls.Proofs.Potential.ReflectedSquareScaling
import HarmonicBalls.Proofs.Sec8.ExitTimeScaling

/-!
# Reflected Brownian motion in the unit square depends on its start through the fold

Reflected Brownian motion in the unit square from `w ∈ ℂ` is the law of `fold ∘ W` for a planar
Brownian motion `W` from `w`, where `fold = squareFold 0 1` folds each coordinate onto `[0, 1]`
by the triangle wave `unitIntervalFold`. This module proves that this law only depends on
`fold w` (`reflectedPlanarBrownianMotion_zero_one_squareFold`).

* The triangle wave is a lattice isometry at every point: `unitIntervalFold u = σ (u - 2n)` with
  `σ = ±1` and `n ∈ ℤ` (`exists_unitIntervalFold_eq`), and it is invariant under these isometries
  (`unitIntervalFold_sign_mul_sub`).
* Planar Gaussian laws, hence planar Brownian motion, are invariant under the coordinate sign
  changes `z ↦ σ₁ Re z + i σ₂ Im z` (`planarGaussian_map_coordSign`,
  `planarBrownianMotion_coordSign`), by the symmetry of the real Gaussian law and the conjugacy
  criterion `planarBrownianMotion_map_rescale_of_heat_conjugacy`.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Set MarkovProcess
open scoped ENNReal NNReal

/-! ### The triangle wave -/

/-- The triangle wave is invariant under `u ↦ σ (u - 2n)` for `σ = ±1` and `n ∈ ℤ`. -/
theorem unitIntervalFold_sign_mul_sub {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (n : ℤ) (u : ℝ) :
    unitIntervalFold (σ * (u - 2 * n)) = unitIntervalFold u := by
  unfold unitIntervalFold
  congr 2
  have h : Real.cos (Real.pi * (u - 2 * n)) = Real.cos (Real.pi * u) := by
    rw [show Real.pi * (u - 2 * n) = Real.pi * u - n * (2 * Real.pi) by ring,
      Real.cos_sub_int_mul_two_pi]
  rcases hσ with rfl | rfl
  · rw [one_mul, h]
  · rw [show Real.pi * (-1 * (u - 2 * n)) = -(Real.pi * (u - 2 * n)) by ring, Real.cos_neg, h]

/-- **The triangle wave is a lattice isometry at every point**: `unitIntervalFold u = σ (u - 2n)`
for some `σ = ±1` and `n ∈ ℤ`. -/
theorem exists_unitIntervalFold_eq (u : ℝ) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∃ n : ℤ, unitIntervalFold u = σ * (u - 2 * n) := by
  set n : ℤ := round (u / 2) with hn
  have hround : |u / 2 - n| ≤ 1 / 2 := abs_sub_round (u / 2)
  have hθ : |Real.pi * (u - 2 * n)| ≤ Real.pi := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    have : |u - 2 * n| ≤ 1 := by
      have h2 : u - 2 * n = 2 * (u / 2 - n) := by ring
      rw [h2, abs_mul, abs_two]
      linarith
    nlinarith [Real.pi_pos]
  have hcos : Real.cos (Real.pi * u) = Real.cos |Real.pi * (u - 2 * n)| := by
    rw [Real.cos_abs, show Real.pi * (u - 2 * n) = Real.pi * u - n * (2 * Real.pi) by ring,
      Real.cos_sub_int_mul_two_pi]
  have hfold : unitIntervalFold u = |u - 2 * n| := by
    unfold unitIntervalFold
    rw [hcos, Real.arccos_cos (abs_nonneg _) hθ, abs_mul, abs_of_pos Real.pi_pos]
    field_simp
  rcases le_or_gt 0 (u - 2 * n) with h | h
  · exact ⟨1, Or.inl rfl, n, by rw [hfold, abs_of_nonneg h, one_mul]⟩
  · exact ⟨-1, Or.inr rfl, n, by rw [hfold, abs_of_neg h]; ring⟩

/-! ### Coordinate sign changes of the plane -/

/-- The coordinate sign change `z ↦ σ₁ Re z + i σ₂ Im z`. -/
def coordSign (σ₁ σ₂ : ℝ) (z : ℂ) : ℂ := ⟨σ₁ * z.re, σ₂ * z.im⟩

theorem continuous_coordSign (σ₁ σ₂ : ℝ) : Continuous (coordSign σ₁ σ₂) := by
  have h1 : Continuous fun z : ℂ => σ₁ * z.re := continuous_const.mul Complex.continuous_re
  have h2 : Continuous fun z : ℂ => σ₂ * z.im := continuous_const.mul Complex.continuous_im
  exact Complex.equivRealProdCLM.symm.continuous.comp (h1.prodMk h2)

theorem coordSign_coordSign {σ₁ σ₂ : ℝ} (h₁ : σ₁ = 1 ∨ σ₁ = -1) (h₂ : σ₂ = 1 ∨ σ₂ = -1)
    (z : ℂ) : coordSign σ₁ σ₂ (coordSign σ₁ σ₂ z) = z := by
  have e₁ : σ₁ * σ₁ = 1 := by rcases h₁ with rfl | rfl <;> norm_num
  have e₂ : σ₂ * σ₂ = 1 := by rcases h₂ with rfl | rfl <;> norm_num
  apply Complex.ext <;> simp only [coordSign, ← mul_assoc, e₁, e₂, one_mul]

/-- The coordinate sign change as an involutive homeomorphism of the plane. -/
def coordSignHomeomorph {σ₁ σ₂ : ℝ} (h₁ : σ₁ = 1 ∨ σ₁ = -1) (h₂ : σ₂ = 1 ∨ σ₂ = -1) :
    ℂ ≃ₜ ℂ where
  toFun := coordSign σ₁ σ₂
  invFun := coordSign σ₁ σ₂
  left_inv := coordSign_coordSign h₁ h₂
  right_inv := coordSign_coordSign h₁ h₂
  continuous_toFun := continuous_coordSign σ₁ σ₂
  continuous_invFun := continuous_coordSign σ₁ σ₂

theorem gaussianReal_map_sign_mul {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (m : ℝ) (v : ℝ≥0) :
    (gaussianReal m v).map (σ * ·) = gaussianReal (σ * m) v := by
  rw [gaussianReal_map_const_mul]
  congr 1
  rcases hσ with rfl | rfl <;> ext <;> simp

/-- **Planar Gaussian laws are invariant under coordinate sign changes.** -/
theorem planarGaussian_map_coordSign {σ₁ σ₂ : ℝ} (h₁ : σ₁ = 1 ∨ σ₁ = -1)
    (h₂ : σ₂ = 1 ∨ σ₂ = -1) (z : ℂ) (t : ℝ≥0) :
    (planarGaussian z t).map (coordSign σ₁ σ₂) = planarGaussian (coordSign σ₁ σ₂ z) t := by
  have he := Complex.measurableEquivRealProd.symm.measurable
  rw [planarGaussian, Measure.map_map (continuous_coordSign σ₁ σ₂).measurable he]
  have hcomp : coordSign σ₁ σ₂ ∘ Complex.measurableEquivRealProd.symm =
      Complex.measurableEquivRealProd.symm ∘ Prod.map (σ₁ * ·) (σ₂ * ·) := by
    funext p
    rfl
  rw [hcomp, ← Measure.map_map he ((measurable_const_mul _).prodMap (measurable_const_mul _)),
    ← Measure.map_prod_map _ _ (measurable_const_mul _) (measurable_const_mul _),
    gaussianReal_map_sign_mul h₁, gaussianReal_map_sign_mul h₂, planarGaussian]
  rfl

/-- **Planar Brownian motion is invariant under coordinate sign changes.** -/
theorem planarBrownianMotion_coordSign {σ₁ σ₂ : ℝ} (h₁ : σ₁ = 1 ∨ σ₁ = -1)
    (h₂ : σ₂ = 1 ∨ σ₂ = -1) (w : ℂ) :
    planarBrownianMotion (coordSign σ₁ σ₂ w) =
      (planarBrownianMotion w).map (ContinuousPath.rescale (coordSignHomeomorph h₁ h₂) 1) := by
  have hconj : SubMarkovKernelSemigroup.IsRescaledConjugate planarHeatSemigroup
      planarHeatSemigroup (coordSignHomeomorph h₁ h₂) 1 := by
    intro t x
    rw [one_mul, planarHeatSemigroup_apply, planarHeatSemigroup_apply]
    change planarGaussian x t = (planarGaussian (coordSign σ₁ σ₂ x) t).map (coordSign σ₁ σ₂)
    rw [planarGaussian_map_coordSign h₁ h₂, coordSign_coordSign h₁ h₂]
  exact planarBrownianMotion_map_rescale_of_heat_conjugacy (coordSignHomeomorph h₁ h₂) 1
    one_pos hconj w

/-! ### Fold invariance of reflected Brownian motion in the unit square -/

theorem squareFold_zero_one_apply (z : ℂ) :
    squareFold 0 1 z = ⟨unitIntervalFold z.re, unitIntervalFold z.im⟩ := by
  simp [squareFold]

/-- **Reflected Brownian motion in the unit square depends on the start only through the fold.** -/
theorem reflectedPlanarBrownianMotion_zero_one_squareFold (w : ℂ) :
    reflectedPlanarBrownianMotion 0 1 (squareFold 0 1 w) = reflectedPlanarBrownianMotion 0 1 w := by
  obtain ⟨σ₁, h₁, n₁, e₁⟩ := exists_unitIntervalFold_eq w.re
  obtain ⟨σ₂, h₂, n₂, e₂⟩ := exists_unitIntervalFold_eq w.im
  set v : ℂ := ⟨2 * n₁, 2 * n₂⟩ with hv
  have hfw : squareFold 0 1 w = coordSign σ₁ σ₂ (w + -v) := by
    rw [squareFold_zero_one_apply, e₁, e₂]
    apply Complex.ext <;> simp [coordSign, hv, sub_eq_add_neg]
  have hinv : ∀ z, squareFold 0 1 (coordSign σ₁ σ₂ (z + -v)) = squareFold 0 1 z := by
    intro z
    rw [squareFold_zero_one_apply, squareFold_zero_one_apply]
    have hre : (coordSign σ₁ σ₂ (z + -v)).re = σ₁ * (z.re - 2 * n₁) := by
      simp [coordSign, hv, sub_eq_add_neg]
    have him : (coordSign σ₁ σ₂ (z + -v)).im = σ₂ * (z.im - 2 * n₂) := by
      simp [coordSign, hv, sub_eq_add_neg]
    rw [hre, him, unitIntervalFold_sign_mul_sub h₁, unitIntervalFold_sign_mul_sub h₂]
  rw [hfw, reflectedPlanarBrownianMotion, Kernel.map_apply _ (measurable_comp_squareFoldCM 0 1),
    Kernel.map_apply _ (measurable_comp_squareFoldCM 0 1), planarBrownianMotion_coordSign h₁ h₂,
    ← Section6.planarBrownianMotion_map_add_from w (-v),
    Measure.map_map (ContinuousPath.measurable_rescale _ _)
      ((Homeomorph.refl NNReal).arrowCongr (Homeomorph.addRight (-v))).measurable,
    Measure.map_map (measurable_comp_squareFoldCM 0 1)
      ((ContinuousPath.measurable_rescale _ _).comp
        ((Homeomorph.refl NNReal).arrowCongr (Homeomorph.addRight (-v))).measurable)]
  congr 1
  funext b
  ext t
  simp only [Function.comp_apply, ContinuousMap.comp_apply, ContinuousPath.rescale_apply, one_mul]
  exact hinv (b t)

/-! ### The Markov property of reflected Brownian motion at a fixed time -/

/-- Events of planar Brownian motion from almost every point of the time-`s` Gaussian law hold
for the path shifted by `s`. -/
theorem ae_planarBrownianMotion_shift_of_ae (x : ℂ) (s : ℝ≥0) {S : Set (ContinuousPath ℂ)}
    (hS : MeasurableSet S)
    (h : ∀ᵐ y ∂(planarGaussian x s), ∀ᵐ b ∂planarBrownianMotion y, b ∈ S) :
    ∀ᵐ b ∂planarBrownianMotion x, ContinuousPath.shift s b ∈ S := by
  have ha : ∀ᵐ b ∂(planarBrownianMotion x).map (ContinuousPath.shift s), b ∈ S := by
    rw [planarBrownianMotion_eq_continuousProcess]
    have hshift := congrArg (fun K => K x)
      (SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousProcess_map_shift
        planarHeatSemigroup isConservative_planarHeatSemigroup
        isFellerKernelSemigroup_planarHeatSemigroup kolmogorovRegular_planarHeatSemigroup s)
    rw [ProbabilityTheory.Kernel.map_apply _ (ContinuousPath.measurable_shift_fixed s) x] at hshift
    rw [hshift]
    apply ProbabilityTheory.Kernel.ae_comp_of_ae_ae hS
    have h' : ∀ᵐ y ∂(planarHeatSemigroup s x), ∀ᵐ b ∂planarBrownianMotion y, b ∈ S := by
      rw [planarHeatSemigroup_apply]
      exact h
    filter_upwards [h'] with y hy
    change ∀ᵐ b ∂(SubMarkovKernelSemigroup.IsConservative.continuousProcess
      planarHeatSemigroup isConservative_planarHeatSemigroup y), b ∈ S
    rw [← planarBrownianMotion_eq_continuousProcess]
    exact hy
  exact (ae_map_iff (ContinuousPath.measurable_shift_fixed s).aemeasurable hS).mp ha

/-- **Markov property of reflected Brownian motion at a fixed time**: events of reflected
Brownian motion from almost every point of the time-`s` Gaussian law hold for the reflected
path shifted by `s`. -/
theorem ae_reflected_shift_of_ae {x : ℂ} {s : ℝ≥0} {S : Set (ContinuousPath ℂ)}
    (hS : MeasurableSet S)
    (h : ∀ᵐ w ∂(planarGaussian x s), ∀ᵐ b ∂(reflectedPlanarBrownianMotion 0 1 w), b ∈ S) :
    ∀ᵐ b ∂(reflectedPlanarBrownianMotion 0 1 x), ContinuousPath.shift s b ∈ S := by
  have hf := measurable_comp_squareFoldCM 0 1
  have hS' : MeasurableSet ((fun b : ContinuousPath ℂ => (squareFoldCM 0 1).comp b) ⁻¹' S) := hf hS
  have hplanar := ae_planarBrownianMotion_shift_of_ae x s hS' (by
    filter_upwards [h] with w hw
    rw [reflectedPlanarBrownianMotion, Kernel.map_apply _ hf] at hw
    exact (ae_map_iff hf.aemeasurable hS).mp hw)
  rw [reflectedPlanarBrownianMotion, Kernel.map_apply _ hf]
  refine (ae_map_iff hf.aemeasurable ((ContinuousPath.measurable_shift_fixed s) hS)).mpr ?_
  filter_upwards [hplanar] with b hb
  exact hb

/-- Planar Gaussian laws at positive times are absolutely continuous with respect to the standard
one. -/
theorem planarGaussian_absolutelyContinuous {s : ℝ≥0} (hs : 0 < s) (x : ℂ) :
    planarGaussian x s ≪ planarGaussian 0 1 := by
  have he := Complex.measurableEquivRealProd.symm.measurable
  rw [planarGaussian, planarGaussian]
  refine Measure.AbsolutelyContinuous.map ?_ he
  have h1 : gaussianReal x.re s ≪ gaussianReal (0 : ℂ).re 1 :=
    (gaussianReal_absolutelyContinuous _ hs.ne').trans
      (gaussianReal_absolutelyContinuous' _ one_ne_zero)
  have h2 : gaussianReal x.im s ≪ gaussianReal (0 : ℂ).im 1 :=
    (gaussianReal_absolutelyContinuous _ hs.ne').trans
      (gaussianReal_absolutelyContinuous' _ one_ne_zero)
  exact h1.prod h2

/-- **Transfer to every start after a positive time**: an event holding almost surely for
reflected Brownian motion from almost every point of the standard Gaussian law holds almost
surely for the reflected path from any start shifted by any positive time. -/
theorem ae_reflected_shift_of_ae_ref {x : ℂ} {s : ℝ≥0} (hs : 0 < s)
    {S : Set (ContinuousPath ℂ)} (hS : MeasurableSet S)
    (h : ∀ᵐ w ∂(planarGaussian 0 1), ∀ᵐ b ∂(reflectedPlanarBrownianMotion 0 1 w), b ∈ S) :
    ∀ᵐ b ∂(reflectedPlanarBrownianMotion 0 1 x), ContinuousPath.shift s b ∈ S :=
  ae_reflected_shift_of_ae hS ((planarGaussian_absolutelyContinuous hs x).ae_le h)

end HarmonicBalls

