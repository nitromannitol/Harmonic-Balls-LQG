import Mathlib
import HarmonicBalls.Defs.Laplacian
import HarmonicBalls.Proofs.Sec11.ClosureScales.RouteACircleSmooth
import HarmonicBalls.Proofs.Sec11.ClosureScales.CircleTestFubiniLimit

/-!
# Deterministic smooth-test convergence of circle averages

Let `φ : ℂ → ℝ` be a test function on the plane (`IsTestFunction univ φ`: smooth with compact
support). For a radius `r`, the circle average `φ_r(v) = Real.circleAverage φ v r` is again a test
function (`CircleTestFubiniLimit`). As `r → 0⁺` every iterated Fréchet derivative of `φ_r` converges
uniformly to the corresponding derivative of `φ`, in the operator norm of the continuous multilinear
maps, and all the supports lie in one fixed compact set `testEnlargement φ`.

This is the deterministic content of the written limit `φ * σ_r → φ` in the test-function topology
(fleet notes `sec11-proof-r10.tex`, lines 1046–1062 and 1353–1378). No probability, Gaussian, Fourier
or distributional input is used. The analytic inputs are differentiation under the circle integral
(`HarmonicBalls.hasFDerivAt_translate_integral`), the commutation of continuous linear maps with
circle averages (`ContinuousLinearMap.circleAverage_comp_comm`), and uniform continuity of compactly
supported continuous functions.

Terminology: a circle average is the planar spherical mean (Armitage–Gardiner, *Classical Potential
Theory*); the test-function topology is the one of Armstrong–Kuusi–Mourrat, here reduced to a fixed
compact support together with uniform convergence of every derivative.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff
open Real

namespace HarmonicBalls.CircleTestFubini

/-- A continuous function is circle integrable on every circle. -/
lemma circleIntegrable_of_continuous {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : ℂ → X} (hf : Continuous f) (c : ℂ) (R : ℝ) : CircleIntegrable f c R :=
  (hf.comp (continuous_circleMap c R)).intervalIntegrable _ _

/-- If `‖H (circleMap w r θ)‖ ≤ M` for every angle `θ`, the circle average of `H` has norm at most `M`. -/
lemma norm_circleAverage_le_of_forall {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {H : ℂ → X} {w : ℂ} {r M : ℝ} (h : ∀ θ : ℝ, ‖H (circleMap w r θ)‖ ≤ M) :
    ‖Real.circleAverage H w r‖ ≤ M := by
  have hpos : (0 : ℝ) < 2 * π := by positivity
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := 2 * π) (f := fun θ => H (circleMap w r θ)) (C := M) (fun θ _ => h θ)
  rw [sub_zero, abs_of_pos hpos] at hI
  rw [Real.circleAverage_def, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hpos.le)]
  calc (2 * π)⁻¹ * ‖∫ θ in (0 : ℝ)..2 * π, H (circleMap w r θ)‖
      ≤ (2 * π)⁻¹ * (M * (2 * π)) := mul_le_mul_of_nonneg_left hI (inv_nonneg.2 hpos.le)
    _ = M := by rw [mul_comm M, ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]

/-- A circle average of a continuous function, minus the value at the centre, is controlled by the
oscillation of the function on the circle. -/
lemma norm_circleAverage_sub_le {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] {G : ℂ → X} (hG : Continuous G) (w : ℂ) {r M : ℝ}
    (h : ∀ θ : ℝ, ‖G (circleMap w r θ) - G w‖ ≤ M) :
    ‖Real.circleAverage G w r - G w‖ ≤ M := by
  have hsub := Real.circleAverage_fun_sub (f₁ := G) (f₂ := fun _ => G w) (c := w) (R := r)
    (circleIntegrable_of_continuous hG w r) (circleIntegrable_const (G w) w r)
  rw [Real.circleAverage_const] at hsub
  rw [← hsub]
  exact norm_circleAverage_le_of_forall (H := fun x => G x - G w) h

/-- **Differentiation under the circle integral.** The derivative of the circle average in the
centre is the circle average of the derivative. -/
lemma hasFDerivAt_circleAverage {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] {g : ℂ → X} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (r : ℝ)
    (w : ℂ) :
    HasFDerivAt (fun y : ℂ => Real.circleAverage g y r) (Real.circleAverage (fderiv ℝ g) w r) w := by
  have hcont : Continuous fun θ : ℝ => circleMap 0 r θ := continuous_circleMap 0 r
  have hfun : (fun y : ℂ => Real.circleAverage g y r) =
      fun y : ℂ => (2 * π)⁻¹ • ∫ θ in Ioc (0 : ℝ) (2 * π), g (y + circleMap 0 r θ) := by
    funext y
    rw [Real.circleAverage_def, intervalIntegral.integral_of_le (by positivity)]
    simp only [circleMap_eq_add_centre y r]
  have key : Real.circleAverage (fderiv ℝ g) w r =
      (2 * π)⁻¹ • ∫ θ in Ioc (0 : ℝ) (2 * π), fderiv ℝ g (w + circleMap 0 r θ) := by
    rw [Real.circleAverage_def, intervalIntegral.integral_of_le (by positivity)]
    simp only [circleMap_eq_add_centre w r]
  rw [hfun, key]
  exact (HarmonicBalls.hasFDerivAt_translate_integral hg hgc hcont w).const_smul (2 * π)⁻¹

/-- The derivative of a circle average is the circle average of the derivative, as functions. -/
lemma fderiv_circleAverage_eq {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] {g : ℂ → X} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (r : ℝ) :
    fderiv ℝ (fun w : ℂ => Real.circleAverage g w r) =
      fun w : ℂ => Real.circleAverage (fderiv ℝ g) w r :=
  funext fun w => (hasFDerivAt_circleAverage hg hgc r w).fderiv

/-- Circle averages commute with a linear isometry equivalence of the target. -/
lemma circleAverage_comp_linearIsometryEquiv {X Y : Type} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (e : X ≃ₗᵢ[ℝ] Y) {f : ℂ → X} (hf : Continuous f) (c : ℂ) (R : ℝ) :
    Real.circleAverage (e ∘ f) c R = e (Real.circleAverage f c R) :=
  (e.toContinuousLinearEquiv.toContinuousLinearMap).circleAverage_comp_comm
    (circleIntegrable_of_continuous hf c R)

/-- **Derivatives commute with circle averages, in every order.** For every `n`, every complete real
normed target `F` and every smooth compactly supported `g : ℂ → F`, the `n`-th Fréchet derivative of
the circle average equals the circle average of the `n`-th Fréchet derivative. -/
theorem iteratedFDeriv_circleAverage_aux (n : ℕ) :
    ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {g : ℂ → F},
      ContDiff ℝ ∞ g → HasCompactSupport g → ∀ (r : ℝ) (v : ℂ),
        iteratedFDeriv ℝ n (fun w : ℂ => Real.circleAverage g w r) v =
          Real.circleAverage (iteratedFDeriv ℝ n g) v r := by
  induction n with
  | zero =>
    intro F _ _ _ g hg _ r v
    have hL : ∀ h : ℂ → F,
        iteratedFDeriv ℝ 0 h = (continuousMultilinearCurryFin0 ℝ ℂ F).symm ∘ h :=
      fun h => iteratedFDeriv_zero_eq_comp
    rw [hL, hL]
    exact (circleAverage_comp_linearIsometryEquiv (continuousMultilinearCurryFin0 ℝ ℂ F).symm
      (f := g) hg.continuous v r).symm
  | succ n ih =>
    intro F _ _ _ g hg hgc r v
    have hg' : ContDiff ℝ ∞ (fderiv ℝ g) := (contDiff_infty_iff_fderiv.1 hg).2
    have hgc' : HasCompactSupport (fderiv ℝ g) := HasCompactSupport.fderiv (𝕜 := ℝ) hgc
    have hfd : fderiv ℝ (fun w : ℂ => Real.circleAverage g w r) =
        fun w : ℂ => Real.circleAverage (fderiv ℝ g) w r :=
      fderiv_circleAverage_eq hg hgc r
    have hih : iteratedFDeriv ℝ n (fun w : ℂ => Real.circleAverage (fderiv ℝ g) w r) =
        fun u : ℂ => Real.circleAverage (iteratedFDeriv ℝ n (fderiv ℝ g)) u r :=
      funext fun u => ih hg' hgc' r u
    have hcont : Continuous (iteratedFDeriv ℝ n (fderiv ℝ g)) :=
      hg'.continuous_iteratedFDeriv (by simp)
    have hsucc : iteratedFDeriv ℝ (n + 1) g =
        (continuousMultilinearCurryRightEquiv' ℝ n ℂ F).symm ∘ iteratedFDeriv ℝ n (fderiv ℝ g) :=
      funext fun u => iteratedFDeriv_succ_eq_comp_right
    rw [iteratedFDeriv_succ_eq_comp_right, hfd, hih, hsucc,
      circleAverage_comp_linearIsometryEquiv (continuousMultilinearCurryRightEquiv' ℝ n ℂ F).symm
        hcont v r]
    try rfl

/-- **Derivatives commute with circle averages.** For a test function `φ` on the plane, the
`n`-th derivative at `v` of the circle average `φ_r` is the circle average of the `n`-th derivative
of `φ`. -/
theorem iteratedFDeriv_circleAverage {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) (n : ℕ) (r : ℝ)
    (v : ℂ) :
    iteratedFDeriv ℝ n (fun w : ℂ => Real.circleAverage φ w r) v =
      Real.circleAverage (iteratedFDeriv ℝ n φ) v r :=
  iteratedFDeriv_circleAverage_aux n hφ.1 hφ.2.1 r v

/-- **Uniform convergence of every derivative of the averaged tests.** For a test function `φ` and
each order `n`, the `n`-th derivatives of `φ_r` converge to the `n`-th derivative of `φ` uniformly on
the plane, in the operator norm of the continuous multilinear maps, as `r → 0⁺`. -/
theorem tendstoUniformly_iteratedFDeriv_circleAverage {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ)
    (n : ℕ) :
    TendstoUniformly (fun r : ℝ => iteratedFDeriv ℝ n (fun v : ℂ => Real.circleAverage φ v r))
      (iteratedFDeriv ℝ n φ) (nhdsWithin (0 : ℝ) (Ioi 0)) := by
  have hcont : Continuous (iteratedFDeriv ℝ n φ) := hφ.1.continuous_iteratedFDeriv (by simp)
  have huc : UniformContinuous (iteratedFDeriv ℝ n φ) :=
    (HasCompactSupport.iteratedFDeriv (𝕜 := ℝ) hφ.2.1 n).uniformContinuous_of_continuous hcont
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδφ⟩ := Metric.uniformContinuous_iff.1 huc (ε / 2) (half_pos hε)
  filter_upwards [Ioo_mem_nhdsGT hδ] with r hr w
  have hr0 : 0 < r := hr.1
  have hrδ : r < δ := hr.2
  show dist (iteratedFDeriv ℝ n φ w)
    (iteratedFDeriv ℝ n (fun v : ℂ => Real.circleAverage φ v r) w) < ε
  rw [iteratedFDeriv_circleAverage hφ n r w, dist_comm, dist_eq_norm]
  have hle : ‖Real.circleAverage (iteratedFDeriv ℝ n φ) w r - iteratedFDeriv ℝ n φ w‖ ≤ ε / 2 := by
    refine norm_circleAverage_sub_le hcont w (fun θ => ?_)
    have hd : dist (circleMap w r θ) w < δ := by
      rw [dist_eq_norm, circleMap_sub_center, norm_circleMap_zero, abs_of_pos hr0]
      exact hrδ
    rw [← dist_eq_norm]
    exact (hδφ hd).le
  linarith

/-- **Smooth-test convergence of circle averages.** For a test function `φ` on the plane there is one
compact set `K` containing the support of `φ` and the support of every average `φ_r` with
`0 < r ≤ 1`, and for every order `n` the `n`-th derivative of `φ_r` converges uniformly to that of
`φ` as `r → 0⁺`. -/
theorem exists_isCompact_smooth_circleAverage {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) :
    ∃ K : Set ℂ, IsCompact K ∧ tsupport φ ⊆ K ∧
      (∀ r : ℝ, 0 < r → r ≤ 1 → tsupport (fun v : ℂ => Real.circleAverage φ v r) ⊆ K) ∧
      ∀ n : ℕ,
        TendstoUniformly (fun r : ℝ => iteratedFDeriv ℝ n (fun v : ℂ => Real.circleAverage φ v r))
          (iteratedFDeriv ℝ n φ) (nhdsWithin (0 : ℝ) (Ioi 0)) := by
  obtain ⟨hK, hr⟩ := fixed_enlargement_circleAverage hφ
  refine ⟨testEnlargement φ, hK, ?_, fun r hr0 hr1 => (hr r hr0 hr1).1.2.2,
    fun n => tendstoUniformly_iteratedFDeriv_circleAverage hφ n⟩
  intro x hx
  exact Set.mem_add.2 ⟨x, hx, 0, Metric.mem_closedBall_self zero_le_one, add_zero x⟩

end HarmonicBalls.CircleTestFubini
