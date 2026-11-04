import HarmonicBalls.Proofs.Sec9.HarmonicBoundaryComparison
import HarmonicBalls.Proofs.Sec9.DominatedGreenPotential
import HarmonicBalls.Proofs.SecA.Basic

/-!
# The auxiliary Green potential for Lemma 9.3

The difference of the potentials has the signed distributional Laplacian used in the proof;
in particular, it is weakly superharmonic on the first set.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Laplacian

/-- A restricted Green potential has continuous boundary values and the expected Laplacian. -/
theorem restricted_greenPotential_regular {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {A : Set ℂ} {R βm βp : ℝ} (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    (hA : A ⊆ ball (0 : ℂ) R) :
    ContinuousOn (fun x => ∫ y in A, greenFunction (ball 0 R) x y ∂μ) (closedBall 0 R) ∧
    HasLaplacian (fun x => ∫ y in A, greenFunction (ball 0 R) x y ∂μ)
      0 (μ.restrict A) (ball 0 R) := by
  have hrest : (μ.restrict A).restrict (ball 0 R) = μ.restrict A := by
    rw [Measure.restrict_restrict measurableSet_ball, inter_eq_right.mpr hA]
  obtain ⟨hc, hΔ⟩ := dominated_greenPotentialBall hμ hR hV (Measure.restrict_le_self (s := A))
  rw [hrest] at hc hΔ
  have heqp : greenPotentialBall (μ.restrict A) R =
      fun x => ∫ y in A, greenFunction (ball 0 R) x y ∂μ := by
    funext x
    simp only [greenPotentialBall, Measure.restrict_restrict measurableSet_ball, inter_eq_right.mpr hA]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => greenFunction_ball_comm R y x)
  rw [heqp] at hc hΔ
  exact ⟨hc, hΔ⟩

/-- The auxiliary potential is continuous and has Laplacian `μ|B - μ|A`. -/
theorem auxiliary_greenPotential_regular {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {A B : Set ℂ} {R βm βp : ℝ} (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    (hA : A ⊆ ball (0 : ℂ) R) (hB : B ⊆ ball (0 : ℂ) R) :
    ContinuousOn (fun x => (∫ y in A, greenFunction (ball 0 R) x y ∂μ) -
      ∫ y in B, greenFunction (ball 0 R) x y ∂μ) (closedBall 0 R) ∧
    HasLaplacian (fun x => (∫ y in A, greenFunction (ball 0 R) x y ∂μ) -
      ∫ y in B, greenFunction (ball 0 R) x y ∂μ) (μ.restrict B) (μ.restrict A) (ball 0 R) := by
  obtain ⟨hcA, hΔA⟩ := restricted_greenPotential_regular hμ hR hV hA
  obtain ⟨hcB, hΔB⟩ := restricted_greenPotential_regular hμ hR hV hB
  refine ⟨hcA.sub hcB, hΔA.1.sub hΔB.1, fun φ hφ => ?_⟩
  obtain ⟨_, hiA, eA⟩ := hΔA.2 φ hφ
  obtain ⟨_, hiB, eB⟩ := hΔB.2 φ hφ
  refine ⟨hiB, hiA, ?_⟩
  have hfun : (fun x => ((∫ y in A, greenFunction (ball 0 R) x y ∂μ) -
      ∫ y in B, greenFunction (ball 0 R) x y ∂μ) * Δ φ x) =
      fun x => (∫ y in A, greenFunction (ball 0 R) x y ∂μ) * Δ φ x -
        (∫ y in B, greenFunction (ball 0 R) x y ∂μ) * Δ φ x := by
    funext x
    ring
  rw [hfun, integral_sub (integrable_mul_laplacian hΔA.1 hφ)
    (integrable_mul_laplacian hΔB.1 hφ), eA, eB]
  simp only [integral_zero_measure]
  ring

/-- If `Δu = μ|B - μ|A`, then `u` is weakly superharmonic on `A`. -/
theorem HasLaplacian.laplacianLE_zero_on_restriction {μ : Measure ℂ} {A B U : Set ℂ}
    {u : ℂ → ℝ} (hΔ : HasLaplacian u (μ.restrict B) (μ.restrict A) U) (hAU : A ⊆ U) :
    LaplacianLE u 0 A := by
  refine ⟨hΔ.1.mono_set hAU, fun φ hφ hφ0 _ => ?_⟩
  have hφU : IsTestFunction U φ := ⟨hφ.1, hφ.2.1, hφ.2.2.trans hAU⟩
  obtain ⟨_, hiA, heq⟩ := hΔ.2 φ hφU
  have hi : Integrable φ μ :=
    (integrableOn_iff_integrable_of_support_subset ((subset_tsupport φ).trans hφ.2.2)).mp hiA
  have hAeq : ∫ y in A, φ y ∂μ = ∫ y, φ y ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun y hy => image_eq_zero_of_notMem_tsupport (fun h => hy (hφ.2.2 h)))
  have hle := integral_mono_measure (Measure.restrict_le_self (s := B))
    (Filter.Eventually.of_forall hφ0) hi
  rw [heq, hAeq]
  simp only [integral_zero_measure]
  linarith

/-- A signed Laplacian `μ|B - μ|A` is nonpositive on any set disjoint from `B`. -/
theorem HasLaplacian.laplacianLE_zero_of_disjoint {μ : Measure ℂ} {A B U V : Set ℂ}
    {u : ℂ → ℝ} (hΔ : HasLaplacian u (μ.restrict B) (μ.restrict A) U)
    (hVU : V ⊆ U) (hVB : Disjoint V B) : LaplacianLE u 0 V := by
  refine ⟨hΔ.1.mono_set hVU, fun φ hφ hφ0 _ => ?_⟩
  have hφU : IsTestFunction U φ := ⟨hφ.1, hφ.2.1, hφ.2.2.trans hVU⟩
  obtain ⟨_, _, heq⟩ := hΔ.2 φ hφU
  have hzero : ∫ y in B, φ y ∂μ = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro y hyB
    apply image_eq_zero_of_notMem_tsupport
    intro hy
    exact (Set.disjoint_left.1 hVB) (hφ.2.2 hy) hyB
  rw [heq, hzero]
  simp only [integral_zero_measure, zero_sub]
  exact neg_nonpos.mpr (integral_nonneg hφ0)

/-- The auxiliary potential is classically superharmonic on the first set. -/
theorem auxiliary_greenPotential_superharmonicOn {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {A B : Set ℂ} {R βm βp : ℝ} (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    (hAopen : IsOpen A) (hA : A ⊆ ball (0 : ℂ) R) (hB : B ⊆ ball (0 : ℂ) R) :
    IsSuperharmonicOn A (fun x => (∫ y in A, greenFunction (ball 0 R) x y ∂μ) -
      ∫ y in B, greenFunction (ball 0 R) x y ∂μ) := by
  obtain ⟨hc, hΔ⟩ := auxiliary_greenPotential_regular hμ hR hV hA hB
  exact superharmonicOfLaplacianLEStep_holds A _ hAopen (hc.mono (hA.trans ball_subset_closedBall))
    (hΔ.laplacianLE_zero_on_restriction hA)

/-- The auxiliary potential is classically superharmonic away from the second set. -/
theorem auxiliary_greenPotential_superharmonicOn_of_disjoint {μ : Measure ℂ}
    (hμ : IsLocallyFiniteMeasure μ) {A B V : Set ℂ} {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (hA : A ⊆ ball (0 : ℂ) R)
    (hB : B ⊆ ball (0 : ℂ) R) (hVopen : IsOpen V) (hVsub : V ⊆ ball (0 : ℂ) R)
    (hVB : Disjoint V B) :
    IsSuperharmonicOn V (fun x => (∫ y in A, greenFunction (ball 0 R) x y ∂μ) -
      ∫ y in B, greenFunction (ball 0 R) x y ∂μ) := by
  obtain ⟨hc, hΔ⟩ := auxiliary_greenPotential_regular hμ hR hV hA hB
  exact superharmonicOfLaplacianLEStep_holds V _ hVopen (hc.mono (hVsub.trans ball_subset_closedBall))
    (hΔ.laplacianLE_zero_of_disjoint hVsub hVB)

end HarmonicBalls
