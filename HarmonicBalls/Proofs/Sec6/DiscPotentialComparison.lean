import HarmonicBalls.Proofs.Sec6.TruncatedOdometerDomination
import HarmonicBalls.Steps.Sec11.SubharmonicMaximum
import HarmonicBalls.Proofs.Sec6.AnnulusGreenMass

/-! # Disc potential comparison

The distributional Laplacian inequality and the maximum principle give the
potential comparison used in the proof of Lemma 6.8.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Laplacian
open scoped ENNReal

/-- A continuous function whose Laplacian dominates a measure, added to a
continuous potential whose Laplacian is its negative, is subharmonic. -/
theorem isSubharmonicOn_add_of_laplacianGE {U : Set ℂ} {v q : ℂ → ℝ}
    {μ ν : Measure ℂ} (hU : IsOpen U) (hν : ν ≤ μ)
    (hvc : ContinuousOn v U) (hqc : ContinuousOn q U)
    (hv : LaplacianGE v μ U) (hq : HasLaplacian q 0 ν U) :
    IsSubharmonicOn U (v + q) := by
  have hle : LaplacianLE (-(v + q)) 0 U := by
    refine ⟨(hv.1.add hq.1).neg, fun φ hφ hφ0 _ => ?_⟩
    obtain ⟨hiμ, hvφ⟩ := hv.2 φ hφ hφ0
    obtain ⟨_, _, hqφ⟩ := hq.2 φ hφ
    have hmeas := integral_mono_measure hν (Filter.Eventually.of_forall hφ0) hiμ
    have hid : (fun x => (-(v + q)) x * Δ φ x) =
        fun x => -(v x * Δ φ x) - q x * Δ φ x := by
      funext x
      simp only [Pi.neg_apply, Pi.add_apply]
      ring
    have hi : Integrable (fun x => -(v x * Δ φ x)) :=
      (integrable_mul_laplacian hv.1 hφ).neg
    rw [hid, integral_sub hi (integrable_mul_laplacian hq.1 hφ)]
    have hneg : (∫ x, -(v x * Δ φ x)) = -(∫ x, v x * Δ φ x) :=
      integral_neg _
    rw [hneg, hqφ]
    simp only [integral_zero_measure]
    linarith
  exact superharmonicOfLaplacianLEStep_holds U _ hU (hvc.add hqc).neg hle

/-- A potential with zero boundary values is bounded at the centre by a
boundary value of any nonnegative function whose Laplacian dominates its
source measure. -/
theorem disc_potential_le_boundary_of_laplacianGE {c : ℂ} {r : ℝ}
    {v q : ℂ → ℝ} {μ ν : Measure ℂ} (hr : 0 < r) (hν : ν ≤ μ)
    (hvc : ContinuousOn v (closedBall c r)) (hqc : ContinuousOn q (closedBall c r))
    (hv : LaplacianGE v μ (ball c r)) (hq : HasLaplacian q 0 ν (ball c r))
    (hv0 : 0 ≤ v c) (hqboundary : ∀ x ∈ sphere c r, q x = 0) :
    ∃ y ∈ sphere c r, q c ≤ v y := by
  have hs := isSubharmonicOn_add_of_laplacianGE isOpen_ball hν
    (hvc.mono ball_subset_closedBall) (hqc.mono ball_subset_closedBall) hv hq
  obtain ⟨y, hy, hmax⟩ := hs.exists_maximum_on_sphere hr (hvc.add hqc)
  refine ⟨y, hy, ?_⟩
  have h := hmax c (mem_closedBall_self hr.le)
  simp only [Pi.add_apply, hqboundary y hy, add_zero] at h
  linarith

/-- The restricted disc Green potential is bounded by the truncated odometer
at a point of the boundary circle, once its regularity is known. -/
theorem restricted_disc_potential_le_truncated_odometer_boundary
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {R βminus βplus : ℝ} (hR : 0 < R) (hV : VolumeGrowth μ R βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) {t : ℝ} (ht : 0 < t)
    {U Λ : Set ℂ} (hU : IsOpen U) (hUsub : U ⊆ ball (0 : ℂ) R \ {z})
    (hΛsub : Λ ⊆ U ∩ cluster μ R z t)
    (hcomp : ∀ x ∈ Λ, connectedComponentIn (U ∩ cluster μ R z t) x ⊆ Λ)
    {c : ℂ} {r : ℝ} (hr : 0 < r) (hdisc : closedBall c r ⊆ U)
    (hqcont : ContinuousOn (fun x => ∫ y in ball c r ∩ Λ,
      greenFunction (ball c r) x y ∂μ) (closedBall c r))
    (hqΔ : HasLaplacian (fun x => ∫ y in ball c r ∩ Λ,
      greenFunction (ball c r) x y ∂μ) 0 (μ.restrict (ball c r ∩ Λ)) (ball c r)) :
    ∃ y ∈ sphere c r, (∫ w in ball c r ∩ Λ, greenFunction (ball c r) c w ∂μ) ≤
      Λ.indicator (odometer μ R z t) y := by
  classical
  have hcluster := (cluster_open_laplacian_of_general greenFunctionBall
    obstacleNonCoincidenceHarmonicGeneral_holds shiftedOdometerLaplacianGeneral_holds
    obstacleCompatibilityShiftStep_holds hμ hR hV hz ht).1
  have hcont := (odometer_continuousOn_and_subharmonic hμ hR hV hz ht).1.mono hUsub
  have hfront : ∀ x ∈ U ∩ frontier Λ, odometer μ R z t x = 0 := by
    intro x hx
    have hnot : x ∉ cluster μ R z t := fun hxcl =>
      disjoint_left.mp (frontier_union_components_disjoint (hU.inter hcluster) hΛsub hcomp)
        hx.2 ⟨hx.1, hxcl⟩
    have hle : ¬ 0 < odometer μ R z t x := fun h =>
      hnot (mem_cluster_iff.mpr ⟨(hUsub hx.1).1, Or.inr h⟩)
    exact le_antisymm (le_of_not_gt hle)
      (odometer_nonneg ht.le (ball_subset_closedBall (hUsub hx.1).1) (hUsub hx.1).2)
  have hvc := (continuousOn_indicator_of_zero_frontier hcont hfront).mono hdisc
  have hge := odometer_indicator_union_components_laplacianGE_restrict
    hμ hR hV hz ht hU hUsub hΛsub hcomp
  have hge' : LaplacianGE (Λ.indicator (odometer μ R z t)) (μ.restrict Λ) (ball c r) := by
    refine ⟨hge.1.mono_set (ball_subset_closedBall.trans hdisc), fun φ hφ hφ0 => ?_⟩
    exact hge.2 φ ⟨hφ.1, hφ.2.1, hφ.2.2.trans (ball_subset_closedBall.trans hdisc)⟩ hφ0
  have hcenter : 0 ≤ Λ.indicator (odometer μ R z t) c := by
    by_cases hc : c ∈ Λ
    · simpa only [indicator_of_mem hc] using odometer_nonneg ht.le
        (ball_subset_closedBall (hUsub (hdisc (mem_closedBall_self hr.le))).1)
        (hUsub (hdisc (mem_closedBall_self hr.le))).2
    · simp [hc]
  apply disc_potential_le_boundary_of_laplacianGE hr
    (Measure.restrict_mono_set μ inter_subset_right) hvc hqcont hge' hqΔ hcenter
  intro x hx
  have hnot : x ∉ ball c r := by
    intro hxin
    have heq := mem_sphere.mp hx
    have hlt := mem_ball.mp hxin
    linarith
  simp only [greenFunction_of_notMem_left hnot, integral_zero]

/-- A mass-carrying disc controls the mass of a set by a boundary value of
the truncated odometer. -/
theorem mass_le_truncated_odometer_of_disc_regular
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {R βminus βplus : ℝ} (hR : 0 < R) (hV : VolumeGrowth μ R βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) {t : ℝ} (ht : 0 < t)
    {U Λ A : Set ℂ} (hU : IsOpen U) (hUsub : U ⊆ ball (0 : ℂ) R \ {z})
    (hΛsub : Λ ⊆ U ∩ cluster μ R z t)
    (hcomp : ∀ x ∈ Λ, connectedComponentIn (U ∩ cluster μ R z t) x ⊆ Λ)
    {c : ℂ} {d : ℝ} {N : ℕ} (hd : 0 < d) (hdisc : closedBall c (2 * d) ⊆ U)
    (hmass : μ (A ∩ Λ) ≤ (N : ℝ≥0∞) * μ (ball c d ∩ Λ))
    (hfinite : μ (ball c d ∩ Λ) ≠ ⊤) (hatom : μ {c} = 0)
    (hint : IntegrableOn (greenFunction (ball c (2 * d)) c) (ball c (2 * d) ∩ Λ) μ)
    (hqcont : ContinuousOn (fun x => ∫ y in ball c (2 * d) ∩ Λ,
      greenFunction (ball c (2 * d)) x y ∂μ) (closedBall c (2 * d)))
    (hqΔ : HasLaplacian (fun x => ∫ y in ball c (2 * d) ∩ Λ,
      greenFunction (ball c (2 * d)) x y ∂μ) 0
      (μ.restrict (ball c (2 * d) ∩ Λ)) (ball c (2 * d))) :
    ∃ y ∈ sphere c (2 * d),
      ((2 * Real.pi)⁻¹ * Real.log (3 / 2)) * (μ (A ∩ Λ)).toReal ≤
        (N : ℝ) * Λ.indicator (odometer μ R z t) y := by
  have hcluster := (cluster_open_laplacian_of_general greenFunctionBall
    obstacleNonCoincidenceHarmonicGeneral_holds shiftedOdometerLaplacianGeneral_holds
    obstacleCompatibilityShiftStep_holds hμ hR hV hz ht).1
  have hΛopen := isOpen_of_union_components (hU.inter hcluster) hΛsub hcomp
  have hsub : ball c d ∩ Λ ⊆ ball c (2 * d) ∩ Λ :=
    inter_subset_inter_left _ (ball_subset_ball (by linarith))
  have hmass' := mass_le_disc_green_integral_of_mass_bound hd hΛopen.measurableSet
    hmass hfinite hatom (hint.mono_set hsub)
  have hle : (∫ y in ball c d ∩ Λ, greenFunction (ball c (2 * d)) c y ∂μ) ≤
      ∫ y in ball c (2 * d) ∩ Λ, greenFunction (ball c (2 * d)) c y ∂μ :=
    setIntegral_mono_set hint (Filter.Eventually.of_forall (greenFunction_nonneg isBounded_ball c))
      (Filter.Eventually.of_forall hsub)
  obtain ⟨y, hy, hybound⟩ := restricted_disc_potential_le_truncated_odometer_boundary
    hμ hR hV hz ht hU hUsub hΛsub hcomp (by linarith : 0 < 2 * d) hdisc hqcont hqΔ
  refine ⟨y, hy, ?_⟩
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  nlinarith

end HarmonicBalls.Section6
