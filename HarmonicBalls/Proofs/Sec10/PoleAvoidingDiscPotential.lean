import HarmonicBalls.Proofs.Sec10.PoleAvoidingRiesz
import HarmonicBalls.Proofs.Sec6.DiscPotentialComparison
import HarmonicBalls.Proofs.Sec6.GreenIntegrability

/-! # Disc potentials for local components avoiding the pole

The ambient disc may contain the pole: a union of components which omits it
has a subharmonic zero extension across the pole.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Laplacian Section6
open scoped ENNReal

/-- A restricted disc Green potential is controlled by the boundary values of
the truncated odometer, including when the disc contains the pole. -/
theorem restricted_disc_potential_le_boundary_of_pole_not_mem
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {R βminus βplus : ℝ} (hR : 0 < R) (hV : VolumeGrowth μ R βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) {t : ℝ} (ht : 0 < t)
    {U Λ : Set ℂ} (hU : IsOpen U) (hUsub : U ⊆ ball (0 : ℂ) R)
    (hΛsub : Λ ⊆ U ∩ cluster μ R z t)
    (hcomp : ∀ x ∈ Λ, connectedComponentIn (U ∩ cluster μ R z t) x ⊆ Λ)
    (hzΛ : z ∉ Λ) {c : ℂ} {r : ℝ} (hr : 0 < r) (hdisc : closedBall c r ⊆ U)
    (hqcont : ContinuousOn (fun x => ∫ y in ball c r ∩ Λ,
      greenFunction (ball c r) x y ∂μ) (closedBall c r))
    (hqΔ : HasLaplacian (fun x => ∫ y in ball c r ∩ Λ,
      greenFunction (ball c r) x y ∂μ) 0 (μ.restrict (ball c r ∩ Λ)) (ball c r)) :
    ∃ y ∈ sphere c r, (∫ w in ball c r ∩ Λ, greenFunction (ball c r) c w ∂μ) ≤
      Λ.indicator (odometer μ R z t) y := by
  have hvc := (odometer_indicator_union_components_continuousOn_and_subharmonic_of_pole_not_mem
    hμ hR hV hz ht hU hUsub hΛsub hcomp hzΛ).1.mono hdisc
  have hge := odometer_indicator_union_components_laplacianGE_restrict_of_pole_not_mem
    hμ hR hV hz ht hU hUsub hΛsub hcomp hzΛ
  have hge' : LaplacianGE (Λ.indicator (odometer μ R z t)) (μ.restrict Λ) (ball c r) := by
    refine ⟨hge.1.mono_set (ball_subset_closedBall.trans hdisc), fun φ hφ hφ0 => ?_⟩
    exact hge.2 φ ⟨hφ.1, hφ.2.1, hφ.2.2.trans (ball_subset_closedBall.trans hdisc)⟩ hφ0
  have hcenter : 0 ≤ Λ.indicator (odometer μ R z t) c := by
    by_cases hc : c ∈ Λ
    · have hcz : c ≠ z := by intro h; subst c; exact hzΛ hc
      simpa only [indicator_of_mem hc] using odometer_nonneg ht.le
        (ball_subset_closedBall (hUsub (hdisc (mem_closedBall_self hr.le)))) (by simpa using hcz)
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

/-- A mass-carrying disc gives a quantitative bound for a pole-avoiding
union of local cluster components. -/
theorem mass_le_truncated_odometer_of_disc_regular_of_pole_not_mem
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {R βminus βplus : ℝ} (hR : 0 < R) (hV : VolumeGrowth μ R βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) {t : ℝ} (ht : 0 < t)
    {U Λ A : Set ℂ} (hU : IsOpen U) (hUsub : U ⊆ ball (0 : ℂ) R)
    (hΛsub : Λ ⊆ U ∩ cluster μ R z t)
    (hcomp : ∀ x ∈ Λ, connectedComponentIn (U ∩ cluster μ R z t) x ⊆ Λ)
    (hzΛ : z ∉ Λ) {c : ℂ} {d : ℝ} {N : ℕ} (hd : 0 < d)
    (hdisc : closedBall c (2 * d) ⊆ U)
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
  obtain ⟨y, hy, hybound⟩ := restricted_disc_potential_le_boundary_of_pole_not_mem
    hμ hR hV hz ht hU hUsub hΛsub hcomp hzΛ (by linarith : 0 < 2 * d) hdisc hqcont hqΔ
  refine ⟨y, hy, ?_⟩
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  nlinarith

/-- Volume growth supplies the integrability, finiteness, and non-atomicity
needed in the mass comparison. -/
theorem mass_le_truncated_odometer_of_potential_regular_of_pole_not_mem
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {R βminus βplus : ℝ} (hR : 0 < R) (hV : VolumeGrowth μ R βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) {t : ℝ} (ht : 0 < t)
    {U Λ A : Set ℂ} (hU : IsOpen U) (hUsub : U ⊆ ball (0 : ℂ) R)
    (hΛsub : Λ ⊆ U ∩ cluster μ R z t)
    (hcomp : ∀ x ∈ Λ, connectedComponentIn (U ∩ cluster μ R z t) x ⊆ Λ)
    (hzΛ : z ∉ Λ) {c : ℂ} {d : ℝ} {N : ℕ} (hd : 0 < d)
    (hdisc : closedBall c (2 * d) ⊆ U)
    (hmass : μ (A ∩ Λ) ≤ (N : ℝ≥0∞) * μ (ball c d ∩ Λ))
    (hqcont : ContinuousOn (fun x => ∫ y in ball c (2 * d) ∩ Λ,
      greenFunction (ball c (2 * d)) x y ∂μ) (closedBall c (2 * d)))
    (hqΔ : HasLaplacian (fun x => ∫ y in ball c (2 * d) ∩ Λ,
      greenFunction (ball c (2 * d)) x y ∂μ) 0
      (μ.restrict (ball c (2 * d) ∩ Λ)) (ball c (2 * d))) :
    ∃ y ∈ sphere c (2 * d),
      ((2 * Real.pi)⁻¹ * Real.log (3 / 2)) * (μ (A ∩ Λ)).toReal ≤
        (N : ℝ) * Λ.indicator (odometer μ R z t) y := by
  let : IsLocallyFiniteMeasure μ := hμ
  have hcenter : c ∈ ball (0 : ℂ) R :=
    hUsub (hdisc (mem_closedBall_self (by linarith)))
  have hsub : ball c (2 * d) ⊆ ball (0 : ℂ) R :=
    ball_subset_closedBall.trans (hdisc.trans hUsub)
  have hint : IntegrableOn (greenFunction (ball c (2 * d)) c) (ball c (2 * d) ∩ Λ) μ :=
    (integrable_greenFunction_of_volumeGrowth hR isOpen_ball hsub hV
      (ball_subset_closedBall hcenter)).integrableOn
  have hfinite : μ (ball c d ∩ Λ) ≠ ⊤ :=
    ne_top_of_le_ne_top (measure_ball_lt_top.ne) (measure_mono inter_subset_left)
  exact mass_le_truncated_odometer_of_disc_regular_of_pole_not_mem
    hμ hR hV hz ht hU hUsub hΛsub hcomp hzΛ hd hdisc hmass hfinite
    (hV.measure_singleton hcenter) hint hqcont hqΔ

end HarmonicBalls
