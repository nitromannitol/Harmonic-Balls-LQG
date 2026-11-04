import HarmonicBalls.Proofs.Sec10.PoleAvoidingRiesz
import HarmonicBalls.Proofs.Sec3.ClusterCompatibility
import HarmonicBalls.Proofs.Sec10.PoleAvoidingAnnulusMass
import HarmonicBalls.Proofs.Sec6.AnnulusOdometerPotential

/-! # Upper Laplacian bounds for componentwise truncations -/

namespace HarmonicBalls

open MeasureTheory Metric Set Laplacian Section6

/-- If a function and its subharmonic remainder are split into two parts,
an upper bound for its Laplacian also bounds the Laplacian of the first part. -/
theorem laplacianLE_of_sub_laplacianGE {U : Set ℂ} {μ : Measure ℂ} {u v : ℂ → ℝ}
    (hu : LaplacianLE u μ U) (hv : LocallyIntegrableOn v U)
    (hrest : LaplacianGE (fun x => u x - v x) 0 U) : LaplacianLE v μ U := by
  refine ⟨hv, fun φ hφ hφ0 hφμ => ?_⟩
  have hbound := hu.2 φ hφ hφ0 hφμ
  have hrest' := (hrest.2 φ hφ hφ0).2
  simp only [integral_zero_measure] at hrest'
  have hfun : (fun x => (u x - v x) * Δ φ x) =
      fun x => u x * Δ φ x - v x * Δ φ x := by
    funext x
    ring
  rw [hfun, integral_sub (integrable_mul_laplacian hu.1 hφ)
    (integrable_mul_laplacian hv hφ)] at hrest'
  linarith

/-- Selecting a union of components from a nonnegative subharmonic function
preserves any upper distributional Laplacian bound. -/
theorem laplacianLE_indicator_of_union_components
    {U G Λ : Set ℂ} {u : ℂ → ℝ} {μ : Measure ℂ}
    (hU : IsOpen U) (hG : IsOpen G) (hGU : G ⊆ U)
    (hΛG : Λ ⊆ G) (hcomp : ∀ x ∈ Λ, connectedComponentIn G x ⊆ Λ)
    (hcont : ContinuousOn u U) (hnonneg : ∀ x ∈ U, 0 ≤ u x)
    (hzero : ∀ x ∈ U, x ∉ G → u x = 0)
    (hsub : IsSubharmonicOn U u) (hle : LaplacianLE u μ U) :
    LaplacianLE (Λ.indicator u) μ U := by
  classical
  have hcomp' : ∀ x ∈ G \ Λ, connectedComponentIn G x ⊆ G \ Λ := by
    intro x hx y hy
    refine ⟨connectedComponentIn_subset G x hy, ?_⟩
    intro hyΛ
    have hxy : x ∈ connectedComponentIn G y := by
      rw [← connectedComponentIn_eq hy]
      exact mem_connectedComponentIn hx.1
    exact hx.2 (hcomp y hyΛ hxy)
  have hrest := laplacianGE_indicator_of_union_components hU hG hGU
    (show G \ Λ ⊆ G from sdiff_subset) hcomp' hcont hnonneg hzero hsub
  have hvc := (laplacianGE_indicator_of_union_components hU hG hGU
    hΛG hcomp hcont hnonneg hzero hsub).1
  have hrest' : LaplacianGE (fun x => u x - Λ.indicator u x) 0 U := by
    have hneg : LaplacianLE (-(G \ Λ).indicator u) 0 U := by
      refine ⟨hrest.1.neg, fun φ hφ hφ0 _ => ?_⟩
      have h := (hrest.2 φ hφ hφ0).2
      simp only [integral_zero_measure] at h ⊢
      simp only [Pi.neg_apply, neg_mul, integral_neg]
      linarith
    apply LaplacianGE.of_laplacianLE_neg
    apply hneg.congr_eqOn hU.measurableSet
    intro x hx
    by_cases hxG : x ∈ G
    · by_cases hxΛ : x ∈ Λ <;> simp [hxG, hxΛ]
    · have hxΛ : x ∉ Λ := fun h => hxG (hΛG h)
      simp [hxG, hxΛ, hzero x hx hxG]
  exact laplacianLE_of_sub_laplacianGE hle hvc hrest'

/-- An upper Laplacian bound away from the pole extends to the zero-truncated
odometer on every union of local components omitting the pole. -/
theorem odometer_indicator_union_components_laplacianLE_of_pole_not_mem
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {R βminus βplus : ℝ} (hR : 0 < R) (hV : VolumeGrowth μ R βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) {t : ℝ} (ht : 0 < t)
    {U Λ : Set ℂ} (hU : IsOpen U) (hUsub : U ⊆ ball (0 : ℂ) R)
    (hΛsub : Λ ⊆ U ∩ cluster μ R z t)
    (hcomp : ∀ x ∈ Λ, connectedComponentIn (U ∩ cluster μ R z t) x ⊆ Λ)
    (hzΛ : z ∉ Λ)
    (hupper : LaplacianLE (odometer μ R z t) μ (U \ {z})) :
    LaplacianLE (Λ.indicator (odometer μ R z t)) μ U := by
  classical
  let V := U \ {z}
  let G := U ∩ cluster μ R z t
  have hVopen : IsOpen V := hU.sdiff isClosed_singleton
  have hcluster := (cluster_open_laplacian_of_general greenFunctionBall
    obstacleNonCoincidenceHarmonicGeneral_holds shiftedOdometerLaplacianGeneral_holds
    obstacleCompatibilityShiftStep_holds hμ hR hV hz ht).1
  have hGopen : IsOpen G := hU.inter hcluster
  have hΛopen : IsOpen Λ := isOpen_of_union_components hGopen hΛsub hcomp
  have hdis := frontier_union_components_disjoint hGopen hΛsub hcomp
  have hzcl : z ∈ U → z ∉ closure Λ := by
    intro hzU hzclosure
    have hzfront : z ∈ frontier Λ := by
      rw [hΛopen.frontier_eq]
      exact ⟨hzclosure, hzΛ⟩
    have hzcluster : z ∈ cluster μ R z t := mem_cluster_iff.mpr ⟨hz, Or.inl rfl⟩
    exact disjoint_left.mp hdis hzfront ⟨hzU, hzcluster⟩
  obtain ⟨hc, hs⟩ := odometer_continuousOn_and_subharmonic hμ hR hV hz ht
  have hVsub : V ⊆ ball (0 : ℂ) R \ {z} := fun x hx => ⟨hUsub hx.1, hx.2⟩
  obtain ⟨hsel, hselcomp⟩ := inter_union_components_of_subset
    (show V ⊆ U from sdiff_subset) hΛsub hcomp
  have hsV : IsSubharmonicOn V (odometer μ R z t) := by
    refine ⟨hs.1.mono hVsub, fun x hx r hr hball => ?_⟩
    exact hs.2 x (hVsub hx) r hr (hball.trans hVsub)
  have hzero : ∀ x ∈ V, x ∉ V ∩ cluster μ R z t → odometer μ R z t x = 0 := by
    intro x hx hxG
    have hxnot : x ∉ cluster μ R z t := fun h => hxG ⟨hx, h⟩
    have hn : ¬ 0 < odometer μ R z t x := fun hp =>
      hxnot (mem_cluster_iff.mpr ⟨(hVsub hx).1, Or.inr hp⟩)
    exact le_antisymm (le_of_not_gt hn)
      (odometer_nonneg ht.le (ball_subset_closedBall (hVsub hx).1) (hVsub hx).2)
  have haway := laplacianLE_indicator_of_union_components hVopen (hVopen.inter hcluster)
    inter_subset_left hsel hselcomp (hc.mono hVsub)
    (fun x hx => odometer_nonneg ht.le (ball_subset_closedBall (hVsub hx).1) (hVsub hx).2)
    hzero hsV hupper
  have haway' : LaplacianLE (Λ.indicator (odometer μ R z t)) μ V := by
    apply haway.congr_eqOn hVopen.measurableSet
    intro x hx
    by_cases hxΛ : x ∈ Λ <;> simp [hx, hxΛ]
  let W := U \ closure Λ
  have hWopen : IsOpen W := hU.sdiff isClosed_closure
  have hzeroW : LaplacianLE (Λ.indicator (odometer μ R z t)) μ W := by
    apply (laplacianLE_zero μ W).congr_eqOn hWopen.measurableSet
    intro x hx
    have hxΛ : x ∉ Λ := fun h => hx.2 (subset_closure h)
    simp [hxΛ]
  have hunion : V ∪ W = U := by
    ext x
    constructor
    · rintro (hx | hx) <;> exact hx.1
    · intro hx
      by_cases hxz : x = z
      · right
        subst x
        exact ⟨hx, hzcl hx⟩
      · left
        exact ⟨hx, by simpa using hxz⟩
  rw [← hunion]
  exact LaplacianLE.union hVopen hWopen haway' hzeroW

/-- The Laplacian of the zero-truncated odometer on any union of local
components omitting the pole is dominated by the original measure, even
when the open domain contains the pole. -/
theorem odometer_indicator_union_components_laplacianLE_of_volumeGrowth
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {R βminus βplus : ℝ} (hR : 0 < R) (hV : VolumeGrowth μ R βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) {t : ℝ} (ht : 0 < t)
    {U Λ : Set ℂ} (hU : IsOpen U) (hUsub : U ⊆ ball (0 : ℂ) R)
    (hΛsub : Λ ⊆ U ∩ cluster μ R z t)
    (hcomp : ∀ x ∈ Λ, connectedComponentIn (U ∩ cluster μ R z t) x ⊆ Λ)
    (hzΛ : z ∉ Λ) :
    LaplacianLE (Λ.indicator (odometer μ R z t)) μ U := by
  have hA : IsOpen (U \ {z}) := hU.sdiff isClosed_singleton
  have hAsub : U \ {z} ⊆ ball (0 : ℂ) R \ {z} :=
    fun x hx => ⟨hUsub hx.1, hx.2⟩
  obtain ⟨η, hη, _, hΔ⟩ := odometer_hasLaplacian_dominated_away_from_pole
    hμ hR hV hz ht hA.measurableSet hAsub
  have hupper : LaplacianLE (odometer μ R z t) μ (U \ {z}) := by
    refine ⟨hΔ.1, fun φ hφ hφ0 hφμ => ?_⟩
    exact (hΔ.laplacianLE.2 φ hφ hφ0 (hφμ.mono_measure hη)).trans
      (integral_mono_measure hη (Filter.Eventually.of_forall hφ0) hφμ)
  exact odometer_indicator_union_components_laplacianLE_of_pole_not_mem
    hμ hR hV hz ht hU hUsub hΛsub hcomp hzΛ hupper

end HarmonicBalls
