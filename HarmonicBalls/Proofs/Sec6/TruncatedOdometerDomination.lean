import HarmonicBalls.Proofs.Sec6.TruncatedOdometerRiesz

/-! # Domination by the Laplacian of a zero extension

The positive-distribution representation and its interior equality imply the
measure-valued inequality needed in the proof of Lemma 6.8.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter Topology Laplacian

/-- A nonnegative distributional Laplacian which equals `μ` on an open set
also dominates the restriction of `μ` to that set on the ambient domain. -/
theorem laplacianGE_restrict_of_interior_identity
    {U Λ : Set ℂ} {v : ℂ → ℝ} {μ : Measure ℂ}
    (hU : IsOpen U) (hΛ : IsOpen Λ) (hΛU : Λ ⊆ U) (hμ : IsLocallyFiniteMeasure μ)
    (hge : LaplacianGE v 0 U) (hΔ : HasLaplacian v (μ.restrict Λ) 0 Λ) :
    LaplacianGE v (μ.restrict Λ) U := by
  let : IsLocallyFiniteMeasure μ := hμ
  obtain ⟨σ, _, hσK, hσφ, hdom⟩ :=
    exists_riesz_measure_with_interior_domination hU hΛU hμ hge hΔ
  refine ⟨hge.1, fun φ hφ hφ0 => ?_⟩
  have hiμ : Integrable φ μ := hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1
  have hiμΛ : Integrable φ (μ.restrict Λ) := hiμ.mono_measure Measure.restrict_le_self
  refine ⟨hiμΛ, ?_⟩
  obtain ⟨V, hV, hKV, hVU, hVc⟩ :=
    exists_open_between_and_isCompact_closure hφ.2.1 hU hφ.2.2
  let σ' := σ.restrict (closure V)
  let : IsFiniteMeasure σ' := isFiniteMeasure_restrict.mpr (hσK _ hVc hVU).ne
  have hsmall : μ.restrict (Λ ∩ V) ≤ σ' := by
    rw [Measure.le_iff]
    intro A hA
    rw [Measure.restrict_apply hA]
    refine (show μ (A ∩ (Λ ∩ V)) ≤ σ' (A ∩ (Λ ∩ V)) from ?_).trans
      (measure_mono inter_subset_left)
    rw [measure_eq_iInf_isOpen (A ∩ (Λ ∩ V)) σ']
    refine le_iInf fun O => le_iInf fun hAO => le_iInf fun hO => ?_
    have hOV : IsOpen (O ∩ (Λ ∩ V)) := hO.inter (hΛ.inter hV)
    have hsub : O ∩ (Λ ∩ V) ⊆ closure V := fun x hx => subset_closure hx.2.2
    have heq : σ' (O ∩ (Λ ∩ V)) = σ (O ∩ (Λ ∩ V)) := by
      rw [show σ' = σ.restrict (closure V) from rfl,
        Measure.restrict_apply hOV.measurableSet, inter_eq_left.mpr hsub]
    calc
      μ (A ∩ (Λ ∩ V)) ≤ μ (O ∩ (Λ ∩ V)) := measure_mono fun x hx => ⟨hAO hx, hx.2⟩
      _ ≤ σ (O ∩ (Λ ∩ V)) := hdom _ hOV (fun x hx => hx.2.1)
      _ = σ' (O ∩ (Λ ∩ V)) := heq.symm
      _ ≤ σ' O := measure_mono inter_subset_left
  have hφV : ∀ x ∉ V, φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (hKV h))
  have hμeq : ∫ x, φ x ∂(μ.restrict (Λ ∩ V)) = ∫ x, φ x ∂(μ.restrict Λ) := by
    have h := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := μ.restrict Λ) hφV
    rw [Measure.restrict_restrict hV.measurableSet] at h
    simpa only [inter_comm] using h
  have hσeq : ∫ x, φ x ∂σ' = ∫ x, φ x ∂σ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    exact hφV x (fun hxV => hx (subset_closure hxV))
  have hiσ' : Integrable φ σ' := (hσφ φ hφ).1.mono_measure Measure.restrict_le_self
  have h := integral_mono_measure hsmall (Eventually.of_forall hφ0) hiσ'
  rw [hμeq, hσeq, (hσφ φ hφ).2] at h
  exact h

/-- The distributional Laplacian of the odometer restricted to a union of
cluster components dominates the measure restricted to those components. -/
theorem odometer_indicator_union_components_laplacianGE_restrict
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {R βminus βplus : ℝ} (hR : 0 < R) (hV : VolumeGrowth μ R βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) {t : ℝ} (ht : 0 < t)
    {U Λ : Set ℂ} (hU : IsOpen U) (hUsub : U ⊆ ball (0 : ℂ) R \ {z})
    (hΛsub : Λ ⊆ U ∩ cluster μ R z t)
    (hcomp : ∀ x ∈ Λ, connectedComponentIn (U ∩ cluster μ R z t) x ⊆ Λ) :
    LaplacianGE (Λ.indicator (odometer μ R z t)) (μ.restrict Λ) U := by
  have hcluster := (cluster_open_laplacian_of_general greenFunctionBall
    obstacleNonCoincidenceHarmonicGeneral_holds shiftedOdometerLaplacianGeneral_holds
    obstacleCompatibilityShiftStep_holds hμ hR hV hz ht).1
  have hΛopen := isOpen_of_union_components (hU.inter hcluster) hΛsub hcomp
  have hΛsub' : Λ ⊆ (ball (0 : ℂ) R \ {z}) ∩ cluster μ R z t :=
    fun x hx => ⟨hUsub (hΛsub hx).1, (hΛsub hx).2⟩
  exact laplacianGE_restrict_of_interior_identity hU hΛopen (hΛsub.trans inter_subset_left) hμ
    (odometer_indicator_union_components_laplacianGE hμ hR hV hz ht hU hUsub hΛsub hcomp)
    (truncated_odometer_hasLaplacian_on_components hμ hR hV hz ht hΛopen hΛsub')

end HarmonicBalls.Section6
