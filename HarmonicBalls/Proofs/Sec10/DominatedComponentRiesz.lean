import HarmonicBalls.Proofs.Sec10.ComponentLaplacianUpper
import HarmonicBalls.Proofs.Sec6.DominatedDiscPotential

/-! # Dominated Riesz measures for pole-avoiding component unions -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Laplacian Section6

/-- A nonnegative distributional Laplacian bounded above by a locally finite
measure is represented by a measure dominated by it and carried by the domain. -/
theorem exists_dominated_riesz_measure {U : Set ℂ} {v : ℂ → ℝ} {μ : Measure ℂ}
    (hU : IsOpen U) (hμ : IsLocallyFiniteMeasure μ)
    (hge : LaplacianGE v 0 U) (hle : LaplacianLE v μ U) :
    ∃ η : Measure ℂ, η ≤ μ ∧ η.restrict U = η ∧ HasLaplacian v η 0 U := by
  let : IsLocallyFiniteMeasure μ := hμ
  let S : (ℂ → ℝ) → ℝ := fun φ => ∫ x, v x * Δ φ x
  have hlin : IsLinearOnTests U S := by
    intro φ ψ hφ hψ a b
    exact integral_mul_laplacian_const_mul_add_const_mul hge.1 hφ hψ a b
  have hpos : IsPositiveOnTests U S := by
    intro φ hφ hφ0
    simpa only [integral_zero_measure] using (hge.2 φ hφ hφ0).2
  obtain ⟨η, hηU, _, hηφ⟩ := exists_measure_of_isPositiveOnTests hU hlin hpos
  have hopen : ∀ V, IsOpen V → V ⊆ U → η V ≤ μ V := by
    intro V hV hVU
    apply measure_le_of_integral_le hV
    intro φ hφ hφ01
    have hφU := hφ.mono_set hVU
    have hiμ : Integrable φ μ := hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1
    refine ⟨(hηφ φ hφU).1, hiμ, ?_⟩
    rw [(hηφ φ hφU).2]
    exact hle.2 φ hφU (fun x => (hφ01 x).1) hiμ
  have hημ : η ≤ μ := by
    rw [Measure.le_iff]
    intro A hA
    rw [measure_eq_iInf_isOpen A μ]
    refine le_iInf fun V => le_iInf fun hAV => le_iInf fun hV => ?_
    have hsub : A ⊆ (V ∩ U) ∪ Uᶜ := fun x hx => by
      by_cases h : x ∈ U
      exacts [Or.inl ⟨hAV hx, h⟩, Or.inr h]
    calc
      η A ≤ η ((V ∩ U) ∪ Uᶜ) := measure_mono hsub
      _ ≤ η (V ∩ U) + η Uᶜ := measure_union_le _ _
      _ = η (V ∩ U) := by rw [hηU, add_zero]
      _ ≤ μ (V ∩ U) := hopen _ (hV.inter hU) inter_subset_right
      _ ≤ μ V := measure_mono inter_subset_left
  refine ⟨η, hημ, Measure.restrict_eq_self_of_ae_mem ?_, hge.1, ?_⟩
  · exact ae_iff.mpr hηU
  · intro φ hφ
    obtain ⟨hi, heq⟩ := hηφ φ hφ
    exact ⟨hi, integrable_zero_measure, by simpa only [integral_zero_measure, sub_zero] using heq.symm⟩

/-- The zero extension of any union of local cluster components omitting the
pole has a dominated measure-valued Laplacian on the entire open domain. -/
theorem odometer_indicator_union_components_hasLaplacian_dominated
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {R βminus βplus : ℝ} (hR : 0 < R) (hV : VolumeGrowth μ R βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) {t : ℝ} (ht : 0 < t)
    {U Λ : Set ℂ} (hU : IsOpen U) (hUsub : U ⊆ ball (0 : ℂ) R)
    (hΛsub : Λ ⊆ U ∩ cluster μ R z t)
    (hcomp : ∀ x ∈ Λ, connectedComponentIn (U ∩ cluster μ R z t) x ⊆ Λ)
    (hzΛ : z ∉ Λ) :
    ∃ η : Measure ℂ, η ≤ μ ∧ η.restrict U = η ∧
      HasLaplacian (Λ.indicator (odometer μ R z t)) η 0 U := by
  obtain ⟨hc, hs⟩ :=
    odometer_indicator_union_components_continuousOn_and_subharmonic_of_pole_not_mem
      hμ hR hV hz ht hU hUsub hΛsub hcomp hzΛ
  have hge : LaplacianGE (Λ.indicator (odometer μ R z t)) 0 U :=
    LaplacianGE.of_laplacianLE_neg
      (laplacianLEOfSuperharmonicStep_holds U _ hU hc.neg hs)
  exact exists_dominated_riesz_measure hU hμ hge
    (odometer_indicator_union_components_laplacianLE_of_volumeGrowth
      hμ hR hV hz ht hU hUsub hΛsub hcomp hzΛ)

/-- A measure carried by the open domain and bounded above distributionally
by a measure-valued Laplacian is bounded by its Riesz measure. -/
theorem measure_le_of_laplacianGE_hasLaplacian
    {U : Set ℂ} {v : ℂ → ℝ} {ν η : Measure ℂ}
    (hU : IsOpen U) (hη : IsLocallyFiniteMeasure η) (hνU : ν Uᶜ = 0)
    (hge : LaplacianGE v ν U) (hΔ : HasLaplacian v η 0 U) : ν ≤ η := by
  let : IsLocallyFiniteMeasure η := hη
  have hopen : ∀ V, IsOpen V → V ⊆ U → ν V ≤ η V := by
    intro V hV hVU
    apply measure_le_of_integral_le hV
    intro φ hφ hφ01
    have hφU := hφ.mono_set hVU
    have hiη : Integrable φ η := hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1
    obtain ⟨hiν, hbound⟩ := hge.2 φ hφU (fun x => (hφ01 x).1)
    obtain ⟨_, _, heq⟩ := hΔ.2 φ hφU
    refine ⟨hiν, hiη, ?_⟩
    simpa only [integral_zero_measure, sub_zero, heq] using hbound
  rw [Measure.le_iff]
  intro A hA
  rw [measure_eq_iInf_isOpen A η]
  refine le_iInf fun V => le_iInf fun hAV => le_iInf fun hV => ?_
  have hsub : A ⊆ (V ∩ U) ∪ Uᶜ := fun x hx => by
    by_cases h : x ∈ U
    exacts [Or.inl ⟨hAV hx, h⟩, Or.inr h]
  calc
    ν A ≤ ν ((V ∩ U) ∪ Uᶜ) := measure_mono hsub
    _ ≤ ν (V ∩ U) + ν Uᶜ := measure_union_le _ _
    _ = ν (V ∩ U) := by rw [hνU, add_zero]
    _ ≤ η (V ∩ U) := hopen _ (hV.inter hU) inter_subset_right
    _ ≤ η V := measure_mono inter_subset_left

/-- The Riesz measure of the truncated odometer lies between the measure
restricted to the selected components and the original measure. -/
theorem odometer_indicator_union_components_hasLaplacian_sandwich
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {R βminus βplus : ℝ} (hR : 0 < R) (hV : VolumeGrowth μ R βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) {t : ℝ} (ht : 0 < t)
    {U Λ : Set ℂ} (hU : IsOpen U) (hUsub : U ⊆ ball (0 : ℂ) R)
    (hΛsub : Λ ⊆ U ∩ cluster μ R z t)
    (hcomp : ∀ x ∈ Λ, connectedComponentIn (U ∩ cluster μ R z t) x ⊆ Λ)
    (hzΛ : z ∉ Λ) :
    ∃ η : Measure ℂ, μ.restrict Λ ≤ η ∧ η ≤ μ ∧ η.restrict U = η ∧
      HasLaplacian (Λ.indicator (odometer μ R z t)) η 0 U := by
  obtain ⟨η, hη, hηU, hΔ⟩ := odometer_indicator_union_components_hasLaplacian_dominated
    hμ hR hV hz ht hU hUsub hΛsub hcomp hzΛ
  have hνU : (μ.restrict Λ) Uᶜ = 0 := by
    rw [Measure.restrict_apply hU.isClosed_compl.measurableSet]
    exact measure_mono_null (show Uᶜ ∩ Λ ⊆ ∅ from
      fun x hx => (hx.1 ((hΛsub hx.2).1)).elim) (measure_empty)
  have hge := odometer_indicator_union_components_laplacianGE_restrict_of_pole_not_mem
    hμ hR hV hz ht hU hUsub hΛsub hcomp hzΛ
  have hηloc : IsLocallyFiniteMeasure η := by
    let : IsLocallyFiniteMeasure μ := hμ
    exact Measure.isLocallyFiniteMeasure_of_le hη
  exact ⟨η, measure_le_of_laplacianGE_hasLaplacian hU hηloc hνU hge hΔ, hη, hηU, hΔ⟩

end HarmonicBalls
