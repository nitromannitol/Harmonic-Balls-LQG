import HarmonicBalls.Proofs.Sec5.CompactFamilyMeasureLocality

/-! # Locality through first contact

Agreement of measures on an open set determines both compact containment
and the regularized family up to its first contact with the complement.
Equality at contact uses the continuity assumed in the family definition.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter TopologicalSpace

/-- Compact containment of a regularized cluster is determined by the
restricted measure. -/
theorem regularizedFamily_containment_iff_of_restrict_eq
    {μ ν : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {U : Set ℂ} (hU : IsOpen U) (hμν : μ.restrict U = ν.restrict U)
    {z : ℂ} {t : ℝ} (ht : 0 < t) {Λ Λ' : ℝ → Set ℂ}
    (hΛ : IsRegularizedClusterFamily μ Λ z) (hΛ' : IsRegularizedClusterFamily ν Λ' z) :
    closure (Λ t) ⊆ U ↔ closure (Λ' t) ⊆ U := by
  constructor
  · intro hcl
    have heq := regularizedFamily_eq_of_restrict_eq_of_volumeGrowth hμ hν hVμ hVν hU
      hμν ht hΛ hΛ' hcl
    simpa only [← heq] using hcl
  · intro hcl
    have heq := regularizedFamily_eq_of_restrict_eq_of_volumeGrowth hν hμ hVν hVμ hU
      hμν.symm ht hΛ' hΛ hcl
    simpa only [← heq] using hcl

/-- Agreement of measures determines the regularized family through a
positive time whose preceding clusters are compactly contained in the domain.
The endpoint is included using the families' assumed Hausdorff continuity. -/
theorem regularizedFamily_eq_through_contact_of_restrict_eq
    {μ ν : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {U : Set ℂ} (hU : IsOpen U) (hμν : μ.restrict U = ν.restrict U)
    {z : ℂ} {T : ℝ} (hT : 0 < T) {Λ Λ' : ℝ → Set ℂ}
    (hΛ : IsRegularizedClusterFamily μ Λ z) (hΛ' : IsRegularizedClusterFamily ν Λ' z)
    (hbefore : ∀ t ∈ Ioo (0 : ℝ) T, closure (Λ t) ⊆ U) :
    EqOn Λ Λ' (Ioc 0 T) := by
  have heq : EqOn (fun t => Closeds.closure (Λ t)) (fun t => Closeds.closure (Λ' t))
      (Ioo (0 : ℝ) T) := by
    intro t ht
    change Closeds.closure (Λ t) = Closeds.closure (Λ' t)
    rw [regularizedFamily_eq_of_restrict_eq_of_volumeGrowth hμ hν hVμ hVν hU
      hμν ht.1 hΛ hΛ' (hbefore t ht)]
  have hc := hausdorffContinuousOn_iff_continuousOn_closure.mp hΛ.1.hausdorffContinuousOn
  have hc' := hausdorffContinuousOn_iff_continuousOn_closure.mp hΛ'.1.hausdorffContinuousOn
  have hsub : Ioc (0 : ℝ) T ⊆ closure (Ioo 0 T) := by
    rw [closure_Ioo hT.ne]
    exact Ioc_subset_Icc_self
  have hext := heq.of_subset_closure (hc.mono Ioc_subset_Ioi_self)
    (hc'.mono Ioc_subset_Ioi_self) Ioo_subset_Ioc_self hsub
  intro t ht
  have hclosed : closure (Λ t) = closure (Λ' t) :=
    congrArg (fun K : Closeds ℂ => (K : Set ℂ)) (hext ht)
  calc
    Λ t = interior (closure (Λ t)) := (hΛ.1.isRegularOpen t ht.1).symm
    _ = interior (closure (Λ' t)) := congrArg interior hclosed
    _ = Λ' t := hΛ'.1.isRegularOpen t ht.1

universe u

/-- For two LQG fields with equal restricted measures, the containment and
contact-time conclusions hold simultaneously for all centres and times. -/
theorem ae_regularizedFamily_locality_through_contact
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC hC' : Ω → (ℂ → ℝ) → ℝ} {hcirc hcirc' : Ω → ℝ → ℂ → ℝ}
    {μ ν : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hGFF' : IsWholePlaneGFF P hC' hcirc')
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hν : IsLQGMeasureOfField P γ α₀ hcirc' ν)
    {U : Set ℂ} (hU : IsOpen U) (hloc : ∀ᵐ ω ∂P, (μ ω).restrict U = (ν ω).restrict U)
    {Λ Λ' : Ω → ℂ → ℝ → Set ℂ}
    (hΛ : ∀ᵐ ω ∂P, ∀ z, IsRegularizedClusterFamily (μ ω) (Λ ω z) z)
    (hΛ' : ∀ᵐ ω ∂P, ∀ z, IsRegularizedClusterFamily (ν ω) (Λ' ω z) z) :
    ∀ᵐ ω ∂P, ∀ z : ℂ,
      (∀ t : ℝ, 0 < t → (closure (Λ ω z t) ⊆ U ↔ closure (Λ' ω z t) ⊆ U)) ∧
      (∀ T : ℝ, 0 < T → (∀ t ∈ Ioo (0 : ℝ) T, closure (Λ ω z t) ⊆ U) →
        EqOn (Λ ω z) (Λ' ω z) (Ioc 0 T)) := by
  obtain ⟨βm, βp, hVμ⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  obtain ⟨βm', βp', hVν⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF' hν
  filter_upwards [hVμ, hVν, hloc, hΛ, hΛ'] with ω hμω hνω hμνω hΛω hΛ'ω
  intro z
  constructor
  · intro t ht
    exact regularizedFamily_containment_iff_of_restrict_eq hμω.1 hνω.1 hμω.2 hνω.2 hU
      hμνω ht (hΛω z) (hΛ'ω z)
  · intro T hT hbefore
    exact regularizedFamily_eq_through_contact_of_restrict_eq hμω.1 hνω.1 hμω.2 hνω.2 hU
      hμνω hT (hΛω z) (hΛ'ω z) hbefore

/-- If two fields have locally equal sufficiently small circle averages,
their regularized families have the same containment times and agree through
contact, simultaneously for all centres. -/
theorem ae_regularizedFamily_locality_through_contact_of_circle_averages
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC hC' : Ω → (ℂ → ℝ) → ℝ} {hcirc hcirc' : Ω → ℝ → ℂ → ℝ}
    {μ ν : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hGFF' : IsWholePlaneGFF P hC' hcirc')
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hν : IsLQGMeasureOfField P γ α₀ hcirc' ν)
    {U : Set ℂ} (hU : IsOpen U)
    (hloc : ∀ᵐ ω ∂P, ∀ K : Set ℂ, IsCompact K → K ⊆ U →
      ∀ᶠ k : ℕ in atTop, ∀ z ∈ K,
        fieldCircleAverage α₀ (hcirc ω) (dyadicScale k) z =
          fieldCircleAverage α₀ (hcirc' ω) (dyadicScale k) z)
    {Λ Λ' : Ω → ℂ → ℝ → Set ℂ}
    (hΛ : ∀ᵐ ω ∂P, ∀ z, IsRegularizedClusterFamily (μ ω) (Λ ω z) z)
    (hΛ' : ∀ᵐ ω ∂P, ∀ z, IsRegularizedClusterFamily (ν ω) (Λ' ω z) z) :
    ∀ᵐ ω ∂P, ∀ z : ℂ,
      (∀ t : ℝ, 0 < t → (closure (Λ ω z t) ⊆ U ↔ closure (Λ' ω z t) ⊆ U)) ∧
      (∀ T : ℝ, 0 < T → (∀ t ∈ Ioo (0 : ℝ) T, closure (Λ ω z t) ⊆ U) →
        EqOn (Λ ω z) (Λ' ω z) (Ioc 0 T)) := by
  have heq : ∀ᵐ ω ∂P, (μ ω).restrict U = (ν ω).restrict U := by
    filter_upwards [hμ, hν, hloc] with ω hμω hνω hlocω
    exact hμω.restrict_eq hνω hU hlocω
  exact ae_regularizedFamily_locality_through_contact hI2 hγ hγ2 hα hGFF hGFF'
    hμ hν hU heq hΛ hΛ'

end HarmonicBalls
