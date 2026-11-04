import HarmonicBalls.Proofs.Sec5.RestrictedClusterLocality
import HarmonicBalls.Steps.Sec5.StrongCompatibility

/-! # Representation of compactly contained families using restricted measures

A cluster family can be represented by the obstacle cluster of a restricted
measure on any disc that contains it. No cluster family or volume growth is
required for the restricted measure.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

/-- A compactly contained regularized family member equals the regularization
of a disc cluster for the measure restricted to its containing open set. -/
theorem regularizedFamily_eq_regularizedCluster_restrict
    {μ : Measure ℂ} {U : Set ℂ} (hU : IsOpen U) {r t : ℝ} {z : ℂ}
    (hr : 0 < r) (ht : 0 < t) {Λ : ℝ → Set ℂ}
    (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hopen : IsOpen (cluster μ r z t))
    (hv : leastSupersolution μ r z t ∈ supersolutions μ r z t)
    (hclU : closure (Λ t) ⊆ U) (hclr : closure (Λ t) ⊆ ball 0 r) :
    Λ t = regularizedCluster (μ.restrict U) r z t := by
  have hz : z ∈ ball (0 : ℂ) r := hclr (subset_closure (hΛ.1.mem t ht))
  have hΛr := hΛ.2.2 t ht r hr hclr r le_rfl
  have hclosure : closure (Λ t) = closure (cluster μ r z t) := by
    rw [hΛr, closure_regularizedCluster_eq_of_isOpen hopen]
  have heq := cluster_restrict_eq_of_closure_subset hU hz ht.le hv
    (hclosure ▸ hclU) (hclosure ▸ hclr)
  rw [hΛr, regularizedCluster, heq, ← regularizedCluster]

/-- The representation holds for all positive times for which the family is
compactly contained in the open set and the chosen disc. -/
theorem regularizedFamily_eq_regularizedCluster_restrict_of_volumeGrowth
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {U : Set ℂ} (hU : IsOpen U) {r βm βp : ℝ} (hr : 0 < r)
    (hV : VolumeGrowth μ r βm βp) {z : ℂ} {Λ : ℝ → Set ℂ}
    (hΛ : IsRegularizedClusterFamily μ Λ z) :
    ∀ t : ℝ, 0 < t → closure (Λ t) ⊆ U → closure (Λ t) ⊆ ball 0 r →
      Λ t = regularizedCluster (μ.restrict U) r z t := by
  intro t ht hclU hclr
  have hz : z ∈ ball (0 : ℂ) r := hclr (subset_closure (hΛ.1.mem t ht))
  have hopen : IsOpen (cluster μ r z t) := by
    rw [(obstacleCompatibilityShiftStep_holds μ hμ r βm βp hr hV z hz t ht).2.2.1]
    exact isOpen_nonCoincidenceSet_of obstacleLeastSuperharmonicMajorantGeneral_holds
      hμ hr hV hz ht
  have hv := (leastSupersolution_mem_of_general obstacleLeastSuperharmonicMajorantGeneral_holds
    obstacleCompatibilityShiftStep_holds hμ hr hV hz ht).2.2
  exact regularizedFamily_eq_regularizedCluster_restrict hU hr ht hΛ hopen hv hclU hclr

/-- One compact-containment hypothesis at time `T` gives the representation
at every positive earlier time, including `T`. -/
theorem regularizedFamily_eq_regularizedCluster_restrict_through_time
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {U : Set ℂ} (hU : IsOpen U) {r βm βp : ℝ} (hr : 0 < r)
    (hV : VolumeGrowth μ r βm βp) {z : ℂ} {Λ : ℝ → Set ℂ}
    (hΛ : IsRegularizedClusterFamily μ Λ z) {T : ℝ} (hT : 0 < T)
    (hclU : closure (Λ T) ⊆ U) (hclr : closure (Λ T) ⊆ ball 0 r) :
    EqOn Λ (fun t => regularizedCluster (μ.restrict U) r z t) (Ioc 0 T) := by
  intro t ht
  have hsub : closure (Λ t) ⊆ closure (Λ T) :=
    closure_mono (hΛ.1.monotoneOn ht.1 hT ht.2)
  exact regularizedFamily_eq_regularizedCluster_restrict_of_volumeGrowth
    hμ hU hr hV hΛ t ht.1 (hsub.trans hclU) (hsub.trans hclr)

universe u

/-- For an LQG measure, the representation holds simultaneously for all open
sets, enclosing discs, centres and positive times. -/
theorem ae_regularizedFamily_eq_regularizedCluster_restrict
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {Λ : Ω → ℂ → ℝ → Set ℂ}
    (hΛ : ∀ᵐ ω ∂P, ∀ z, IsRegularizedClusterFamily (μ ω) (Λ ω z) z) :
    ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → ∀ r : ℝ, 0 < r → ∀ z : ℂ, ∀ t : ℝ,
      0 < t → closure (Λ ω z t) ⊆ U → closure (Λ ω z t) ⊆ ball 0 r →
      Λ ω z t = regularizedCluster ((μ ω).restrict U) r z t := by
  obtain ⟨βm, βp, hae⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hae, hΛ] with ω hω hΛω
  intro U hU r hr z
  exact regularizedFamily_eq_regularizedCluster_restrict_of_volumeGrowth
    hω.1 hU hr (hω.2 r hr) (hΛω z)

end HarmonicBalls
