import HarmonicBalls.Proofs.Sec5.DominatedShiftCompatibility
import HarmonicBalls.Proofs.Sec5.RestrictedFamilyRepresentation
import HarmonicBalls.Proofs.Sec5.ClusterMeasurability

/-! # Field-local representatives for compactly contained cluster families

The disc clusters of a restricted LQG measure admit a field-local representative.
This gives a representative for every compactly contained member of an existing
regularized family, with one exceptional event for all centres and times.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

universe u

/-- The disc cluster family of the restriction to an open set is represented
by a measurable function of the field on that set. -/
theorem exists_local_lqg_restricted_clusterFamily_representative
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc)
    {U : Set ℂ} (hU : IsOpen U) {R : ℝ} (hR : 0 < R) :
    ∃ F : Ω → (ball (0 : ℂ) R × Ioi (0 : ℝ) → Set ℂ),
      Measurable[fieldSigmaAlgebra α₀ hC U] F ∧
      ∀ᵐ ω ∂P, F ω = fun p => cluster ((μ ω).restrict U) R p.1 p.2 := by
  obtain ⟨F, hF, hFeq⟩ := exists_local_lqg_restricted_nonCoincidenceFamily_representative
    hI2 hγ hγ2 hα hGFF hμ hloc hU hR
  obtain ⟨βm, βp, hae⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  refine ⟨F, hF, ?_⟩
  filter_upwards [hFeq, hae] with ω hFω hω
  funext p
  rw [hFω]
  exact (cluster_eq_nonCoincidenceSet_of_dominated hω.1 hR (hω.2 R hR)
    Measure.restrict_le_self p.2.property.le).symm

/-- A field-local representative agrees with every regularized family member
whose closure is contained in both the open set and the chosen disc. The
agreement is simultaneous for all disc centres and positive times. -/
theorem exists_local_lqg_compact_regularizedFamily_representative
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc)
    {U : Set ℂ} (hU : IsOpen U) {R : ℝ} (hR : 0 < R)
    {Λ : Ω → ℂ → ℝ → Set ℂ}
    (hΛ : ∀ᵐ ω ∂P, ∀ z, IsRegularizedClusterFamily (μ ω) (Λ ω z) z) :
    ∃ F : Ω → (ball (0 : ℂ) R × Ioi (0 : ℝ) → Set ℂ),
      Measurable[fieldSigmaAlgebra α₀ hC U] F ∧
      ∀ᵐ ω ∂P, ∀ p : ball (0 : ℂ) R × Ioi (0 : ℝ),
        closure (Λ ω p.1 p.2) ⊆ U → closure (Λ ω p.1 p.2) ⊆ ball 0 R →
        F ω p = Λ ω p.1 p.2 := by
  obtain ⟨F, hF, hFeq⟩ := exists_local_lqg_restricted_clusterFamily_representative
    hI2 hγ hγ2 hα hGFF hμ hloc hU hR
  obtain ⟨βm, βp, hae⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  refine ⟨fun ω p => denseSequenceRegularization (F ω p),
    measurable_denseSequenceRegularization_family.comp hF, ?_⟩
  filter_upwards [hFeq, hae, hΛ] with ω hFω hω hΛω
  intro p hclU hclR
  have hopen : IsOpen (cluster (μ ω) R p.1 p.2) := by
    rw [(obstacleCompatibilityShiftStep_holds (μ ω) hω.1 R βm βp hR
      (hω.2 R hR) p.1 p.1.property p.2 p.2.property).2.2.1]
    exact isOpen_nonCoincidenceSet_of obstacleLeastSuperharmonicMajorantGeneral_holds
      hω.1 hR (hω.2 R hR) p.1.property p.2.property
  have hv := (leastSupersolution_mem_of_general obstacleLeastSuperharmonicMajorantGeneral_holds
    obstacleCompatibilityShiftStep_holds hω.1 hR (hω.2 R hR) p.1.property p.2.property).2.2
  have hΛR := (hΛω p.1).2.2 p.2 p.2.property R hR hclR R le_rfl
  have hclosure : closure (Λ ω p.1 p.2) = closure (cluster (μ ω) R p.1 p.2) := by
    rw [hΛR, closure_regularizedCluster_eq_of_isOpen hopen]
  have hcluster := cluster_restrict_eq_of_closure_subset hU p.1.property p.2.property.le hv
    (hclosure ▸ hclU) (hclosure ▸ hclR)
  have hregular := regularizedFamily_eq_regularizedCluster_restrict_of_volumeGrowth
    hω.1 hU hR (hω.2 R hR) (hΛω p.1) p.2 p.2.property hclU hclR
  have hopen' : IsOpen (cluster ((μ ω).restrict U) R p.1 p.2) := hcluster ▸ hopen
  rw [hFω, denseSequenceRegularization_eq hopen']
  exact hregular.symm

/-- On a bounded open set, a single field-local representative agrees with
all members of an existing regularized family compactly contained in the set,
simultaneously for every centre and positive time. -/
theorem exists_local_lqg_bounded_compact_regularizedFamily_representative
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {Λ : Ω → ℂ → ℝ → Set ℂ}
    (hΛ : ∀ᵐ ω ∂P, ∀ z, IsRegularizedClusterFamily (μ ω) (Λ ω z) z) :
    ∃ F : Ω → (ℂ × Ioi (0 : ℝ) → Set ℂ),
      Measurable[fieldSigmaAlgebra α₀ hC U] F ∧
      ∀ᵐ ω ∂P, ∀ z : ℂ, ∀ t : Ioi (0 : ℝ), closure (Λ ω z t) ⊆ U →
        F ω (z, t) = Λ ω z t := by
  classical
  obtain ⟨r, hr⟩ := hUb.subset_ball (0 : ℂ)
  let R := max 1 r + 1
  have hR : 0 < R := by
    have h := le_max_left (1 : ℝ) r
    dsimp [R]
    linarith
  have hrR : r ≤ R := by
    have h := le_max_right (1 : ℝ) r
    dsimp [R]
    linarith
  have hUR : U ⊆ ball (0 : ℂ) R := hr.trans (ball_subset_ball hrR)
  obtain ⟨G, hG, hGeq⟩ := exists_local_lqg_compact_regularizedFamily_representative
    hI2 hγ hγ2 hα hGFF hμ hloc hU hR hΛ
  let F : Ω → (ℂ × Ioi (0 : ℝ) → Set ℂ) := fun ω p =>
    if hp : p.1 ∈ ball (0 : ℂ) R then G ω (⟨p.1, hp⟩, p.2) else ∅
  have hF : Measurable[fieldSigmaAlgebra α₀ hC U] F := by
    let : MeasurableSpace Ω := fieldSigmaAlgebra α₀ hC U
    apply Measurable.of_eval
    intro p
    by_cases hp : p.1 ∈ ball (0 : ℂ) R
    · simpa only [F, dite_eq_left hp, Function.comp_def] using (measurable_pi_apply (⟨p.1, hp⟩, p.2)).comp hG
    · simpa only [F, dite_eq_right hp] using (measurable_const : Measurable (fun _ : Ω => (∅ : Set ℂ)))
  refine ⟨F, hF, ?_⟩
  filter_upwards [hGeq, hΛ] with ω hGω hΛω
  intro z t hclU
  have hzR : z ∈ ball (0 : ℂ) R :=
    hUR (hclU (subset_closure ((hΛω z).1.mem t t.property)))
  have heq := hGω (⟨z, hzR⟩, t) hclU (hclU.trans hUR)
  simpa only [F, dite_eq_left hzR] using heq

end HarmonicBalls
