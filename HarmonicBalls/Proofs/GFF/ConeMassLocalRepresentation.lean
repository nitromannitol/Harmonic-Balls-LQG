import HarmonicBalls.Proofs.GFF.FixedShiftCircleLQGRepresentation
import HarmonicBalls.Steps.Sec11.PinchLocalData
import HarmonicBalls.Steps.Sec11.PinchGreenMeasurable

/-! # Local cone mass observables

The imported fixed-shift decoder uses Leonardo Bonanno's LatticeProb
formalization. The extended Green kernel retains its infinite diagonal.
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace HarmonicBalls

/-- The cone mass event depends only on the restriction to any measurable set
containing both the cone annulus and the Green-potential annulus. -/
theorem coneMassEvent_iff_of_restrict_eq
    {μ ν : Measure ℂ} {U Q : Set ℂ} (M r : ℝ) (z : ℂ)
    (hU : MeasurableSet U)
    (hcone : annulus z r (2 * r) ∩ coneAt Q z ⊆ U)
    (hgreen : annulus z (3 * r) (6 * r) ⊆ U)
    (hlocal : μ.restrict U = ν.restrict U) :
    coneMassEvent μ Q M r z ↔ coneMassEvent ν Q M r z := by
  have hg : μ.restrict (annulus z (3 * r) (6 * r)) =
      ν.restrict (annulus z (3 * r) (6 * r)) := by
    rw [← Measure.restrict_restrict_of_subset hgreen, hlocal,
      Measure.restrict_restrict_of_subset hgreen]
  have hm : μ (annulus z r (2 * r) ∩ coneAt Q z) =
      ν (annulus z r (2 * r) ∩ coneAt Q z) := by
    have h := congrArg (fun m : Measure ℂ => m (annulus z r (2 * r) ∩ coneAt Q z)) hlocal
    simpa only [Measure.restrict_apply' hU, inter_eq_self_of_subset_left hcone] using h
  simp only [coneMassEvent, annulusGreenPotentialSup_eq_of_restrict_eq z _ _ hg, hm]

/-- The cone mass event is measurable as a function of the measure when the
cone annulus is Borel. -/
theorem measurableSet_coneMassEvent (Q : Set ℂ) (M r : ℝ) (z : ℂ)
    (hQ : MeasurableSet (annulus z r (2 * r) ∩ coneAt Q z)) :
    MeasurableSet {μ : Measure ℂ | coneMassEvent μ Q M r z} := by
  exact measurableSet_le (measurable_const.mul (measurable_annulusGreenPotentialSup z _ _))
    (Measure.measurable_coe hQ)

/-- A normalized local restriction encodes the original event when the
reference mass is positive and finite. -/
theorem coneMassEvent_normalizedRestriction_iff
    (μ : Measure ℂ) {U Q : Set ℂ} (M r : ℝ) (z : ℂ)
    (hU : MeasurableSet U)
    (hcone : annulus z r (2 * r) ∩ coneAt Q z ⊆ U)
    (hgreen : annulus z (3 * r) (6 * r) ⊆ U)
    (hzero : μ U ≠ 0) (htop : μ U ≠ ∞) :
    coneMassEvent (normalizedRestriction μ U) Q M r z ↔ coneMassEvent μ Q M r z := by
  have hlocal : (normalizedRestriction μ U).restrict U = ((μ U)⁻¹ • μ).restrict U := by
    rw [normalizedRestriction, Measure.restrict_smul,
      Measure.restrict_restrict_of_subset (Subset.refl U), Measure.restrict_smul]
  exact (coneMassEvent_iff_of_restrict_eq M r z hU hcone hgreen hlocal).trans
    (coneMassEvent_smul_iff μ Q M r z (ENNReal.inv_ne_zero.mpr htop)
      (ENNReal.inv_ne_top.mpr hzero))

/-- A common measurable decoder of normalized local measures produces both
cone-event representations, with an arbitrary deterministic insertion. -/
theorem coneMassEvent_representation_of_measure_decoder
    {Ω Ξ κ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) (P' : Measure Ξ) (X : Ω → κ → ℝ) (X' : Ξ → κ → ℝ)
    (k : κ → ℝ) (D : (κ → ℝ) → Measure ℂ) (hD : Measurable D)
    (μ : Ω → Measure ℂ) (ν : Ξ → Measure ℂ) {U Q : Set ℂ}
    (M r : ℝ) (z : ℂ) (hU : MeasurableSet U)
    (hQ : MeasurableSet (annulus z r (2 * r) ∩ coneAt Q z))
    (hcone : annulus z r (2 * r) ∩ coneAt Q z ⊆ U)
    (hgreen : annulus z (3 * r) (6 * r) ⊆ U)
    (hμ : ∀ᵐ ω ∂P, μ ω U ≠ 0 ∧ μ ω U ≠ ∞ ∧
      D (X ω) = normalizedRestriction (μ ω) U)
    (hν : ∀ᵐ ω ∂P', ν ω U ≠ 0 ∧ ν ω U ≠ ∞ ∧
      D (X' ω) = normalizedRestriction (ν ω) U) :
    ∃ B : Set (κ → ℝ), MeasurableSet B ∧
      (∀ᵐ ω ∂P, coneMassEvent (μ ω) Q M r z ↔ (fun φ => X ω φ + k φ) ∈ B) ∧
      ∀ᵐ ω ∂P', coneMassEvent (ν ω) Q M r z ↔ (fun φ => X' ω φ + k φ) ∈ B := by
  let T : (κ → ℝ) → (κ → ℝ) := fun x φ => x φ - k φ
  have hT : Measurable T := measurable_pi_iff.mpr fun φ =>
    (measurable_pi_apply φ).sub_const _
  refine ⟨(D ∘ T) ⁻¹' {η | coneMassEvent η Q M r z},
    (hD.comp hT) (measurableSet_coneMassEvent Q M r z hQ), ?_, ?_⟩
  · filter_upwards [hμ] with ω hω
    have heq : T (fun φ => X ω φ + k φ) = X ω := by
      funext φ
      simp [T]
    change coneMassEvent (μ ω) Q M r z ↔ coneMassEvent (D (T _)) Q M r z
    rw [heq, hω.2.2]
    exact (coneMassEvent_normalizedRestriction_iff (μ ω) M r z hU hcone hgreen
      hω.1 hω.2.1).symm
  · filter_upwards [hν] with ω hω
    have heq : T (fun φ => X' ω φ + k φ) = X' ω := by
      funext φ
      simp [T]
    change coneMassEvent (ν ω) Q M r z ↔ coneMassEvent (D (T _)) Q M r z
    rw [heq, hω.2.2]
    exact (coneMassEvent_normalizedRestriction_iff (ν ω) M r z hU hcone hgreen
      hω.1 hω.2.1).symm

#print axioms coneMassEvent_representation_of_measure_decoder
#print axioms coneMassEvent_iff_of_restrict_eq
#print axioms measurableSet_coneMassEvent
#print axioms coneMassEvent_normalizedRestriction_iff

end HarmonicBalls
