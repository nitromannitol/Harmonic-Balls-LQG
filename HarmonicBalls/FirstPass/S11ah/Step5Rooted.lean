import HarmonicBalls.FirstPass.S11ah.Step5Local
import HarmonicBalls.FirstPass.S11r.RootedJoint

/-!
# Step 5 for the rooted decoders, Ω-indexed form

Rooted analogue of `exists_modified_failureSet_closed_localCert` (`S11ah/Step5Local.lean`), for the rooted decoders
`ω ↦ decoderOn (ball c₂ r₂) (m (campbellReferenceObs γ α (ball c₂ r₂) (hC ω) z).2)` at a root `z`. The index is the sample
point `ω`: no pushforward of `P` to the observables is used.

Input: `RootedLengthPropertyStmt` (the rooted length property, for Lebesgue-a.e. root and `P`-a.s. sample). It is
proved in `S11ah/RootedLengthProperty.lean` (`rootedLengthProperty`) from identity (20) of `LocalMetricReplacementStmt`,
the frozen rooted continuity `RootedPhysicalMetricContinuousAtInsertionFrozen` and the LQG axiom I; that file also gives
`exists_modified_failureSet_rooted_localCert_discharged`, this theorem with the hypothesis `hLen` discharged.
Identity (20) is not used by the Step 5 argument itself.
-/

open MeasureTheory ProbabilityTheory Metric Set Filter Topology HarmonicBalls
open scoped ENNReal

namespace FirstPassS11ah

/-- **The rooted length property** (proved as `rootedLengthProperty`, `S11ah/RootedLengthProperty.lean`). For Lebesgue-a.e. root `z` in `ball c₁ r₁`, `P`-almost
surely in the sample `ω`, the rooted decoder `decoderOn (ball c₂ r₂) (m (campbellReferenceObs γ α (ball c₂ r₂) (hC ω) z).2)`
is a Euclidean length metric on `ball c₂ r₂` (`IsLengthMetricOn`). Its fields not supplied by identity (20) are the
non-degeneracy `eq_of_eq_zero` and the Euclidean topology `isOpen_iff`. -/
def RootedLengthPropertyStmt {Ω : Type} [MeasurableSpace Ω] (γ α : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ) (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ)
    (m : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) →
      ContinuousMap ↥(ball c₂ r₂ ×ˢ ball c₂ r₂ : Set (ℂ × ℂ)) ℝ) : Prop :=
  ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ᵐ ω ∂P,
    IsLengthMetricOn (ball c₂ r₂) (decoderOn (ball c₂ r₂) (m (campbellReferenceObs γ α (ball c₂ r₂) (hC ω) z).2))

/-- **Step 5 for the rooted decoders, Ω-indexed.** For Lebesgue-a.e. root `z` in `ball c₁ r₁`, there is a measurable
modification `D'` of the rooted decoders, with the length property for every `ω`, whose Step 5 failure set is measurable
and agrees, for `P`-a.e. `ω`, with the failure set of the rooted decoders on every section. The rooted length property
`hLen` is the only named input. -/
theorem exists_modified_failureSet_rooted_localCert {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (hr₂ : 0 < r₂) (κ : Kernel Ω ℂ) [IsSFiniteKernel κ]
    (m : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) →
      ContinuousMap ↥(ball c₂ r₂ ×ˢ ball c₂ r₂ : Set (ℂ × ℂ)) ℝ)
    (hm : Measurable m) (hLen : RootedLengthPropertyStmt γ α c₁ c₂ r₁ r₂ P hC m)
    {U V W T Q' Q : Set ℂ} {δ : ℝ} (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    {M : ℝ} (hU : MeasurableSet U) {A : Set ℂ} (hA : MeasurableSet A) (q : ℝ) :
    ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∃ D' : Ω → ℂ → ℂ → ℝ,
      (∀ x ∈ ball c₂ r₂, ∀ y ∈ ball c₂ r₂, Measurable fun ω => D' ω x y) ∧
      (∀ ω, IsLengthMetricOn (ball c₂ r₂) (D' ω)) ∧
      MeasurableSet (failureSet A (fun n x => localCert (ball c₂ r₂) (fun ω => κ ω) D' (pinchOmegaGeom W Q δ)
        U V W T Q' Q δ M n x.2 x.1) q) ∧
      ∀ᵐ ω ∂P, ∀ z' : ℂ,
        ((z', ω) ∈ failureSet A (fun n x => localCert (ball c₂ r₂) (fun ω => κ ω)
            (fun ω => decoderOn (ball c₂ r₂) (m (campbellReferenceObs γ α (ball c₂ r₂) (hC ω) z).2))
            (pinchOmegaGeom W Q δ) U V W T Q' Q δ M n x.2 x.1) q ↔
          (z', ω) ∈ failureSet A (fun n x => localCert (ball c₂ r₂) (fun ω => κ ω) D' (pinchOmegaGeom W Q δ)
            U V W T Q' Q δ M n x.2 x.1) q) := by
  obtain ⟨hOo, h0O, hsph, -⟩ := FirstPassS11ap.pinchOmegaGeom_certificate_data hgeo
  filter_upwards [hLen] with z hz
  have hzmap : Measurable fun ω : Ω => ((z, ω) : ℂ × Ω) := measurable_const.prodMk measurable_id
  have hobs : Measurable fun ω : Ω => campbellReferenceObs γ α (ball c₂ r₂) (hC ω) z :=
    (measurable_campbellReferenceObs_joint P hC hcirc hG γ α (ball c₂ r₂)).comp hzmap
  have hm' : Measurable fun ω : Ω => m (campbellReferenceObs γ α (ball c₂ r₂) (hC ω) z).2 :=
    hm.comp (measurable_snd.comp hobs)
  have hDm := measurable_decoderOn hm'
  obtain ⟨H, hH, hPH, D', hm'', hl, hmeas, hagree⟩ :=
    exists_modified_failureSet_localCert hr₂ κ P (D := fun ω => decoderOn (ball c₂ r₂)
        (m (campbellReferenceObs γ α (ball c₂ r₂) (hC ω) z).2)) hDm hz
      (certificateEventLocality_pinch hgeo) hOo h0O hsph hU hgeo.delta_pos hA q
  refine ⟨D', hm'', hl, hmeas, ?_⟩
  have hHae : ∀ᵐ ω ∂P, ω ∈ H := by
    rw [ae_iff]
    exact hPH
  filter_upwards [hHae] with ω hω
  intro z'
  exact hagree ω hω z'

end FirstPassS11ah
