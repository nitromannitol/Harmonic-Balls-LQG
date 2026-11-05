import HarmonicBalls.Proofs.Sec5.RestrictedContainmentTest

/-! # Locality of general-domain cluster containment

The countable restricted-disc test supplies local representatives for regularized
clusters. Strong compatibility transfers them to the general-domain cluster.
The volume-growth and Section 5 statements remain explicit hypotheses.
-/

namespace HarmonicBalls

open MeasureTheory Set Filter

universe u

/-- General-domain cluster containment is field-local, conditional on volume
 growth, existence of regularized clusters, and strong compatibility. The LQG
 measure locality input in the resulting step remains staged. -/
theorem clusterContainmentLocality_of_steps
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h55 : ExistenceHarmonicBallsStmt.{u})
    (h58 : ClusterStrongCompatibilityStmt.{u}) :
    ClusterContainmentLocalityStep.{u} := by
  classical
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ hloc U hU hUb x hx t ht
  let Λ : Ω → ℂ → ℝ → Set ℂ := fun ω z =>
    if h : ∃ A, IsRegularizedClusterFamily (μ ω) A z then Classical.choose h else fun _ => ∅
  have hΛ : ∀ᵐ ω ∂P, ∀ z, IsRegularizedClusterFamily (μ ω) (Λ ω z) z := by
    filter_upwards [h55 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hω
    intro z
    dsimp only [Λ]
    simpa only [dite_eq_left (hω z)] using Classical.choose_spec (hω z)
  obtain ⟨F, hF, hFeq⟩ := exists_local_lqg_bounded_compactContainmentFamily_representative
    hI2 hγ hγ2 hα hGFF hμ hloc hU hUb hΛ
  let p : U × Ioi (0 : ℝ) := (⟨x, hx⟩, ⟨t, ht⟩)
  let E : Set Ω := {ω | F ω p}
  have hE : MeasurableSet[fieldSigmaAlgebra α₀ hC U] E := by
    let : MeasurableSpace Ω := fieldSigmaAlgebra α₀ hC U
    exact ((measurable_pi_apply p).comp hF).setOf
  refine ⟨E, hE, ?_⟩
  filter_upwards [hFeq, h58 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ Λ hΛ U hU hUb] with ω hf hc
  apply propext
  have he := hf p
  have hcompat := hc t ht x hx
  change (closure (clusterOn (μ ω) U x t) ⊆ U) ↔ F ω p
  constructor
  · intro h
    apply he.mpr
    exact (hcompat (Or.inr h)) ▸ h
  · intro h
    have h' := he.mp h
    exact (hcompat (Or.inl h')) ▸ h'

/-- Proposition 1.3 follows from the numbered upstream inputs and the staged
locality of LQG masses, without a separate containment-measurability premise. -/
theorem harmonicBallLocalSet_of_volumeGrowth_and_compatibility
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h55 : ExistenceHarmonicBallsStmt.{u})
    (h56 : UniquenessHarmonicBallsStmt.{u})
    (h58 : ClusterStrongCompatibilityStmt.{u})
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureLocality P γ α₀ hC hcirc) : HarmonicBallLocalSetStmt.{u} :=
  harmonicBallLocalSet_of_steps h58 h55 h56
    (clusterContainmentLocality_of_steps hI2 h55 h58) hmeasure

#print axioms clusterContainmentLocality_of_steps
#print axioms harmonicBallLocalSet_of_volumeGrowth_and_compatibility

end HarmonicBalls
