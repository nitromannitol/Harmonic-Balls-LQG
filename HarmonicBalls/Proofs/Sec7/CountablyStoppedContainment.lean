import HarmonicBalls.Proofs.Sec7.StoppedLocalContainment

/-! # Countably selected local containment

Field-measurable selection among countably many centres and positive random
times preserves the local containment event and its family representative.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

universe u

/-- Countably many field-local stopping rules can be selected using a
field-measurable index. The containment event and the stopped family then
have field-local representatives on one common full-measure event. -/
theorem exists_fieldLocal_countably_selected_containment_and_family
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {Λ : Ω → ℂ → ℝ → Set ℂ}
    (hΛ : ∀ᵐ ω ∂P, ∀ z, IsRegularizedClusterFamily (μ ω) (Λ ω z) z)
    (z : ℕ → U) (τ : ℕ → Ω → Ioi (0 : ℝ))
    (hτ : ∀ n, Measurable[fieldSigmaAlgebra α₀ hC U] (τ n))
    (κ : Ω → ℕ) (hκ : Measurable[fieldSigmaAlgebra α₀ hC U] κ) :
    ∃ E : Set Ω, ∃ F : Ω → Set ℂ,
      MeasurableSet[fieldSigmaAlgebra α₀ hC U] E ∧
      Measurable[fieldSigmaAlgebra α₀ hC U] F ∧
      ∀ᵐ ω ∂P, (ω ∈ E ↔ closure (Λ ω (z (κ ω)) (τ (κ ω) ω)) ⊆ U) ∧
        (ω ∈ E → F ω = Λ ω (z (κ ω)) (τ (κ ω) ω)) := by
  classical
  have hex : ∀ n, ∃ E : Set Ω, ∃ F : Ω → Set ℂ,
      MeasurableSet[fieldSigmaAlgebra α₀ hC U] E ∧
      Measurable[fieldSigmaAlgebra α₀ hC U] F ∧
      ∀ᵐ ω ∂P, (ω ∈ E ↔ closure (Λ ω (z n) (τ n ω)) ⊆ U) ∧
        (ω ∈ E → F ω = Λ ω (z n) (τ n ω)) := fun n =>
    exists_fieldLocal_stopped_containment_and_family hI2 hfull hγ hγ2 hα hGFF hμ
      hloc hU hUb hΛ (z n) (τ n) (hτ n)
  choose E F hE hF hEF using hex
  let E' : Set Ω := {ω | ∃ n, κ ω = n ∧ ω ∈ E n}
  let F' : Ω → Set ℂ := fun ω => {x | ∃ n, κ ω = n ∧ x ∈ F n ω}
  have hE' : MeasurableSet[fieldSigmaAlgebra α₀ hC U] E' := by
    let : MeasurableSpace Ω := fieldSigmaAlgebra α₀ hC U
    apply measurableSet_setOfPred.mpr
    apply Measurable.exists
    intro n
    exact (measurableSet_setOfPred.mp (hκ (measurableSet_singleton n))).and
      (measurableSet_setOfPred.mp (hE n))
  have hF' : Measurable[fieldSigmaAlgebra α₀ hC U] F' := by
    let : MeasurableSpace Ω := fieldSigmaAlgebra α₀ hC U
    apply Measurable.of_eval
    intro x
    change Measurable (fun ω => ∃ n, κ ω = n ∧ x ∈ F n ω)
    apply Measurable.exists
    intro n
    apply Measurable.and
    · exact measurableSet_setOfPred.mp (hκ (measurableSet_singleton n))
    · exact (measurable_pi_apply x).comp (hF n)
  refine ⟨E', F', hE', hF', ?_⟩
  filter_upwards [ae_all_iff.mpr hEF] with ω hω
  have hmem : ω ∈ E' ↔ ω ∈ E (κ ω) := by
    simp only [E', mem_ofPred_eq]
    constructor
    · rintro ⟨n, hn, he⟩
      simpa only [← hn] using he
    · intro he
      exact ⟨κ ω, rfl, he⟩
  refine ⟨hmem.trans (hω (κ ω)).1, ?_⟩
  intro he
  have hval : F' ω = F (κ ω) ω := by
    ext x
    simp only [F', mem_ofPred_eq]
    constructor
    · rintro ⟨n, hn, hx⟩
      simpa only [← hn] using hx
    · intro hx
      exact ⟨κ ω, rfl, hx⟩
  rw [hval]
  exact (hω (κ ω)).2 (hmem.mp he)

#print axioms exists_fieldLocal_countably_selected_containment_and_family

end HarmonicBalls
