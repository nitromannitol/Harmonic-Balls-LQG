import HarmonicBalls.Proofs.Sec5.LocalCompactFamilyRepresentative

/-! # Local representatives at random times

A countable union of earlier family members gives a field-local representative
at a positive random time. Left continuity and compact containment remain
explicit hypotheses; no continuity at boundary contact is used.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

universe u

/-- A regularized family at a positive field-measurable random time has a
field-local representative on the event of compact containment, provided
that the member at that time is the union of its earlier rational members.
The same exceptional event works for the given centre and random time. -/
theorem exists_fieldLocal_stopped_regularizedFamily_representative
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {Λ : Ω → ℂ → ℝ → Set ℂ}
    (hΛ : ∀ᵐ ω ∂P, ∀ z, IsRegularizedClusterFamily (μ ω) (Λ ω z) z)
    (z : ℂ) (τ : Ω → Ioi (0 : ℝ))
    (hτ : Measurable[fieldSigmaAlgebra α₀ hC U] τ)
    (hleft : ∀ᵐ ω ∂P, closure (Λ ω z (τ ω)) ⊆ U → Λ ω z (τ ω) =
      ⋃ q : {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < τ ω}, Λ ω z q) :
    ∃ F : Ω → Set ℂ, Measurable[fieldSigmaAlgebra α₀ hC U] F ∧
      ∀ᵐ ω ∂P, closure (Λ ω z (τ ω)) ⊆ U → F ω = Λ ω z (τ ω) := by
  classical
  obtain ⟨G, hG, hGeq⟩ := exists_local_lqg_bounded_compact_regularizedFamily_representative
    hI2 hγ hγ2 hα hGFF hμ hloc hU hUb hΛ
  let Q := {q : ℚ // 0 < (q : ℝ)}
  let F : Ω → Set ℂ := fun ω => ⋃ q : Q,
    {x | (q : ℝ) < τ ω ∧ x ∈ G ω (z, ⟨q, q.property⟩)}
  have hF : Measurable[fieldSigmaAlgebra α₀ hC U] F := by
    let : MeasurableSpace Ω := fieldSigmaAlgebra α₀ hC U
    apply Measurable.of_eval
    intro x
    change Measurable (fun ω => x ∈ F ω)
    simp only [F, mem_iUnion, mem_ofPred_eq]
    apply Measurable.exists
    intro q
    apply Measurable.and
    · exact measurableSet_setOfPred.mp (measurableSet_lt measurable_const (measurable_subtype_coe.comp hτ))
    · change Measurable (fun ω => G ω (z, ⟨q, q.property⟩) x)
      have hs : Measurable (fun ω => G ω (z, ⟨(q : ℚ), q.property⟩)) :=
        (measurable_pi_apply (z, (⟨(q : ℚ), q.property⟩ : Ioi (0 : ℝ)))).comp hG
      exact (measurable_pi_apply x).comp hs
  refine ⟨F, hF, ?_⟩
  filter_upwards [hGeq, hΛ, hleft] with ω heq hfamily hleftω hcontain
  rw [hleftω hcontain]
  ext x
  simp only [F, mem_iUnion, mem_ofPred_eq]
  constructor
  · rintro ⟨q, hqt, hx⟩
    have hsub := (hfamily z).1.monotoneOn q.property (τ ω).property hqt.le
    have hq : closure (Λ ω z q) ⊆ U := (closure_mono hsub).trans hcontain
    exact ⟨⟨q, q.property, hqt⟩, (heq z ⟨q, q.property⟩ hq) ▸ hx⟩
  · rintro ⟨q, hx⟩
    have hsub := (hfamily z).1.monotoneOn q.property.1 (τ ω).property q.property.2.le
    have hq : closure (Λ ω z q) ⊆ U := (closure_mono hsub).trans hcontain
    exact ⟨⟨q, q.property.1⟩, q.property.2, (heq z ⟨q, q.property.1⟩ hq).symm ▸ hx⟩

/-- A countably selected centre and positive time have a field-local family
representative on the compact-containment event. This version requires no
left-continuity assumption. -/
theorem exists_fieldLocal_countably_stopped_regularizedFamily_representative
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {Λ : Ω → ℂ → ℝ → Set ℂ}
    (hΛ : ∀ᵐ ω ∂P, ∀ z, IsRegularizedClusterFamily (μ ω) (Λ ω z) z)
    (z : ℕ → ℂ) (t : ℕ → Ioi (0 : ℝ)) (κ : Ω → ℕ)
    (hκ : Measurable[fieldSigmaAlgebra α₀ hC U] κ) :
    ∃ F : Ω → Set ℂ, Measurable[fieldSigmaAlgebra α₀ hC U] F ∧
      ∀ᵐ ω ∂P, closure (Λ ω (z (κ ω)) (t (κ ω))) ⊆ U →
        F ω = Λ ω (z (κ ω)) (t (κ ω)) := by
  classical
  obtain ⟨G, hG, hGeq⟩ := exists_local_lqg_bounded_compact_regularizedFamily_representative
    hI2 hγ hγ2 hα hGFF hμ hloc hU hUb hΛ
  let F : Ω → Set ℂ := fun ω => ⋃ n : ℕ, {x | κ ω = n ∧ x ∈ G ω (z n, t n)}
  have hF : Measurable[fieldSigmaAlgebra α₀ hC U] F := by
    let : MeasurableSpace Ω := fieldSigmaAlgebra α₀ hC U
    apply Measurable.of_eval
    intro x
    change Measurable (fun ω => x ∈ F ω)
    simp only [F, mem_iUnion, mem_ofPred_eq]
    apply Measurable.exists
    intro n
    apply Measurable.and
    · exact measurableSet_setOfPred.mp (hκ (measurableSet_singleton n))
    · change Measurable (fun ω => G ω (z n, t n) x)
      have hs : Measurable (fun ω => G ω (z n, t n)) :=
        (measurable_pi_apply (z n, t n)).comp hG
      exact (measurable_pi_apply x).comp hs
  refine ⟨F, hF, ?_⟩
  filter_upwards [hGeq] with ω heq hcontain
  ext x
  simp only [F, mem_iUnion, mem_ofPred_eq]
  constructor
  · rintro ⟨n, hn, hx⟩
    subst n
    exact (heq _ _ hcontain) ▸ hx
  · intro hx
    exact ⟨κ ω, rfl, (heq _ _ hcontain).symm ▸ hx⟩

end HarmonicBalls
