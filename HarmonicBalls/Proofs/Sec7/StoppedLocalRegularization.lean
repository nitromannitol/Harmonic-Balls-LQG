import HarmonicBalls.Proofs.Sec7.StoppedLocalFamily
import HarmonicBalls.Proofs.Sec5.LeftContinuity

/-! # Local regularized families at arbitrary positive times

Mass continuity and full support identify a regular-open family member with
the regularization of its earlier rational members. This uses no right
continuity at a boundary-contact time.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal

universe u

/-- A regular-open increasing mass-parameterized family is the
regularization of the union of its earlier rational members. -/
theorem regularOpenFamily_eq_regularization_earlier_rat
    {μ : Measure ℂ} [μ.IsOpenPosMeasure] {A : ℝ → Set ℂ} {z : ℂ}
    (hA : SatisfiesHarmonicBallConditions μ A z) {t : ℝ} (ht : 0 < t) :
    A t = interior (closure (⋃ q : {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < t}, A q)) := by
  let T := t + 1
  have htT : t ∈ Ioo (0 : ℝ) T := ⟨ht, by dsimp [T]; linarith⟩
  have hreal : A t ⊆ closure (⋃ s ∈ Ioo (0 : ℝ) t, A s) :=
    subset_closure_iUnion_of_mass_continuity htT (hA.isRegularOpen t ht).isOpen
      (fun s hs r hr hsr => hA.monotoneOn hs.1 hr.1 hsr)
      (fun s hs => hA.measure_eq s hs.1)
  have hu : (⋃ s ∈ Ioo (0 : ℝ) t, A s) =
      ⋃ q : {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < t}, A q := by
    ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨s, hs, hx⟩
      obtain ⟨q, hsq, hqt⟩ := exists_rat_btwn hs.2
      exact ⟨⟨q, lt_trans hs.1 hsq, hqt⟩,
        hA.monotoneOn hs.1 (lt_trans hs.1 hsq) hsq.le hx⟩
    · rintro ⟨q, hx⟩
      exact ⟨q, q.property, hx⟩
  rw [hu] at hreal
  have hsub : (⋃ q : {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < t}, A q) ⊆ A t := by
    intro x hx
    obtain ⟨q, hq⟩ := mem_iUnion.mp hx
    exact hA.monotoneOn q.property.1 ht q.property.2.le hq
  have hcl : closure (A t) =
      closure (⋃ q : {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < t}, A q) :=
    Subset.antisymm (closure_minimal hreal isClosed_closure) (closure_mono hsub)
  exact (hA.isRegularOpen t ht).symm.trans (congrArg interior hcl)

/-- At a positive field-measurable time, a regularized family has a field-local
representative wherever it is compactly contained. Full support and mass
continuity provide its earlier-time reconstruction. -/
theorem exists_fieldLocal_stopped_regularizedFamily_of_fullSupport
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {Λ : Ω → ℂ → ℝ → Set ℂ}
    (hΛ : ∀ᵐ ω ∂P, ∀ z, IsRegularizedClusterFamily (μ ω) (Λ ω z) z)
    (z : ℂ) (τ : Ω → Ioi (0 : ℝ))
    (hτ : Measurable[fieldSigmaAlgebra α₀ hC U] τ) :
    ∃ F : Ω → Set ℂ, Measurable[fieldSigmaAlgebra α₀ hC U] F ∧
      ∀ᵐ ω ∂P, closure (Λ ω z (τ ω)) ⊆ U → F ω = Λ ω z (τ ω) := by
  classical
  obtain ⟨G, hG, hGeq⟩ := exists_local_lqg_bounded_compact_regularizedFamily_representative
    hI2 hγ hγ2 hα hGFF hμ hloc hU hUb hΛ
  let Q := {q : ℚ // 0 < (q : ℝ)}
  let H : Ω → Set ℂ := fun ω => ⋃ q : Q,
    {x | (q : ℝ) < τ ω ∧ x ∈ G ω (z, ⟨q, q.property⟩)}
  have hH : Measurable[fieldSigmaAlgebra α₀ hC U] H := by
    let : MeasurableSpace Ω := fieldSigmaAlgebra α₀ hC U
    apply Measurable.of_eval
    intro x
    change Measurable (fun ω => x ∈ H ω)
    simp only [H, mem_iUnion, mem_ofPred_eq]
    apply Measurable.exists
    intro q
    apply Measurable.and
    · exact measurableSet_setOfPred.mp
        (measurableSet_lt measurable_const (measurable_subtype_coe.comp hτ))
    · change Measurable (fun ω => G ω (z, ⟨q, q.property⟩) x)
      have hs : Measurable (fun ω => G ω (z, ⟨(q : ℚ), q.property⟩)) :=
        (measurable_pi_apply (z, (⟨(q : ℚ), q.property⟩ : Ioi (0 : ℝ)))).comp hG
      exact (measurable_pi_apply x).comp hs
  refine ⟨fun ω => denseSequenceRegularization (H ω),
    measurable_denseSequenceRegularization.comp hH, ?_⟩
  filter_upwards [hGeq, hΛ, hfull γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ]
    with ω heq hfamily hsupport hcontain
  let : (μ ω).IsOpenPosMeasure := ⟨fun V hV hne => (hsupport V hV hne).ne'⟩
  let B : Set ℂ := ⋃ q : {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < τ ω}, Λ ω z q
  have hBopen : IsOpen B := isOpen_iUnion fun q =>
    ((hfamily z).1.isRegularOpen q q.property.1).isOpen
  have hHB : H ω = B := by
    ext x
    simp only [H, B, mem_iUnion, mem_ofPred_eq]
    constructor
    · rintro ⟨q, hqt, hx⟩
      have hsub := (hfamily z).1.monotoneOn q.property (τ ω).property hqt.le
      have hq : closure (Λ ω z q) ⊆ U := (closure_mono hsub).trans hcontain
      exact ⟨⟨q, q.property, hqt⟩, (heq z ⟨q, q.property⟩ hq) ▸ hx⟩
    · rintro ⟨q, hx⟩
      have hsub := (hfamily z).1.monotoneOn q.property.1 (τ ω).property q.property.2.le
      have hq : closure (Λ ω z q) ⊆ U := (closure_mono hsub).trans hcontain
      exact ⟨⟨q, q.property.1⟩, q.property.2, (heq z ⟨q, q.property.1⟩ hq).symm ▸ hx⟩
  rw [hHB, denseSequenceRegularization_eq hBopen]
  exact (regularOpenFamily_eq_regularization_earlier_rat (hfamily z).1 (τ ω).property).symm

end HarmonicBalls
