import HarmonicBalls.Steps.Sec11.PinchNormalizedLocalEvent
import HarmonicBalls.Steps.Sec11.PinchLocalMeasure

/-! # Local Green-potential representatives from normalized measure data -/

namespace HarmonicBalls

open MeasureTheory Metric Set Topology Filter
open scoped ENNReal

/-- Local Borel mass representatives determine a local representative of the
annular Green-potential supremum for an arbitrary random measure. -/
theorem exists_local_annulusGreenPotentialSup_of_borel_mass
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (m : MeasurableSpace Ω)
    (ν : Ω → Measure ℂ) (z : ℂ) (a b : ℝ)
    (hmass : ∀ B : Set ℂ, MeasurableSet B → B ⊆ ball z b →
      ∃ Y : Ω → ℝ≥0∞, Measurable[m] Y ∧ ∀ᵐ ω ∂P, ν ω B = Y ω) :
    ∃ Y : Ω → ℝ≥0∞, Measurable[m] Y ∧
      ∀ᵐ ω ∂P, annulusGreenPotentialSup (ν ω) z a b = Y ω := by
  let V := ball z b
  let A := annulus z a b
  let K : A → ℂ → ℝ≥0∞ := fun x y =>
    if y = x then ∞ else ENNReal.ofReal (greenFunction V x y)
  have hAmeas : MeasurableSet A := (isOpen_ball.sdiff isClosed_closedBall).measurableSet
  have hAV : A ⊆ V := sdiff_subset
  have hK (x : A) : Measurable (K x) := by
    exact Measurable.ite (measurableSet_singleton (x : ℂ)) measurable_const
      ((measurable_greenFunction isOpen_ball x).ennreal_ofReal)
  have hsections (x : A) : ∃ Y : Ω → ℝ≥0∞, Measurable[m] Y ∧
      ∀ᵐ ω ∂P, (∫⁻ y in A, K x y ∂(ν ω)) = Y ω := by
    refine @exists_local_lintegral_representative Ω ℂ mΩ inferInstance P m
      (fun ω => (ν ω).restrict A) (K x) (hK x) ?_
    intro B hB
    obtain ⟨Y, hY, hYeq⟩ := hmass (B ∩ A) (hB.inter hAmeas)
      (inter_subset_right.trans hAV)
    refine ⟨Y, hY, ?_⟩
    filter_upwards [hYeq] with ω hω
    simpa only [Measure.restrict_apply hB] using hω
  choose G hG hEq using hsections
  let F : Ω → A → ℝ≥0∞ := fun ω x => ∫⁻ y in A, K x y ∂(ν ω)
  have hsc : ∀ ω, LowerSemicontinuous (F ω) := by
    intro ω
    apply lowerSemicontinuous_lintegral_of_sections
    · exact hK
    · intro y
      have hc := (continuousOn_extendedGreenKernel_ball_centered z b y).mono hAV
      exact (continuousOn_iff_continuous_domRestrict.mp hc).lowerSemicontinuous
  obtain ⟨Y, hY, hYeq⟩ :=
    @exists_measurable_iSup_representative_of_lowerSemicontinuous Ω A mΩ inferInstance
      inferInstance P m F (fun ω x => G x ω) hG hEq (Filter.Eventually.of_forall hsc)
  refine ⟨Y, hY, ?_⟩
  filter_upwards [hYeq] with ω hω
  simpa only [annulusGreenPotentialSup, F, K, V, A, iSup_subtype] using hω

/-- Local Borel masses and local internal metric data for normalized measure
and metric imply a local representative of the original pinch event. -/
theorem exists_local_pinchEvent_representative_of_normalized_borel_mass
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {m : MeasurableSpace Ω}
    {D : Ω → ℂ → ℂ → ℝ} {μ : Ω → Measure ℂ} {G : Ω → ℂ → ℂ → ℝ≥0∞}
    {U T Q' Q : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q' Q)
    (M : ℝ) (z : ℂ) {r : ℝ} (hr : 0 < r)
    (c : Ω → ℝ) (a : Ω → ℝ≥0∞)
    (hscale : ∀ᵐ ω ∂P, 0 < c ω ∧ a ω ≠ 0 ∧ a ω ≠ ∞)
    (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hG : ∀ x y, Measurable[m] fun ω => G ω x y)
    (hGeq : ∀ᵐ ω ∂P, ∀ x ∈ ball z (6 * r), ∀ y ∈ ball z (6 * r),
      internalMetric (fun x y => c ω * D ω x y) (ball z (6 * r)) x y = G ω x y)
    (hmass : ∀ B : Set ℂ, MeasurableSet B → B ⊆ ball z (6 * r) →
      ∃ Y : Ω → ℝ≥0∞, Measurable[m] Y ∧ ∀ᵐ ω ∂P, (a ω • μ ω) B = Y ω) :
    ∃ E : Set Ω, MeasurableSet[m] E ∧ ∀ᵐ ω ∂P,
      (pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M r z ↔ ω ∈ E) := by
  have hU5 : rescaledSet U r z ⊆ ball z (5 * r) := by
    apply rescaledSet_subset_ball _ hr z
    intro x hx
    have h := hconfig.U_subset hx
    change dist x 0 < 5
    change dist x 0 < 2 ∧ _ at h
    linarith [h.1]
  have hU6 : rescaledSet U r z ⊆ ball z (6 * r) := by
    intro x hx
    have h := hU5 hx
    rw [mem_ball] at h ⊢
    nlinarith
  have hUm : MeasurableSet (rescaledSet U r z) :=
    (isOpen_rescaledSet hconfig.isOpen_U (ne_of_gt hr) z).measurableSet
  have hgreen := @exists_local_annulusGreenPotentialSup_of_borel_mass Ω mΩ P m
    (fun ω => a ω • μ ω) z (3 * r) (6 * r) hmass
  exact @exists_local_pinchEvent_representative_of_normalized_data Ω mΩ P m D μ G U T Q' Q
    hconfig M z r hr c a hscale hD hG hGeq hgreen (hmass _ hUm hU6)

#print axioms exists_local_annulusGreenPotentialSup_of_borel_mass
#print axioms exists_local_pinchEvent_representative_of_normalized_borel_mass

end HarmonicBalls
