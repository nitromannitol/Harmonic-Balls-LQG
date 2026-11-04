import HarmonicBalls.Steps.Sec11.PinchLocalMeasure
import HarmonicBalls.Steps.Sec11.PinchMeasurable
import HarmonicBalls.Steps.Sec11.MetricField

/-! # Local representatives of the strengthened pinch event -/

namespace HarmonicBalls

open Set Metric MeasureTheory Topology
open scoped ENNReal

/-- Local representatives of internal distance, Green potential and mass
produce a local representative of the strengthened pinch event. -/
theorem exists_local_pinchEvent_representative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {m : MeasurableSpace Ω}
    {D : Ω → ℂ → ℂ → ℝ} {μ : Ω → Measure ℂ} {G : Ω → ℂ → ℂ → ℝ≥0∞}
    {U T Q' Q : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q' Q)
    (M : ℝ) (z : ℂ) {r : ℝ} (hr : 0 < r)
    (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hG : ∀ x y, Measurable[m] fun ω => G ω x y)
    (hGeq : ∀ᵐ ω ∂P, ∀ x ∈ ball z (6 * r), ∀ y ∈ ball z (6 * r),
      internalMetric (D ω) (ball z (6 * r)) x y = G ω x y)
    (hgreen : ∃ Y : Ω → ℝ≥0∞, Measurable[m] Y ∧
      ∀ᵐ ω ∂P, annulusGreenPotentialSup (μ ω) z (3 * r) (6 * r) = Y ω)
    (hmass : ∃ Y : Ω → ℝ≥0∞, Measurable[m] Y ∧
      ∀ᵐ ω ∂P, μ ω (rescaledSet U r z) = Y ω) :
    ∃ E : Set Ω, MeasurableSet[m] E ∧ ∀ᵐ ω ∂P,
      (pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M r z ↔ ω ∈ E) := by
  let V := ball z (6 * r)
  let S := sphere z (5 * r)
  let A := rescaledSet Q' r z
  let B := frontier (rescaledSet Q r z)
  let C := rescaledSet T r z
  have hz : ({z} : Set ℂ) ⊆ V := by
    intro x hx
    have hxz : x = z := mem_singleton_iff.mp hx
    subst x
    change z ∈ ball z (6 * r)
    simp only [mem_ball, dist_self]
    positivity
  have hs : S ⊆ V := by
    intro x hx
    change x ∈ sphere z (5 * r) at hx
    change x ∈ ball z (6 * r)
    rw [mem_sphere] at hx
    rw [mem_ball]
    nlinarith
  have hc : C ⊆ V := by
    have hC5 : rescaledSet T r z ⊆ ball z (5 * r) := by
      apply rescaledSet_subset_ball _ hr z
      exact hconfig.T_subset.trans (fun _ hx => hx.1)
    intro x hx
    have hx5 := hC5 hx
    change x ∈ ball z (6 * r)
    rw [mem_ball] at hx5 ⊢
    nlinarith
  have hQ : rescaledSet Q r z ⊆ ball z (5 * r) := by
    apply rescaledSet_subset_ball _ hr z
    exact hconfig.Q_subset.trans (fun _ hx => hx.1.1)
  have hQclosure : closure (rescaledSet Q r z) ⊆ V := by
    apply (closure_mono hQ).trans
    have h5 : 0 < 5 * r := by positivity
    rw [closure_ball z h5.ne']
    intro x hx
    rw [mem_closedBall] at hx
    change x ∈ ball z (6 * r)
    rw [mem_ball]
    nlinarith
  have ha : A ⊆ V := by
    apply (Set.image_mono (subset_closure.trans hconfig.closure_Q'_subset)).trans
    exact subset_closure.trans hQclosure
  have hb : B ⊆ V := frontier_subset_closure.trans hQclosure
  obtain ⟨Y₁, hY₁, hY₁eq⟩ :=
    @exists_local_iSup_internalMetric_representative Ω mΩ P m D G V {z} S
      isOpen_ball hz hs hD (fun x _ y _ => hG x y)
      (hGeq.mono fun _ h x hx y hy => h x (hz hx) y (hs hy))
  obtain ⟨Y₂, hY₂, hY₂eq⟩ :=
    @exists_local_iSup_internalMetric_representative Ω mΩ P m D G V C C
      isOpen_ball hc hc hD (fun x _ y _ => hG x y)
      (hGeq.mono fun _ h x hx y hy => h x (hc hx) y (hc hy))
  obtain ⟨Y₃, hY₃, hY₃eq⟩ :=
    @exists_local_iInf_internalMetric_representative Ω mΩ P m D G V A B
      isOpen_ball ha hb hD (fun x _ y _ => hG x y)
      (hGeq.mono fun _ h x hx y hy => h x (ha hx) y (hb hy))
  obtain ⟨Y₄, hY₄, hY₄eq⟩ :=
    @exists_local_iInf_internalMetric_representative Ω mΩ P m D G V {z} S
      isOpen_ball hz hs hD (fun x _ y _ => hG x y)
      (hGeq.mono fun _ h x hx y hy => h x (hz hx) y (hs hy))
  obtain ⟨Y₅, hY₅, hY₅eq⟩ := hgreen
  obtain ⟨Y₆, hY₆, hY₆eq⟩ := hmass
  let E : Set Ω := {ω | Y₁ ω < Y₃ ω ∧ Y₂ ω < Y₄ ω ∧ ENNReal.ofReal M * Y₅ ω < Y₆ ω}
  have hE : MeasurableSet[m] E := by
    let : MeasurableSpace Ω := m
    exact (measurableSet_lt hY₁ hY₃).inter ((measurableSet_lt hY₂ hY₄).inter
      (measurableSet_lt ((measurable_const : Measurable (fun _ : Ω => ENNReal.ofReal M)).mul hY₅) hY₆))
  refine ⟨E, hE, ?_⟩
  filter_upwards [hD, hY₁eq, hY₂eq, hY₃eq, hY₄eq, hY₅eq, hY₆eq] with ω hDω h₁ h₂ h₃ h₄ h₅ h₆
  simp only [pinchPointEventWithInternalBounds, E, mem_ofPred_eq]
  rw [ofReal_setDist_pinch_boundary_eq_internalMetric hDω hconfig z hr,
    ofReal_setDist_center_sphere_eq_internalMetric hDω z hr]
  simp only [iSup_singleton] at h₁
  simp only [iInf_singleton] at h₄
  rw [h₁, h₂, h₃, h₄, h₅, h₆]

/-- The strengthened LQG pinch event has a representative measurable with
respect to the field on its radius-six ball. Both locality inputs are staged
literature propositions. -/
theorem exists_local_lqg_pinchEvent_representative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {γ ξ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {U T Q' Q : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q' Q)
    (M : ℝ) (z : ℂ) {r : ℝ} (hr : 0 < r)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α₀ < lqgQ γ)
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hD : IsLQGMetricOfField P γ ξ α₀ hC D)
    (hmloc : LQGMeasureLocality P γ α₀ hC hcirc)
    (haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc) :
    ∃ E : Set Ω, MeasurableSet[fieldSigmaAlgebra α₀ hC (ball z (6 * r))] E ∧
      ∀ᵐ ω ∂P, (pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M r z ↔ ω ∈ E) := by
  let V := ball z (6 * r)
  have hmetric := ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α₀ hC hcirc D
    haxioms hgff hγ hγ₂ hα hD
  obtain ⟨𝔇, h𝔇, hrepr⟩ := hD
  obtain ⟨_, hlocal, _, _⟩ := haxioms hgff hγ hγ₂ hα 𝔇 h𝔇
  obtain ⟨G, hG, hGeq⟩ := hlocal V isOpen_ball
  have hdist : ∀ᵐ ω ∂P, ∀ x ∈ V, ∀ y ∈ V, internalMetric (D ω) V x y = G ω x y := by
    filter_upwards [hrepr, hGeq] with ω hrepr hGeq
    have heq : D ω = fun u v =>
        (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal := by
      funext u v
      rw [← (hrepr u v).2, ENNReal.toReal_ofReal (hrepr u v).1]
    simpa only [← heq] using hGeq
  have hUV : rescaledSet U r z ⊆ V := by
    have hU5 : rescaledSet U r z ⊆ ball z (5 * r) := by
      apply rescaledSet_subset_ball _ hr z
      intro x hx
      have h := hconfig.U_subset hx
      change dist x 0 < 5
      change dist x 0 < 2 ∧ _ at h
      linarith [h.1]
    intro x hx
    have h := hU5 hx
    change x ∈ ball z (6 * r)
    rw [mem_ball] at h ⊢
    nlinarith
  have hmass : ∃ Y : Ω → ℝ≥0∞, Measurable[fieldSigmaAlgebra α₀ hC V] Y ∧
      ∀ᵐ ω ∂P, μ ω (rescaledSet U r z) = Y ω := by
    obtain ⟨Y, hY, hYeq⟩ := @exists_local_lqg_borel_mass_representative Ω mΩ P γ α₀ hC hcirc μ
      hγ hγ₂ hα hgff hμ hmloc V isOpen_ball isBounded_ball (rescaledSet U r z)
      (isOpen_rescaledSet hconfig.isOpen_U (ne_of_gt hr) z).measurableSet
    exact ⟨Y, hY, hYeq.mono fun _ h => by simpa only [inter_eq_self_of_subset_left hUV] using h⟩
  have hgreen := @exists_local_annulusGreenPotentialSup_representative Ω mΩ P γ α₀ hC hcirc μ
    hγ hγ₂ hα hgff hμ hmloc z (3 * r) (6 * r)
  exact @exists_local_pinchEvent_representative Ω mΩ P (fieldSigmaAlgebra α₀ hC V) D μ G
    U T Q' Q hconfig M z r hr hmetric hG hdist hgreen hmass

end HarmonicBalls
