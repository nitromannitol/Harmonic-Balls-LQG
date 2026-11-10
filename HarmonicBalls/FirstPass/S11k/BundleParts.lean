import HarmonicBalls.FirstPass.S11k
import HarmonicBalls.FirstPass.S11k.ExteriorDistances

/-!
# First pass, Section 11: the exterior version bundle from its parts (fp-S11k, owner z3)

`PinchSecondExteriorVersionsStep` (`FirstPass/S11k.lean`) is assembled from

* the EXTERNAL metric axioms `LQGMetricFieldAxiomsUnivFrozen` (items I and II, locality on open sets);
* the frozen circle-average limit `WholePlaneCircleAverageLimitFrozen` (n4);
* `PinchFirstLExteriorStep` (NEW, OPEN): the first conjunct `L` of `pinchFirstEvent` has a zero-mean exterior version.
  Its domain `(thickening (2δ) (Q ∪ W))ᶜ` is closed; no source gives its internal metric as a function of the outside field
  (see `reports/z3.md`, Blocker 1);
* `PinchSecondAnnulusStep` (NEW, OPEN, the N2 output of `exists_exterior_annulusGreenPotentialSup_of_frozen_base`,
  `FirstPass/S11p/ExteriorMass.lean:137`, whose named inputs `hBase`, `hSing` are not yet bridged to this form).

The other three terms `a₀`, `d₀`, `a₁` and the sphere distance `d` are proved in `S11k/ExteriorDistances.lean`.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric Topology
open scoped ENNReal

universe u

namespace BundleParts

/-- OPEN (NEW): the closed-domain first conjunct `L` of `pinchFirstEvent` has a zero-mean exterior version. -/
def PinchFirstLExteriorStep : Prop :=
  ∀ (U V W T Q' Q : Set ℂ) (δ : ℝ), IsBufferedPinchGeometry U V W T Q' Q δ →
  ∀ γ α₀ ξ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc → IsLQGMetricOfField P γ ξ α₀ hC D →
    ∃ L : Ω → ℝ≥0∞,
      Measurable[MeasurableSpace.comap (localModConstPairings α₀ hC (closure W)ᶜ) inferInstance] L ∧
        ∀ᵐ ω ∂P, L ω = ⨆ x ∈ sphere (0 : ℂ) 5, internalMetric (D ω) (thickening (2 * δ) (Q ∪ W))ᶜ 0 x

/-- OPEN (NEW, N2): the annular Green-potential supremum of every LQG measure has an exterior version, finite a.s. -/
def PinchSecondAnnulusStep : Prop :=
  ∀ (U V W T Q' Q : Set ℂ) (δ : ℝ), IsBufferedPinchGeometry U V W T Q' Q δ →
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∃ G : Ω → ℝ≥0∞,
      Measurable[MeasurableSpace.comap (localModConstPairings α₀ hC (closure W)ᶜ) inferInstance] G ∧
        (∀ᵐ ω ∂P, G ω = annulusGreenPotentialSup (μ ω) 0 3 6) ∧ ∀ᵐ ω ∂P, G ω ≠ ⊤

/-- The thickened unit-circle complement: `closure W` lies in `1 < |z|`. -/
theorem closure_W_norm_gt_one {U V W T Q' Q : Set ℂ} {δ : ℝ} (hG : IsBufferedPinchGeometry U V W T Q' Q δ)
    {z : ℂ} (hz : z ∈ closure W) : 1 < ‖z‖ := by
  have h := hG.T_subset (hG.closure_W_subset_T hz)
  have h2 : z ∉ closedBall (0 : ℂ) 1 := h.2
  rw [mem_closedBall, dist_zero_right, not_le] at h2
  exact h2

/-- A bounded nonempty open connected set in `ℂ` other than `univ` has nonempty frontier. -/
theorem frontier_nonempty_of_open_ne_univ {Q : Set ℂ} (hne : Q.Nonempty) (hQne : Q ≠ univ) :
    (frontier Q).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hc : IsClopen Q := isClopen_iff_frontier_eq_empty.2 h
  exact hQne ((isClopen_iff.1 hc).resolve_left hne.ne_empty)

/-- The bundle, assembled from its parts: the item-II locality and the item-I measure of `LQGMetricFieldAxiomsUnivFrozen`,
the frozen circle-average limit, `PinchFirstLExteriorStep` (OPEN) and `PinchSecondAnnulusStep` (OPEN). -/
theorem pinchSecondExteriorVersionsStep_of_parts (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hb : WholePlaneCircleAverageLimitFrozen.{u}) (hL : PinchFirstLExteriorStep.{u})
    (hS : PinchSecondAnnulusStep.{u}) : PinchSecondExteriorVersionsStep.{u} := by
  intro U V W T Q' Q δ hG γ α₀ ξ hγ0 hγ2 hα Ω _ P hC hcirc μ D hGFF hμ hD
  have hD' := hD
  obtain ⟨𝔇, h𝔇, hDae⟩ := hD
  obtain ⟨hI, hII, -, -⟩ := hAx Ω P γ ξ α₀ hC hcirc hGFF hγ0 hγ2 hα 𝔇 h𝔇
  have hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω) := by
    filter_upwards [hI, hDae] with ω h1 h2
    have hDeq : D ω = fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal := by
      funext u v
      have h3 := ENNReal.toReal_ofReal (h2 u v).1
      rw [(h2 u v).2] at h3
      exact h3.symm
    rw [hDeq]
    exact h1.2
  have hloc : ∀ V : Set ℂ, IsOpen V → V ⊆ (closure W)ᶜ → ∃ G : Ω → ℂ → ℂ → ℝ≥0∞,
      (∀ z w, Measurable[fieldSigmaAlgebra α₀ hC V] fun ω => G ω z w) ∧
        ∀ᵐ ω ∂P, ∀ z ∈ V, ∀ w ∈ V, internalMetric (D ω) V z w = G ω z w := by
    intro V hV _
    obtain ⟨G, hGm, hGa⟩ := hII V hV
    refine ⟨G, hGm, ?_⟩
    filter_upwards [hGa, hmetric, hDae] with ω h1 h2 h3
    have hDeq : D ω = fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal := by
      funext u v
      have h4 := ENNReal.toReal_ofReal (h3 u v).1
      rw [(h3 u v).2] at h4
      exact h4.symm
    rw [hDeq]
    exact h1
  have hδpos : 0 < δ := hG.delta_pos
  have hδlt : δ < 1 / 1000 := hG.delta_lt
  have hE : IsOpen (closure W)ᶜ := isClosed_closure.isOpen_compl
  have hsph : sphere (0 : ℂ) 1 ⊆ (closure W)ᶜ := fun z hz hzW => by
    have := closure_W_norm_gt_one hG hzW
    rw [mem_sphere_zero_iff_norm] at hz
    linarith
  have hBE2 : ball (0 : ℂ) (2 * δ) ⊆ (closure W)ᶜ := fun z hz hzW => by
    have := closure_W_norm_gt_one hG hzW
    rw [mem_ball_zero_iff] at hz
    linarith
  have hBE3 : ball (0 : ℂ) (3 * δ) ⊆ (closure W)ᶜ := fun z hz hzW => by
    have := closure_W_norm_gt_one hG hzW
    rw [mem_ball_zero_iff] at hz
    linarith
  have hann : IsOpen (annulus (0 : ℂ) 4 5) := isOpen_ball.sdiff isClosed_closedBall
  have hVa : IsOpen (annulus (0 : ℂ) 4 5 \ closure T) := hann.sdiff isClosed_closure
  have hVaE : annulus (0 : ℂ) 4 5 \ closure T ⊆ (closure W)ᶜ := fun z hz hzW =>
    hz.2 ((hG.closure_W_subset_T.trans subset_closure) hzW)
  have hQne : Q.Nonempty := hG.isConnected_Q.nonempty
  have hQ'ne : Q'.Nonempty := hG.isConnected_Q'.nonempty
  have hQ'Q : Q' ⊆ Q := subset_closure.trans hG.closure_Q'_subset_Q
  have hQ_ne_univ : Q ≠ univ := by
    intro h
    have h10 : (10 : ℂ) ∈ closure Q := by
      rw [h, closure_univ]
      exact mem_univ _
    have h' : (10 : ℂ) ∈ ball (0 : ℂ) 5 := (hG.closure_Q_subset h10).1.1
    rw [mem_ball_zero_iff] at h'
    have h10n : ‖(10 : ℂ)‖ = 10 := by norm_num
    linarith
  have hfrQ : (frontier Q).Nonempty := frontier_nonempty_of_open_ne_univ hQne hQ_ne_univ
  obtain ⟨L', hL'm, hL'a⟩ := hL U V W T Q' Q δ hG γ α₀ ξ hγ0 hγ2 hα Ω P hC hcirc D hGFF hD'
  obtain ⟨aQ, haQm, haQa⟩ := ExteriorDistances.exists_exterior_setDist_exit hb hGFF α₀ hE hsph hmetric hloc
    (U := Q) (V := annulus (0 : ℂ) 4 5 \ closure T) (A := Q') hG.isOpen_Q hVa hVaE hQ'Q
    hG.closure_Q_subset hQ'ne hfrQ
  obtain ⟨a0, ha0m, ha0a⟩ := ExteriorDistances.exists_exterior_setDist_origin hb hGFF α₀ hE hsph hmetric hloc
    hδpos hBE2
  obtain ⟨dS, hdSm, hdSa⟩ := ExteriorDistances.exists_exterior_setDist_spheres hb hGFF α₀ hE hsph hmetric hloc
    hδpos hBE3
  obtain ⟨aT, haTm, haTa⟩ := ExteriorDistances.exists_exterior_internalDiam_version hb hGFF α₀ hE hsph hmetric
    hloc hδpos (A := T \ thickening (3 * δ) W)
    (ExteriorDistances.thickening_subset_compl_closure hδpos (fun x hx => hx.2))
  obtain ⟨G, hGm, hGa, hGfin⟩ := hS U V W T Q' Q δ hG γ α₀ hγ0 hγ2 hα Ω P hC hcirc μ hGFF hμ
  refine ⟨{ω | L' ω < aQ ω ∧ aT ω < a0 ω}, ?_, ?_, dS, hdSm, hdSa, ?_⟩
  · exact (measurableSet_lt hL'm haQm).inter (measurableSet_lt haTm ha0m)
  · filter_upwards [hL'a, haQa, haTa, ha0a] with ω e1 e2 e3 e4
    show (L' ω < aQ ω ∧ aT ω < a0 ω) ↔ pinchFirstEvent (D ω) W T Q' Q δ
    rw [e1, e2, ← e3, e4]
    try rfl
  · intro M _
    refine ⟨fun ω => ENNReal.ofReal M * G ω, hGm.const_mul _, ?_, ?_⟩
    · filter_upwards [hGa] with ω h
      show ENNReal.ofReal M * annulusGreenPotentialSup (μ ω) 0 3 6 ≤ ENNReal.ofReal M * G ω
      rw [h]
    · filter_upwards [hGfin] with ω h _
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top h

/-- Lemma 11.16, corrected form, with the exterior version bundle replaced by its two OPEN parts `PinchFirstLExteriorStep`
(closed-domain `L`, Blocker 1 of `reports/z3.md`) and `PinchSecondAnnulusStep` (N2), and with the frozen circle-average
limit `WholePlaneCircleAverageLimitFrozen` (n4) as an explicit hypothesis. All other hypotheses are as in
`firstPass_11_16_corrected_of_versions`. -/
theorem firstPass_11_16_corrected_of_parts (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hb : WholePlaneCircleAverageLimitFrozen.{u}) (hL : PinchFirstLExteriorStep.{u})
    (hS : PinchSecondAnnulusStep.{u}) (hPos : PinchFirstEventFaithfulStmt.{u})
    (hD : SmallMetricDiameterLargeMassStmt.{u}) (hM : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u}) (hMk : DomainMarkovConditionalPositiveFrozen.{u}) :
    PinchSecondEventFaithfulStmt.{u} :=
  firstPass_11_16_corrected_of_versions (pinchSecondExteriorVersionsStep_of_parts hAx hb hL hS) hPos hAx hD hM hDiam hMk

end BundleParts

end HarmonicBalls
