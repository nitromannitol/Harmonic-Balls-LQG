import HarmonicBalls.FirstPass.S11ab
import HarmonicBalls.FirstPass.S11ae.Count
import HarmonicBalls.FirstPass.S11j.C42Six
import HarmonicBalls.FirstPass.S11j.FieldLevel11_15
import HarmonicBalls.FirstPass.Frozen.S11d
import HarmonicBalls.FirstPass.Frozen.S11j
import HarmonicBalls.Steps.Sec11.MetricField

/-!
# Metric event certificates for the local events

The base a.s. form `MetricEventCertificateStmt` (`FirstPass/S11ab.lean`) holds for the local first event
`pinchFirstEventLocal` and the local third event `pinchThirdEventLocal` (`FirstPass/S11h/LocalEvents.lean`).

Route: the internal metrics of the inserted LQG metric are
replaced by field-level decoders `Φ` (frozen input `LQGInternalMetricWeylAeMeasurableFrozen`, a.s. equal to the internal
metric for each fixed open domain and pair of points). The event is the countable formula of `Count.lean` at the
decoders; it is measurable for the distribution σ-algebra, and a.s. equal to the event of the metric, by the
countable-dense reductions of `Count.lean`. Inputs used: `LQGInternalMetricWeylAeMeasurableFrozen`
(`FirstPass/Frozen/S11d.lean`) and `LQGMetricFieldAxiomsUnivFrozen` (`FirstPass/Frozen/S11j.lean`), passed as hypotheses.
No other frozen input is used. The shifted clause `hshift` of `FirstPass/S11ab.lean` is not used here.
-/

namespace HarmonicBalls.S11ae

open MeasureTheory Set Metric Filter
open scoped ENNReal

universe u

/-- The corridor containment `∂B₅ ⊆ pinchOmegaGeom W Q δ` of the buffered pinch geometry: the sphere lies in the
component of `0` in `B₆ \ (closure B_{2δ}(Q) ∪ closure B_{2δ}(W))`, which is contained in the component in `B₇ \ ...`. -/
theorem sphere_five_subset_pinchOmegaGeom {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) : sphere (0 : ℂ) 5 ⊆ pinchOmegaGeom W Q δ := by
  unfold pinchOmegaGeom
  exact (hgeo.sphere_subset_connectedComponentIn_six).trans
    (connectedComponentIn_mono 0 (sdiff_subset_sdiff_left (ball_subset_ball (by norm_num))))

/-- The base a.s. form of the rule for the local first event `pinchFirstEventLocal`, for `0 < γ < 2` and the buffered
pinch geometry. -/
theorem metricEventCertificate_firstLocal {U V W T Q' Q : Set ℂ} {δ γ ξ : ℝ}
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{u}) (hax : LQGMetricFieldAxiomsUnivFrozen.{u}) :
    MetricEventCertificateStmt.{u} γ ξ (fun d => pinchFirstEventLocal d W T Q' Q δ) := by
  unfold MetricEventCertificateStmt
  intro α hα Ω _ P _ hC hcirc D hGFF hD
  have hδ : 0 < δ := hgeo.delta_pos
  have hΩ : sphere (0 : ℂ) 5 ⊆ pinchOmegaGeom W Q δ := sphere_five_subset_pinchOmegaGeom hgeo
  have hD0 := hD
  unfold IsLQGMetricOfField at hD0
  obtain ⟨𝔇, hL, hrep⟩ := hD0
  have hlen : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω) :=
    ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α hC hcirc D
      (hax Ω P γ ξ α hC hcirc) hGFF hγ hγ₂ hα hD
  have hnn : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ D ω x y := by
    filter_upwards [hrep] with ω hω
    exact fun x y => (hω x y).1
  have hDrep : ∀ᵐ ω ∂P, D ω = insertedLQGMetric 𝔇 ξ α (hC ω) := by
    filter_upwards [hrep] with ω hω
    funext x y
    have h0 := (hω x y).1
    have h1 := (hω x y).2
    show D ω x y = (weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) x y).toReal
    rw [← h1, ENNReal.toReal_ofReal h0]
  obtain ⟨Φ, hΦ⟩ := exists_fieldDecoders hfr hGFF hγ hγ₂ hα hL
  have hdec : ∀ W : Set ℂ, IsOpen W → ∀ x y : ℂ,
      ∀ᵐ ω ∂P, Φ W x y (hC ω) = internalMetric (D ω) W x y := by
    intro W hW x y
    filter_upwards [(hΦ W hW x y).2 (fun _ => 0) continuous_const, hDrep] with ω h1 h2
    rw [addFunPairing_zero_shift] at h1
    rw [h2]
    exact h1
  obtain ⟨Sp, hSpA, hSpN, hSpD⟩ := exists_countable_dense_sub (sphere (0 : ℂ) 5)
  obtain ⟨Qp, hQpA, hQpN, hQpD⟩ := exists_countable_dense_sub (closure Q')
  obtain ⟨Fp, hFpA, hFpN, hFpD⟩ := exists_countable_dense_sub (frontier Q)
  obtain ⟨Cp, hCpA, hCpN, hCpD⟩ := exists_countable_dense_sub (closure (T \ thickening (3 * δ) W))
  obtain ⟨Ep, hEpA, hEpN, hEpD⟩ := exists_countable_dense_sub (sphere (0 : ℂ) δ)
  have hO : IsOpen (pinchOmegaGeom W Q δ) := HarmonicBalls.S11m.E1Bounds.pinchOmegaGeom_isOpen W Q δ
  refine ⟨{F | localFirstCount (fun W' x y => Φ W' x y F) (pinchOmegaGeom W Q δ)
      (thickening δ (closure (T \ thickening (3 * δ) W))) Sp Qp Fp Cp Ep}, ?_, ?_⟩
  · exact measurableSet_localFirstCount (fun W' hW' x y => (hΦ W' hW' x y).1) hO isOpen_thickening
      hSpN hQpN hFpN hCpN hEpN
  · have hS1 : ∀ᵐ ω ∂P, ∀ y ∈ Sp,
        Φ (pinchOmegaGeom W Q δ) 0 y (hC ω) = internalMetric (D ω) (pinchOmegaGeom W Q δ) 0 y :=
      ae_forall_mem_of_countable hSpN (fun y _ => hdec _ hO 0 y)
    have hS2 : ∀ᵐ ω ∂P, ∀ a ∈ Qp, ∀ b ∈ Fp, Φ univ a b (hC ω) = internalMetric (D ω) univ a b :=
      ae_forall_mem_of_countable hQpN (fun a _ =>
        ae_forall_mem_of_countable hFpN (fun b _ => hdec univ isOpen_univ a b))
    have hS3 : ∀ᵐ ω ∂P, ∀ x ∈ Cp, ∀ y ∈ Cp,
        Φ (thickening δ (closure (T \ thickening (3 * δ) W))) x y (hC ω) =
          internalMetric (D ω) (thickening δ (closure (T \ thickening (3 * δ) W))) x y :=
      ae_forall_mem_of_countable hCpN (fun x _ =>
        ae_forall_mem_of_countable hCpN (fun y _ => hdec _ isOpen_thickening x y))
    have hS4 : ∀ᵐ ω ∂P, ∀ b ∈ Ep, Φ univ 0 b (hC ω) = internalMetric (D ω) univ 0 b :=
      ae_forall_mem_of_countable hEpN (fun b _ => hdec univ isOpen_univ 0 b)
    filter_upwards [hS1, hS2, hS3, hS4, hlen, hnn] with ω h1 h2 h3 h4 hl hn
    have key := localFirstCount_congr (g := fun W' x y => Φ W' x y (hC ω))
      (h := fun W' x y => internalMetric (D ω) W' x y)
      (fun y hy => h1 y hy) (fun a ha b hb => h2 a ha b hb) (fun x hx y hy => h3 x hx y hy)
      (fun b hb => h4 b hb)
    exact key.trans (pinchFirstEventLocal_iff_count hl hn hgeo hΩ hSpA hSpD hQpA hQpD hFpA hFpD
      hCpA hCpD hEpA hEpD).symm

/-- The base a.s. form of the rule for the local third event `pinchThirdEventLocal`, for `0 < γ < 2` and `0 < δ`. -/
theorem metricEventCertificate_thirdLocal {δ γ ξ : ℝ} (V W : Set ℂ) (hδ : 0 < δ)
    (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{u}) (hax : LQGMetricFieldAxiomsUnivFrozen.{u}) :
    MetricEventCertificateStmt.{u} γ ξ (fun d => pinchThirdEventLocal d V W δ) := by
  unfold MetricEventCertificateStmt
  intro α hα Ω _ P _ hC hcirc D hGFF hD
  have hD0 := hD
  unfold IsLQGMetricOfField at hD0
  obtain ⟨𝔇, hL, hrep⟩ := hD0
  have hlen : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω) :=
    ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α hC hcirc D
      (hax Ω P γ ξ α hC hcirc) hGFF hγ hγ₂ hα hD
  have hnn : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ D ω x y := by
    filter_upwards [hrep] with ω hω
    exact fun x y => (hω x y).1
  have hDrep : ∀ᵐ ω ∂P, D ω = insertedLQGMetric 𝔇 ξ α (hC ω) := by
    filter_upwards [hrep] with ω hω
    funext x y
    have h0 := (hω x y).1
    have h1 := (hω x y).2
    show D ω x y = (weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) x y).toReal
    rw [← h1, ENNReal.toReal_ofReal h0]
  obtain ⟨Φ, hΦ⟩ := exists_fieldDecoders hfr hGFF hγ hγ₂ hα hL
  have hdec : ∀ W : Set ℂ, IsOpen W → ∀ x y : ℂ,
      ∀ᵐ ω ∂P, Φ W x y (hC ω) = internalMetric (D ω) W x y := by
    intro W hW x y
    filter_upwards [(hΦ W hW x y).2 (fun _ => 0) continuous_const, hDrep] with ω h1 h2
    rw [addFunPairing_zero_shift] at h1
    rw [h2]
    exact h1
  obtain ⟨Sp2, hS2A, hS2N, hS2D⟩ := exists_countable_dense_sub (sphere (0 : ℂ) (2 * δ))
  obtain ⟨Sp3, hS3A, hS3N, hS3D⟩ := exists_countable_dense_sub (sphere (0 : ℂ) (3 * δ))
  obtain ⟨Cp, hCpA, hCpN, hCpD⟩ := exists_countable_dense_sub (closure (thickening (3 * δ) W \ V))
  refine ⟨{F | localThirdCount (fun W' x y => Φ W' x y F)
      (thickening δ (closure (thickening (3 * δ) W \ V))) Sp2 Sp3 Cp}, ?_, ?_⟩
  · exact measurableSet_localThirdCount (fun W' hW' x y => (hΦ W' hW' x y).1) isOpen_thickening
      hS2N hS3N hCpN
  · have hT1 : ∀ᵐ ω ∂P, ∀ x ∈ Cp, ∀ y ∈ Cp,
        Φ (thickening δ (closure (thickening (3 * δ) W \ V))) x y (hC ω) =
          internalMetric (D ω) (thickening δ (closure (thickening (3 * δ) W \ V))) x y :=
      ae_forall_mem_of_countable hCpN (fun x _ =>
        ae_forall_mem_of_countable hCpN (fun y _ => hdec _ isOpen_thickening x y))
    have hT2 : ∀ᵐ ω ∂P, ∀ a ∈ Sp2, ∀ b ∈ Sp3, Φ univ a b (hC ω) = internalMetric (D ω) univ a b :=
      ae_forall_mem_of_countable hS2N (fun a _ =>
        ae_forall_mem_of_countable hS3N (fun b _ => hdec univ isOpen_univ a b))
    filter_upwards [hT1, hT2, hlen, hnn] with ω h1 h2 hl hn
    have key := localThirdCount_congr (g := fun W' x y => Φ W' x y (hC ω))
      (h := fun W' x y => internalMetric (D ω) W' x y)
      (fun x hx y hy => h1 x hx y hy) (fun a ha b hb => h2 a ha b hb)
    exact key.trans (pinchThirdEventLocal_iff_count hl hn hδ V W hS2A hS2D hS3A hS3D hCpA hCpD).symm

end HarmonicBalls.S11ae
