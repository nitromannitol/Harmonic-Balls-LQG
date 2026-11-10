import HarmonicBalls.FirstPass.S11ah.CutoffLength
import HarmonicBalls.FirstPass.S11ah.Modified
import HarmonicBalls.FirstPass.S11ap
import HarmonicBalls.FirstPass.Frozen.S11c

/-!
# Step 5 for the local decoders, with no named input (fp-S11ah-11-13-steps-4-5c, owner n4; wave 32)

Closed forms of the Step 5 interface of `S11ah/LQGDecoder.lean` and `S11ah/Modified.lean`:

* the cutoff transfer R1 is proved (`cutoffInternalLengthStmt`, `S11ah/CutoffLength.lean`), so the a.s. length
  property of the decoders needs no named input;
* the measurability in `ω` of the observables `localMeanZeroObs α D (hC ω)` follows from the measurability of the
  pairings `hC ω φ` (`IsWholePlaneGFF.measurable_pairing`), so the measurability `hm` of the decoder family is derived
  from the measurability `Measurable m` of identity (18);
* locality of the certificate event (operator item (a)) is derived from the containments of the paper's pinch
  geometry (`FirstPassS11ap.pinchOmegaGeom_certificate_data`) with `Ostar = pinchOmegaGeom W Q δ`, `η = δ`.

The decoders are indexed by the model sample space `Ω` (which carries `hC`), not by the observables, because identity
(18) relates `m (obs ω)` to the LQG metric of `hC ω`.
-/

open MeasureTheory ProbabilityTheory Metric Set Filter Topology HarmonicBalls
open scoped ENNReal

noncomputable section

namespace FirstPassS11ah

/-- The mean-zero observables of the whole-plane field are measurable in `ω`: each coordinate is `hC ω φ` minus a
constant, and `hC ω φ` is measurable by `IsWholePlaneGFF.measurable_pairing`. -/
theorem measurable_localMeanZeroObs_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc) (α : ℝ) (D : Set ℂ) :
    Measurable fun ω => localMeanZeroObs α D (hC ω) := by
  refine measurable_pi_iff.2 fun φ => ?_
  have hφ : IsTestFunction univ φ.1 := ⟨φ.2.1.1, φ.2.1.2.1, subset_univ _⟩
  exact (hG.measurable_pairing φ.1 hφ).sub measurable_const

/-- **Locality of the pinch certificate event** (operator item (a)): for the paper's `Ostar = pinchOmegaGeom W Q δ`
and `η = δ`, the locality hypothesis `CertificateEventLocality` holds, from the containments of the buffered pinch
geometry (`FirstPassS11ap.pinchOmegaGeom_certificate_data`). -/
theorem certificateEventLocality_pinch {U V W T Q' Q : Set ℂ} {δ M : ℝ}
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) :
    CertificateEventLocality (pinchOmegaGeom W Q δ) U V W T Q' Q δ M :=
  certificateEventLocality_of_containments (FirstPassS11ap.pinchOmegaGeom_certificate_data hgeo).2.2.2

/-- **Step 5 for the unrooted local decoders, closed form.** Let `m` be the Borel map of identity (18) on the disc
`B = ball c R` (with `0 ∉ closedBall c R`), and let `hid` be identity (18) for the observables of the model. Then the
decoders `decoderOn (ball c R) (m (obs ω))`, indexed by the model sample `ω`, admit a `P`-a.s. modification `D'` that is
an `IsLengthMetricOn (ball c R)` metric for every sample, measurable in each pair of points, with a measurable failure
set (K) at `Ostar = pinchOmegaGeom W Q δ`, `η = δ`, whose `P`-a.s. slices agree with those of the decoders. -/
theorem exists_modified_failureSet_closed {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hL : IsLQGMetric γ ξ 𝔇) (hG : IsWholePlaneGFF P hC hcirc)
    {c : ℂ} {R : ℝ} (hR : 0 < R) (h0ball : (0 : ℂ) ∉ closedBall c R)
    (κ : Kernel Ω ℂ) [IsSFiniteKernel κ]
    (m : ({φ : ℂ → ℝ // IsTestFunction (ball c R) φ ∧ ∫ x, φ x = 0} → ℝ) →
      ContinuousMap ↥(ball c R ×ˢ ball c R : Set (ℂ × ℂ)) ℝ)
    (hm : Measurable m) (α : ℝ)
    (hid : ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧ ∀ p : ↥(ball c R ×ˢ ball c R : Set (ℂ × ℂ)),
      ENNReal.ofReal (m (localMeanZeroObs α (ball c R) (hC ω)) p) =
        ENNReal.ofReal b * internalMetric (weylLogReal (𝔇 (hC ω)) ξ α) (ball c R) p.1.1 p.1.2)
    {U V W T Q' Q : Set ℂ} {δ : ℝ} (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    {M : ℝ} (hU : MeasurableSet U) {A : Set ℂ} (hA : MeasurableSet A) (q : ℝ) :
    ∃ D' : Ω → ℂ → ℂ → ℝ,
      (∀ x ∈ ball c R, ∀ y ∈ ball c R, Measurable fun ω => D' ω x y) ∧
      (∀ ω, IsLengthMetricOn (ball c R) (D' ω)) ∧
      MeasurableSet (failureSetLoc c R κ D' (pinchOmegaGeom W Q δ) U V W T Q' Q δ M A q) ∧
      ∀ᵐ ω ∂P, ∀ z : ℂ,
        ((z, ω) ∈ failureSetLoc c R κ (fun ω => decoderOn (ball c R) (m (localMeanZeroObs α (ball c R) (hC ω))))
            (pinchOmegaGeom W Q δ) U V W T Q' Q δ M A q ↔
          (z, ω) ∈ failureSetLoc c R κ D' (pinchOmegaGeom W Q δ) U V W T Q' Q δ M A q) := by
  have hBc : IsConnected (ball c R) := (convex_ball c R).isConnected (Metric.nonempty_ball.mpr hR)
  have hBcpt : IsCompact (closure (ball c R)) :=
    (isCompact_closedBall c R).of_isClosed_subset isClosed_closure closure_ball_subset_closedBall
  have h0c : (0 : ℂ) ∉ closure (ball c R) := fun h => h0ball (closure_ball_subset_closedBall h)
  have hm' : Measurable fun ω => m (localMeanZeroObs α (ball c R) (hC ω)) :=
    hm.comp (measurable_localMeanZeroObs_ae hG α (ball c R))
  have hLen : ∀ᵐ ω ∂P, IsLengthMetricOn (ball c R)
      (decoderOn (ball c R) (m (localMeanZeroObs α (ball c R) (hC ω)))) :=
    ae_isLengthMetricOn_decoderOn hL hG (cutoffInternalLengthStmt ξ α) isOpen_ball hBc hBcpt h0c
      (fun ω => m (localMeanZeroObs α (ball c R) (hC ω))) hid
  obtain ⟨hOo, h0O, hsph, -⟩ := FirstPassS11ap.pinchOmegaGeom_certificate_data hgeo
  exact exists_modified_failureSet_ae hR κ P (fun ω => decoderOn (ball c R) (m (localMeanZeroObs α (ball c R) (hC ω))))
    (measurable_decoderOn hm') hLen hOo h0O hsph hU hgeo.delta_pos hA q

end FirstPassS11ah

end
