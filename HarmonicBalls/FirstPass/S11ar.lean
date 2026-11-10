import HarmonicBalls.FirstPass.S11ah.LQGDecoder
import HarmonicBalls.FirstPass.S11ah.CutoffLength
import HarmonicBalls.FirstPass.S11ao.LqgDecoder

/-!
# First pass, the decoder modification assembled from the LQG metric (fp-S11ar-11-13-decoder-modification-assembly, owner q3)

This file is downstream of `S11ah/LQGDecoder.lean` (which imports `S11ah/Modified.lean`, where the hypothesis `hq3` lived) and of
`S11ao/LqgDecoder.lean`. It breaks the cycle `Modified → S11ao → LQGDecoder → Modified` by discharging `hq3` here.

* Named input R1 `CutoffInternalLengthStmt ξ α` is discharged by `FirstPassS11ah.cutoffInternalLengthStmt ξ α`
  (`S11ah/CutoffLength.lean`, proof of n4), so it is not a hypothesis of the statements below.
* `localLengthModification_decoderOn_of_lqg` is the instance of `hq3` (the `P`-a.s. modification
  `LocalLengthModification P c R D` of `S11ah/Modified.lean`) for the decoders `D ω = decoderOn (ball c R) (mω ω)`, from
  `FirstPassS11ao.exists_localDecoderModification_of_lqg`.
* `decoderOn_ae_length_and_modification` is the combined statement consumed by n3 and n4: the almost-sure length property
  `hae` (`FirstPassS11ah.ae_isLengthMetricOn_decoderOn`) together with the instance of `hq3`. Its hypotheses are only the LQG
  metric structure `IsLQGMetric`, the whole-plane GFF `IsWholePlaneGFF`, the disc `ball c R` with `0 ∉ closedBall c R`, and identity
  (18) for the continuous decoders `mω ω`. No frozen input and no named input is used.
-/

open MeasureTheory Set Metric Filter Topology HarmonicBalls
open scoped ENNReal
noncomputable section

namespace FirstPassS11ar

open FirstPassS11ah

/-- **Instance of `hq3` (fp-S11ar).** For the LQG metric `𝔇` and the whole-plane GFF `hC`, the decoder family
`ω ↦ decoderOn (ball c R) (mω ω)` has a `P`-a.s. modification `LocalLengthModification P c R (...)`: a family `D'` measurable in
each pair of points of `ball c R`, an `IsLengthMetricOn (ball c R)` metric for every `ω`, and `D' ω = decoderOn (ball c R) (mω ω)`
`P`-a.s. The input R1 is `cutoffInternalLengthStmt`. -/
theorem localLengthModification_decoderOn_of_lqg {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hL : IsLQGMetric γ ξ 𝔇) (hG : IsWholePlaneGFF P hC hcirc)
    {c : ℂ} {R : ℝ} (hR : 0 < R) (h0ball : (0 : ℂ) ∉ closedBall c R)
    (mω : Ω → ContinuousMap ↥(ball c R ×ˢ ball c R : Set (ℂ × ℂ)) ℝ) (hm : Measurable mω)
    (hid : ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧ ∀ p : ↥(ball c R ×ˢ ball c R : Set (ℂ × ℂ)),
      ENNReal.ofReal (mω ω p) =
        ENNReal.ofReal b * internalMetric (weylLogReal (𝔇 (hC ω)) ξ α) (ball c R) p.1.1 p.1.2) :
    LocalLengthModification P c R (fun ω => decoderOn (ball c R) (mω ω)) := by
  obtain ⟨H, -, hH0, D', hDm, hlen, hgood, -⟩ :=
    FirstPassS11ao.exists_localDecoderModification_of_lqg hL hG (cutoffInternalLengthStmt ξ α) hR h0ball mω hm hid
  refine ⟨D', hDm, hlen, ?_⟩
  have hH : ∀ᵐ ω ∂P, ω ∈ H := by
    rw [ae_iff]
    exact hH0
  filter_upwards [hH] with ω hω
  exact (hgood ω hω).2

/-- **Combined statement for n3 and n4 (fp-S11ar; `hq3` and `hae` discharged, R1 discharged).** For the LQG metric `𝔇`
(`IsLQGMetric`), the whole-plane GFF `hC` (`IsWholePlaneGFF`), a disc `ball c R` with `0 < R` and `0 ∉ closedBall c R`, measurable
continuous decoders `mω` on `ball c R ×ˢ ball c R` satisfying identity (18) almost surely, the decoders are almost surely
`IsLengthMetricOn (ball c R)` metrics (`hae`), and they admit the `P`-a.s. measurable modification `LocalLengthModification`
(`hq3`). -/
theorem decoderOn_ae_length_and_modification {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hL : IsLQGMetric γ ξ 𝔇) (hG : IsWholePlaneGFF P hC hcirc)
    {c : ℂ} {R : ℝ} (hR : 0 < R) (h0ball : (0 : ℂ) ∉ closedBall c R)
    (mω : Ω → ContinuousMap ↥(ball c R ×ˢ ball c R : Set (ℂ × ℂ)) ℝ) (hm : Measurable mω)
    (hid : ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧ ∀ p : ↥(ball c R ×ˢ ball c R : Set (ℂ × ℂ)),
      ENNReal.ofReal (mω ω p) =
        ENNReal.ofReal b * internalMetric (weylLogReal (𝔇 (hC ω)) ξ α) (ball c R) p.1.1 p.1.2) :
    (∀ᵐ ω ∂P, IsLengthMetricOn (ball c R) (decoderOn (ball c R) (mω ω))) ∧
      LocalLengthModification P c R (fun ω => decoderOn (ball c R) (mω ω)) := by
  have hBc : IsConnected (ball c R) := (convex_ball c R).isConnected (Metric.nonempty_ball.mpr hR)
  have hBcpt : IsCompact (closure (ball c R)) :=
    (isCompact_closedBall c R).of_isClosed_subset isClosed_closure closure_ball_subset_closedBall
  have h0c : (0 : ℂ) ∉ closure (ball c R) := fun h => h0ball (closure_ball_subset_closedBall h)
  exact ⟨ae_isLengthMetricOn_decoderOn hL hG (cutoffInternalLengthStmt ξ α) isOpen_ball hBc hBcpt h0c mω hid,
    localLengthModification_decoderOn_of_lqg hL hG hR h0ball mω hm hid⟩

end FirstPassS11ar
