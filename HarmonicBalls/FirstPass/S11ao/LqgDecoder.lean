import HarmonicBalls.FirstPass.S11ah.LQGDecoder
import HarmonicBalls.FirstPass.S11ao

/-!
# The P-a.s. modification of the Step 5 decoders

This file closes the link between the almost-sure length property `hae` and the device
`FirstPassS11ao.exists_measurable_localLengthModification` (`S11ao.lean`).

* `hae` is `FirstPassS11ah.ae_isLengthMetricOn_decoderOn` (`S11ah/LQGDecoder.lean`). Its inputs are identity (18) (the
  hypothesis `hid`), the LQG metric structure `IsLQGMetric` with the whole-plane GFF (the a.s. Euclidean length property
  `ae_isEuclideanLengthMetric_of_lqg`, from the field `satisfiesLQGMetricAxioms` of `IsLQGMetric`), and the named input R1
  `CutoffInternalLengthStmt` (hypothesis `hR1`, item 4 gives the length property of the internal distance of the
  logarithmic Weyl scaling on the disc). No frozen input (`LQGMetricLengthUnivFrozen`, `LQGMetricFieldAxiomsUnivFrozen`,
  `LQGMetricSatisfiesAxiomsUnivFrozen`) is used.
* N4, the ofReal-length property of `b · I_B(g)` on the disc, is `IsLengthMetricOn.const_mul` (`S11ah/LengthScale.lean`),
  with the `ofReal_eq_internalMetric` field; see `ofReal_mul_internalReal_eq_internalMetric` below.
-/

open MeasureTheory Set Metric Filter Topology HarmonicBalls
open scoped ENNReal
noncomputable section

namespace FirstPassS11ao

open FirstPassS11ah

/-- **N4 (ofReal-length property of `b · I_B(g)`).** If `internalReal G B` is a length metric on `B` and `b > 0`, then
for `x, y ∈ B`, `ofReal (b · I_B(G)(x, y)) = internalMetric (b · I_B(G)) B x y`, the length property of the scaled
internal distance. Immediate from `IsLengthMetricOn.const_mul` (`S11ah/LengthScale.lean`). -/
theorem ofReal_mul_internalReal_eq_internalMetric {B : Set ℂ} {G : ℂ → ℂ → ℝ}
    (hR : IsLengthMetricOn B (internalReal G B)) {b : ℝ} (hb : 0 < b) {x y : ℂ} (hx : x ∈ B) (hy : y ∈ B) :
    ENNReal.ofReal (b * internalReal G B x y) =
      internalMetric (fun u v => b * internalReal G B u v) B x y :=
  (hR.const_mul hb).ofReal_eq_internalMetric x hx y hy

/-- **Modified Step 5 decoders, P-a.s. form.** Under the LQG metric `𝔇` (`IsLQGMetric`), the whole-plane GFF `hC`, the
named input R1 `CutoffInternalLengthStmt` and identity (18) for the continuous decoders `mω ω` on the disc `ball c R`
(`0 ∉ closedBall c R`), there is a measurable full-measure set `H` and a modification `D'` such that: `D' ω` is an
`IsLengthMetricOn (ball c R)` metric for every `ω`; `D'` is measurable in `ω` at each pair of points of the disc; on `H`
`D' ω` is the decoder `decoderOn (ball c R) (mω ω)` (which is `IsLengthMetricOn` there); off `H` it is the Euclidean
distance. The almost-sure input `hae` is discharged by `ae_isLengthMetricOn_decoderOn`. -/
theorem exists_localDecoderModification_of_lqg {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hL : IsLQGMetric γ ξ 𝔇) (hG : IsWholePlaneGFF P hC hcirc) (hR1 : CutoffInternalLengthStmt ξ α)
    {c : ℂ} {R : ℝ} (hR : 0 < R) (h0ball : (0 : ℂ) ∉ closedBall c R)
    (mω : Ω → ContinuousMap ↥(ball c R ×ˢ ball c R : Set (ℂ × ℂ)) ℝ) (hm : Measurable mω)
    (hid : ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧ ∀ p : ↥(ball c R ×ˢ ball c R : Set (ℂ × ℂ)),
      ENNReal.ofReal (mω ω p) =
        ENNReal.ofReal b * internalMetric (weylLogReal (𝔇 (hC ω)) ξ α) (ball c R) p.1.1 p.1.2) :
    ∃ H : Set Ω, MeasurableSet H ∧ P Hᶜ = 0 ∧ ∃ D' : Ω → ℂ → ℂ → ℝ,
      (∀ x ∈ ball c R, ∀ y ∈ ball c R, Measurable fun ω => D' ω x y) ∧
      (∀ ω, IsLengthMetricOn (ball c R) (D' ω)) ∧
      (∀ ω ∈ H, IsLengthMetricOn (ball c R) (decoderOn (ball c R) (mω ω)) ∧
        D' ω = decoderOn (ball c R) (mω ω)) ∧
      (∀ ω ∉ H, D' ω = fun z w => dist z w) := by
  have hBc : IsConnected (ball c R) := (convex_ball c R).isConnected (Metric.nonempty_ball.mpr hR)
  have hBcpt : IsCompact (closure (ball c R)) :=
    (isCompact_closedBall c R).of_isClosed_subset isClosed_closure closure_ball_subset_closedBall
  have h0c : (0 : ℂ) ∉ closure (ball c R) := fun h => h0ball (closure_ball_subset_closedBall h)
  have hLen : ∀ᵐ ω ∂P, IsLengthMetricOn (ball c R) (decoderOn (ball c R) (mω ω)) :=
    ae_isLengthMetricOn_decoderOn hL hG hR1 isOpen_ball hBc hBcpt h0c mω hid
  exact exists_measurable_localLengthModification (P := P) (D := fun ω => decoderOn (ball c R) (mω ω))
    (convex_ball c R) isOpen_ball (measurable_decoderOn hm) hLen

end FirstPassS11ao

end
