import HarmonicBalls.FirstPass.S11n
import HarmonicBalls.FirstPass.Frozen.S11n
import HarmonicBalls.FirstPass.Frozen.S11j
import HarmonicBalls.Proposed.LQG
import HarmonicBalls.Steps.Sec11.MetricArcLength

/-! # Base comparison of LQG metric assignments at insertion zero (fp-S11ak, owner z6)

`LQGMetricBaseComparisonStmt` (CHATGPT-lh-R4-R5.md §R5b.1): two γ-LQG metric assignments `𝔇₀`, `𝔇` (Gwynne-Miller
arXiv:1905.00383v3, Theorem 1.2, p. 6) differ, on a whole-plane GFF model, by one random positive factor for all
endpoint pairs.

The proof is the bridge from the frozen canonical identification `LQGCanonicalDecodersExistStmt`
(`FirstPass/Frozen/S11n.lean`) at insertion `α₀ = 0`: both metric assignments, read as `IsLQGMetricOfField` at
`α₀ = 0`, are identified with positive multiples of one canonical decoder `Dd`, on a common conull event.
The insertion-zero Weyl scaling is the metric itself (`IsEuclideanLengthMetric.weylScaling_zero`).

Inputs: `LQGCanonicalDecodersExistStmt.{u}` (frozen), `LQGMetricLengthUnivFrozen.{u}` (frozen, axiom I of Fact 2.2 for
`𝔇(h^ℂ)`), and `LQGMeasureExistence` (Proposed, pending source-check; used only to supply the measure that the
identification clause takes as a premise).
-/

namespace HarmonicBalls.S11ak

open MeasureTheory

universe u

/-- The base comparison statement (CHATGPT-lh-R4-R5.md §R5b.1, exact form): for `0 < γ < 2` and two γ-LQG metrics
`𝔇₀`, `𝔇` of the same Weyl exponent `ξ`, almost surely on every whole-plane GFF model there is a positive constant `b`
with `𝔇(h^ℂ) = b · 𝔇₀(h^ℂ)` on all endpoint pairs. -/
def LQGMetricBaseComparisonStmt.{v} : Prop :=
  ∀ (γ ξ : ℝ), 0 < γ → γ < 2 →
  ∀ (𝔇₀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ),
    HarmonicBalls.IsLQGMetric γ ξ 𝔇₀ →
    HarmonicBalls.IsLQGMetric γ ξ 𝔇 →
  ∀ (Ω : Type v) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    HarmonicBalls.IsWholePlaneGFF P hC hcirc →
    ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧ ∀ x y : ℂ,
      𝔇 (hC ω) x y = b * 𝔇₀ (hC ω) x y

/-- The LQG metric of a whole-plane GFF, read at insertion zero, is an `IsLQGMetricOfField` at `α₀ = 0` once it is a
Euclidean length metric almost surely (the weight-zero Weyl scaling is the metric itself,
`IsEuclideanLengthMetric.weylScaling_zero`). -/
theorem isLQGMetricOfField_zero_of_length (γ ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ)
    (h𝔇 : HarmonicBalls.IsLQGMetric γ ξ 𝔇) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hLen : ∀ᵐ ω ∂P, HarmonicBalls.IsEuclideanLengthMetric (𝔇 (hC ω))) :
    HarmonicBalls.IsLQGMetricOfField P γ ξ 0 hC (fun ω u v => 𝔇 (hC ω) u v) := by
  refine ⟨𝔇, h𝔇, ?_⟩
  have hw : (fun x : ℂ => -(0 : ℝ) * Real.log ‖x‖) = fun _ => 0 := by
    funext x
    simp
  filter_upwards [hLen] with ω hω
  intro u v
  refine ⟨?_, ?_⟩
  · have htri := hω.triangle u v u
    rw [hω.self_eq_zero, hω.symm v u] at htri
    linarith
  · rw [hw]
    exact (hω.weylScaling_zero ξ u v).symm

/-- **Base comparison at insertion zero** (`LQGMetricBaseComparisonStmt`). From the frozen canonical decoders
(`LQGCanonicalDecodersExistStmt.{u}`) at `α₀ = 0`: the identification clause, applied with one common insertion-zero
LQG measure to the two metric assignments, gives positive constants `b₁`, `b₀` with `𝔇 = b₁ X` and `𝔇₀ = b₀ X` for the
same canonical decoder value `X`; hence `𝔇 = (b₁ / b₀) 𝔇₀` almost surely. -/
theorem lqgMetricBaseComparison_of_canonical
    (hEx : HarmonicBalls.LQGCanonicalDecodersExistStmt.{u})
    (hLen : HarmonicBalls.LQGMetricLengthUnivFrozen.{u})
    (hMeas : ∀ (γ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), HarmonicBalls.LQGMeasureExistence P γ 0 hC hcirc) :
    LQGMetricBaseComparisonStmt.{u} := by
  intro γ ξ hγ hγ2 𝔇₀ 𝔇 h₀ h𝔇 Ω _ P hC hcirc hG
  have hα : (0 : ℝ) < HarmonicBalls.lqgQ γ := by
    unfold HarmonicBalls.lqgQ
    positivity
  obtain ⟨Dμ, Dd, hid⟩ := hEx γ ξ 0 hγ hγ2 hα
  obtain ⟨μ, hμ⟩ := hMeas γ Ω P hC hcirc hG hγ hγ2 hα
  have hl₀ := hLen γ ξ 𝔇₀ hγ hγ2 h₀ Ω P hC hcirc hG
  have hl := hLen γ ξ 𝔇 hγ hγ2 h𝔇 Ω P hC hcirc hG
  have hD₀ := hid Ω P hC hcirc μ (fun ω u v => 𝔇₀ (hC ω) u v) hG hμ
    (isLQGMetricOfField_zero_of_length γ ξ 𝔇₀ h₀ P hC hl₀)
  have hD := hid Ω P hC hcirc μ (fun ω u v => 𝔇 (hC ω) u v) hG hμ
    (isLQGMetricOfField_zero_of_length γ ξ 𝔇 h𝔇 P hC hl)
  filter_upwards [hD₀, hD] with ω h₀ h
  obtain ⟨a₀, b₀, ha₀, hb₀, -, hX₀⟩ := h₀
  obtain ⟨a, b, ha, hb, -, hX⟩ := h
  refine ⟨b / b₀, div_pos hb hb₀, fun x y => ?_⟩
  have e₀ := hX₀ x y
  have e := hX x y
  rw [e, e₀]
  field_simp

end HarmonicBalls.S11ak
