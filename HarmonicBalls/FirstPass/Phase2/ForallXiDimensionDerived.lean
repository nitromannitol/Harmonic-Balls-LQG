import HarmonicBalls.FirstPass.Phase2.ForallXiDecodersDerived
import HarmonicBalls.FirstPass.Phase2.LQGGraphDimensionDerived

/-!
# The forall-`ξ` results without the dimension input

The canonical Weyl exponent of the paper, `lqgXi γ = γ / lqgGraphDimension γ`, equals
`LQGMetric.xiGamma γ = γ / d_γ`: the graph-distance dimension of the whole-plane GFF is
`d_γ = 2 / chiDZZ γ` (`isWholePlaneLQGDimension_dGamma`, Ding--Gwynne, arXiv:1807.01072v3,
Theorem 1.4). This supplies the input `hDimW` of the forall-`ξ` forms of Lemma 11.13 (corrected),
Proposition 11.11 and Theorem 1.2, and of the reduction of the free-`ξ` measurable decoders to the
canonical exponent; what remains are the canonical-exponent decoders `hCanonX` and the Weyl exponent
identification `hXi`.

## Main results

* `HarmonicBalls.lqgXi_eq_xiGamma_derived`: `lqgXi γ = LQGMetric.xiGamma γ` for `0 < γ < 2`.
* `HarmonicBalls.lqgCanonicalDecodersMeasurableExist_of_canonXi_derived`: the free-`ξ` measurable
  decoders from `hXi` and the canonical-exponent decoders.
* `HarmonicBalls.correctedLemma11_13_of_canonXiDecoders_derived`,
  `HarmonicBalls.firstPass_11_11_of_canonXiDecoders_derived`,
  `HarmonicBalls.firstPass_1_2_of_canonXiDecoders_derived`: the forall-`ξ` results from `hCanonX`
  and `hXi` alone.
-/

universe u

namespace HarmonicBalls

/-- **The canonical Weyl exponents agree**: `lqgXi γ = γ / d_γ` for `0 < γ < 2`, where `d_γ` is
the Liouville graph-distance dimension (Ding--Gwynne, arXiv:1807.01072v3, Theorem 1.4). -/
theorem lqgXi_eq_xiGamma_derived :
    ∀ γ : ℝ, 0 < γ → γ < 2 → lqgXi γ = LQGMetric.xiGamma γ :=
  lqgXi_eq_xiGamma_of_dimension fun _ hγ hγ2 => isWholePlaneLQGDimension_dGamma hγ hγ2

/-- **The free-`ξ` measurable decoders from the canonical-exponent ones**, given only that every
γ-LQG metric has Weyl exponent `LQGMetric.xiGamma γ` (`hXi`). -/
theorem lqgCanonicalDecodersMeasurableExist_of_canonXi_derived
    (hXi : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
      ξ = LQGMetric.xiGamma γ)
    (h : LQGCanonicalDecodersMeasurableExistCanonXiStmt.{u}) :
    LQGCanonicalDecodersMeasurableExistStmt.{u} :=
  lqgCanonicalDecodersMeasurableExist_of_canonXi hXi lqgXi_eq_xiGamma_derived h

/-- **Lemma 11.13 (corrected, every `ξ`, every universe)** from the canonical-exponent measurable
decoders `hCanonX` and the Weyl exponent identification `hXi`. -/
theorem correctedLemma11_13_of_canonXiDecoders_derived
    (hCanonX : LQGCanonicalDecodersMeasurableExistCanonXiStmt.{0})
    (hXi : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
      ξ = LQGMetric.xiGamma γ) :
    CorrectedLemma11_13Stmt.{u} :=
  correctedLemma11_13_of_dimension hCanonX hXi fun _ hγ hγ2 => isWholePlaneLQGDimension_dGamma hγ hγ2

/-- **Proposition 11.11 (every `ξ`, every universe)** from `hCanonX` and `hXi`. -/
theorem firstPass_11_11_of_canonXiDecoders_derived
    (hCanonX : LQGCanonicalDecodersMeasurableExistCanonXiStmt.{0})
    (hXi : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
      ξ = LQGMetric.xiGamma γ) :
    HarmonicBallNotMetricBallStmt.{u} :=
  firstPass_11_11_of_dimension hCanonX hXi fun _ hγ hγ2 => isWholePlaneLQGDimension_dGamma hγ hγ2

/-- **Theorem 1.2 (every `ξ`, every universe)** from `hCanonX` and `hXi`. -/
theorem firstPass_1_2_of_canonXiDecoders_derived
    (hCanonX : LQGCanonicalDecodersMeasurableExistCanonXiStmt.{0})
    (hXi : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
      ξ = LQGMetric.xiGamma γ) :
    HarmonicBallNoveltyStmt.{u} :=
  firstPass_1_2_of_dimension hCanonX hXi fun _ hγ hγ2 => isWholePlaneLQGDimension_dGamma hγ hγ2

end HarmonicBalls
