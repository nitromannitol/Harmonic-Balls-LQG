import HarmonicBalls.FirstPass.Phase2.CanonicalDecodersCanonXiProof
import HarmonicBalls.FirstPass.Phase2.ForallXiDimensionDerived

/-!
# The forall-`ξ` results from the Weyl exponent identification alone

The canonical-exponent measurable decoders `LQGCanonicalDecodersMeasurableExistCanonXiStmt.{0}` follow from the
identification `lqgXi γ = γ / d_γ` (`lqgCanonicalDecodersMeasurableExistCanonXi_of_dim`), and that identification is a
theorem (`lqgXi_eq_xiGamma_derived`, from the Liouville graph-distance dimension of Ding-Gwynne). So the
canonical-exponent decoders hold with no hypothesis, and the forall-`ξ` forms of Lemma 11.13 (corrected),
Proposition 11.11 and Theorem 1.2 rest on one literature input: every γ-LQG metric has Weyl exponent `γ / d_γ`
(`hXi`; Ding-Funaki-Gwynne-Pfeffer-Sun, Theorem 1.5, with Ding-Gwynne).

## Main results

* `HarmonicBalls.lqgCanonicalDecodersMeasurableExistCanonXi_derived`: the canonical-exponent measurable decoders.
* `HarmonicBalls.lqgCanonicalDecodersMeasurableExist_of_xi_derived`: the free-`ξ` measurable decoders from `hXi`.
* `HarmonicBalls.correctedLemma11_13_of_xi_derived`, `HarmonicBalls.firstPass_11_11_of_xi_derived`,
  `HarmonicBalls.firstPass_1_2_of_xi_derived`: the forall-`ξ` rows from `hXi`.
-/

universe u

namespace HarmonicBalls

/-- **The measurable canonical decoders at the canonical exponent**, with no hypothesis: the canonical measure kernel
and the canonical metric decoder of a reference γ-LQG metric, at `ξ = lqgXi γ = γ / d_γ`. -/
theorem lqgCanonicalDecodersMeasurableExistCanonXi_derived : LQGCanonicalDecodersMeasurableExistCanonXiStmt.{0} :=
  lqgCanonicalDecodersMeasurableExistCanonXi_of_dim lqgXi_eq_xiGamma_derived

/-- **The free-`ξ` measurable decoders** from the Weyl exponent identification `hXi` alone. -/
theorem lqgCanonicalDecodersMeasurableExist_of_xi_derived
    (hXi : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
      ξ = LQGMetric.xiGamma γ) :
    LQGCanonicalDecodersMeasurableExistStmt.{0} :=
  lqgCanonicalDecodersMeasurableExist_of_canonXi_derived hXi lqgCanonicalDecodersMeasurableExistCanonXi_derived

/-- **Lemma 11.13 (corrected, every `ξ`, every universe)** from the Weyl exponent identification `hXi` alone. -/
theorem correctedLemma11_13_of_xi_derived
    (hXi : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
      ξ = LQGMetric.xiGamma γ) :
    CorrectedLemma11_13Stmt.{u} :=
  correctedLemma11_13_of_canonXiDecoders_derived lqgCanonicalDecodersMeasurableExistCanonXi_derived hXi

/-- **Proposition 11.11 (every `ξ`, every universe)** from the Weyl exponent identification `hXi` alone. -/
theorem firstPass_11_11_of_xi_derived
    (hXi : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
      ξ = LQGMetric.xiGamma γ) :
    HarmonicBallNotMetricBallStmt.{u} :=
  firstPass_11_11_of_canonXiDecoders_derived lqgCanonicalDecodersMeasurableExistCanonXi_derived hXi

/-- **Theorem 1.2 (every `ξ`, every universe)** from the Weyl exponent identification `hXi` alone. -/
theorem firstPass_1_2_of_xi_derived
    (hXi : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
      ξ = LQGMetric.xiGamma γ) :
    HarmonicBallNoveltyStmt.{u} :=
  firstPass_1_2_of_canonXiDecoders_derived lqgCanonicalDecodersMeasurableExistCanonXi_derived hXi

end HarmonicBalls
