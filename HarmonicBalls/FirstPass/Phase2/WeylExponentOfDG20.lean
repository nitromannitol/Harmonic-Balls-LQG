import HarmonicBalls.FirstPass.Phase2.WeylExponentOfWeakMetric
import LatticeProb.Probability.WeakLQGMetricExponentDG20

/-!
# The Weyl exponent identification, unconditionally

`HarmonicBalls/FirstPass/Phase2/WeylExponentOfWeakMetric.lean` derives the forall-`ξ` forms of
Lemma 11.13, Proposition 11.11 and Theorem 1.2 from one input `hexp`: every weak LQG metric with
parameter `ξ` and exponent `Q` has `Q = Q(ξ)`, the LFPP distance exponent `distExp 2 ξ`.

`HarmonicBalls/FirstPass/Phase2/WeylExponentOfPointTightness.lean` reduces `hexp` to Pfeffer's
Proposition 1.9 (`hPL`, arXiv:2104.04020, p. 7) and the point-to-point tightness of supercritical
LFPP of Ding-Gwynne (`hR1`, Section 4). The Lattice-Probability theorems used here supply both:
* `LQGMetric.HeatCircle.distExp_eq_of_isWeakLQGMetric_of_dg20` proves `hexp` from the Ding-Gwynne
  percolation estimate `hPerc` and exponent relation `hExp` for supercritical LFPP (through
  `iface_plThm19_of_dg20` for `hPL` and `dg20Section4_point_tight_of_inputs` for `hR1`);
* `LQGMetric.HeatCircle.distExp_eq_of_isWeakLQGMetric` proves `hexp` with no hypothesis, the
  percolation estimate and the exponent relation being proved for every `ξ > 0`.

## Main statements

* `HarmonicBalls.xi_eq_xiGamma_derived`: every γ-LQG metric has `ξ = γ / d_γ`.
* `HarmonicBalls.correctedLemma11_13_forallXi_derived`,
  `HarmonicBalls.firstPass_11_11_forallXi_derived`,
  `HarmonicBalls.firstPass_1_2_forallXi_derived`: the forall-`ξ` rows with no hypothesis.
* The `_of_dg20` forms take the two Ding-Gwynne inputs `hPerc` and `hExp` explicitly.
-/

namespace HarmonicBalls

universe u

section DG20

variable (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
  (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)

include hPerc hExp

/-- **Every γ-LQG metric has `ξ = γ / d_γ`**, from the Ding-Gwynne percolation estimate and
exponent relation for supercritical LFPP. -/
theorem xi_eq_xiGamma_of_dg20 :
    ∀ γ ξ : ℝ, 0 < γ → γ < 2 → ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
      ξ = LQGMetric.xiGamma γ :=
  xi_eq_xiGamma_of_weakLQGMetricExponent
    (LQGMetric.HeatCircle.distExp_eq_of_isWeakLQGMetric_of_dg20 hPerc hExp)

/-- **Lemma 11.13 (corrected, every `ξ`, every universe)** from the Ding-Gwynne estimates. -/
theorem correctedLemma11_13_of_dg20 : CorrectedLemma11_13Stmt.{u} :=
  correctedLemma11_13_of_weakLQGMetricExponent
    (LQGMetric.HeatCircle.distExp_eq_of_isWeakLQGMetric_of_dg20 hPerc hExp)

/-- **Proposition 11.11 (every `ξ`, every universe)** from the Ding-Gwynne estimates. -/
theorem firstPass_11_11_of_dg20 : HarmonicBallNotMetricBallStmt.{u} :=
  firstPass_11_11_of_weakLQGMetricExponent
    (LQGMetric.HeatCircle.distExp_eq_of_isWeakLQGMetric_of_dg20 hPerc hExp)

/-- **Theorem 1.2 (every `ξ`, every universe)** from the Ding-Gwynne estimates. -/
theorem firstPass_1_2_of_dg20 : HarmonicBallNoveltyStmt.{u} :=
  firstPass_1_2_of_weakLQGMetricExponent
    (LQGMetric.HeatCircle.distExp_eq_of_isWeakLQGMetric_of_dg20 hPerc hExp)

end DG20

/-- **Every γ-LQG metric has Weyl exponent `ξ_γ = γ / d_γ`**, with no hypothesis. -/
theorem xi_eq_xiGamma_derived :
    ∀ γ ξ : ℝ, 0 < γ → γ < 2 → ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
      ξ = LQGMetric.xiGamma γ :=
  xi_eq_xiGamma_of_weakLQGMetricExponent LQGMetric.HeatCircle.distExp_eq_of_isWeakLQGMetric

/-- **Lemma 11.13 (corrected, every `ξ`, every universe)**, with no hypothesis. -/
theorem correctedLemma11_13_forallXi_derived : CorrectedLemma11_13Stmt.{u} :=
  correctedLemma11_13_of_weakLQGMetricExponent LQGMetric.HeatCircle.distExp_eq_of_isWeakLQGMetric

/-- **Proposition 11.11 (every `ξ`, every universe)**, with no hypothesis. -/
theorem firstPass_11_11_forallXi_derived : HarmonicBallNotMetricBallStmt.{u} :=
  firstPass_11_11_of_weakLQGMetricExponent LQGMetric.HeatCircle.distExp_eq_of_isWeakLQGMetric

/-- **Theorem 1.2 (every `ξ`, every universe)**, with no hypothesis. -/
theorem firstPass_1_2_forallXi_derived : HarmonicBallNoveltyStmt.{u} :=
  firstPass_1_2_of_weakLQGMetricExponent LQGMetric.HeatCircle.distExp_eq_of_isWeakLQGMetric

end HarmonicBalls
