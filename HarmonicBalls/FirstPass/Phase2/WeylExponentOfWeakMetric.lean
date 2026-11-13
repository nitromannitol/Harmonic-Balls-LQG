import HarmonicBalls.FirstPass.Phase2.ForallXiWeylExponentDerived
import HarmonicBalls.FirstPass.Phase2.LQGMetricXiPos
import HarmonicBalls.Proofs.GFF.DistributionMetricAxioms
import LatticeProb.LQG.ContMetricStrongWeak

/-!
# The Weyl exponent of a γ-LQG metric from the scaling exponent of weak LQG metrics

A γ-LQG metric `𝔇` with Weyl exponent `ξ` (`IsLQGMetric γ ξ 𝔇`, `0 < γ < 2`) has `ξ > 0`
(`isLQGMetric_xi_pos`), and its metric assignment on distributions (`distributionMetric 𝔇`) satisfies the
Gwynne-Miller axioms with Weyl exponent `ξ` and exponent `Q_γ = 2/γ + γ/2` (`DistributionMetricAxioms.lean`).
As a lower semicontinuous metric it is then a weak LQG metric with parameter `ξ` and exponent `Q_γ` in the
sense of Ding-Gwynne (arXiv:2110.00177, Section 1.2). By Pfeffer (arXiv:2104.04020, Proposition 1.9, p. 7),
the exponent of a weak LQG metric with parameter `ξ` is the LFPP distance exponent `Q(ξ)` (`hexp`); and
`Q(ξ) = Q_γ` forces `ξ = ξ_γ = γ / d_γ` (Lattice-Probability `distExp_two_eq_Q_iff`). So the Weyl exponent
identification `hXi` of the forall-`ξ` rows rests on Pfeffer's Proposition 1.9 alone.

## Main results

* `HarmonicBalls.xi_eq_xiGamma_of_weakLQGMetricExponent`: `hXi` from `hexp`.
* `HarmonicBalls.correctedLemma11_13_of_weakLQGMetricExponent`,
  `HarmonicBalls.firstPass_11_11_of_weakLQGMetricExponent`,
  `HarmonicBalls.firstPass_1_2_of_weakLQGMetricExponent`: the forall-`ξ` rows from `hexp`.
-/

noncomputable section

open MeasureTheory

namespace HarmonicBalls

universe u

/-- **Every γ-LQG metric has Weyl exponent `ξ_γ = γ / d_γ`**, given Pfeffer's Proposition 1.9
(arXiv:2104.04020, p. 7) in the form `hexp`: every weak LQG metric with parameter `ξ` and exponent `Q`
has `Q = Q(ξ)`, the LFPP distance exponent `distExp 2 ξ`. -/
theorem xi_eq_xiGamma_of_weakLQGMetricExponent
    (hexp : ∀ (ξ' : Set.Ioi (0 : ℝ)) (Q : ℝ)
      (D' : LQGMetric.DistC → SupercriticalLQGUniqueness.LSCMetric),
      SupercriticalLQGUniqueness.IsWeakLQGMetric ξ' Q D' → HigherDimLQGMetric.distExp 2 ξ' = Q) :
    ∀ γ ξ : ℝ, 0 < γ → γ < 2 → ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
      ξ = LQGMetric.xiGamma γ := by
  intro γ ξ hγ hγ2 𝔇 h𝔇
  have hξ : 0 < ξ := isLQGMetric_xi_pos γ ξ 𝔇 hγ hγ2 h𝔇
  have hcm : ∀ D : ℂ → ℂ → ℝ, LatticeProb.LQG.IsEuclideanLengthMetric D →
      ∃ d : LQGMetric.ContMetric, (∀ u v, d.1 (u, v) = D u v) ∧ d.IsLength :=
    fun _ hD => LatticeProb.LQG.exists_contMetric_of_isEuclideanLengthMetric hD
  exact LatticeProb.LQG.eq_xiGamma_of_axioms hγ hγ2 hξ
    (measurable_distributionMetric h𝔇.measurable_apply)
    (by intro Ω _ P _ h hh; exact ae_isLength_distributionMetric h𝔇 hcm hh)
    (by intro Ω _ P _ h hh U; exact locality_distributionMetric h𝔇 hcm hh U)
    (by intro Ω _ P _ h hh; exact ae_weylScale_distributionMetric h𝔇 hcm hh)
    (by intro Ω _ P _ h hh r hr z; exact ae_coord_distributionMetric h𝔇 hcm hh hr z) hexp

/-- **Lemma 11.13 (corrected, every `ξ`, every universe)** from Pfeffer's Proposition 1.9 (`hexp`). -/
theorem correctedLemma11_13_of_weakLQGMetricExponent
    (hexp : ∀ (ξ' : Set.Ioi (0 : ℝ)) (Q : ℝ)
      (D' : LQGMetric.DistC → SupercriticalLQGUniqueness.LSCMetric),
      SupercriticalLQGUniqueness.IsWeakLQGMetric ξ' Q D' → HigherDimLQGMetric.distExp 2 ξ' = Q) :
    CorrectedLemma11_13Stmt.{u} :=
  correctedLemma11_13_of_xi_derived (xi_eq_xiGamma_of_weakLQGMetricExponent hexp)

/-- **Proposition 11.11 (every `ξ`, every universe)** from Pfeffer's Proposition 1.9 (`hexp`). -/
theorem firstPass_11_11_of_weakLQGMetricExponent
    (hexp : ∀ (ξ' : Set.Ioi (0 : ℝ)) (Q : ℝ)
      (D' : LQGMetric.DistC → SupercriticalLQGUniqueness.LSCMetric),
      SupercriticalLQGUniqueness.IsWeakLQGMetric ξ' Q D' → HigherDimLQGMetric.distExp 2 ξ' = Q) :
    HarmonicBallNotMetricBallStmt.{u} :=
  firstPass_11_11_of_xi_derived (xi_eq_xiGamma_of_weakLQGMetricExponent hexp)

/-- **Theorem 1.2 (every `ξ`, every universe)** from Pfeffer's Proposition 1.9 (`hexp`). -/
theorem firstPass_1_2_of_weakLQGMetricExponent
    (hexp : ∀ (ξ' : Set.Ioi (0 : ℝ)) (Q : ℝ)
      (D' : LQGMetric.DistC → SupercriticalLQGUniqueness.LSCMetric),
      SupercriticalLQGUniqueness.IsWeakLQGMetric ξ' Q D' → HigherDimLQGMetric.distExp 2 ξ' = Q) :
    HarmonicBallNoveltyStmt.{u} :=
  firstPass_1_2_of_xi_derived (xi_eq_xiGamma_of_weakLQGMetricExponent hexp)

end HarmonicBalls
