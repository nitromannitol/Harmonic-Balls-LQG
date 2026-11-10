import HarmonicBalls.Defs.GFF
import HarmonicBalls.Defs.LQGMetric
import HarmonicBalls.FirstPass.Frozen.S11c

/-!
# First-pass frozen inputs: whole-plane GFF existence and the normalised local metric decoder (fp-S11r, owner n2)

Two EXTERNAL facts. (1) `WholePlaneGFFExistsFrozen`: existence of a whole-plane GFF, used by the realization lemma
`hmodel_at_gamma` (FirstPass/S11r.lean, the model hypothesis of Lemma 11.13 in FirstPass/S11i/CertificateCanonical.lean).
(2) `LocalLQGMetricNormalizedMeasurableFrozen`: the measurable local metric decoder of answer section 4.1 (equation (21)),
the external input of the local metric replacement (`LocalMetricReplacementStmt`, S11r/LocalMetricReplacement.lean).
Both are general mathematics, not specific to this paper. `def ... : Prop`s, never axioms.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

universe u

/-- FIRST-PASS FROZEN. Existence of the whole-plane Gaussian free field (EXTERNAL, general): for every universe `u` there
are a probability space `Ω : Type u`, a pairing `hC` and a circle-average process `hcirc` with `IsWholePlaneGFF P hC hcirc`,
that is a centred Gaussian field with covariance `wholePlaneCov` (`log (max(|z|,1) max(|w|,1) / |z-w|)`, normalised so that
the average on the unit circle vanishes), whose circle averages are a.s. continuous in `(r, z) ∈ (0, ∞) × ℂ`.
Sources: Miller-Sheffield, Imaginary Geometry IV, arXiv:1302.4738v2 §2.2.1, pp. 46-47, eq. (2.7); Duplantier-Sheffield,
arXiv:0808.1560v2 §3.1, eq. (10) and Prop. 3.1, p. 17; Bou-Rabee-Gwynne, arXiv:2208.11795v3 §2.1, eq. (2.1), p. 8.
Used by: `hmodel_at_gamma` (FirstPass/S11r.lean), hence the model hypothesis `hmodel` of `certificate_canonical_pos`
(FirstPass/S11i/CertificateCanonical.lean).
Truth check TRUE (ChatGPT, 01:17 UTC, notes/fp-gaps/CHATGPT-hb-frozen-truth-S11r-S11j.md §1): true in every universe `u`
(by `ULift` for larger universes). -/
def WholePlaneGFFExistsFrozen : Prop :=
  ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc

/-- FIRST-PASS FROZEN, EXTERNAL. PENDING TRUTH CHECK. The measurable normalised local metric decoder of the ordinary GFF
(answer CHATGPT-n3-B1-B2.md section 4.1, equation (21)). For `0 < γ < 2`, `ξ ∈ ℝ` and a disk `D = ball c r` with
`0 ∉ closedBall c r` there are a smooth probability bump `ρ` supported in `D` (`∫ ρ = 1`) and a Borel map `M` from the
mean-zero observables of `D` (`localMeanZeroObs 0 D`) to continuous functions on `D × D` such that, for every whole-plane
GFF `(Ω, P, hC, hcirc)` and every LQG metric `𝔇` of exponent `ξ` (`IsLQGMetric γ ξ 𝔇`), almost surely
`M (obs_D g) = e^{-ξ ⟨g,ρ⟩} D_g(·,·;D)` on `D × D`, where `D_g = 𝔇 (hC ω)`, `⟨g,ρ⟩ = fieldPairing 0 (hC ω) ρ` and
`D_g(·,·;D)` is the internal metric on `D` (`internalMetric`).
Reading: `e^{-ξ⟨g,ρ⟩} D_g` is the metric `D_{g_D}` of the normalised field `g_D = g - ⟨g,ρ⟩` (`D_{h+c} = e^{ξc} D_h`),
a function of the mean-zero local observation; the statement is that this metric is a Borel function of that observation,
with the normalisation fixed by `ρ`. Continuity of `D_g` on `D × D` is part of the cited proper-domain statement.
Sources: Gwynne-Miller, arXiv:1905.00383v3 §1.2, p. 6 (the metric as a measurable map from distributions to continuous
metrics), Theorem 1.2, p. 6 (existence and uniqueness), Remark 1.5, p. 8 (proper domains); answer §4.1, eq. (21).
Used by: the local metric replacement (`LocalMetricReplacementStmt`, S11r/LocalMetricReplacement.lean), via the
countable consistency (22) and the rooted identity (20). -/
def LocalLQGMetricNormalizedMeasurableFrozen : Prop :=
  ∀ (γ ξ : ℝ) (c : ℂ) (r : ℝ), 0 < γ → γ < 2 → 0 < r → (0 : ℂ) ∉ closedBall c r →
    ∃ (ρ : ℂ → ℝ) (M : ({φ : ℂ → ℝ // IsTestFunction (ball c r) φ ∧ ∫ x, φ x = 0} → ℝ) →
        ContinuousMap ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)) ℝ),
      IsTestFunction (ball c r) ρ ∧ ∫ x, ρ x = 1 ∧ Measurable M ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ),
        IsWholePlaneGFF P hC hcirc → IsLQGMetric γ ξ 𝔇 →
        ∀ᵐ ω ∂P, ∀ p : ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)),
          ENNReal.ofReal (M (localMeanZeroObs 0 (ball c r) (hC ω)) p) =
            ENNReal.ofReal (Real.exp (-ξ * fieldPairing 0 (hC ω) ρ)) *
              internalMetric (𝔇 (hC ω)) (ball c r) p.1.1 p.1.2

end HarmonicBalls
