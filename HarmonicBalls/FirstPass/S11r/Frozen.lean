import HarmonicBalls.Defs.GFF
import HarmonicBalls.Defs.LQGMetric
import HarmonicBalls.Defs.LQG
import HarmonicBalls.FirstPass.Frozen.S11c

/-!
# First-pass frozen inputs: whole-plane GFF existence and the normalised local metric decoder

Four EXTERNAL facts, all general mathematics, not specific to this paper, all `def ... : Prop`s, never axioms.
(1) `WholePlaneGFFExistsFrozen`: existence of a whole-plane GFF, used by the realization lemma `hmodel_at_gamma`
(FirstPass/S11r.lean, the model hypothesis of Lemma 11.13 in FirstPass/S11i/CertificateCanonical.lean).
(2) `LocalLQGMetricNormalizedMeasurableFixedMetricFrozen`: the fixed-metric measurable local metric decoder (answer section
4.1, equation (21), corrected order), the external input of the local metric replacement (`LocalMetricReplacementStmt`,
S11r/LocalMetricReplacement.lean). The retired unnormalised `LocalLQGMetricNormalizedMeasurableFrozen` is kept only for the record.
(3) `RootedPhysicalMetricContinuousAtInsertionFrozen`: continuity of the physical metric of the rooted field `f_z` at its
insertion `z` (DFGPS Prop 3.17), the external input `he_cont` of `eq_const_mul_of_rat_disk_agreement` (RootedGluing.lean).
(4) `LocalMeasureKernelStmt`: the whole-measure local kernel identity (A), the measure companion of (2)-(3) on the same disks
(the local LQG measure input, HB Fact 2.1 (II), (III)); the external input of the measure side of the local replacement.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

universe u

/-- FROZEN. Truth check TRUE,
in every universe `u` (ULift for larger universes).
Existence of the whole-plane Gaussian free field (EXTERNAL, general): for every universe `u` there
are a probability space `Ω : Type u`, a pairing `hC` and a circle-average process `hcirc` with `IsWholePlaneGFF P hC hcirc`,
that is a centred Gaussian field with covariance `wholePlaneCov` (`log (max(|z|,1) max(|w|,1) / |z-w|)`, normalised so that
the average on the unit circle vanishes), whose circle averages are a.s. continuous in `(r, z) ∈ (0, ∞) × ℂ`.
Sources: Miller-Sheffield, Imaginary Geometry IV, arXiv:1302.4738v2 §2.2.1, pp. 46-47, eq. (2.7); Duplantier-Sheffield,
arXiv:0808.1560v2 §3.1, eq. (10) and Prop. 3.1, p. 17; Bou-Rabee-Gwynne, arXiv:2208.11795v3 §2.1, eq. (2.1), p. 8.
Used by: `hmodel_at_gamma` (FirstPass/S11r.lean), hence the model hypothesis `hmodel` of `certificate_canonical_pos`
(FirstPass/S11i/CertificateCanonical.lean).
Truth check TRUE: true in every universe `u`
(by `ULift` for larger universes). -/
def WholePlaneGFFExistsFrozen : Prop :=
  ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc

/-- RETIRED (FALSE): the decoder is chosen before the metric
assignment, but the equality fixes the normalisation of the metric, and `2 𝔇` is also an LQG metric. Superseded by
`LocalLQGMetricNormalizedMeasurableFixedMetricFrozen` below; do not use. The text below is the retired statement.

FROZEN, EXTERNAL (retired, truth check FALSE). The measurable normalised local metric decoder
of the ordinary GFF (equation (21)). For `0 < γ < 2`, `ξ ∈ ℝ` and a disk `D = ball c r` with
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

/-- FROZEN, EXTERNAL. Truth check TRUE.
The fixed-metric normalised local metric decoder of the ordinary GFF (the minimal correction of the retired `LocalLQGMetricNormalizedMeasurableFrozen`,
used with the write-up equation (21)). The metric assignment `𝔇` is fixed BEFORE the decoder is
chosen: for every LQG metric `𝔇` of exponent `ξ` (`IsLQGMetric γ ξ 𝔇`) there are a smooth probability bump `ρ` supported in
`D = ball c r` and a Borel map `M` from the mean-zero observables of `D` to continuous functions on `D × D` such that, for
every whole-plane GFF `(Ω, P, hC, hcirc)`, almost surely, for all endpoints `p ∈ D × D`,
`M (obs_D g) p = e^{-ξ ⟨g,ρ⟩} · D_g(·,·;D) p`, where `D_g = 𝔇 (hC ω)`, `⟨g,ρ⟩ = fieldPairing 0 (hC ω) ρ` and
`D_g(·,·;D)` is the internal metric on `D` (`internalMetric`). The normalisation is fixed by `ρ` together with `𝔇`.
Sources: Gwynne-Miller, arXiv:1905.00383v3, §1.2 pp. 5-6 (continuous metrics and their Borel structure), p. 6 (metric
definition, Axioms I-III and (1.8): measurable assignment, length property, locality, Weyl scaling), p. 6 Theorem 1.2 and
p. 7 (uniqueness up to a deterministic positive constant), p. 8 Remark 1.5 and (1.10) (proper domains). The raw-coordinate
decoder and the universe-polymorphic signature are deductions from these, not printed theorems (section 1, "Exact printed
source"); the independently quantified exponent `ξ` is justified conditionally by the supplied axioms (paper (1.5) p. 4 fixes
`ξ = γ/d_γ`).
Used by: `LocalMetricReplacementStmt` (S11r/LocalMetricReplacement.lean), through (22) and (20). -/
def LocalLQGMetricNormalizedMeasurableFixedMetricFrozen : Prop :=
  ∀ (γ ξ : ℝ) (c : ℂ) (r : ℝ), 0 < γ → γ < 2 → 0 < r → (0 : ℂ) ∉ closedBall c r →
    ∀ (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ), IsLQGMetric γ ξ 𝔇 →
    ∃ (ρ : ℂ → ℝ)
      (M : ({φ : ℂ → ℝ // IsTestFunction (ball c r) φ ∧ ∫ x, φ x = 0} → ℝ) →
        ContinuousMap ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)) ℝ),
      IsTestFunction (ball c r) ρ ∧ ∫ x, ρ x = 1 ∧ Measurable M ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        IsWholePlaneGFF P hC hcirc →
        ∀ᵐ ω ∂P, ∀ p : ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)),
          ENNReal.ofReal (M (localMeanZeroObs 0 (ball c r) (hC ω)) p) =
            ENNReal.ofReal (Real.exp (-ξ * fieldPairing 0 (hC ω) ρ)) *
              internalMetric (𝔇 (hC ω)) (ball c r) p.1.1 p.1.2

/-- FROZEN, EXTERNAL. Truth check TRUE, as typed: no
change to the hypotheses, the quantifier order or the `nhds` filter. Continuity of the physical metric of the rooted field
at its insertion (DFGPS Prop 3.17). For `0 < γ < 2`, `α < Q_γ = lqgQ γ`, a point `z ≠ 0`, a whole-plane GFF `hC` and an LQG
metric `𝔇` of exponent `ξ`, for each fixed `z` and almost surely in `ω`, the Weyl-scaled metric of `𝔇 (hC ω)` by the rooted
weight `-α log|·| - γ log|· - z| + γ log max(1, |·|)` (the metric of `f_z` in `LocalMetricReplacementStmt`, equation (20))
tends to `0` at `z` in the Euclidean topology. This is the `he_cont` input of `eq_const_mul_of_rat_disk_agreement`
(RootedGluing.lean), through `tendsto_toReal_nhdsWithin_zero_of_tendsto`. Source: Dubédat-Falconet-Gwynne-Pfeffer-Sun,
arXiv:1905.00380v2, Proposition 3.17, printed p. 43, eq. (3.56) (the metric induces the Euclidean topology for insertions
`α ∈ (-∞, Q)`). It is stated as a consequence of DFGPS
Prop 3.17 (insertion `γ` at `z`) plus the local path comparison, valid for arbitrary `ξ`; it is not
a verbatim printed statement. -/
def RootedPhysicalMetricContinuousAtInsertionFrozen : Prop :=
  ∀ (γ ξ α : ℝ) (z : ℂ), 0 < γ → γ < 2 → α < lqgQ γ → z ≠ 0 →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc →
      ∀ (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ), IsLQGMetric γ ξ 𝔇 →
      ∀ᵐ ω ∂P, Filter.Tendsto
        (fun x => weylScaling (𝔇 (hC ω)) ξ
          (fun w => -α * Real.log ‖w‖ - γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖)) x z)
        (nhds z) (nhds 0)

/-- FROZEN, EXTERNAL. Truth check TRUE (no change needed). The whole-measure local kernel identity (A) (first line), the measure companion of `LocalMetricReplacementStmt` on the same disks
`U = ball c₁ r₁`, `D = ball c₂ r₂`, with `0 < γ < 2`, `closedBall c₁ r₁ ⊆ D`, `closedBall c₂ r₂ ⊆ ball 0 1`, `0 ∉ closedBall c₂ r₂`.
There is one measurable kernel `κ` from the mean-zero observations of `D` to measures on `ℂ`, fixed before `α`, the
probability space and the root, such that, restricted to `D`: (A-unrooted) for `α < Q_γ`, every whole-plane GFF model and
every γ-LQG measure `μ` of `h^α = h^ℂ - α log|·|`, a.s. `κ(obs_D h^α)` is a positive multiple of `μ`; (A-rooted) for Lebesgue-a.e.
root `z ∈ U`, every γ-LQG measure `μz` of the rooted field `f_z` (`addCircleAverage` of `fieldCircleAverage`), a.s. `κ` of the
campbellReferenceObs observation is a positive multiple of `μz`. The scalar `a` may depend on `ω` and on `z`.
Same-kernel requirement: `κ` is one map, used for every `α`, every model and both
identities; the unrooted decoder is not transferred to other observation codes under the rooted law. The exceptional null
sets need not be common to all `μz`, and the scalar need not be jointly measurable (section 2.1).
Source: Bou-Rabee-Gwynne, arXiv:2208.11795v3 §2.2, printed p. 9, equation (2.6) (circle-average construction) and Fact 2.1
(II) (locality) and (III) (Weyl scaling), paper line 407; the Borel kernel on observation codes is derived from the
construction, not the literal assertion of Fact 2.1 (II). Construction behind the statement (section 2.3): one explicit local
GMC map by circle averages with the additive constant fixed by a unit-integral test function; approximants Duplantier-Sheffield,
arXiv:0808.1560v2, Proposition 1.1, p. 5, and Sheffield-Wang, arXiv:1605.06171v2, Theorems 1.1-1.2 and Remark 1.3, p. 3.
Predicates: `IsLQGMeasure`, `IsLQGMeasureOfField` (Defs/LQG.lean). -/
def LocalMeasureKernelStmt (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ) : Prop :=
  0 < γ → γ < 2 → 0 < r₁ → 0 < r₂ → closedBall c₁ r₁ ⊆ ball c₂ r₂ → closedBall c₂ r₂ ⊆ ball (0 : ℂ) 1 →
  (0 : ℂ) ∉ closedBall c₂ r₂ →
  ∃ κ : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ, Measurable κ ∧
    (∀ α : ℝ, α < lqgQ γ → ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α hcirc μ →
      ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
        (κ (localMeanZeroObs α (ball c₂ r₂) (hC ω))).restrict (ball c₂ r₂) =
          ENNReal.ofReal a • (μ ω).restrict (ball c₂ r₂)) ∧
    (∀ α : ℝ, α < lqgQ γ → ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc →
      ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ μz : Ω → Measure ℂ,
        IsLQGMeasure P γ (fun ω => addCircleAverage (fieldCircleAverage α (hcirc ω))
          (fun w => -γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖))) μz →
        ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
          (κ (campbellReferenceObs γ α (ball c₂ r₂) (hC ω) z).2).restrict (ball c₂ r₂) =
            ENNReal.ofReal a • (μz ω).restrict (ball c₂ r₂))

/-- Deterministic step (no input): a limit to `0` in `ENNReal` at `z` gives the limit of the real values
`(f x).toReal` to `0` within any set `D`. This converts the Weyl-scaled metric of
`RootedPhysicalMetricContinuousAtInsertionFrozen` into the real-valued `he_cont` of `eq_const_mul_of_rat_disk_agreement`. -/
theorem tendsto_toReal_nhdsWithin_zero_of_tendsto {f : ℂ → ENNReal} {z : ℂ} (D : Set ℂ)
    (h : Filter.Tendsto f (nhds z) (nhds 0)) :
    Filter.Tendsto (fun x => (f x).toReal) (nhdsWithin z D) (nhds 0) := by
  have h1 : Filter.Tendsto (fun x => (f x).toReal) (nhds z) (nhds (0 : ENNReal).toReal) :=
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  have h2 := h1.mono_left (nhdsWithin_le_nhds (s := D))
  rwa [ENNReal.toReal_zero] at h2

end HarmonicBalls
