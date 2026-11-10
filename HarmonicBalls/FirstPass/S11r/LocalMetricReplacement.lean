import HarmonicBalls.FirstPass.S11r.RootedNull
import HarmonicBalls.Defs.LQGMetric

/-!
# First pass, target of the local metric replacement (fp-S11r part (b), owner n2)

The statement of the B2 local metric decoder of CHATGPT-n3-B1-B2.md section 4 (eqs (17)-(20)), as one Prop that
n3 imports as a named hypothesis until it is proved. Nothing is proved here: `LocalMetricReplacementStmt` is a `def`.

Conventions: `D = ball c₂ r₂`, `U = ball c₁ r₁`, `h^α = h^ℂ - α log|·|` (`fieldPairing α`, `localMeanZeroObs α D`),
the metric of `h^α` is `weylScaling (𝔇 (hC ω)) ξ (-α log|·|)` for an LQG metric `𝔇` of exponent `ξ`
(`IsLQGMetric γ ξ 𝔇`, `Defs/LQGMetric.lean`), and the rooted field is
`f_z = h^ℂ - α log|·| - γ log|· - z| + γ log max(1, |·|)` (`campbellReferenceObs`). The identities are on `D × D`
with the internal metric `internalMetric · D`, equality up to a positive constant `b`.

Status: the statement only. Its proof needs (i) the fixed-metric decoder of the corrected frozen input
`LocalLQGMetricNormalizedMeasurableFixedMetricFrozen` (section 4.1; the retired unnormalised version was FALSE),
(ii) the unrooted identity (18) for a fixed metric, `unrooted_identity_fixedMetric` (FirstPass/S11r/UnrootedFixed.lean,
with the named universe-u shift axioms `LQGShiftAxiomI` / `LQGShiftAxiomIII`), (iii) the countable reconstruction (22)
(`internalMetric_normalised_consistency`, Consistency.lean, hII proved), (iv) the rooted identity (20) via
`ae_root_rootedObs_eq_zero_of_obs_null_noMeas` (RootedJoint.lean, weighted by `rootWeight`) and
`eq_of_local_internalMetric_agreement_off_point` (InternalDeletion.lean), and its constant-multiple form
`eq_const_mul_of_disk_agreement` (RootedGluing.lean). Quantifier: the decoder is chosen after the metric `𝔇`, as in the
corrected frozen input (CHATGPT-n2-frozen-S11r.md section 1.5); the order `∃ m ∀ 𝔇` would need
`LQGMetricExistenceUniqueness` (Proposed/LQG.lean:173) and is not stated here. Open: (26) (CM and locality for `f_z`
on disks avoiding `z`) and the physical-metric continuity at `z` (DFGPS Prop 3.17, not yet staged); see notes/n2.md.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric
open scoped ENNReal

universe u

/-- **Target B2: local metric replacement** (CHATGPT-n3-B1-B2.md section 4, eqs (17)-(20)). For `0 < γ < 2`, a disk
`U = ball c₁ r₁` with `closedBall c₁ r₁ ⊆ D = ball c₂ r₂`, `closedBall c₂ r₂ ⊆ ball 0 1` and `0 ∉ closedBall c₂ r₂`
(the restriction (16) of CHATGPT-n3-B1-B2.md section 4, "for clarity": the Campbell shift `γ log max(1, |·|)` of (19)
vanishes on `D` and the cut-offs are smooth; disks not in `B_1 ∖ {0}` are covered by countably many such disks there),
and every LQG metric `𝔇` of exponent `ξ` (fixed before `m` is chosen), there is a Borel map `m`
from the mean-zero observables of `D` to continuous functions on `D × D` such that:

* (18) unrooted: for every `α < Q_γ` and every whole-plane GFF model, almost surely
  `m(obs_D h^α)` is a positive multiple of the internal metric of `h^α` on `D`, on `D × D`;
* (20) rooted: for Lebesgue-a.e. root `z ∈ U`, the same holds with `obs_D f_z` and the metric of `f_z`, a.s.

The positive constants may depend on `ω` (resp. on `z`): the scalar is `b = b(z, ω)`, constant over all endpoint pairs
`p ∈ D × D` (CHATGPT-n2-hII.md section 2.2; the rooted convention is correct). The root quantifier is Lebesgue-a.e.
(answer, section 4.2). -/
def LocalMetricReplacementStmt (γ ξ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ) : Prop :=
  0 < γ → γ < 2 → 0 < r₁ → 0 < r₂ → closedBall c₁ r₁ ⊆ ball c₂ r₂ → closedBall c₂ r₂ ⊆ ball (0 : ℂ) 1 →
  (0 : ℂ) ∉ closedBall c₂ r₂ →
  ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
  ∃ m : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) →
      ContinuousMap ↥(ball c₂ r₂ ×ˢ ball c₂ r₂ : Set (ℂ × ℂ)) ℝ,
    Measurable m ∧
    -- (18), unrooted, for every insertion `α < Q_γ`.
    (∀ α : ℝ, α < lqgQ γ → ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc →
      ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧ ∀ p : ↥(ball c₂ r₂ ×ˢ ball c₂ r₂ : Set (ℂ × ℂ)),
        ENNReal.ofReal (m (localMeanZeroObs α (ball c₂ r₂) (hC ω)) p) =
          ENNReal.ofReal b * internalMetric
            (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v).toReal)
            (ball c₂ r₂) p.1.1 p.1.2) ∧
    -- (20), rooted, for Lebesgue-a.e. root in `U`.
    (∀ α : ℝ, α < lqgQ γ → ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc →
      ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧
        ∀ p : ↥(ball c₂ r₂ ×ˢ ball c₂ r₂ : Set (ℂ × ℂ)),
          ENNReal.ofReal (m (campbellReferenceObs γ α (ball c₂ r₂) (hC ω) z).2 p) =
            ENNReal.ofReal b * internalMetric
              (fun u v => (weylScaling (𝔇 (hC ω)) ξ
                (fun w => -α * Real.log ‖w‖ - γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖)) u v).toReal)
              (ball c₂ r₂) p.1.1 p.1.2)

/-- **Whole-measure local kernel identity (A)** (CHATGPT-n3-Q1-eq34.md section 1, identity (A), first line; restriction
(16) as in `LocalMetricReplacementStmt`). For `0 < γ < 2` and disks `U = ball c₁ r₁`, `D = ball c₂ r₂` as there, there is a
measurable kernel `κ` from the mean-zero observables of `D` to measures on `ℂ` such that, with the observations of
`LocalMetricReplacementStmt`:
* (A-unrooted) for every `α < Q_γ`, every whole-plane GFF model and every γ-LQG measure `μ` of `h^α = h^ℂ - α log|·|`
  (`IsLQGMeasureOfField P γ α hcirc μ`), almost surely the restriction of `κ(obs_D h^α)` to `D` is a positive multiple of
  `μ` restricted to `D`;
* (A-rooted) for every `α < Q_γ`, every model, for Lebesgue-a.e. root `z ∈ U`, and every γ-LQG measure `μz` of the rooted
  field `f_z = h^α - γ log|· - z| + γ log max(1, |·|)` (circle averages `addCircleAverage`), almost surely the restriction
  of `κ(campbellReferenceObs obs)` to `D` is a positive multiple of `μz` restricted to `D`.
The constants `a > 0` may depend on `ω` (and on `z`). The identities are identities of restricted measures on one event
(the restriction to `D` is the restricted measure `κ_D` of (A)); the measure `κ` is the local kernel `κ_D` and is not
claimed to be global. Its metric companion is `LocalMetricReplacementStmt` (the same disks, same observations, fixed-metric
order). Not proved; the LQG measure existence is `LQGMeasureExistence` (Proposed/LQG.lean). -/
def LocalMeasureKernelStmt (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ) : Prop :=
  0 < γ → γ < 2 → 0 < r₁ → 0 < r₂ → closedBall c₁ r₁ ⊆ ball c₂ r₂ → closedBall c₂ r₂ ⊆ ball (0 : ℂ) 1 →
  (0 : ℂ) ∉ closedBall c₂ r₂ →
  ∃ κ : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ, Measurable κ ∧
    -- (A), unrooted.
    (∀ α : ℝ, α < lqgQ γ → ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α hcirc μ →
      ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
        (κ (localMeanZeroObs α (ball c₂ r₂) (hC ω))).restrict (ball c₂ r₂) =
          ENNReal.ofReal a • (μ ω).restrict (ball c₂ r₂)) ∧
    -- (A), rooted, for Lebesgue-a.e. root in `U`.
    (∀ α : ℝ, α < lqgQ γ → ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc →
      ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ μz : Ω → Measure ℂ,
        IsLQGMeasure P γ (fun ω => addCircleAverage (fieldCircleAverage α (hcirc ω))
          (fun w => -γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖))) μz →
        ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
          (κ (campbellReferenceObs γ α (ball c₂ r₂) (hC ω) z).2).restrict (ball c₂ r₂) =
            ENNReal.ofReal a • (μz ω).restrict (ball c₂ r₂))

end HarmonicBalls
