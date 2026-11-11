import HarmonicBalls.FirstPass.S11r.RootedNull
import HarmonicBalls.Defs.LQGMetric

/-!
# target of the local metric replacement

The statement of the local metric decoder, as one Prop that is imported as a named hypothesis until it is proved. Nothing is proved here: `LocalMetricReplacementStmt` is a `def`.

Conventions: `D = ball c₂ r₂`, `U = ball c₁ r₁`, `h^α = h^ℂ - α log|·|` (`fieldPairing α`, `localMeanZeroObs α D`),
the metric of `h^α` is `weylScaling (𝔇 (hC ω)) ξ (-α log|·|)` for an LQG metric `𝔇` of exponent `ξ`
(`IsLQGMetric γ ξ 𝔇`, `Defs/LQGMetric.lean`), and the rooted field is
`f_z = h^ℂ - α log|·| - γ log|· - z| + γ log max(1, |·|)` (`campbellReferenceObs`). The identities are on `D × D`
with the internal metric `internalMetric · D`, equality up to a positive constant `b`.

Status: FROZEN, EXTERNAL (docstring only, no statement change). DERIVED BRIDGE, not printed: plausibly true; proof architecture
l.142-172 (five steps); phase-2 obligation. Closest printed statements: Gwynne-Miller, arXiv:1905.00383,
Axiom II, Theorem 1.2, Remark 1.5; Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380, Theorem 1.10, Proposition 3.17.
The bridge theorem is to be proved in phase 2 by the route of section 1 (normalize, Axiom II, Doob-Dynkin factorization, ...).
Its proof needs (i) the fixed-metric decoder of the corrected frozen input
`LocalLQGMetricNormalizedMeasurableFixedMetricFrozen` (the retired unnormalised version was FALSE),
(ii) the unrooted identity (18) for a fixed metric, `unrooted_identity_fixedMetric` (FirstPass/S11r/UnrootedFixed.lean,
with the named universe-u shift axioms `LQGShiftAxiomI` / `LQGShiftAxiomIII`), (iii) the countable reconstruction (22)
(`internalMetric_normalised_consistency`, Consistency.lean, hII proved), (iv) the rooted identity (20) via
`ae_root_rootedObs_eq_zero_of_obs_null_noMeas` (RootedJoint.lean, weighted by `rootWeight`) and
`eq_of_local_internalMetric_agreement_off_point` (InternalDeletion.lean), and its constant-multiple form
`eq_const_mul_of_disk_agreement` (RootedGluing.lean). Quantifier: the decoder is chosen after the metric `𝔇`, as in the
corrected frozen input; the order `∃ m ∀ 𝔇` would need
`LQGMetricExistenceUniqueness` (Proposed/LQG.lean:173) and is not stated here. Open: (26) (CM and locality for `f_z`
on disks avoiding `z`). The physical-metric continuity at `z` is the frozen input
`RootedPhysicalMetricContinuousAtInsertionFrozen`, and the whole-measure companion (A) is the frozen input
`LocalMeasureKernelStmt`, both in FirstPass/S11r/Frozen.lean.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric
open scoped ENNReal

universe u

/-- FROZEN, EXTERNAL (see the module docstring, Status). **Local metric replacement.**
For `0 < γ < 2`, a disk
`U = ball c₁ r₁` with `closedBall c₁ r₁ ⊆ D = ball c₂ r₂`, `closedBall c₂ r₂ ⊆ ball 0 1` and `0 ∉ closedBall c₂ r₂`
(the restriction (16), "for clarity": the Campbell shift `γ log max(1, |·|)` of (19)
vanishes on `D` and the cut-offs are smooth; the extension to disks not contained in `B_1 ∖ {0}` is not claimed here: it is
the dilation corollary of z6 (`FirstPass/S11ak/Dilation.lean`, not yet committed)),
and every LQG metric `𝔇` of exponent `ξ` (fixed before `m` is chosen), there is a Borel map `m`
from the mean-zero observables of `D` to continuous functions on `D × D` such that:

* (18) unrooted: for every `α < Q_γ` and every whole-plane GFF model, almost surely
  `m(obs_D h^α)` is a positive multiple of the internal metric of `h^α` on `D`, on `D × D`;
* (20) rooted: for Lebesgue-a.e. root `z ∈ U`, the same holds with `obs_D f_z` and the metric of `f_z`, a.s.

The positive constants may depend on `ω` (resp. on `z`): the scalar is `b = b(z, ω)`, constant over all endpoint pairs
`p ∈ D × D` (the rooted convention is correct). The root quantifier is Lebesgue-a.e.
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

end HarmonicBalls
