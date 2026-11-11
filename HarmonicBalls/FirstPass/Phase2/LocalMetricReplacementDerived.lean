import HarmonicBalls.FirstPass.S11r.LocalMetricReplacement
import HarmonicBalls.FirstPass.S11r.UnrootedFixed
import HarmonicBalls.Proposed.LQG

/-!
# Local metric replacement: derived parts (audit B1, owner z4)

Target: `LocalMetricReplacementStmt` (`FirstPass/S11r/LocalMetricReplacement.lean:58`), whose conclusion is a
conjunction of the unrooted clause (18) and the rooted clause (20) for ONE decoder `m`.

This file derives the unrooted clause (18) for each fixed LQG metric `𝔇` from `unrooted_identity_fixedMetric`
(`FirstPass/S11r/UnrootedFixed.lean`), which is proved in Lean from its binders. The binders of this theorem are:

* `hFA`: `LQGMetricFieldAxioms`, the Proposed literature input (`HarmonicBalls/Proposed/LQG.lean:225`, Gwynne-Miller 2021,
  Section 1.2, with the logarithmic-singularity sources; pending operator source-check);
* `hB1`: `LocalLQGMetricNormalizedMeasurableFixedMetricFrozen`, the fixed-metric normalized decoder (route step 1 of
  `notes/fp-gaps/CHATGPT-hb-11-12-audit-PRO.md` section 1.6). It is NOT a printed statement: it is an unprinted frozen input;
* `hCM`: `CameronMartinGFFMutualAbsCont` (`FirstPass/Frozen/S11d.lean:74`), mutual absolute continuity of shifted GFF laws
  (Cameron-Martin / Feldman-Hajek; cited in prose only). NOT a printed numbered statement;
* `hPhi`: `LQGInternalMetricWeylAeMeasurableFrozen` (`FirstPass/Frozen/S11d.lean:130`), measurability of the Weyl-scaled
  internal metric. NOT a printed statement.

So the unrooted clause is derived from the unprinted inputs `hB1`, `hCM`, `hPhi` and the Proposed input `hFA`. The rooted
clause (20) is not derived here; see `reports/z4.md` for the blocked steps.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric
open scoped ENNReal

universe u

/-- **Unrooted clause (18) of `LocalMetricReplacementStmt`, derived for every LQG metric.** For `0 < γ < 2`, a disk
`ball c r` with `0 ∉ closedBall c r`, and an LQG metric `𝔇` of exponent `ξ`, there is a continuous-valued Borel decoder `m`
such that for every insertion `α < Q_γ`, every whole-plane GFF model, almost surely `m(obs_D h^α)` is a positive multiple of
the internal metric of the Weyl-scaled metric of `h^α` on `D × D`. Proof: `unrooted_identity_fixedMetric`. -/
theorem localMetricReplacement_unrooted_derived {γ ξ : ℝ} {c : ℂ} {r : ℝ}
    (hB1 : LocalLQGMetricNormalizedMeasurableFixedMetricFrozen.{u})
    (hCM : CameronMartinGFFMutualAbsCont.{u})
    (hPhi : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hFA : ∀ α : ℝ, α < lqgQ γ → ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms P γ ξ α hC hcirc)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hr : 0 < r) (h0 : (0 : ℂ) ∉ closedBall c r)
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇) :
    ∃ m : ({φ : ℂ → ℝ // IsTestFunction (ball c r) φ ∧ ∫ x, φ x = 0} → ℝ) →
        ContinuousMap ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)) ℝ,
      Measurable m ∧
      ∀ α : ℝ, α < lqgQ γ → ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        IsWholePlaneGFF P hC hcirc → ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧
          ∀ p : ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)),
            ENNReal.ofReal (m (localMeanZeroObs α (ball c r) (hC ω)) p) =
              ENNReal.ofReal b * internalMetric
                (fun x y => (weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) x y).toReal)
                (ball c r) p.1.1 p.1.2 :=
  unrooted_identity_fixedMetric hB1 hCM hPhi hFA hγ0 hγ2 hr h0 h𝔇

end HarmonicBalls
