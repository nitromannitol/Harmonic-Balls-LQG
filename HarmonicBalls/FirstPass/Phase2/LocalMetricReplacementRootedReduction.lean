import HarmonicBalls.FirstPass.Phase2.LocalMetricReplacementDerived
import HarmonicBalls.FirstPass.Phase2.FixedMetricDecoderUniv
import HarmonicBalls.FirstPass.Phase2.DerivedInputs9
import HarmonicBalls.FirstPass.Phase2.FieldAxiomsConsequencesDerived

/-!
# Local metric replacement: the unrooted clause without inputs, and the reduction to the rooted clause

Target: `LocalMetricReplacementStmt` (`FirstPass/S11r/LocalMetricReplacement.lean:57`), the conjunction of the unrooted
identity (18) and the rooted identity (20) for one Borel decoder `m`.

* `localMetricReplacement_unrooted_noInputs`: the unrooted clause (18), for every LQG metric `𝔇` of exponent `ξ` and every
  disk `D = ball c r` with `0 ∉ closedBall c r`, with no hypothesis. It is `localMetricReplacement_unrooted_derived` with its
  four inputs supplied: the fixed-metric normalised decoder (`localLQGMetricNormalizedMeasurableFixedMetric_derived`), the
  Cameron-Martin mutual absolute continuity (`DerivedInputs9.cameronMartinGFFMutualAbsCont_derived`), the a.e.
  measurability of the Weyl-scaled internal metric (`lqgInternalMetricWeylAeMeasurableFrozen_derived`) and the field axioms
  of the LQG metric (`lqgMetricFieldAxioms_forall_derived`).
* `localMetricReplacementStmt_of_rootedTransfer`: `LocalMetricReplacementStmt` from the rooted transfer `hroot` alone: every
  Borel decoder satisfying the unrooted clause (18) on `D` also satisfies the rooted clause (20) for roots in `U`. The
  transfer is the Campbell (rooted measure) step: under the rooted law the field is `h^α + γ G(·, z)`, whose mixture over
  Lebesgue-a.e. root `z ∈ U` is absolutely continuous with respect to the law of `h^α` (the rooted measure of
  Duplantier-Sheffield and Berestycki-Powell), together with the Weyl scaling of the metric by the
  logarithmic singularity at the root (Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380, Proposition 3.17).
-/

namespace HarmonicBalls

open MeasureTheory Set Metric
open scoped ENNReal

universe u

/-- **Unrooted clause (18) of `LocalMetricReplacementStmt`, without inputs.** For `0 < γ < 2`, a disk `D = ball c r` with
`0 ∉ closedBall c r` and an LQG metric `𝔇` of exponent `ξ`, there is a Borel decoder `m` from the mean-zero observables of
`D` to continuous functions on `D × D` such that, for every insertion `α < Q_γ` and every whole-plane GFF model, almost
surely `m(obs_D h^α)` is a positive multiple of the internal metric on `D` of the metric of `h^α`. -/
theorem localMetricReplacement_unrooted_noInputs {γ ξ : ℝ} {c : ℂ} {r : ℝ}
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
  localMetricReplacement_unrooted_derived.{u} localLQGMetricNormalizedMeasurableFixedMetric_derived
    DerivedInputs9.cameronMartinGFFMutualAbsCont_derived lqgInternalMetricWeylAeMeasurableFrozen_derived
    (fun α _ Ω _ P _ hC hcirc => lqgMetricFieldAxioms_forall_derived γ ξ α Ω P hC hcirc) hγ0 hγ2 hr h0 h𝔇

/-- **Local metric replacement from the rooted transfer.** `LocalMetricReplacementStmt γ ξ c₁ c₂ r₁ r₂` holds as soon as
every Borel decoder `m` on `D = ball c₂ r₂` that satisfies the unrooted clause (18) also satisfies the rooted clause (20)
for Lebesgue-a.e. root in `U = ball c₁ r₁` (hypothesis `hroot`, under the disk conditions of the statement). The decoder is
the one of `localMetricReplacement_unrooted_noInputs`. -/
theorem localMetricReplacementStmt_of_rootedTransfer {γ ξ : ℝ} {c₁ c₂ : ℂ} {r₁ r₂ : ℝ}
    (hroot : 0 < γ → γ < 2 → 0 < r₁ → 0 < r₂ → closedBall c₁ r₁ ⊆ ball c₂ r₂ → closedBall c₂ r₂ ⊆ ball (0 : ℂ) 1 →
      (0 : ℂ) ∉ closedBall c₂ r₂ →
      ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
      ∀ m : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) →
          ContinuousMap ↥(ball c₂ r₂ ×ˢ ball c₂ r₂ : Set (ℂ × ℂ)) ℝ,
        Measurable m →
        (∀ α : ℝ, α < lqgQ γ → ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
          IsWholePlaneGFF P hC hcirc →
          ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧ ∀ p : ↥(ball c₂ r₂ ×ˢ ball c₂ r₂ : Set (ℂ × ℂ)),
            ENNReal.ofReal (m (localMeanZeroObs α (ball c₂ r₂) (hC ω)) p) =
              ENNReal.ofReal b * internalMetric
                (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v).toReal)
                (ball c₂ r₂) p.1.1 p.1.2) →
        (∀ α : ℝ, α < lqgQ γ → ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
          IsWholePlaneGFF P hC hcirc →
          ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧
            ∀ p : ↥(ball c₂ r₂ ×ˢ ball c₂ r₂ : Set (ℂ × ℂ)),
              ENNReal.ofReal (m (campbellReferenceObs γ α (ball c₂ r₂) (hC ω) z).2 p) =
                ENNReal.ofReal b * internalMetric
                  (fun u v => (weylScaling (𝔇 (hC ω)) ξ
                    (fun w => -α * Real.log ‖w‖ - γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖)) u v).toReal)
                  (ball c₂ r₂) p.1.1 p.1.2)) :
    LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂ := by
  intro hγ0 hγ2 hr₁ hr₂ hU hD hD0 𝔇 h𝔇
  obtain ⟨m, hm, h18⟩ := localMetricReplacement_unrooted_noInputs.{u} hγ0 hγ2 hr₂ hD0 h𝔇
  exact ⟨m, hm, h18, hroot hγ0 hγ2 hr₁ hr₂ hU hD hD0 𝔇 h𝔇 m hm h18⟩

end HarmonicBalls
