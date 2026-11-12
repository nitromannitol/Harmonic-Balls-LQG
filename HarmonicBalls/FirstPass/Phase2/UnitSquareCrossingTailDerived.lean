import HarmonicBalls.FirstPass.Phase2.UnitTailCountedForms
import HarmonicBalls.Proofs.GFF.BonannoNormalizedVersion
import LatticeProb.LQG.InternalMetricUniformCrossingTail
import LatticeProb.Gauss.GFFIncrementBound

/-!
# The uniform tail of the unit-square crossing distance (derived)

`unitSquareCrossingTail_derived`: for every `γ ∈ (0, 2)` and every `γ`-LQG metric `𝔇` with exponent `ξ` there are
`δ < ξ (Q - 2) log 2` and `p : ℕ → ℝ≥0∞` with `∑ 4^n p n ≠ ∞` such that, for every whole-plane GFF, the probability that
`[0, 1]²` has no `D_h`-short half-crossings at level `e^{δ n}` is at most `p n` (Dubédat-Falconet-Gwynne-Pfeffer-Sun,
arXiv:1905.00380v2, Proposition 3.1 and the proof of Proposition 3.17, pp. 43-44). This is the input `hUniv` of
`UnitTailCountedForms`.

Proof. The strip distances have exponential tails in one realization of the whole-plane GFF
(`LatticeProb.LQG.IsLQGMetric.exists_uniform_crossing_tail`), the realization being the one of
`LatticeProb.Gauss.exists_isWholePlaneGFF_proved` with its reconstructed distribution-valued version
(`reconstructedGFF`), and the tail of the unit square in every realization is the union bound over the four strips.
-/

open MeasureTheory
open scoped ENNReal

universe u

namespace HarmonicBalls

/-- The reconstructed distribution agrees almost surely with the pairings of a whole-plane GFF on every test function. -/
theorem IsWholePlaneGFF.ae_reconstructedGFF_pairing {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    (φ : LQGMetric.TestC) : (fun ω => reconstructedGFF hC ω φ) =ᵐ[P] fun ω => hC ω φ := by
  obtain ⟨K, _, hv, _⟩ := hh.exists_fullTest_distribution_version
  filter_upwards [ae_fullTestDistributionVersion_eq_of_version K hv, hv φ] with ω h₁ h₂
  exact congrFun (congrArg DFunLike.coe h₁) φ |>.trans h₂

/-- **Derived.** The uniform tail of the unit-square crossing distance of a `γ`-LQG metric. -/
theorem unitSquareCrossingTail_derived : ∀ (γ ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ), 0 < γ → γ < 2 →
    IsLQGMetric γ ξ 𝔇 →
      ∃ δ : ℝ, δ < ξ * (lqgQ γ - 2) * Real.log 2 ∧ ∃ p : ℕ → ℝ≥0∞, ∑' n, 4 ^ n * p n ≠ ⊤ ∧
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
          IsWholePlaneGFF P hC hcirc → ∀ n : ℕ,
            P {ω | ¬ LatticeProb.LQG.HasShortHalfCrossings (𝔇 (hC ω)) 0 1 0 1
              (ENNReal.ofReal (Real.exp (δ * n)))} ≤ p n := by
  intro γ ξ 𝔇 hγ hγ2 h𝔇
  have hξ : 0 < ξ := isLQGMetric_xi_pos γ ξ 𝔇 hγ hγ2 h𝔇
  have hL := (LPBridge.isLQGMetric_iff γ ξ 𝔇).1 h𝔇
  obtain ⟨Ω, _, P, hP, hC, hcirc, hG⟩ := LatticeProb.Gauss.exists_isWholePlaneGFF_proved
  have hGHB := (LPBridge.isWholePlaneGFF_iff P hC hcirc).2 hG
  obtain ⟨δ, hδ, p, hp, huniv⟩ := hL.exists_uniform_crossing_tail hξ hγ hγ2
    ⟨Ω, _, P, hP, hC, hcirc, hG, reconstructedGFF hC, hGHB.reconstructedGFF_normalized.1,
      hGHB.ae_reconstructedGFF_pairing, fun _ hr z => hGHB.ae_circleAvg_reconstructedGFF hr z⟩
  exact ⟨δ, hδ, p, hp, fun Ω₁ _ P₁ hC₁ hcirc₁ hG₁ n =>
    huniv Ω₁ P₁ hC₁ hcirc₁ ((LPBridge.isWholePlaneGFF_iff P₁ hC₁ hcirc₁).1 hG₁) n⟩

/-- **Derived.** The small internal diameters of the clipped enlarged dyadic cells, from the field-free proof of the
unit-square crossing tail. -/
theorem dyadicCellDiamSmallFrozen_derived : DyadicCellDiamSmallFrozen.{u} :=
  dyadicCellDiamSmallFrozen_of_unitTail_xiPos unitSquareCrossingTail_derived

/-- **Derived.** The finite internal diameters of connected finite unions of closed rectangles from the field axioms
alone (the unit-square crossing tail being `unitSquareCrossingTail_derived`). -/
theorem connectedSquareUnionDiamFiniteFrozen_derivedUnitTail (hAx : LQGMetricFieldAxiomsUnivFrozen.{u}) :
    ConnectedSquareUnionDiamFiniteFrozen.{u} :=
  connectedSquareUnionDiamFiniteFrozen_of_unitTail_xiPos hAx unitSquareCrossingTail_derived

/-- **Derived.** Draft Lemma 11.17 (`PinchThirdEventPositiveStmt`) from the field axioms alone. -/
theorem pinchThirdEventPositiveStmt_derivedUnitTail (hAx : LQGMetricFieldAxiomsUnivFrozen.{u}) :
    PinchThirdEventPositiveStmt.{u} :=
  pinchThirdEventPositiveStmt_derivedInputsUnitTail unitSquareCrossingTail_derived hAx

/-- **Derived.** Draft Lemma 11.16 (`PinchSecondEventPositiveStmt`) from the field axioms alone. -/
theorem firstPass_11_16_derivedUnitTail (hAx : LQGMetricFieldAxiomsUnivFrozen.{u}) :
    PinchSecondEventPositiveStmt.{u} :=
  firstPass_11_16_derivedInputsUnitTail unitSquareCrossingTail_derived hAx

/-- **Derived.** Lemma 11.12 (Draft form) from the field axioms alone. -/
theorem firstPass_11_12_derivedUnitTail (hAx : LQGMetricFieldAxiomsUnivFrozen.{u}) :
    PinchEventPositiveProbabilityStmt.{u} :=
  firstPass_11_12_derivedInputsUnitTail unitSquareCrossingTail_derived hAx

end HarmonicBalls

namespace HarmonicBalls.S11c

/-- **Derived.** Lemma 11.10 (closed-square form, `SmallMetricDiameterLargeMassSquareStmt`) from the field axioms
alone. -/
theorem firstPass_11_10_derivedUnitTail
    (hAx : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms.{u} P γ ξ α₀ hC hcirc) :
    SmallMetricDiameterLargeMassSquareStmt.{u} :=
  firstPass_11_10_derivedInputsUnitTail HarmonicBalls.unitSquareCrossingTail_derived hAx

end HarmonicBalls.S11c

namespace HarmonicBalls.FirstPassPhase2Step8WholePlaneFromSeed

/-- **Derived.** Lemma 11.13 at the canonical exponent (universe `0`) from the field axioms `hAx`, the local metric
replacement `hN2` and the continuity of the rooted physical metric at the insertion `hfr`. -/
theorem firstPass_11_13_canonical_of_seedInputs_derivedUnitTail
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{0} γ ξ c₁ c₂ r₁ r₂)
    (hfr : HarmonicBalls.RootedPhysicalMetricContinuousAtInsertionFrozen.{0}) :
    CorrectedLemma11_13CanonicalStmt.{0} :=
  firstPass_11_13_canonical_of_seedInputs_unitTail hAx hN2 hfr HarmonicBalls.unitSquareCrossingTail_derived

end HarmonicBalls.FirstPassPhase2Step8WholePlaneFromSeed
