import HarmonicBalls.FirstPass.Phase2.LocalityInternalMetricDerived
import HarmonicBalls.FirstPass.LPBridge.M5a
import LatticeProb.LQG.LengthMetricDerived
import LatticeProb.LQG.WeylChainMeasurable

/-!
# The internal diameter of a closed dyadic square for the Weyl-shifted LQG metric is a.s. measurable

Derivation of `WeylShiftedSupMeasurableFrozen` (`FirstPass/Frozen/S11c.lean:217`) from the field axioms
`LQGMetricFieldAxiomsUnivFrozen` alone (Fact 2.2 I-IV for `h = h^ℂ - α₀ log |·|`), for every real `ξ`. Let `D_h` be
the LQG metric, `f` continuous with compact support, and `E = e^{ξ f} · D_h` the Weyl-shifted metric
(`(weylShiftPair γ ξ f (μ, D_h)).2`). The route:

1. Axiom I: a.s. `D_h` is a Euclidean length metric, hence so is `E` (`weylScaledEuclidean_derived`), and
   `E(x, y) ≤ e^K D_h(x, y) < ∞` for `ξ f ≤ K`.
2. Axiom II (locality, `aemeasurable_internalMetric_of_fieldAxioms`): the local internal metrics
   `D_h(a, b; B(a, r) ∩ U)` of an open `U` are a.s. measurable.
3. Chain formula for the internal metric of a Weyl scaling (`LatticeProb.LQG.aemeasurable_internalMetric_weylScaling`):
   `E(x, y; U)` is the infimum over `n` of `e^{η_n}` times a countable infimum of weighted chain sums of local internal
   metrics of `D_h`, so `ω ↦ E(x, y; U)` is a.s. measurable for every open `U`. Here `ξ f` is uniformly continuous and
   bounded above because `f` is continuous with compact support.
4. Closed-set exhaustion (`internalMetric_closed_eq_iSup_thickening_of_bounded`): `E(x, y; S)` is the supremum over `k`
   of `E(x, y; U_k)` for the open thickenings `U_k` of `S`.
5. Lower semicontinuity of `(x, y) ↦ E(x, y; S)` on `S ×ˢ S` reduces the supremum over `S ×ˢ S` to a countable dense
   subset (`LatticeProb.Prob.aemeasurable_iSup_mem_of_lowerSemicontinuousOn`).

The inputs `WeylScalingCompositionFrozen` and `LQGInternalMetricWeylAeMeasurableFrozen` of
`weylShiftedSupMeasurable_derived` are not used. The counted form of Lemma 11.10 without the hypothesis
`WeylShiftedSupMeasurableFrozen` is `S11c.firstPass_11_10_derivedInputsWeylShiftedSup` below.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set
open scoped ENNReal

universe u

/-- **Derived** (`WeylShiftedSupMeasurableFrozen` from the field axioms). For the γ-LQG metric `D_h` of
`h = h^ℂ - α₀ log |·|`, a continuous compactly supported `f` and a closed dyadic square `S`, the supremum over
`u, v ∈ S` of the internal metric of `S` for the Weyl-shifted metric `e^{ξ f} · D_h` is a.s. measurable. Proof: locality
of `D_h` and the chain formula for Weyl scalings give a.s. measurability on open sets; closed-set exhaustion passes to
`S`, and lower semicontinuity on `S ×ˢ S` reduces the supremum to a countable dense set. -/
theorem weylShiftedSupMeasurable_of_fieldAxioms (hAx : LQGMetricFieldAxiomsUnivFrozen.{u}) :
    WeylShiftedSupMeasurableFrozen.{u} := by
  intro γ α₀ ξ hγ0 hγ2 hα Ω _ P hC hcirc μ D hW _ hLQG f hf hfc _ S hS
  obtain ⟨hSc, hSb⟩ := isClosed_and_isBounded_of_isClosedDyadicSquare hS
  -- the LQG metric is a.s. a Euclidean length metric (axiom I)
  have hEucD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω) := by
    obtain ⟨𝔇, h𝔇, hD⟩ := hLQG
    filter_upwards [(hAx Ω P γ ξ α₀ hC hcirc hW hγ0 hγ2 hα 𝔇 h𝔇).1, hD] with ω hI hDω
    have hDeq : D ω = fun a b => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) a b).toReal := by
      funext a b
      obtain ⟨h0, h1⟩ := hDω a b
      rw [← h1, ENNReal.toReal_ofReal h0]
    rw [hDeq]
    exact hI.2
  -- so is the Weyl-shifted metric
  have hEucE : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (weylShiftPair γ ξ f (μ ω, D ω)).2 := by
    filter_upwards [hEucD] with ω hω
    exact weylScaledEuclidean_derived (D ω) ξ f hω hf hfc
  obtain ⟨K, hK⟩ := exists_const_mul_le_of_hasCompactSupport hf hfc ξ
  have hg := uniformContinuous_const_mul_of_hasCompactSupport hf hfc ξ
  -- a.s. measurability of the internal metric of the Weyl-shifted metric on open sets (chain formula)
  have hopen : ∀ U : Set ℂ, IsOpen U → ∀ x y : ℂ,
      AEMeasurable (fun ω => internalMetric (weylShiftPair γ ξ f (μ ω, D ω)).2 U x y) P := by
    intro U hU x y
    exact LatticeProb.LQG.aemeasurable_internalMetric_weylScaling (D := D)
      (E := fun ω => (weylShiftPair γ ξ f (μ ω, D ω)).2) hf hK hg hU
      (fun a b _ _ => aemeasurable_internalMetric_of_fieldAxioms hAx hγ0 hγ2 hα hW hLQG
        (Metric.isOpen_ball.inter hU) a b)
      (by filter_upwards [hEucD] with ω hω; exact (LPBridge.isEuclideanLengthMetric_iff _).1 hω)
      (by filter_upwards [hEucE] with ω hω; exact (LPBridge.isEuclideanLengthMetric_iff _).1 hω)
      (Eventually.of_forall fun _ _ _ => ENNReal.toReal_nonneg)
      (by
        filter_upwards [hEucD] with ω hω
        intro a b
        show ENNReal.ofReal (weylScaling (D ω) ξ f a b).toReal = _
        exact ENNReal.ofReal_toReal (ne_top_of_le_ne_top
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
          (LatticeProb.LQG.IsEuclideanLengthMetric.weylScaling_le_exp_mul
            ((LPBridge.isEuclideanLengthMetric_iff _).1 hω) hK a b)))
      x y
  -- closed-set exhaustion: a.s. measurability on `S`
  have hmeas : ∀ x y : ℂ, AEMeasurable (fun ω => internalMetric (weylShiftPair γ ξ f (μ ω, D ω)).2 S x y) P := by
    intro x y
    refine (AEMeasurable.iSup fun k : ℕ =>
      hopen (Metric.thickening (((k : ℝ) + 1)⁻¹) S) Metric.isOpen_thickening x y).congr ?_
    filter_upwards [hEucE] with ω hω
    exact (internalMetric_closed_eq_iSup_thickening_of_bounded hω hSc hSb x y).symm
  -- a.s. lower semicontinuity on `S ×ˢ S`
  have hlsc : ∀ᵐ ω ∂P, LowerSemicontinuousOn
      (fun p : ℂ × ℂ => internalMetric (weylShiftPair γ ξ f (μ ω, D ω)).2 S p.1 p.2) (S ×ˢ S) := by
    filter_upwards [hEucE] with ω hω
    exact hω.lowerSemicontinuousOn_internalMetric_pair_closed (fun _ _ => ENNReal.toReal_nonneg) hSc hSb
  obtain ⟨D₀, hD₀S, hD₀c, hSD₀⟩ := exists_countable_dense_subset_of_set S
  have key := LatticeProb.Prob.aemeasurable_iSup_mem_of_lowerSemicontinuousOn (P := P)
    (F := fun ω p => internalMetric (weylShiftPair γ ξ f (μ ω, D ω)).2 S p.1 p.2)
    (S := S ×ˢ S) (D := D₀ ×ˢ D₀) (hD₀c.prod hD₀c) (Set.prod_mono hD₀S hD₀S)
    (by rw [closure_prod_eq]; exact Set.prod_mono hSD₀ hSD₀)
    (fun p _ => hmeas p.1 p.2) hlsc
  refine key.congr (Eventually.of_forall fun ω => ?_)
  exact biSup_prod

/-- `SmallMetricDiameterLargeMassSquareStmt` (Lemma 11.10) from the hypotheses of
`S11c.firstPass_11_10_derivedInputsSupMeasurable` without `hM1`, which is supplied by
`weylShiftedSupMeasurable_of_fieldAxioms` from `hAx`. -/
theorem S11c.firstPass_11_10_derivedInputsWeylShiftedSup
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hCM : CameronMartinEventTransferFrozen.{u})
    (hPos : LQGMeasureSquarePositiveFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hAx : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms.{u} P γ ξ α₀ hC hcirc) :
    SmallMetricDiameterLargeMassSquareStmt.{u} :=
  S11c.firstPass_11_10_derivedInputsSupMeasurable hDC hCM hPos hFin
    (weylShiftedSupMeasurable_of_fieldAxioms fun Ω _ P γ ξ α₀ hC hcirc => hAx γ ξ α₀ Ω P hC hcirc) hAx

end HarmonicBalls
