import HarmonicBalls.FirstPass.Phase2.DerivedInputsContinuousShift
import HarmonicBalls.FirstPass.Phase2.WeylShiftedSupDerived2

/-!
# The internal diameter of the LQG metric over a finite union of closed rectangles is a.s. measurable

Derivation of `LQGMetricSupMeasurableFrozen` (`FirstPass/Frozen/S11c.lean:103`) from the field axioms
`LQGMetricFieldAxiomsUnivFrozen` (Fact 2.2 I-IV for `h = h^ℂ - α₀ log |·|`), at the same universe. For a compact set
`K` (in particular a finite union of closed rectangles, connected or not), `ω ↦ sup_{u, v ∈ K} D_h(u, v; K)` is a.s.
equal to a measurable function. The route:

1. Axiom I: a.s. `D_h` is a Euclidean length metric with nonnegative values.
2. Closed-set exhaustion (`internalMetric_closed_eq_iSup_thickening_of_bounded`): `D_h(x, y; K)` is the supremum over
   `k` of the internal metrics of the open neighbourhoods `U_k = thickening ((k+1)⁻¹) K`.
3. Axiom II (locality) on each open `U_k`: `D_h(x, y; U_k)` is a.s. equal to a `σ(h|_{U_k})`-measurable function, and
   `σ(h|_{U_k})` is a sub-σ-algebra of the ambient one (`IsWholePlaneGFF.fieldSigmaAlgebra_le`). Hence for fixed
   `x, y ∈ K` the internal distance `D_h(x, y; K)` is a.s. measurable (a countable supremum).
4. `(x, y) ↦ D_h(x, y; K)` is a.s. lower semicontinuous on `K ×ˢ K`
   (`IsEuclideanLengthMetric.lowerSemicontinuousOn_internalMetric_pair_closed`), so the supremum over `K ×ˢ K` equals
   the supremum over a countable dense subset (`LatticeProb.Prob.aemeasurable_iSup_mem_of_lowerSemicontinuousOn`).

No quantitative estimate on the LQG metric is used. The counted form of Lemma 11.10 without the hypothesis
`LQGMetricSupMeasurableFrozen` is `S11c.firstPass_11_10_derivedInputsSupMeasurable` below.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set
open scoped ENNReal

universe u

/-- A finite union of closed axis-parallel rectangles is compact. -/
theorem isCompact_biUnion_isClosedRectangle {F : Finset (Set ℂ)} (hF : ∀ R ∈ F, IsClosedRectangle R) :
    IsCompact (⋃ R ∈ F, R) := by
  refine F.isCompact_biUnion fun R hR => ?_
  obtain ⟨a₁, a₂, b₁, b₂, -, -, rfl⟩ := hF R hR
  exact isCompact_Icc.reProdIm isCompact_Icc

/-- **Derived** (`LQGMetricSupMeasurableFrozen` from the field axioms). For the γ-LQG metric `D_h` of
`h = h^ℂ - α₀ log |·|` and a finite union `K` of closed rectangles, the internal diameter
`ω ↦ sup_{u, v ∈ K} D_h(u, v; K)` is a.s. measurable. Proof: closed-set exhaustion of `D_h(·, ·; K)` by the internal
metrics of open neighbourhoods of `K`, each a.s. measurable by locality (axiom II), and lower semicontinuity of
`D_h(·, ·; K)` on `K ×ˢ K`, which reduces the supremum to a countable dense set. -/
theorem lqgMetricSupMeasurable_of_fieldAxioms (hAx : LQGMetricFieldAxiomsUnivFrozen.{u}) :
    LQGMetricSupMeasurableFrozen.{u} := by
  intro γ α₀ ξ hγ0 hγ2 hα Ω _ P hC hcirc D hW hLQG K hK
  obtain ⟨𝔇, h𝔇, hD⟩ := hLQG
  have hax := hAx Ω P γ ξ α₀ hC hcirc hW hγ0 hγ2 hα 𝔇 h𝔇
  have hKcpt : IsCompact K := by
    obtain ⟨F, hF, rfl⟩ := hK
    exact isCompact_biUnion_isClosedRectangle hF
  -- a.s. `D ω` is the `toReal` of the Weyl-scaled metric of the field axioms
  have hDeq : ∀ᵐ ω ∂P, D ω = fun a b =>
      (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) a b).toReal := by
    filter_upwards [hD] with ω hDω
    funext a b
    obtain ⟨h0, h1⟩ := hDω a b
    rw [← h1, ENNReal.toReal_ofReal h0]
  -- axiom I: a.s. `D ω` is a Euclidean length metric
  have hEucD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω) := by
    filter_upwards [hax.1, hDeq] with ω hI hω
    rw [hω]
    exact hI.2
  -- a.s. lower semicontinuity of the internal metric of `K` on `K ×ˢ K`
  have hlsc : ∀ᵐ ω ∂P,
      LowerSemicontinuousOn (fun p : ℂ × ℂ => internalMetric (D ω) K p.1 p.2) (K ×ˢ K) := by
    filter_upwards [hEucD, hD] with ω hω hDω
    exact hω.lowerSemicontinuousOn_internalMetric_pair_closed (fun a b => (hDω a b).1) hKcpt.isClosed
      hKcpt.isBounded
  -- for fixed endpoints in `K`, the internal distance in `K` is a.s. measurable (axiom II on open neighbourhoods)
  have hmeas : ∀ x ∈ K, ∀ y ∈ K, AEMeasurable (fun ω => internalMetric (D ω) K x y) P := by
    intro x hx y hy
    have hk : ∀ k : ℕ, AEMeasurable
        (fun ω => internalMetric (D ω) (Metric.thickening (((k : ℝ) + 1)⁻¹) K) x y) P := by
      intro k
      have hδ : (0 : ℝ) < ((k : ℝ) + 1)⁻¹ := by positivity
      obtain ⟨G, hGm, hGae⟩ := hax.2.1 (Metric.thickening (((k : ℝ) + 1)⁻¹) K) Metric.isOpen_thickening
      refine ((hGm x y).mono (hW.fieldSigmaAlgebra_le α₀ _) le_rfl).aemeasurable.congr ?_
      filter_upwards [hGae, hDeq] with ω hω hDω
      rw [hDω]
      exact (hω x (Metric.self_subset_thickening hδ K hx) y (Metric.self_subset_thickening hδ K hy)).symm
    refine (AEMeasurable.iSup hk).congr ?_
    filter_upwards [hEucD] with ω hω
    exact (internalMetric_closed_eq_iSup_thickening_of_bounded hω hKcpt.isClosed hKcpt.isBounded x y).symm
  obtain ⟨D₀, hD₀K, hD₀c, hKD₀⟩ := exists_countable_dense_subset_of_set K
  have key := LatticeProb.Prob.aemeasurable_iSup_mem_of_lowerSemicontinuousOn (P := P)
    (F := fun ω p => internalMetric (D ω) K p.1 p.2)
    (S := K ×ˢ K) (D := D₀ ×ˢ D₀) (hD₀c.prod hD₀c) (Set.prod_mono hD₀K hD₀K)
    (by rw [closure_prod_eq]; exact Set.prod_mono hKD₀ hKD₀)
    (fun p hp => hmeas p.1 (hD₀K hp.1) p.2 (hD₀K hp.2)) hlsc
  refine key.congr (Eventually.of_forall fun ω => ?_)
  exact biSup_prod

/-- `SmallMetricDiameterLargeMassSquareStmt` (Lemma 11.10) from the hypotheses of
`S11c.firstPass_11_10_derivedInputsContinuousShift` without `hSupM`, which is supplied by
`lqgMetricSupMeasurable_of_fieldAxioms` from `hAx`. -/
theorem S11c.firstPass_11_10_derivedInputsSupMeasurable
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hCM : CameronMartinEventTransferFrozen.{u})
    (hPos : LQGMeasureSquarePositiveFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hM1 : WeylShiftedSupMeasurableFrozen.{u})
    (hAx : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms.{u} P γ ξ α₀ hC hcirc) :
    SmallMetricDiameterLargeMassSquareStmt.{u} :=
  S11c.firstPass_11_10_derivedInputsContinuousShift hDC hCM hPos
    (lqgMetricSupMeasurable_of_fieldAxioms fun Ω _ P γ ξ α₀ hC hcirc => hAx γ ξ α₀ Ω P hC hcirc) hFin hM1 hAx

end HarmonicBalls
