import HarmonicBalls.FirstPass.Frozen.S11j
import HarmonicBalls.FirstPass.Frozen.S11c
import HarmonicBalls.FirstPass.LPBridge.M5a
import HarmonicBalls.FirstPass.Phase2.WeylLogTruncationDerivedInputs
import LatticeProb.LQG.InternalDiamRectangleUnion

/-!
# Finite internal diameters of connected unions of rectangles for the singular LQG metric

For a γ-LQG metric `𝔇` (`IsLQGMetric`), the metric of `h - α₀ log |·|` is `D_h = e^{-ξ α₀ log |·|} · 𝔇(h)`
(`IsLQGMetricOfField`). This file collects the deterministic and almost sure facts about `D_h` that reduce the finite
internal diameter of a compact connected finite union of closed rectangles to the finite internal diameter of a single
closed square.

* `ae_isEuclideanLengthMetric_of_isLQGMetricOfField`: under the field axioms of the LQG metric
  (`LQGMetricFieldAxiomsUnivFrozen`, axiom I), almost surely `D_h` is a Euclidean length metric.
* `connectedSquareUnionDiamFiniteFrozen_iff_closedSquare`: under the field axioms, the finite internal diameter of
  compact connected finite unions of closed rectangles (`ConnectedSquareUnionDiamFiniteFrozen`) is equivalent to its
  special case for one closed square. The reduction covers the union by closed squares
  (`LatticeProb.Topology.exists_finset_closedSquare_cover_biUnion`) and chains the internal metrics of the squares
  through the connected intersection graph (`LatticeProb.LQG.ae_exists_internalMetric_rectangleUnion_le_ofReal`).
* `S11c.firstPass_11_10_derivedInputsClosedSquare`: Lemma 11.10 with the closed-square case in place of `hFin`.

The closed-square case itself is the internal boundary estimate of Dubédat-Falconet-Gwynne-Pfeffer-Sun,
arXiv:1905.00380v2, Proposition 3.10 (p. 34), with Proposition 3.17 (pp. 43-44) for squares meeting the singularity at
`0`; it is not proved here.
-/

namespace HarmonicBalls

universe u

open MeasureTheory Set Filter

open scoped ENNReal

/-- The singular LQG metric is almost surely a Euclidean length metric. If `D` is the LQG metric of
`h^ℂ - α₀ log |·|` for a whole-plane GFF `h^ℂ` (`IsLQGMetricOfField`), then under the field axioms
(`LQGMetricFieldAxiomsUnivFrozen`), almost surely `D ω` is a Euclidean length metric. Route: almost surely
`D ω = (e^{-ξ α₀ log |·|} · 𝔇(h^ℂ)).toReal` (the defining identity of `IsLQGMetricOfField`, with `D ω ≥ 0`), and the
right side is a Euclidean length metric by axiom I. -/
theorem ae_isEuclideanLengthMetric_of_isLQGMetricOfField (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    {γ ξ α₀ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {D : Ω → ℂ → ℂ → ℝ} (hW : IsWholePlaneGFF P hC hcirc)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ) (hD : IsLQGMetricOfField P γ ξ α₀ hC D) :
    ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω) := by
  obtain ⟨𝔇, h𝔇, hDeq⟩ := hD
  have hAxω := hAx Ω P γ ξ α₀ hC hcirc hW hγ0 hγ2 hα 𝔇 h𝔇
  filter_upwards [hAxω.1, hDeq] with ω hI hω
  have hfun : D ω = fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal := by
    funext u v
    rw [← (hω u v).2, ENNReal.toReal_ofReal (hω u v).1]
  rw [hfun]
  exact hI.2

/-- The finite internal diameter of compact connected finite unions of closed rectangles for the singular LQG metric
(`ConnectedSquareUnionDiamFiniteFrozen`) is equivalent, under the field axioms of the LQG metric, to its special case
for one closed square: for every closed square `Q`, almost surely `sup_{u, v ∈ Q} D_h(u, v; Q) < ∞`.
Forward: a closed square is a connected union of one closed rectangle. Backward: almost surely `D_h` is a Euclidean
length metric (`ae_isEuclideanLengthMetric_of_isLQGMetricOfField`), so
`LatticeProb.LQG.ae_exists_internalMetric_rectangleUnion_le_ofReal` applies. -/
theorem connectedSquareUnionDiamFiniteFrozen_iff_closedSquare (hAx : LQGMetricFieldAxiomsUnivFrozen.{u}) :
    ConnectedSquareUnionDiamFiniteFrozen.{u} ↔
      ∀ (γ α₀ ξ : ℝ), 0 < γ → γ < 2 → α₀ < lqgQ γ →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
        (D : Ω → ℂ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc → IsLQGMetricOfField P γ ξ α₀ hC D →
      ∀ Q : Set ℂ, LatticeProb.Topology.IsClosedSquare Q →
      ∀ᵐ ω ∂P, ∃ A : ℝ, ∀ u ∈ Q, ∀ v ∈ Q, internalMetric (D ω) Q u v ≤ ENNReal.ofReal A := by
  constructor
  · intro h γ α₀ ξ hγ0 hγ2 hα Ω _ P hC hcirc D hW hD Q hQ
    refine h γ α₀ ξ hγ0 hγ2 hα Ω P hC hcirc D hW hD Q ⟨{Q}, ?_, by simp⟩ ?_
    · intro R hR
      rw [Finset.mem_singleton] at hR
      subst hR
      exact hQ.isClosedRectangle
    · obtain ⟨x, y, s, hs, rfl⟩ := hQ
      refine Convex.isConnected ?_ ⟨⟨x, y⟩, ?_⟩
      · exact ((convex_Icc x (x + s)).linear_preimage Complex.reLm).inter
          ((convex_Icc y (y + s)).linear_preimage Complex.imLm)
      · simp only [Complex.mem_reProdIm, Set.mem_Icc]
        exact ⟨⟨le_rfl, by linarith⟩, le_rfl, by linarith⟩
  · intro hSq γ α₀ ξ hγ0 hγ2 hα Ω _ P hC hcirc D hW hD K hK hKc
    have hDL : ∀ᵐ ω ∂P, LatticeProb.LQG.IsEuclideanLengthMetric (D ω) :=
      (ae_isEuclideanLengthMetric_of_isLQGMetricOfField hAx hW hγ0 hγ2 hα hD).mono
        fun ω h => (LPBridge.isEuclideanLengthMetric_iff _).mp h
    exact LatticeProb.LQG.ae_exists_internalMetric_rectangleUnion_le_ofReal hDL
      (hSq γ α₀ ξ hγ0 hγ2 hα Ω P hC hcirc D hW hD) hK hKc.isPreconnected

/-- **Derived.** Lemma 11.10 with the finite internal diameter of compact connected finite unions of closed rectangles
(`hFin : ConnectedSquareUnionDiamFiniteFrozen`) replaced by its special case for one closed square `hSq`
(Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380v2, Proposition 3.10, p. 34, and Proposition 3.17, pp. 43-44).
The hypothesis `hFin` of `S11c.firstPass_11_10_derivedInputsFieldAxioms` is supplied by
`connectedSquareUnionDiamFiniteFrozen_iff_closedSquare`; the other hypotheses are unchanged. -/
theorem S11c.firstPass_11_10_derivedInputsClosedSquare
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hPos : LQGMeasureSquarePositiveFrozen.{u})
    (hSq : ∀ (γ α₀ ξ : ℝ), 0 < γ → γ < 2 → α₀ < lqgQ γ →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
        (D : Ω → ℂ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc → IsLQGMetricOfField P γ ξ α₀ hC D →
      ∀ Q : Set ℂ, LatticeProb.Topology.IsClosedSquare Q →
      ∀ᵐ ω ∂P, ∃ A : ℝ, ∀ u ∈ Q, ∀ v ∈ Q, internalMetric (D ω) Q u v ≤ ENNReal.ofReal A)
    (hAx : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms.{u} P γ ξ α₀ hC hcirc) :
    SmallMetricDiameterLargeMassSquareStmt.{u} :=
  S11c.firstPass_11_10_derivedInputsFieldAxioms hDC hPos
    ((connectedSquareUnionDiamFiniteFrozen_iff_closedSquare
      fun Ω _ P γ ξ α₀ hC hcirc => hAx γ ξ α₀ Ω P hC hcirc).mpr hSq) hAx

end HarmonicBalls
