# Boundary-touching right continuity: proof attempt

The obstacle and compactness infrastructure used below incorporates work by Leonardo Bonanno. The requested post-contact inclusion is **not proved**. No new Lean premise or numbered-result closure is introduced.

The corrected paper states right continuity for every positive time in Proposition 5.2, lines 828–838. Proposition 7.2, lines 2025–2032, requires compact containment in the unit disc. Its proof uses this explicitly: the annular cover is compactly contained in the disc and the present cluster has mass `t` (lines 2045–2067). The appeal at lines 2105–2108 does not address the boundary-contact case. This is a gap in the displayed argument, not a counterexample to Proposition 5.2.

For a concrete measure, the missing deterministic implication, as a *goal* rather than an assumed premise, is the following. Its validity under exactly these hypotheses has not been established; it may require additional conditions on the measure.

```lean
∀ (μ : MeasureTheory.Measure ℂ) [MeasureTheory.IsLocallyFiniteMeasure μ]
  (βm βp : ℝ), VolumeGrowth μ 1 βm βp →
  ∀ z ∈ Metric.ball (0 : ℂ) (1 / 2), ∀ t : ℝ, 0 < t →
    (⋂ n : ℕ, closure (cluster μ 1 z (t + dyadicScale n))) ⊆
      closure (cluster μ 1 z t)
```

A possible intermediate goal is the boundary interior-ball property in `Proofs/Sec5/BoundaryInteriorBallContinuity.lean:57–60`, derived from the obstacle and the standing assumptions. Together with vanishing increment mass and the interior inclusion, that property supplies right continuity, as proved at lines 49–74. However `BoundaryInteriorBallNecessity.lean:86` proves its equivalence to right continuity under the existing conditions; it cannot be counted as an independently established estimate. A genuine proof needs a boundary nondegeneracy or barrier argument and cannot take that property as a hypothesis.

`InteriorTimeContinuity.lean:21,55` proves vanishing added mass and absence of new interior points, respectively, on the events and under the numbered-result hypotheses displayed there. `LocalOdometerIncrement.lean:19` controls test functions with support inside the disc, and `GeneralDomainTimeConvexity.lean:115` gives uniform time-Lipschitz bounds for least-supersolution values. Neither prevents a noncontact layer of vanishing thickness along the Dirichlet boundary. This is a real limitation of those reductions: `MacroscopicBoundaryJumpModel.lean:197` constructs increasing open connected subsets of the unit disc with vanishing added area and no new interior limit points, yet a new boundary arc. That model is not an obstacle-cluster counterexample.

The larger-disc approach also does not settle the deficient-mass regime. Since the smaller cluster is contained in the unit disc and the disc has finite mass under local finiteness, for any `t > (μ (Metric.ball (0 : ℂ) 1)).toReal` its mass is strictly below `ENNReal.ofReal t`. Under the open-set, null-frontier and larger-disc mass-conservation hypotheses explicitly listed in `LargerDiscMassEquivalence.lean:14–22`, equality of the two cluster closures would force full mass. The first-contact/full-mass transfers therefore cannot be extended by merely asserting that equality.

No published source establishing the displayed post-contact implication under these exact hypotheses was identified in the checked material. The supplied paper does not provide a boundary-touching proof in the cited Proposition 7.2. A source for a stronger boundary estimate, or a new proof (or a genuine obstacle-cluster counterexample), remains necessary.
