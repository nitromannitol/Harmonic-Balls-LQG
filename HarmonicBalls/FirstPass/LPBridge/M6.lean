import HarmonicBalls.Defs.LQGGraphDistance
import HarmonicBalls.Proposed.LQGDimension
import HarmonicBalls.LPStage.LiouvilleGraph
import HarmonicBalls.FirstPass.LPBridge.M1
import HarmonicBalls.FirstPass.LPBridge.M4

/-!
# Bridge to the staged Liouville graph-distance objects (module M6)

For each of the five staged definitions of `HarmonicBalls/LPStage/LiouvilleGraph.lean` there is a bridge lemma relating
the HB definition (`HarmonicBalls.*`, Defs/LQGGraphDistance.lean) to its LP copy (`LatticeProb.LQG.*`), and the staged
input `WholePlaneLQGGraphDimension` (Proposed/LQGDimension.lean) has an equivalence with its LP copy. The HB definitions
are kept, and no HB statement is changed.

* `liouvilleGraphDistance_eq`, `liouvilleGraphExponent_eq`: definitional equalities (`rfl`); the bodies are identical.
* `isLiouvilleGraphCover_iff`, `isLiouvilleGraphDimension_iff`: definitional equivalences (`Iff.rfl`); the bodies are
  identical up to the bridged names.
* `isWholePlaneLQGDimension_iff`: not `rfl`, since the body quantifies over `IsWholePlaneGFF` and `IsLQGMeasureOfField`,
  which are bridged by `isWholePlaneGFF_iff` (M1) and `isLQGMeasureOfField_iff` (M4), so it is an equivalence.
* `wholePlaneLQGGraphDimension_iff`: the input, an equivalence through `isWholePlaneLQGDimension_iff`.
-/

namespace HarmonicBalls.LPBridge

open MeasureTheory Filter Topology

/-- The HB cover predicate is definitionally its LP copy. -/
theorem isLiouvilleGraphCover_iff (μ : Measure ℂ) (ε : ℝ) (z w : ℂ) (count : ℕ) :
    HarmonicBalls.IsLiouvilleGraphCover μ ε z w count ↔
      LatticeProb.LQG.IsLiouvilleGraphCover μ ε z w count :=
  Iff.rfl

/-- The HB Liouville graph distance is the LP copy (definitional). -/
theorem liouvilleGraphDistance_eq (μ : Measure ℂ) (ε : ℝ) (z w : ℂ) :
    HarmonicBalls.liouvilleGraphDistance μ ε z w = LatticeProb.LQG.liouvilleGraphDistance μ ε z w :=
  rfl

/-- The HB dyadic point-to-point exponent is the LP copy (definitional). -/
theorem liouvilleGraphExponent_eq (μ : Measure ℂ) (z w : ℂ) (index : ℕ) :
    HarmonicBalls.liouvilleGraphExponent μ z w index =
      LatticeProb.LQG.liouvilleGraphExponent μ z w index :=
  rfl

/-- The HB dimension predicate `IsLiouvilleGraphDimension` is definitionally its LP copy. -/
theorem isLiouvilleGraphDimension_iff (μ : Measure ℂ) (z w : ℂ) (dimension : ℝ) :
    HarmonicBalls.IsLiouvilleGraphDimension μ z w dimension ↔
      LatticeProb.LQG.IsLiouvilleGraphDimension μ z w dimension :=
  Iff.rfl

/-- The HB whole-plane LQG dimension predicate is equivalent to its LP copy. The quantifier over realizations is
transported by `isWholePlaneGFF_iff` (M1) and `isLQGMeasureOfField_iff` (M4), and the almost-sure predicate by
`isLiouvilleGraphDimension_iff`. -/
theorem isWholePlaneLQGDimension_iff (γ dimension : ℝ) :
    HarmonicBalls.IsWholePlaneLQGDimension γ dimension ↔
      LatticeProb.LQG.IsWholePlaneLQGDimension γ dimension := by
  constructor
  · rintro ⟨hpos, h⟩
    refine ⟨hpos, ?_⟩
    intro Ω _ P _ hC hcirc μ hgff hμ
    exact (h Ω P hC hcirc μ ((isWholePlaneGFF_iff P hC hcirc).2 hgff)
      ((isLQGMeasureOfField_iff P γ 0 hcirc μ).2 hμ)).mono fun ω hω =>
        (isLiouvilleGraphDimension_iff _ _ _ _).1 hω
  · rintro ⟨hpos, h⟩
    refine ⟨hpos, ?_⟩
    intro Ω _ P _ hC hcirc μ hgff hμ
    exact (h Ω P hC hcirc μ ((isWholePlaneGFF_iff P hC hcirc).1 hgff)
      ((isLQGMeasureOfField_iff P γ 0 hcirc μ).1 hμ)).mono fun ω hω =>
        (isLiouvilleGraphDimension_iff _ _ _ _).2 hω

/-- The HB literature input `WholePlaneLQGGraphDimension` is equivalent to its LP copy. -/
theorem wholePlaneLQGGraphDimension_iff :
    HarmonicBalls.WholePlaneLQGGraphDimension ↔ LatticeProb.LQG.WholePlaneLQGGraphDimension := by
  constructor
  · intro h γ hγ hγ2
    obtain ⟨d, hd⟩ := h γ hγ hγ2
    exact ⟨d, (isWholePlaneLQGDimension_iff γ d).1 hd⟩
  · intro h γ hγ hγ2
    obtain ⟨d, hd⟩ := h γ hγ hγ2
    exact ⟨d, (isWholePlaneLQGDimension_iff γ d).2 hd⟩

end HarmonicBalls.LPBridge
