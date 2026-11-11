import HarmonicBalls.Defs.GFF
import HarmonicBalls.Defs.LQG
import HarmonicBalls.Defs.Notation
import HarmonicBalls.LPStage.GFF
import HarmonicBalls.LPStage.LQGMeasure

/-!
# Bridge to the staged γ-LQG area measure definitions (module M4)

For each of the six staged definitions of `HarmonicBalls/LPStage/LQGMeasure.lean` there is a bridge lemma
relating the HB definition (`HarmonicBalls.*`, Defs/LQG.lean and Defs/Notation.lean) to its LP copy
(`LatticeProb.LQG.*`). The HB definitions are kept, and the counted theorems are unchanged.

* `dyadicScale_eq`, `lqgQ_eq`, `lqgApprox_eq`: definitional equalities (`rfl`); the bodies are identical.
* `isLQGLimit_iff`: `IsLQGLimit` is a structure, so each copy is a distinct type; the bridge is an equivalence,
  constructor by constructor (the two fields have the same statements).
* `isLQGMeasure_iff`: the almost-sure quantifier over `IsLQGLimit`, transported by `isLQGLimit_iff`.
* `isLQGMeasureOfField_iff`: `IsLQGMeasure` applied to the circle averages `HarmonicBalls.fieldCircleAverage α₀ (hcirc ω)`,
  which agree with `LatticeProb.Gauss.fieldCircleAverage α₀ (hcirc ω)` by `rfl` (`fieldCircleAverage_eq` in M1).
-/

namespace HarmonicBalls.LPBridge

open MeasureTheory Filter Topology

/-- The HB dyadic scale is the LP dyadic scale (definitional). -/
theorem dyadicScale_eq (k : ℕ) :
    HarmonicBalls.dyadicScale k = LatticeProb.LQG.dyadicScale k := rfl

/-- The HB LQG constant is the LP LQG constant (definitional). -/
theorem lqgQ_eq (γ : ℝ) : HarmonicBalls.lqgQ γ = LatticeProb.LQG.lqgQ γ := rfl

/-- The HB approximation measure `ε^{γ²/2} e^{γ hε ε z} dz` is the LP one (definitional). -/
theorem lqgApprox_eq (γ : ℝ) (hε : ℝ → ℂ → ℝ) (ε : ℝ) :
    HarmonicBalls.lqgApprox γ hε ε = LatticeProb.LQG.lqgApprox γ hε ε := rfl

/-- The HB limit predicate `IsLQGLimit` is equivalent to its LP copy (constructor by constructor). -/
theorem isLQGLimit_iff (γ : ℝ) (hε : ℝ → ℂ → ℝ) (m : Measure ℂ) :
    HarmonicBalls.IsLQGLimit γ hε m ↔ LatticeProb.LQG.IsLQGLimit γ hε m :=
  ⟨fun h => ⟨h.isLocallyFiniteMeasure, h.tendsto_integral⟩,
    fun h => ⟨h.isLocallyFiniteMeasure, h.tendsto_integral⟩⟩

/-- The HB almost-sure LQG measure predicate `IsLQGMeasure` is equivalent to its LP copy. -/
theorem isLQGMeasure_iff {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hε : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) :
    HarmonicBalls.IsLQGMeasure P γ hε μ ↔ LatticeProb.LQG.IsLQGMeasure P γ hε μ := by
  unfold HarmonicBalls.IsLQGMeasure LatticeProb.LQG.IsLQGMeasure
  exact Filter.eventually_congr (Filter.Eventually.of_forall fun ω => isLQGLimit_iff γ (hε ω) (μ ω))

/-- The HB predicate `IsLQGMeasureOfField` (the γ-LQG measure of the field `h^ℂ - α₀ log |·|`) is equivalent to its
LP copy. The circle averages agree by `rfl`, so the bridge is `isLQGMeasure_iff` at the HB circle averages. -/
theorem isLQGMeasureOfField_iff {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) :
    HarmonicBalls.IsLQGMeasureOfField P γ α₀ hcirc μ ↔
      LatticeProb.LQG.IsLQGMeasureOfField P γ α₀ hcirc μ := by
  unfold HarmonicBalls.IsLQGMeasureOfField LatticeProb.LQG.IsLQGMeasureOfField
  exact isLQGMeasure_iff P γ (fun ω => HarmonicBalls.fieldCircleAverage α₀ (hcirc ω)) μ

end HarmonicBalls.LPBridge
