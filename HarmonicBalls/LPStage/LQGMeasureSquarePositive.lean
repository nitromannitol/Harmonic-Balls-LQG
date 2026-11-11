import Mathlib
import HarmonicBalls.LPStage.GFF
import HarmonicBalls.LPStage.LQGMeasure
import HarmonicBalls.LPStage.PlaneTopology

/-!
# LP stage: square positivity of the LQG measure (row 23; z3, task `fp-lpstage-lqg-metric-univ-and-square-positive`, item 3)

Status (partial; see the report): the LP form of the frozen row 23 is defined, and the elementary part of its derivation is
proved. The LP-stage proof of the square positivity itself is NOT here: the HB derivation
`HarmonicBalls.lqgMeasureSquarePositiveFrozen_derived` (`FirstPass/Phase2/SquarePositiveDerived.lean:40`) passes through the
full-support statement `lqgMeasureFullSupportStmt_of_existence` (`Proofs/Sec9/LQGExistenceConsequences.lean:46`), whose HB
closure is larger than the copy budget (see the report). The three binders of the HB derivation are given LP forms in
`LPStage/LQGMeasureInputs.lean`.

* `LatticeProb.Topology.exists_isOpen_nonempty_subset_closedDyadicSquare`: LP port of
  `HarmonicBalls.exists_isOpen_nonempty_subset_closedDyadicSquare` (`SquarePositiveDerived.lean:24`).
* `LatticeProb.LQG.LQGMeasureSquarePositiveLP`: LP form of `LQGMeasureSquarePositiveFrozen` (`FirstPass/Frozen/S11c.lean:130`);
  a definition only.
* `LatticeProb.LQG.ae_pos_closedDyadicSquare_of_charges`: the elementary step of `SquarePositiveDerived.lean:40`: if almost
  surely `μ` charges every nonempty open set, then almost surely `μ(S) > 0` for every closed dyadic square `S`. No LQG input.
-/

open MeasureTheory Set Filter Topology Metric

universe u

namespace LatticeProb.Topology

/-- A closed dyadic square contains a nonempty open rectangle: the open product of the open intervals
`(j 2^{-n}, (j+1) 2^{-n})` and `(k 2^{-n}, (k+1) 2^{-n})`. -/
theorem exists_isOpen_nonempty_subset_closedDyadicSquare (n j k : ℤ) :
    ∃ U : Set ℂ, IsOpen U ∧ U.Nonempty ∧ U ⊆ closedDyadicSquare n j k := by
  have hs : (0 : ℝ) < (2 : ℝ) ^ (-n) := zpow_pos (by norm_num) _
  have h1 : (j : ℝ) * 2 ^ (-n) < ((j : ℝ) + 1) * 2 ^ (-n) := by nlinarith
  have h2 : (k : ℝ) * 2 ^ (-n) < ((k : ℝ) + 1) * 2 ^ (-n) := by nlinarith
  refine ⟨Ioo ((j : ℝ) * 2 ^ (-n)) (((j : ℝ) + 1) * 2 ^ (-n)) ×ℂ
    Ioo ((k : ℝ) * 2 ^ (-n)) (((k : ℝ) + 1) * 2 ^ (-n)), ?_, ?_, ?_⟩
  · exact isOpen_Ioo.reProdIm isOpen_Ioo
  · exact Complex.reProdIm_nonempty.2 ⟨nonempty_Ioo.2 h1, nonempty_Ioo.2 h2⟩
  · exact (Complex.reProdIm_subset_iff).2
      (Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self)

end LatticeProb.Topology

namespace LatticeProb.LQG

open LatticeProb.Gauss LatticeProb.Topology

/-- **LP form of `LQGMeasureSquarePositiveFrozen`** (`FirstPass/Frozen/S11c.lean:130`): for `0 < γ < 2` and `α₀ < Q`, on every
whole-plane GFF space in `Type u` and for every LQG measure `μ` of the field, almost surely every closed dyadic square has
positive mass. A definition only: this Prop is not proved in the LP stage yet (row 23 is open). -/
def LQGMeasureSquarePositiveLP : Prop :=
  ∀ (γ α₀ : ℝ), 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ S : Set ℂ, LatticeProb.Topology.IsClosedDyadicSquare S → ∀ᵐ ω ∂P, 0 < μ ω S

/-- Elementary step of the HB derivation (`SquarePositiveDerived.lean:40`): if almost surely `μ` charges every nonempty
open set, then almost surely `μ(closedDyadicSquare n j k) > 0`. The closed square contains a nonempty open rectangle, and
the measure is monotone. No LQG input is used. -/
theorem ae_pos_closedDyadicSquare_of_charges {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {μ : Ω → Measure ℂ}
    (h : ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ ω U) (n j k : ℤ) :
    ∀ᵐ ω ∂P, 0 < μ ω (closedDyadicSquare n j k) := by
  obtain ⟨U, hUo, hUne, hUS⟩ := exists_isOpen_nonempty_subset_closedDyadicSquare n j k
  filter_upwards [h] with ω hω
  exact lt_of_lt_of_le (hω U hUo hUne) (measure_mono hUS)

/-- The elementary step for a set `S` that is a closed dyadic square (`LatticeProb.Topology.IsClosedDyadicSquare`). -/
theorem ae_pos_isClosedDyadicSquare_of_charges {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {μ : Ω → Measure ℂ}
    (h : ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ ω U) {S : Set ℂ}
    (hS : LatticeProb.Topology.IsClosedDyadicSquare S) : ∀ᵐ ω ∂P, 0 < μ ω S := by
  obtain ⟨n, j, k, rfl⟩ := hS
  exact ae_pos_closedDyadicSquare_of_charges h n j k

end LatticeProb.LQG
