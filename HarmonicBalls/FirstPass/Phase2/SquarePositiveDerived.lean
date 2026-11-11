import HarmonicBalls.Proofs.Sec9.LQGExistenceConsequences
import HarmonicBalls.FirstPass.Frozen.S11c

/-!
# Square positivity of the LQG measure from the existence inputs

The frozen statement
`LQGMeasureSquarePositiveFrozen` (FirstPass/Frozen/S11c.lean:130) asks that, almost surely, every closed dyadic
square `S` satisfies `0 < μ_h(S)`. It follows from the full-support statement `LQGMeasureFullSupportStmt`
, which is obtained from the existence inputs
`hDG`, `hCC` (at `α₀ = 0`) and `hE` by `lqgMeasureFullSupportStmt_of_existence`
(Proofs/Sec9/LQGExistenceConsequences.lean:46). The only further step is elementary: a closed dyadic square contains
a nonempty open rectangle, and the LQG measure is monotone on Borel sets.
-/

open MeasureTheory Set Filter Topology Metric

universe u

namespace HarmonicBalls

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

/-- Square positivity of the LQG measure (FirstPass/Frozen/S11c.lean:130) from the full-support consequence
`lqgMeasureFullSupportStmt_of_existence`: for each closed dyadic square `S`, almost surely `0 < μ_h(S)`, because
`μ_h` charges the nonempty open rectangle contained in `S` almost surely (for all open nonempty sets at once), and
`μ_h` is monotone. Premises: `hDG`, `hCC`, `hE` (the existence inputs, as in `lqgMeasureFullSupportStmt_of_existence`). -/
theorem lqgMeasureSquarePositiveFrozen_derived
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ α hC hcirc) :
    LQGMeasureSquarePositiveFrozen.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hG hμ S hS
  obtain ⟨n, j, k, rfl⟩ := hS
  obtain ⟨U, hUo, hUne, hUS⟩ := exists_isOpen_nonempty_subset_closedDyadicSquare n j k
  filter_upwards [lqgMeasureFullSupportStmt_of_existence.{u} hDG hCC hE γ α₀ hγ hγ2 hα Ω P hC hcirc μ hG hμ]
    with ω hω
  exact lt_of_lt_of_le (hω U hUo hUne) (measure_mono hUS)

end HarmonicBalls
