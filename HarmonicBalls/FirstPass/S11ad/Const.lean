import HarmonicBalls.FirstPass.S11m.FirstPos

/-!
# Positive-probability choice of the constants `c, d` (note §6.4)

`exists_const_pos_of_pos`: a positive-probability set on which a lower bound `a₂ > 0` and an upper bound
`d₂ < ∞` hold contains a subset `{a₂ ≥ c, d₂ ≤ d}` of positive probability (continuity from below along
an increasing family). Split out of `S11ad` so that `S11ad.Third` can use it without an import cycle.
-/

open MeasureTheory Set Metric
open scoped ENNReal

namespace HarmonicBalls
namespace S11ad

/-- §6.4 of the certificate note (choice of `c, d`). If a measurable set `A` has positive probability and on `A` the
lower bound `a₂ > 0` and the upper bound `d₂ < ∞` hold, then for some `c, d > 0` the set `{a₂ ≥ c, d₂ ≤ d} ∩ A` has
positive probability. Continuity from below along the increasing family `S n`. -/
theorem exists_const_pos_of_pos {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {A : Set Ω}
    (hAp : 0 < P A) {a₂ : Ω → ℝ} {d₂ : Ω → ℝ≥0∞} (hpos : ∀ ω ∈ A, 0 < a₂ ω ∧ d₂ ω ≠ ∞) :
    ∃ c d : ℝ, 0 < c ∧ 0 < d ∧ 0 < P (A ∩ {ω | c ≤ a₂ ω ∧ d₂ ω ≤ ENNReal.ofReal d}) := by
  set S : ℕ → Set Ω := fun n => A ∩ {ω | 1 / ((n : ℝ) + 1) ≤ a₂ ω ∧ d₂ ω ≤ ENNReal.ofReal ((n : ℝ) + 1)}
    with hS_def
  have hmono : Monotone S := by
    intro m n hmn ω hω
    obtain ⟨hA, h1, h2⟩ := hω
    refine ⟨hA, le_trans ?_ h1, le_trans h2 ?_⟩
    · have hm : (m : ℝ) ≤ n := by exact_mod_cast hmn
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    · exact ENNReal.ofReal_le_ofReal (by
        have hm : (m : ℝ) ≤ n := by exact_mod_cast hmn
        linarith)
  have hcover : A ⊆ ⋃ n, S n := by
    intro ω hωA
    obtain ⟨ha, hd⟩ := hpos ω hωA
    obtain ⟨n₁, hn₁⟩ := exists_nat_one_div_lt ha
    obtain ⟨n₂, hn₂⟩ := ENNReal.exists_nat_gt hd
    refine mem_iUnion.2 ⟨n₁ + n₂, hωA, ?_, ?_⟩
    · have hle : 1 / (((n₁ + n₂ : ℕ) : ℝ) + 1) ≤ 1 / ((n₁ : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        push_cast
        have : (0 : ℝ) ≤ n₂ := by positivity
        linarith
      exact le_trans hle hn₁.le
    · have hle : d₂ ω ≤ ENNReal.ofReal (((n₁ + n₂ : ℕ) : ℝ) + 1) := by
        have h1 : d₂ ω ≤ ((n₂ : ℕ) : ℝ≥0∞) := hn₂.le
        refine le_trans h1 ?_
        rw [← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal (by push_cast; linarith [(Nat.cast_nonneg n₁ : (0 : ℝ) ≤ n₁)])
      exact hle
  have hunion : P A ≤ ⨆ n, P (S n) := by
    calc P A ≤ P (⋃ n, S n) := measure_mono hcover
      _ = ⨆ n, P (S n) := hmono.measure_iUnion
  have hex : ∃ n, 0 < P (S n) := by
    by_contra hcon
    have hle0 : ∀ n, P (S n) ≤ 0 := fun n => not_lt.1 (fun h => hcon ⟨n, h⟩)
    have : ⨆ n, P (S n) = 0 := le_antisymm (iSup_le hle0) zero_le
    exact absurd (lt_of_lt_of_le hAp (this ▸ hunion)) (lt_irrefl _)
  obtain ⟨n, hn⟩ := hex
  refine ⟨1 / ((n : ℝ) + 1), (n : ℝ) + 1, by positivity, by positivity, ?_⟩
  exact hn

end S11ad
end HarmonicBalls
