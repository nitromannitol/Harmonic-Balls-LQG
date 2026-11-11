import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# Countable exhaustion of a good event has positive probability

Route: "By countable exhaustion choose deterministic
`c₁,…,c₄ > 0` such that `F = {L ≥ c₁, A ≤ c₂, D(0,∂B) ≥ c₃, d₀ ≤ c₄}` has positive probability."

Generic probability: if almost surely `0 < L`, `A < ∞`, `0 < a`, `d < ∞`, then for some `n : ℕ` the event
`{1/(n+1) ≤ L, A ≤ n, 1/(n+1) ≤ a, d ≤ n}` has positive (outer) probability. No measurability of the events is needed:
the union over `n` is an almost sure event, and countable subadditivity of the outer measure gives the conclusion.
-/

namespace HarmonicBalls

open MeasureTheory Set
open scoped ENNReal

/-- `x < ∞` and `x.toReal ≤ N` give `x ≤ N` in `[0, ∞]`. -/
theorem le_natCast_of_toReal_le {x : ℝ≥0∞} (hx : x < ⊤) (N : ℕ) (h : x.toReal ≤ N) : x ≤ (N : ℝ≥0∞) := by
  calc x = ENNReal.ofReal x.toReal := (ENNReal.ofReal_toReal hx.ne).symm
    _ ≤ ENNReal.ofReal N := ENNReal.ofReal_le_ofReal h
    _ = (N : ℝ≥0∞) := ENNReal.ofReal_natCast N

/-- Pointwise: a good point lies in some exhaustion set. -/
theorem exists_nat_mem_exhaustion {L a : ℝ} {A d : ℝ≥0∞} (hL : 0 < L) (ha : 0 < a) (hA : A < ⊤) (hd : d < ⊤) :
    ∃ n : ℕ, 1 / ((n : ℝ) + 1) ≤ L ∧ A ≤ (n : ℝ≥0∞) ∧ 1 / ((n : ℝ) + 1) ≤ a ∧ d ≤ (n : ℝ≥0∞) := by
  set m := min L a with hm_def
  have hm : 0 < m := lt_min hL ha
  obtain ⟨n, hn⟩ := exists_nat_gt (max (1 / m) (max A.toReal d.toReal))
  have hR1 : 1 / m < n := lt_of_le_of_lt (le_max_left _ _) hn
  have hR2 : A.toReal < n := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hn
  have hR3 : d.toReal < n := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hn
  have hmn : 1 < (n : ℝ) * m := by
    have := (div_lt_iff₀ hm).1 hR1
    linarith
  have hbound : 1 / ((n : ℝ) + 1) ≤ m := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  refine ⟨n, ?_, le_natCast_of_toReal_le hA n hR2.le, ?_, le_natCast_of_toReal_le hd n hR3.le⟩
  · exact hbound.trans (min_le_left _ _)
  · exact hbound.trans (min_le_right _ _)

/-- Countable exhaustion: almost surely `0 < L`, `A < ∞`, `0 < a`, `d < ∞` implies that for some `n` the event
`{1/(n+1) ≤ L, A ≤ n, 1/(n+1) ≤ a, d ≤ n}` has positive probability (outer measure; no measurability is assumed). -/
theorem exists_pos_measure_exhaustion {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (L a : Ω → ℝ) (A d : Ω → ℝ≥0∞) (hgood : ∀ᵐ ω ∂P, 0 < L ω ∧ A ω < ⊤ ∧ 0 < a ω ∧ d ω < ⊤) :
    ∃ n : ℕ, 0 < P {ω | 1 / ((n : ℝ) + 1) ≤ L ω ∧ A ω ≤ (n : ℝ≥0∞) ∧ 1 / ((n : ℝ) + 1) ≤ a ω ∧
      d ω ≤ (n : ℝ≥0∞)} := by
  by_contra hcon
  set F : ℕ → Set Ω := fun n => {ω | 1 / ((n : ℝ) + 1) ≤ L ω ∧ A ω ≤ (n : ℝ≥0∞) ∧
    1 / ((n : ℝ) + 1) ≤ a ω ∧ d ω ≤ (n : ℝ≥0∞)} with hF
  have hle : ∀ n, P (F n) ≤ 0 := fun n => not_lt.1 fun h => hcon ⟨n, h⟩
  have hnull : P (⋃ n, F n) = 0 :=
    measure_iUnion_null fun n => le_antisymm (hle n) zero_le
  have hae : ∀ᵐ ω ∂P, ω ∈ ⋃ n, F n := by
    filter_upwards [hgood] with ω hω
    obtain ⟨hL, hA, ha, hd⟩ := hω
    obtain ⟨n, h1, h2, h3, h4⟩ := exists_nat_mem_exhaustion hL ha hA hd
    exact mem_iUnion.2 ⟨n, h1, h2, h3, h4⟩
  have hcompl : P (⋃ n, F n)ᶜ = 0 := ae_iff.1 hae
  have hsub := measure_union_le (μ := P) (⋃ n, F n) (⋃ n, F n)ᶜ
  rw [union_compl_self, measure_univ, hnull, hcompl, add_zero] at hsub
  exact one_ne_zero (le_antisymm hsub zero_le)

end HarmonicBalls
