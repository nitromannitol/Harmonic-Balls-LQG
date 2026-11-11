import Mathlib

/-!
# A positive box of finitely many a.s. positive variables

Step 4.3 of the written proof chooses deterministic thresholds `c > 0` with
`P(F) > 0` "by countable exhaustion of positive finite variables". Steps 4.4 and 4.5 use the same choice.
This file proves that choice: if finitely many measurable real functions are almost surely strictly positive, one
common threshold `c > 0` gives an event of positive probability on which all of them are at least `c`.
Upper bounds are the same statement applied to the negated variables.
-/

namespace HarmonicBalls.S11m

open MeasureTheory

/-- Countable exhaustion of finitely many a.s. positive variables. If `f 0, …, f (k-1)` are measurable and each is
almost surely strictly positive, then for some `c > 0` the event `{ω | c ≤ f i ω for all i}` is measurable and has
positive probability. -/
theorem exists_pos_measure_box {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} (f : Fin k → Ω → ℝ) (hf : ∀ i, Measurable (f i))
    (hpos : ∀ i, ∀ᵐ ω ∂P, 0 < f i ω) :
    ∃ c : ℝ, 0 < c ∧ MeasurableSet {ω | ∀ i, c ≤ f i ω} ∧ 0 < P {ω | ∀ i, c ≤ f i ω} := by
  set B : ℕ → Set Ω := fun n => {ω | ∀ i, 1 / ((n : ℝ) + 1) ≤ f i ω} with hB
  have hae : ∀ᵐ ω ∂P, ∀ i, 0 < f i ω := ae_all_iff.2 hpos
  have hcover : ∀ ω, (∀ i, 0 < f i ω) → ∃ n : ℕ, ω ∈ B n := by
    intro ω hω
    choose n hn using fun i => exists_nat_one_div_lt (hω i)
    refine ⟨Finset.univ.sup n, fun i => ?_⟩
    have hle : n i ≤ Finset.univ.sup n := Finset.le_sup (Finset.mem_univ i)
    have hcast : (n i : ℝ) ≤ ((Finset.univ.sup n : ℕ) : ℝ) := by exact_mod_cast hle
    have hpos' : (0 : ℝ) < (n i : ℝ) + 1 := by positivity
    have hmono : 1 / (((Finset.univ.sup n : ℕ) : ℝ) + 1) ≤ 1 / ((n i : ℝ) + 1) :=
      one_div_le_one_div_of_le hpos' (by linarith)
    exact hmono.trans (hn i).le
  have hU : ∀ᵐ ω ∂P, ω ∈ ⋃ n, B n := by
    filter_upwards [hae] with ω hω
    obtain ⟨n, hn⟩ := hcover ω hω
    exact Set.mem_iUnion.2 ⟨n, hn⟩
  have hUne : P (⋃ n, B n) ≠ 0 := by
    have hc : P (⋃ n, B n)ᶜ = 0 := ae_iff.1 hU
    rw [measure_congr (ae_eq_univ.2 hc), measure_univ]
    exact one_ne_zero
  obtain ⟨n, hn⟩ : ∃ n : ℕ, P (B n) ≠ 0 := by
    by_contra hno
    exact hUne (measure_iUnion_null fun n => by_contra fun h => hno ⟨n, h⟩)
  have hBeq : B n = {ω | ∀ i, 1 / ((n : ℝ) + 1) ≤ f i ω} := rfl
  refine ⟨1 / ((n : ℝ) + 1), by positivity, ?_, ?_⟩
  · have hset : {ω | ∀ i, 1 / ((n : ℝ) + 1) ≤ f i ω} = ⋂ i, {ω | 1 / ((n : ℝ) + 1) ≤ f i ω} := by
      ext ω
      simp
    rw [hset]
    exact MeasurableSet.iInter fun i => measurableSet_le measurable_const (hf i)
  · rw [← hBeq]
    exact pos_iff_ne_zero.2 hn

end HarmonicBalls.S11m

