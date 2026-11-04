import HarmonicBalls.Draft.Section8

/-!
# Frequencies on comparable scales

A limiting frequency along initial intervals also controls the number of good
scales in the interval from `N + 1` to `2 * N`.
-/

open Filter Finset
open scoped BigOperators Topology

namespace HarmonicBalls

/-- A limiting cumulative frequency gives the same limiting frequency on the
interval between `N` and `2N`. -/
theorem tendsto_double_prefix_sub (cumulative : ℕ → ℝ) (q : ℝ)
    (h : Tendsto (fun n : ℕ => cumulative n / (n : ℝ)) atTop (𝓝 q)) :
    Tendsto (fun n : ℕ => (cumulative (2 * n) - cumulative n) / (n : ℝ)) atTop (𝓝 q) := by
  have hdouble : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_mono (fun n => by simp only [id_eq]; omega) tendsto_id
  have hh := ((h.comp hdouble).const_mul 2).sub h
  have hh' : Tendsto (fun n : ℕ => 2 * (cumulative (2 * n) / ((2 * n : ℕ) : ℝ)) -
      cumulative n / (n : ℝ)) atTop (𝓝 q) := by
    simpa only [Function.comp_apply, show (2 : ℝ) * q - q = q by ring] using hh
  apply hh'.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  push_cast
  field_simp

/-- A strictly smaller frequency is eventually a lower bound for the block
count. -/
theorem eventually_le_double_prefix_sub (cumulative : ℕ → ℝ) {q c : ℝ}
    (h : Tendsto (fun n : ℕ => cumulative n / (n : ℝ)) atTop (𝓝 q)) (hc : c < q) :
    ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ≤ cumulative (2 * n) - cumulative n := by
  have he := (tendsto_double_prefix_sub cumulative q h).eventually (Ioi_mem_nhds hc)
  filter_upwards [he, eventually_ge_atTop (1 : ℕ)] with n hn hpos
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  exact (le_of_lt ((lt_div_iff₀ hnpos).mp hn))

/-- The indicator sum on the first `2N` scales splits at `N`. -/
theorem goodScale_sum_split (p : ℕ → Prop) [DecidablePred p] (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 (2 * N), if p n then (1 : ℝ) else 0) =
      (∑ n ∈ Finset.Icc 1 N, if p n then (1 : ℝ) else 0) +
      (∑ n ∈ Finset.Icc (N + 1) (2 * N), if p n then (1 : ℝ) else 0) := by
  have h := Finset.sum_Ico_consecutive (fun n : ℕ => if p n then (1 : ℝ) else 0)
    (show 1 ≤ N + 1 by omega) (show N + 1 ≤ 2 * N + 1 by omega)
  simpa only [Finset.Ico_add_one_right_eq_Icc] using h.symm

/-- A positive asymptotic frequency controls the cardinality of a block of
consecutive good scales. -/
theorem eventually_goodScale_block_count (p : ℕ → Prop) [DecidablePred p] {q c : ℝ}
    (h : Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.Icc 1 N, if p n then (1 : ℝ) else 0) / (N : ℝ)) atTop (𝓝 q))
    (hc : c < q) :
    ∀ᶠ N : ℕ in atTop,
      c * (N : ℝ) ≤ ((Finset.Icc (N + 1) (2 * N)).filter p).card := by
  have he := eventually_le_double_prefix_sub
    (fun N => ∑ n ∈ Finset.Icc 1 N, if p n then (1 : ℝ) else 0) h hc
  filter_upwards [he] with N hN
  rw [goodScale_sum_split p N] at hN
  simpa only [Finset.sum_boole, add_sub_cancel_left] using hN

/-- The block-frequency estimate expressed using set cardinality. -/
theorem eventually_goodScale_block_ncard (p : ℕ → Prop) [DecidablePred p] {q c : ℝ}
    (h : Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.Icc 1 N, if p n then (1 : ℝ) else 0) / (N : ℝ)) atTop (𝓝 q))
    (hc : c < q) :
    ∀ᶠ N : ℕ in atTop,
      c * (N : ℝ) ≤ ({n : ℕ | n ∈ Set.Icc (N + 1) (2 * N) ∧ p n}.ncard : ℝ) := by
  filter_upwards [eventually_goodScale_block_count p h hc] with N hN
  have hs : {n : ℕ | n ∈ Set.Icc (N + 1) (2 * N) ∧ p n} =
      ↑((Finset.Icc (N + 1) (2 * N)).filter p) := by
    ext n
    simp
  simpa only [hs, Set.ncard_coe_finset] using hN

open Classical in
/-- The frequency conclusion of Lemma 8.3 follows from the limiting
frequency of its very-good, comparable annulus events. -/
theorem eventually_veryGoodComparableScaleCount
    (μ : MeasureTheory.Measure ℂ) (βminus : ℝ) (z : ℂ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ m : ℝ) {q ζ : ℝ}
    (h : Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.Icc 1 N, if IsVeryGoodAnnulus μ βminus (dyadicScale n) z N₀
        a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison μ n z m then (1 : ℝ) else 0) /
          (N : ℝ)) atTop (𝓝 q)) (hq : 1 - ζ < q) :
    ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
      veryGoodComparableScaleCount μ βminus z N₀ a b C₁m C₁p C₂m C₂p C₃ m N := by
  classical
  simpa only [veryGoodComparableScaleCount] using
    (eventually_goodScale_block_ncard
      (fun n => IsVeryGoodAnnulus μ βminus (dyadicScale n) z N₀
        a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison μ n z m) h hq)

end HarmonicBalls
