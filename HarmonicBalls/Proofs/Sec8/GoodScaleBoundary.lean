import HarmonicBalls.Defs.Annuli

/-!
# Good scales and boundary points

Deterministic steps in the proof of Proposition 8.1: the count in Lemma 8.2
provides arbitrarily large good scales, and the annulus-ball comparison turns
small cluster mass in the ball into the hypothesis of the Harnack estimate.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

/-- A positive lower density of good scales in `[N + 1, 2N]` yields arbitrarily
large scales at which both the very good event and annulus-ball comparison hold. -/
theorem exists_veryGoodComparableScale_ge_of_count
    (μ : Measure ℂ) (βminus : ℝ) (z : ℂ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ) (hζ : ζ < 1)
    (hcount : ∀ᶠ N : ℕ in atTop,
      (1 - ζ) * (N : ℝ) ≤
        veryGoodComparableScaleCount μ βminus z N₀ a b C₁m C₁p C₂m C₂p C₃ m N) :
    ∀ K : ℕ, ∃ n : ℕ, K ≤ n ∧
      IsVeryGoodAnnulus μ βminus (dyadicScale n) z N₀ a b C₁m C₁p C₂m C₂p C₃ ∧
      AnnulusBallComparison μ n z m := by
  intro K
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hcount
  let M := max N (max K 1)
  have hNM : N ≤ M := le_max_left _ _
  have hKM : K ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
  have hM : 0 < M := lt_of_lt_of_le (by omega : 0 < 1) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hpos : 0 < (veryGoodComparableScaleCount μ βminus z N₀ a b C₁m C₁p C₂m C₂p C₃ m M : ℝ) :=
    lt_of_lt_of_le (mul_pos (sub_pos.mpr hζ) (Nat.cast_pos.mpr hM)) (hN M hNM)
  have hnat : 0 < veryGoodComparableScaleCount μ βminus z N₀ a b C₁m C₁p C₂m C₂p C₃ m M := by
    exact_mod_cast hpos
  unfold veryGoodComparableScaleCount at hnat
  have hf : {n : ℕ | n ∈ Icc (M + 1) (2 * M) ∧
      IsVeryGoodAnnulus μ βminus (dyadicScale n) z N₀ a b C₁m C₁p C₂m C₂p C₃ ∧
      AnnulusBallComparison μ n z m}.Finite :=
    (Set.finite_Icc _ _).subset fun _ hn => hn.1
  obtain ⟨n, hn, hv, hc⟩ := (Set.ncard_pos hf).1 hnat
  have hlo : M + 1 ≤ n := hn.1
  exact ⟨n, by omega, hv, hc⟩

/-- At a comparable scale, a small mass inside the ball gives the small-annulus
hypothesis of the Harnack estimate. -/
theorem measure_inter_annulus_le_of_ball_comparison
    (μ : Measure ℂ) (s : Set ℂ) (z : ℂ) (n : ℕ) (α m : ℝ)
    (hcomp : AnnulusBallComparison μ n z m)
    (hsmall : μ (s ∩ ball z (dyadicScale n)) ≤
      ENNReal.ofReal α * (ENNReal.ofReal m * μ (ball z (dyadicScale n)))) :
    μ (s ∩ annulus z (dyadicScale (n + 1)) (dyadicScale n)) ≤
      ENNReal.ofReal α * μ (annulus z (dyadicScale (n + 1)) (dyadicScale n)) := by
  calc
    _ ≤ μ (s ∩ ball z (dyadicScale n)) := measure_mono (inter_subset_inter_right _ sdiff_subset)
    _ ≤ ENNReal.ofReal α * (ENNReal.ofReal m * μ (ball z (dyadicScale n))) := hsmall
    _ ≤ ENNReal.ofReal α * μ (annulus z (dyadicScale (n + 1)) (dyadicScale n)) :=
      mul_le_mul_right hcomp _

/-- The Harnack exclusion of a ball about `z` contradicts `z ∈ closure s`. -/
theorem not_mem_closure_of_disjoint_ball {s : Set ℂ} {z : ℂ} {r : ℝ}
    (hr : 0 < r) (h : s ∩ ball z r = ∅) : z ∉ closure s := by
  intro hz
  obtain ⟨y, hy, hyd⟩ := Metric.mem_closure_iff.1 hz r hr
  have hyball : y ∈ ball z r := by simpa only [mem_ball, dist_comm] using hyd
  have : y ∈ s ∩ ball z r := ⟨hy, hyball⟩
  rw [h] at this
  exact this

/-- The pointwise contradiction in Proposition 8.1. Once the ball mass is
small at every sufficiently fine scale, any later very good comparable scale
excludes the point from the closure of the cluster. The last hypothesis is
the relevant application of the Harnack estimate. -/
theorem not_mem_closure_of_good_scale_count
    (μ : Measure ℂ) (s : Set ℂ) (βminus : ℝ) (z : ℂ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ m α ζ : ℝ) (hζ : ζ < 1)
    (hcount : ∀ᶠ N : ℕ in atTop,
      (1 - ζ) * (N : ℝ) ≤
        veryGoodComparableScaleCount μ βminus z N₀ a b C₁m C₁p C₂m C₂p C₃ m N)
    (hsmall : ∀ᶠ n : ℕ in atTop,
      μ (s ∩ ball z (dyadicScale n)) ≤
        ENNReal.ofReal α * (ENNReal.ofReal m * μ (ball z (dyadicScale n))))
    (hexclude : ∀ n : ℕ,
      IsVeryGoodAnnulus μ βminus (dyadicScale n) z N₀ a b C₁m C₁p C₂m C₂p C₃ →
      μ (s ∩ annulus z (dyadicScale (n + 1)) (dyadicScale n)) ≤
        ENNReal.ofReal α * μ (annulus z (dyadicScale (n + 1)) (dyadicScale n)) →
      s ∩ ball z (dyadicScale n / 2) = ∅) :
    z ∉ closure s := by
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 hsmall
  obtain ⟨n, hn, hv, hc⟩ :=
    exists_veryGoodComparableScale_ge_of_count μ βminus z N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ hζ hcount K
  have hmass := measure_inter_annulus_le_of_ball_comparison μ s z n α m hc (hK n hn)
  exact not_mem_closure_of_disjoint_ball (half_pos (dyadicScale_pos n)) (hexclude n hv hmass)

/-- A boundary has zero measure when its almost-everywhere points satisfy the
good-scale, small-ball-mass, and Harnack-exclusion conditions. -/
theorem measure_frontier_eq_zero_of_good_scales
    (μ : Measure ℂ) (s : Set ℂ) (βminus : ℝ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ m α ζ : ℝ) (hζ : ζ < 1)
    (hpoint : ∀ᵐ z ∂μ.restrict (frontier s),
      (∀ᶠ N : ℕ in atTop,
        (1 - ζ) * (N : ℝ) ≤
          veryGoodComparableScaleCount μ βminus z N₀ a b C₁m C₁p C₂m C₂p C₃ m N) ∧
      (∀ᶠ n : ℕ in atTop,
        μ (s ∩ ball z (dyadicScale n)) ≤
          ENNReal.ofReal α * (ENNReal.ofReal m * μ (ball z (dyadicScale n)))) ∧
      (∀ n : ℕ,
        IsVeryGoodAnnulus μ βminus (dyadicScale n) z N₀ a b C₁m C₁p C₂m C₂p C₃ →
        μ (s ∩ annulus z (dyadicScale (n + 1)) (dyadicScale n)) ≤
          ENNReal.ofReal α * μ (annulus z (dyadicScale (n + 1)) (dyadicScale n)) →
        s ∩ ball z (dyadicScale n / 2) = ∅)) :
    μ (frontier s) = 0 := by
  apply ae_restrict_eq_bot.1
  apply Filter.eventually_false_iff_eq_bot.1
  filter_upwards [hpoint, ae_restrict_mem isClosed_frontier.measurableSet] with z hz hfront
  exact not_mem_closure_of_good_scale_count μ s βminus z N₀ a b C₁m C₁p C₂m C₂p C₃ m α ζ
    hζ hz.1 hz.2.1 hz.2.2 (frontier_subset_closure hfront)

end HarmonicBalls
