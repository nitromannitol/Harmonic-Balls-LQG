import HarmonicBalls.Defs.Annuli

/-! # helper: the annulus-ball comparison fails with small probability for small `m`

The origin annulus-ball comparison `AnnulusBallComparison μ 0 0 m` (Defs/Annuli.lean, the comparison `G_0(0; m)` of the
phase bound) reads `m · μ(B_1(0)) ≤ μ(𝔸_{1/2,1}(0))` (`annulusBallComparison_zero_iff`). Its failure events
`E_k = {μ(𝔸) < (k+1)⁻¹ μ(B)}` decrease in `k`, and their intersection is null, because almost surely `μ(𝔸) > 0`
(full support, `hpos`) and `μ(B) < ∞` (local finiteness, `hloc`). Continuity from above then gives a `m > 0` with
`P(not AnnulusBallComparison(·, 0, 0, m)) ≤ ζ`. The Weyl and density inputs are not used here.

No new mathematics: continuity of a finite measure along a decreasing sequence of null-measurable sets, and the
elementary inequality `(k+1)⁻¹ · b < a` for some `k` when `0 < a` and `b < ∞`. -/

open MeasureTheory Metric Set Filter
open scoped ENNReal

namespace HarmonicBalls

/-- The origin annulus-ball comparison at scale `1`: `m · μ(B_1) ≤ μ(𝔸_{1/2,1})`. -/
theorem annulusBallComparison_zero_iff (μ : Measure ℂ) (m : ℝ) :
    AnnulusBallComparison μ 0 0 m ↔ ENNReal.ofReal m * μ (ball 0 1) ≤ μ (annulus 0 (1 / 2) 1) := by
  unfold AnnulusBallComparison dyadicScale
  norm_num

/-- The origin annulus-ball comparison fails with arbitrarily small probability for small `m`. -/
theorem annulus_ball_comparison_small {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure ℂ) (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (ν ω))
    (hpos : ∀ᵐ ω ∂P, 0 < ν ω (annulus 0 (1 / 2) 1))
    (hB : AEMeasurable (fun ω => ν ω (ball 0 1)) P)
    (hA : AEMeasurable (fun ω => ν ω (annulus 0 (1 / 2) 1)) P)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ m : ℝ, 0 < m ∧ P {ω | ¬ AnnulusBallComparison (ν ω) 0 0 m} ≤ ENNReal.ofReal ζ := by
  set E : ℕ → Set Ω := fun k => {ω | ν ω (annulus 0 (1 / 2) 1) <
    ENNReal.ofReal (1 / ((k : ℝ) + 1)) * ν ω (ball 0 1)} with hE
  have hEset : ∀ k : ℕ, {ω | ¬ AnnulusBallComparison (ν ω) 0 0 (1 / ((k : ℝ) + 1))} = E k := by
    intro k
    ext ω
    simp only [E, Set.mem_ofPred_eq, annulusBallComparison_zero_iff, not_le]
  have hanti : Antitone E := by
    intro k k' hkk' ω hω
    simp only [E, Set.mem_ofPred_eq] at hω ⊢
    have hkk'R : ((k : ℝ) + 1) ≤ ((k' : ℝ) + 1) := by
      have := (Nat.cast_le (α := ℝ)).2 hkk'
      linarith
    have hdiv : 1 / ((k' : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) hkk'R
    exact lt_of_lt_of_le hω (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hdiv) zero_le)
  have hmeas : ∀ k : ℕ, NullMeasurableSet (E k) P := by
    intro k
    exact nullMeasurableSet_lt hA (hB.const_mul _)
  have hnull : P (⋂ k, E k) = 0 := by
    have hae : ∀ᵐ ω ∂P, ω ∉ ⋂ k, E k := by
      filter_upwards [hpos, hloc] with ω hp hl hmem
      have hk : ∀ k : ℕ, ν ω (annulus 0 (1 / 2) 1) <
          ENNReal.ofReal (1 / ((k : ℝ) + 1)) * ν ω (ball 0 1) := fun k => Set.mem_iInter.1 hmem k
      have hB0 : ν ω (ball 0 1) < ∞ := measure_ball_lt_top
      have hA0 : ν ω (annulus 0 (1 / 2) 1) < ∞ :=
        lt_of_lt_of_le (hk 0) (le_of_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hB0))
      set a : ℝ := (ν ω (annulus 0 (1 / 2) 1)).toReal with ha
      set b : ℝ := (ν ω (ball 0 1)).toReal with hb
      have ha0 : 0 < a := ENNReal.toReal_pos hp.ne' hA0.ne
      have hb0 : 0 ≤ b := ENNReal.toReal_nonneg
      obtain ⟨k, hk'⟩ := exists_nat_one_div_lt (show 0 < a / (b + 1) by positivity)
      have hle : ENNReal.ofReal (1 / ((k : ℝ) + 1)) * ν ω (ball 0 1) ≤ ν ω (annulus 0 (1 / 2) 1) := by
        rw [← ENNReal.ofReal_toReal hB0.ne, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_toReal hA0.ne]
        apply ENNReal.ofReal_le_ofReal
        have h1 : 1 / ((k : ℝ) + 1) * b ≤ a / (b + 1) * b := mul_le_mul_of_nonneg_right hk'.le hb0
        have h2 : a / (b + 1) * b ≤ a := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith
        linarith
      exact absurd (hk k) (not_lt.2 hle)
    simpa only [not_not, Set.ofPred_mem_eq] using ae_iff.1 hae
  have hT := tendsto_measure_iInter_atTop (μ := P) (s := E) hmeas hanti ⟨0, measure_ne_top P _⟩
  rw [hnull] at hT
  have hev := (tendsto_order.1 hT).2 (ENNReal.ofReal ζ) (ENNReal.ofReal_pos.2 hζ)
  obtain ⟨k, hk⟩ := hev.exists
  refine ⟨1 / ((k : ℝ) + 1), by positivity, ?_⟩
  rw [hEset k]
  exact hk.le


end HarmonicBalls
