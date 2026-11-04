import HarmonicBalls.Steps.Sec11.PowerBoundPunctureCriterion

/-! # From small-scale exponents to discrete metric scales

This file proves the deterministic consequences of an asymptotic exponent.
The LQG scaling estimate itself remains an explicit external input.
-/

namespace HarmonicBalls

open Filter
open scoped ENNReal Topology

/-- For a base below one, an exponent tending to q gives every weaker
power bound near zero. -/
theorem eventually_power_bound_of_exponent_error
    (a : ℝ → ℝ≥0∞) (q θ : ℝ) (e : ℝ → ℝ) (C : ℝ≥0∞)
    (hθ : θ < q) (he : Tendsto e (𝓝[>] (0 : ℝ)) (𝓝 0))
    (ha : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      a r ≤ C * ENNReal.ofReal (Real.rpow r (q + e r))) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), a r ≤ C * ENNReal.ofReal (Real.rpow r θ) := by
  have herr : ∀ᶠ r in 𝓝[>] (0 : ℝ), θ - q < e r :=
    he.eventually (eventually_gt_nhds (sub_neg.mpr hθ))
  have hr1 : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < 1 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  have hr0 : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r := self_mem_nhdsWithin
  filter_upwards [ha, herr, hr1, hr0] with r ha' herr' hr1' hr0'
  calc
    a r ≤ C * ENNReal.ofReal (Real.rpow r (q + e r)) := ha'
    _ ≤ C * ENNReal.ofReal (Real.rpow r θ) := by
      gcongr
      exact Real.rpow_le_rpow_of_exponent_ge hr0' hr1'.le (by linarith)

/-- The exponentially spaced radii used in the puncture argument approach
zero from above. -/
theorem tendsto_exponential_radii (s : ℝ) :
    Tendsto (fun n : ℕ => Real.exp (-(s + (n : ℝ)))) atTop (𝓝[>] (0 : ℝ)) := by
  apply Real.tendsto_exp_atBot_nhdsGT.comp
  apply tendsto_neg_atTop_atBot.comp
  exact tendsto_atTop_add_const_left atTop s tendsto_natCast_atTop_atTop

/-- A small-radius power bound specializes to the exponentially spaced
radii in the puncture argument. -/
theorem eventually_exponential_scale_power_bound
    (a : ℝ → ℝ≥0∞) (s θ : ℝ) (C : ℝ≥0∞)
    (ha : ∀ᶠ r in 𝓝[>] (0 : ℝ), a r ≤ C * ENNReal.ofReal (Real.rpow r θ)) :
    ∀ᶠ (n : ℕ) in atTop, a (Real.exp (-(s + (n : ℝ)))) ≤
      C * ENNReal.ofReal (Real.exp (-θ * (s + (n : ℝ)))) := by
  have ht := (tendsto_exponential_radii s).eventually ha
  apply ht.mono
  intro n hn
  convert hn using 2
  congr 1
  change Real.exp (-θ * (s + (n : ℝ))) =
    (Real.exp (-(s + (n : ℝ))) : ℝ) ^ θ
  rw [← Real.exp_mul]
  congr 1
  ring

/-- An asymptotic exponent bound supplies the discrete scale hypothesis. -/
theorem eventually_exponential_scale_bound_of_exponent_error
    (a : ℝ → ℝ≥0∞) (s q θ : ℝ) (e : ℝ → ℝ) (C : ℝ≥0∞)
    (hθ : θ < q) (he : Tendsto e (𝓝[>] (0 : ℝ)) (𝓝 0))
    (ha : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      a r ≤ C * ENNReal.ofReal (Real.rpow r (q + e r))) :
    ∀ᶠ (n : ℕ) in atTop, a (Real.exp (-(s + (n : ℝ)))) ≤
      C * ENNReal.ofReal (Real.exp (-θ * (s + (n : ℝ)))) :=
  eventually_exponential_scale_power_bound a s θ C
    (eventually_power_bound_of_exponent_error a q θ e C hθ he ha)

#print axioms eventually_power_bound_of_exponent_error
#print axioms tendsto_exponential_radii
#print axioms eventually_exponential_scale_power_bound
#print axioms eventually_exponential_scale_bound_of_exponent_error

end HarmonicBalls
