import HarmonicBalls.Proofs.GFF.LQGMeasureContinuumConvergence

/-!
# Quantitative mass bounds for singular approximations

Continuum maximal estimates give a geometric bound for masses near the insertion.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open LatticeProb.LQG LatticeProb.Gauss

namespace HarmonicBalls

/-- Subexponential growth of the continuum maximal masses gives geometric decay of
singular approximation masses in dyadic balls around the insertion. -/
theorem eventually_lqgApprox_fieldCircleAverage_ball_le_geometric {γ α : ℝ} (hγ : 0 < γ)
    (hαQ : α < lqgQ γ) {h : ℝ → ℂ → ℝ} (hZ : ContinuumOriginGrowth γ h) :
    ∀ᶠ J : ℕ in atTop, ∀ s : ℝ, 0 < s → s < dyadicScale J →
      lqgApprox γ (fieldCircleAverage α h) s (ball 0 (dyadicScale J)) ≤
        ENNReal.ofReal (Real.exp (γ * (|α| * Real.log 2)) *
          (Real.exp (-(γ * (lqgQ γ - α) * Real.log 2 / 2)) ^ J /
            (1 - Real.exp (-(γ * (lqgQ γ - α) * Real.log 2 / 2))))) := by
  have hσ : 0 < γ * (lqgQ γ - α) := mul_pos hγ (sub_pos.2 hαQ)
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set σ := γ * (lqgQ γ - α)
  set c := Real.exp (γ * (|α| * Real.log 2))
  set r := Real.exp (-(σ * Real.log 2 / 2))
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    have : 0 < σ * Real.log 2 / 2 := by positivity
    calc r < Real.exp 0 := Real.exp_lt_exp.2 (by linarith)
      _ = 1 := Real.exp_zero
  obtain ⟨J₀, hJ₀⟩ := eventually_atTop.1 (hZ (σ * Real.log 2 / 2) (by positivity))
  filter_upwards [eventually_ge_atTop J₀] with J hJ
  intro s hs hsJ
  have hJ1 : dyadicScale J ≤ 1 := dyadicScale_le_one' J
  obtain ⟨k, hk₁, hk₂⟩ := exists_dyadicScale_bracket hs (hsJ.trans_le hJ1)
  have hJk : J ≤ k := by
    by_contra h
    have hle : k + 1 ≤ J := by omega
    have hmono := dyadicScale_le_of_le hle
    linarith
  refine (lqgApprox_fieldCircleAverage_ball_le_continuum_sum hγ α h hJk
    (by simpa only [dyadicScale_succ_eq_half] using hk₁) hk₂.le).trans ?_
  have hterm : ∀ j ∈ Finset.Ico J (k + 1),
      ENNReal.ofReal (dyadicScale j ^ σ * Real.exp (γ * h (dyadicScale j) 0)) *
          (⨆ u ∈ Ioc (0 : ℝ) 1, lqgApprox γ (dilateRecentre (dyadicScale j) h) u (ball 0 1)) ≤
        ENNReal.ofReal (r ^ j) := by
    intro j hj
    have hjJ : J₀ ≤ j := hJ.trans (Finset.mem_Ico.1 hj).1
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (dyadicScale_pos_bracket j).le _), mul_assoc]
    calc ENNReal.ofReal (dyadicScale j ^ σ) *
          (ENNReal.ofReal (Real.exp (γ * h (dyadicScale j) 0)) *
            ⨆ u ∈ Ioc (0 : ℝ) 1, lqgApprox γ (dilateRecentre (dyadicScale j) h) u (ball 0 1))
        ≤ ENNReal.ofReal (dyadicScale j ^ σ) * ENNReal.ofReal (Real.exp (σ * Real.log 2 / 2 * j)) := by
          gcongr
          exact hJ₀ j hjJ
      _ = ENNReal.ofReal (r ^ j) := by
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (dyadicScale_pos_bracket j).le _),
            ← Real.exp_nat_mul, Real.rpow_def_of_pos (dyadicScale_pos_bracket j), ← Real.exp_add]
          congr 2
          simp only [dyadicScale, Real.log_pow, Real.log_inv]
          ring
  calc ENNReal.ofReal c * ∑ j ∈ Finset.Ico J (k + 1),
          ENNReal.ofReal (dyadicScale j ^ σ * Real.exp (γ * h (dyadicScale j) 0)) *
            ⨆ u ∈ Ioc (0 : ℝ) 1, lqgApprox γ (dilateRecentre (dyadicScale j) h) u (ball 0 1)
      ≤ ENNReal.ofReal c * ∑ j ∈ Finset.Ico J (k + 1), ENNReal.ofReal (r ^ j) := by
        gcongr with j hj
        exact hterm j hj
    _ = ENNReal.ofReal (c * ∑ j ∈ Finset.Ico J (k + 1), r ^ j) := by
        rw [ENNReal.ofReal_mul (Real.exp_pos _).le,
          ENNReal.ofReal_sum_of_nonneg (fun j _ => pow_nonneg hr0 j)]
    _ ≤ ENNReal.ofReal (c * (r ^ J / (1 - r))) := ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hr0 hr1) (Real.exp_pos _).le)

/-- The geometric singular mass bound holds almost surely for a whole-plane GFF. -/
theorem ae_eventually_lqgApprox_fieldCircleAverage_ball_le_geometric
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    {γ α : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ) :
    ∀ᵐ ω ∂P, ∀ᶠ J : ℕ in atTop, ∀ s : ℝ, 0 < s → s < dyadicScale J →
      lqgApprox γ (fieldCircleAverage α (hcirc ω)) s (ball 0 (dyadicScale J)) ≤
        ENNReal.ofReal (Real.exp (γ * (|α| * Real.log 2)) *
          (Real.exp (-(γ * (lqgQ γ - α) * Real.log 2 / 2)) ^ J /
            (1 - Real.exp (-(γ * (lqgQ γ - α) * Real.log 2 / 2))))) := by
  filter_upwards [hh.ae_continuumOriginGrowth hγ0 hγ2] with ω hω
  exact eventually_lqgApprox_fieldCircleAverage_ball_le_geometric hγ0 hαQ hω

end HarmonicBalls
