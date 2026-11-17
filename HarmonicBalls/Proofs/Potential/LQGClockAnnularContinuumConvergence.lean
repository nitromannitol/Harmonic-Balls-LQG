import HarmonicBalls.Proofs.Potential.LQGClockAnnularGridOccupationIncrement
import LatticeProb.LQG.GMCRatioLimit

/-! # Annular clocks at continuum smoothing radii

A fine geometric grid controls the annular occupation clock at every positive
smoothing radius in each dyadic shell.
-/

open MeasureTheory Set MarkovProcess Filter LatticeProb.LQG
open LatticeProb.LQG.GMCScaleGrid LatticeProb.LQG.GMCRatioLimit
open scoped Topology NNReal ENNReal

namespace HarmonicBalls

/-- Every radius in a dyadic shell has a nearby grid radius whose annular clock
is relatively close, uniformly in the path and stopped time. -/
theorem ae_eventually_annular_exit_clock_grid_comparison
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (α γ : ℝ)
    {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c) (D : Set ℂ) :
    ∃ η : ℕ → ℝ, Tendsto η atTop (𝓝 0) ∧
      ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ∀ s : ℝ,
        dyadicScale k / 2 ≤ s → s ≤ dyadicScale k →
        ∃ i ≤ gridCount c k, ∀ (b : ContinuousPath ℂ) (t : ℝ≥0),
          let r := gridScale (gridCount c) k i
          let A : ℝ → ℝ := fun v => ∫ u in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D b).toReal,
            {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
              v ^ (γ ^ 2 / 2) * Real.exp (γ *
                LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) v z)) (b u.toNNReal)
          |A s - A r| ≤ η k * A r := by
  obtain ⟨β, hβ, hmod⟩ :=
    ae_eventually_annular_stopped_occupation_radial_difference_le hh α γ hδ
      (show 0 < c / 4 by positivity) D
  let B : ℕ → ℝ := fun k => |γ| * dyadicScale k ^ β + γ ^ 2 * dyadicScale k ^ (c / 4)
  have hpow (p : ℝ) (hp : 0 < p) : Tendsto (fun k => dyadicScale k ^ p) atTop (𝓝 0) := by
    have h0 : Tendsto dyadicScale atTop (𝓝 (0 : ℝ)) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa [Real.zero_rpow hp.ne'] using h0.rpow_const (Or.inr hp.le)
  have hB : Tendsto B atTop (𝓝 0) := by
    dsimp [B]
    simpa using ((hpow β hβ).const_mul |γ|).add
      ((hpow (c / 4) (by positivity)).const_mul (γ ^ 2))
  refine ⟨fun k => B k * Real.exp (B k), ?_, ?_⟩
  · simpa using hB.mul ((Real.continuous_exp.tendsto 0).comp hB)
  · filter_upwards [hmod] with ω hω
    filter_upwards [hω, eventually_ge_atTop 1] with k hk hk1 s hs1 hs2
    have he : 0 < dyadicScale k := dyadicScale_pos k
    have helt : dyadicScale k < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
    obtain ⟨hN, hmesh⟩ := one_le_gridCount_and_mesh_le hc.le k
    obtain ⟨i, hi, hnear⟩ := exists_gridScale_near (gridCount c) hN hs1 hs2
    obtain ⟨hr1, hr2⟩ := gridScale_mem_Icc (gridCount c) hi
    have hclose : |s - gridScale (gridCount c) k i| < dyadicScale k * dyadicScale k ^ (c / 4) :=
      (hnear.trans hmesh).trans_lt (mul_lt_mul_of_pos_left
        (Real.rpow_lt_rpow_of_exponent_gt he helt (by linarith)) he)
    refine ⟨i, hi, ?_⟩
    intro b t
    exact hk b t s _ hs1 hs2 hr1 hr2 hclose

end HarmonicBalls
