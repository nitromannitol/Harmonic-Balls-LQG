import HarmonicBalls.Proofs.Potential.LQGClockAnnularAnnealedIncrement
import LatticeProb.LQG.LQGCircleDecoupling

/-! # Two-point estimates for Liouville clock densities

A Gaussian decoupling bound controls the two-point function of the circle-average
approximation with a logarithmic insertion.
-/

open MeasureTheory
open scoped ENNReal

namespace HarmonicBalls

/-- The two-point function of the normalized circle-average density is bounded by
an inverse power of the distance between distinct points in the unit disc. -/
theorem integral_gmcDensity_mul_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε : ℝ} (hε : 0 < ε)
    (γ : ℝ) {z w : ℂ} (hz : ‖z‖ + ε ≤ 1) (hw : ‖w‖ + ε ≤ 1) (hzw : z ≠ w) :
    (∫ ω, LatticeProb.Gauss.gmcDensity hcirc γ ε z ω *
      LatticeProb.Gauss.gmcDensity hcirc γ ε w ω ∂P) ≤
      (2 / ‖z - w‖) ^ (γ ^ 2) := by
  have hr : 0 < ‖z - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzw)
  have h := hh.integral_prod_gmcDensity_two_le hε hr γ
    (fun _ : Fin 1 => z) (fun _ : Fin 1 => w)
    (fun _ => hz) (fun _ => hw) (fun _ _ => le_rfl)
  simpa only [Finset.univ_unique, Fin.default_eq_zero, Finset.prod_singleton,
    Fintype.card_fin, Nat.cast_one, one_mul, mul_one,
    show (∫ ω, LatticeProb.Gauss.gmcDensity hcirc γ ε z ω ∂P) = 1 from
      hh.integral_rpow_mul_exp_circle hε hz γ,
    show (∫ ω, LatticeProb.Gauss.gmcDensity hcirc γ ε w ω ∂P) = 1 from
      hh.integral_rpow_mul_exp_circle hε hw γ] using h

/-- The two-point function of the actual logarithmically inserted density is bounded by
the product of the insertion weights and the Gaussian inverse-distance kernel. -/
theorem integral_inserted_clock_density_mul_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε : ℝ} (hε : 0 < ε)
    (γ α : ℝ) {z w : ℂ} (hz : ‖z‖ + ε ≤ 1) (hw : ‖w‖ + ε ≤ 1) (hzw : z ≠ w) :
    (∫ ω, (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) *
      (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε w)) ∂P) ≤
      (Real.exp (-(γ * α) * Real.log (max ε ‖z‖)) *
        Real.exp (-(γ * α) * Real.log (max ε ‖w‖))) *
        (2 / ‖z - w‖) ^ (γ ^ 2) := by
  let A := Real.exp (-(γ * α) * Real.log (max ε ‖z‖)) *
    Real.exp (-(γ * α) * Real.log (max ε ‖w‖))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have heq : (∫ ω, (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) *
      (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε w)) ∂P) =
      A * ∫ ω, LatticeProb.Gauss.gmcDensity hcirc γ ε z ω *
        LatticeProb.Gauss.gmcDensity hcirc γ ε w ω ∂P := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_recentered_inserted_circle_average hh α, hh.ae_circleAverage_one_zero] with ω hω hzero
    rw [← hω ε z hε, ← hω ε w hε, hzero]
    simp only [sub_zero]
    have hz' : γ * (hcirc ω ε z - α * Real.log (max ε ‖z‖)) =
        γ * hcirc ω ε z + (-(γ * α) * Real.log (max ε ‖z‖)) := by ring
    have hw' : γ * (hcirc ω ε w - α * Real.log (max ε ‖w‖)) =
        γ * hcirc ω ε w + (-(γ * α) * Real.log (max ε ‖w‖)) := by ring
    rw [hz', hw', Real.exp_add, Real.exp_add]
    dsimp [A, LatticeProb.Gauss.gmcDensity]
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left (integral_gmcDensity_mul_le hh hε γ hz hw hzw) hA

end HarmonicBalls
