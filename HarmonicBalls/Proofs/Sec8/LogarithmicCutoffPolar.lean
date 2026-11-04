import HarmonicBalls.Proofs.Sec8.LogarithmicCutoff
import HarmonicBalls.Proofs.Sec8.CircleDensityRadial
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Polar integral for logarithmic-capacity cutoffs

The imported Section 8 reduction uses Leonardo Bonanno's LatticeProb formalization. -/

open MeasureTheory Set Metric Filter Real
open scoped Topology Real
namespace HarmonicBalls

/-- The logarithmic capacity kernel has logarithmic mass on a planar annulus. -/
theorem integral_inverse_square_annulus {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ z : ℂ, (Ioc a b).indicator (fun r : ℝ => (r ^ 2)⁻¹) ‖z‖) =
      2 * Real.pi * Real.log (b / a) := by
  rw [show (∫ z : ℂ, (Ioc a b).indicator (fun r : ℝ => (r ^ 2)⁻¹) ‖z‖) =
      2 * Real.pi * ∫ r in Ioi (0 : ℝ), r * (Ioc a b).indicator (fun r : ℝ => (r ^ 2)⁻¹) r by
        simpa using integral_radial ((Ioc a b).indicator (fun r : ℝ => (r ^ 2)⁻¹)) 0]
  congr 1
  have heq : (fun r : ℝ => r * (Ioc a b).indicator (fun r : ℝ => (r ^ 2)⁻¹) r) =
      (Ioc a b).indicator (fun r : ℝ => r⁻¹) := by
    funext r
    by_cases hr : r ∈ Ioc a b
    · have hne : r ≠ 0 := ne_of_gt (ha.trans hr.1)
      simp only [indicator_of_mem hr]
      field_simp
    · simp [indicator_of_notMem hr]
  rw [heq, integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc]
  have hint : Ioc a b ∩ Ioi 0 = Ioc a b := by
    ext r
    simp only [mem_inter_iff, mem_Ioc, mem_Ioi]
    constructor
    · exact And.left
    · intro hr
      exact ⟨hr, ha.trans hr.1⟩
  rw [hint, ← intervalIntegral.integral_of_le hab, integral_inv_of_pos ha (ha.trans_le hab)]
/-- The inverse-square mass of the logarithmic transition annulus is linear in `t`. -/
theorem integral_inverse_square_logarithmic_annulus {t : ℝ} (ht : 0 < t) :
    (∫ z : ℂ, (Ioc (Real.exp (-2 * t)) (Real.exp (-t))).indicator
      (fun r : ℝ => (r ^ 2)⁻¹) ‖z‖) = 2 * Real.pi * t := by
  have hle : Real.exp (-2 * t) ≤ Real.exp (-t) := by
    apply Real.exp_le_exp.mpr
    linarith
  rw [integral_inverse_square_annulus (Real.exp_pos _) hle,
    Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt (Real.exp_pos _)),
    Real.log_exp, Real.log_exp]
  ring

end HarmonicBalls
