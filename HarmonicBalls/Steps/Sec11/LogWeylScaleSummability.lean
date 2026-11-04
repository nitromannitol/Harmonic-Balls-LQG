import HarmonicBalls.Steps.Sec11.WeylAnnulusBounds
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Summability of logarithmic Weyl weights

A base-metric annulus bound with exponential decay beats the logarithmic Weyl
weight when its exponent is strictly larger than the singularity exponent.
-/

namespace HarmonicBalls

open scoped ENNReal

/-- Exponential base-metric decay is summable after multiplication by the
Weyl weight at exponentially small inner radii, under the strict exponent
inequality. -/
theorem logWeyl_weighted_exponential_tsum_ne_top
    {ξ α β κ : ℝ} (hgap : ξ * α < β) {C : ℝ≥0∞} (hC : C ≠ ∞) :
    (∑' n : ℕ, ENNReal.ofReal (Real.exp (ξ * (-α *
      Real.log (Real.exp (-((n : ℝ) + κ)))))) *
      (C * ENNReal.ofReal (Real.exp (-β * (n : ℝ))))) ≠ ∞ := by
  have hr : ENNReal.ofReal (Real.exp (ξ * α - β)) < 1 := by
    rw [← ENNReal.ofReal_one]
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Real.exp_pos _).le).2
    rw [Real.exp_lt_one_iff]
    linarith
  have heq (n : ℕ) :
      ENNReal.ofReal (Real.exp (ξ * (-α * Real.log (Real.exp (-((n : ℝ) + κ)))))) *
        (C * ENNReal.ofReal (Real.exp (-β * (n : ℝ)))) =
      (C * ENNReal.ofReal (Real.exp (ξ * α * κ))) *
        (ENNReal.ofReal (Real.exp (ξ * α - β))) ^ n := by
    have hre : Real.exp (ξ * (-α * Real.log (Real.exp (-((n : ℝ) + κ))))) *
        Real.exp (-β * (n : ℝ)) =
        Real.exp (ξ * α * κ) * Real.exp (ξ * α - β) ^ n := by
      rw [Real.log_exp, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    calc
      _ = C * ENNReal.ofReal (Real.exp (ξ * (-α *
            Real.log (Real.exp (-((n : ℝ) + κ))))) *
            Real.exp (-β * (n : ℝ))) := by
        rw [ENNReal.ofReal_mul (Real.exp_nonneg _)]
        ac_rfl
      _ = C * ENNReal.ofReal (Real.exp (ξ * α * κ) *
            Real.exp (ξ * α - β) ^ n) := by rw [hre]
      _ = _ := by
        rw [ENNReal.ofReal_mul (Real.exp_nonneg _), ENNReal.ofReal_pow (Real.exp_nonneg _)]
        ac_rfl
  simp_rw [heq]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  finiteness [(tsub_pos_iff_lt.2 hr).ne']

/-- A base-metric annulus estimate with exponent greater than `ξ * α`
gives point removal for the logarithmically Weyl-scaled metric. -/
theorem IsEuclideanLengthMetric.internalMetric_sdiff_zero_eq_of_log_scale_bounds
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) (hEnonneg : ∀ x y, 0 ≤ E x y)
    {ξ α β κ : ℝ} (hξ : 0 ≤ ξ) (hα : 0 ≤ α) (hgap : ξ * α < β)
    (V : Set ℂ)
    (hzero : ∀ x y, weylScaling D ξ 0 x y = ENNReal.ofReal (D x y))
    (hscale : ∀ x y, ENNReal.ofReal (E x y) =
      weylScaling D ξ (fun z => -α * Real.log ‖z‖) x y)
    {R q : ℝ} (hR : 0 < R) (hq : 0 < q) (hq1 : q < 1)
    (W : ℕ → Set ℂ) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hWopen : ∀ n, IsOpen (W n)) (hWsub : ∀ n, W n ⊆ V \ {0})
    (hinner : ∀ n z, z ∈ W n → Real.exp (-((n : ℝ) + κ)) ≤ ‖z‖)
    (hbase : ∀ n, ∀ x ∈ geometricShell R q n, ∀ y ∈ geometricShell R q n,
      internalMetric D (W n) x y ≤ C * ENNReal.ofReal (Real.exp (-β * (n : ℝ))))
    {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    internalMetric E (V \ {0}) x y = internalMetric E V x y := by
  apply hD.internalMetric_sdiff_zero_eq_of_log_corridors hE hEnonneg hξ hα V hzero
    hscale hR hq hq1 W (fun n => Real.exp (-((n : ℝ) + κ)))
    (fun n => C * ENNReal.ofReal (Real.exp (-β * (n : ℝ))))
    hWopen hWsub (fun _ => Real.exp_pos _) hinner hbase ?_ hx hy
  exact logWeyl_weighted_exponential_tsum_ne_top hgap hC

#print axioms logWeyl_weighted_exponential_tsum_ne_top
#print axioms IsEuclideanLengthMetric.internalMetric_sdiff_zero_eq_of_log_scale_bounds

end HarmonicBalls
