import HarmonicBalls.Proofs.Potential.LQGClockNonpositiveMeasurableLimit
import HarmonicBalls.Proofs.Potential.LQGClockNonpositiveInsertedAnnealedTail

/-! # Nonpositive half-disc clock integrability

Brownian occupation energy bounds for nonpositive inserted clocks.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set
open scoped NNReal ENNReal

namespace HarmonicBalls

/-- The geometric occupation-energy envelope has a summable mean independent
of the Brownian starting point. -/
theorem exists_uniform_summable_inner_energy_bound {γ d u v : ℝ}
    (hd0 : 0 < d) (hd2 : d < 2) (hu : 0 < u) (hv : 0 < v) :
    ∃ A : ℕ → ℝ, Summable A ∧ ∀ x : ℂ, ∀ n : ℕ,
      Integrable (fun b => ((Real.exp (γ^2 * Real.log 2) - 1) *
        (unitOccupationRieszEnergy d b * 2^d) + 1) / 2 *
        Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1)) * u) +
        2 * Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1)) * v))
        (planarBrownianMotion x) ∧
      (∫ b, ((Real.exp (γ^2 * Real.log 2) - 1) *
        (unitOccupationRieszEnergy d b * 2^d) + 1) / 2 *
        Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1)) * u) +
        2 * Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1)) * v)
        ∂(planarBrownianMotion x)) = A n := by
  let B : ContinuousPath ℂ → ℝ := fun b =>
    ((Real.exp (γ^2 * Real.log 2) - 1) * (unitOccupationRieszEnergy d b * 2^d) + 1) / 2
  have hB (x : ℂ) : Integrable B (planarBrownianMotion x) := by
    have hE := integrable_unitOccupationRieszEnergy x hd0 hd2
    dsimp [B]
    fun_prop
  let c : ℝ := ∫ b, B b ∂(planarBrownianMotion 0)
  let A : ℕ → ℝ := fun n => c * Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1)) * u) +
    2 * Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1)) * v)
  have hA : Summable A := by
    have h1 := LatticeProb.Gauss.summable_exp_log_dyadicScale_mul hu
    have h2 := LatticeProb.Gauss.summable_exp_log_dyadicScale_mul hv
    exact (summable_nat_add_iff 1).2 ((h1.mul_left c).add (h2.mul_left 2))
  refine ⟨A, hA, ?_⟩
  intro x n
  have hBc : (∫ b, B b ∂(planarBrownianMotion x)) = c := by
    dsimp [B, c]
    rw [integral_div, integral_div]
    congr 1
    rw [integral_add ((integrable_unitOccupationRieszEnergy x hd0 hd2).mul_const _ |>.const_mul _)
      (integrable_const _),
      integral_add ((integrable_unitOccupationRieszEnergy 0 hd0 hd2).mul_const _ |>.const_mul _)
      (integrable_const _)]
    simp only [integral_const_mul, integral_mul_const, integral_const, smul_eq_mul,
      Measure.real, measure_univ, ENNReal.toReal_one, one_mul]
    rw [integral_unitOccupationRieszEnergy_eq x 0 hd0 hd2]
  refine ⟨?_, ?_⟩
  · change Integrable (fun b => B b * _ + _) _
    fun_prop
  · change (∫ b, B b * _ + _ ∂planarBrownianMotion x) = A n
    rw [integral_add ((hB x).mul_const _) (integrable_const _), integral_mul_const, hBc]
    simp [A]
end HarmonicBalls
