import HarmonicBalls.Proofs.Potential.LQGClockAnnularAnnealedIncrement
import LatticeProb.Analysis.MonotoneGridApprox

/-! # Expected uniform increments of monotone clocks

A grid estimate reduces a uniform clock increment to pointwise increments and a
mesh oscillation of one clock.
-/

namespace HarmonicBalls

open MeasureTheory Set
open scoped ENNReal BigOperators

/-- The expected uniform difference of two monotone clocks is bounded by the sum of
expected grid-point differences and the expected mesh oscillation of one clock. -/
theorem lintegral_iSup_abs_sub_le_grid {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f g : Ω → ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) {m : ℕ} (hm : 0 < m)
    (hf : ∀ ω, MonotoneOn (f ω) (Icc 0 T))
    (hg : ∀ ω, MonotoneOn (g ω) (Icc 0 T))
    (hgrid : ∀ j : ℕ, Measurable (fun ω => |f ω (j * T / m) - g ω (j * T / m)|))
    (K : Ω → ℝ) (hK0 : ∀ ω, 0 ≤ K ω)
    (hK : ∀ ω j, j < m → g ω ((j + 1) * T / m) - g ω (j * T / m) ≤ K ω) :
    (∫⁻ ω, ⨆ t : Icc (0 : ℝ) T, ENNReal.ofReal |f ω t - g ω t| ∂μ) ≤
      (∑ j ∈ Finset.range (m + 1), ∫⁻ ω, ENNReal.ofReal |f ω (j * T / m) - g ω (j * T / m)| ∂μ) +
        ∫⁻ ω, ENNReal.ofReal (K ω) ∂μ := by
  let D : Ω → ℝ := fun ω => ∑ j ∈ Finset.range (m + 1),
    |f ω (j * T / m) - g ω (j * T / m)|
  have hDm : Measurable D := by
    exact Finset.measurable_sum _ (fun j _ => hgrid j)
  have hD0 (ω : Ω) : 0 ≤ D ω := by
    exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hpoint (ω : Ω) :
      (⨆ t : Icc (0 : ℝ) T, ENNReal.ofReal |f ω t - g ω t|) ≤
        ENNReal.ofReal (D ω) + ENNReal.ofReal (K ω) := by
    apply iSup_le
    intro t
    rw [← ENNReal.ofReal_add (hD0 ω) (hK0 ω)]
    apply ENNReal.ofReal_le_ofReal
    apply LatticeProb.abs_sub_le_of_grid hm hT (hf ω) (hg ω) ?_ (hK ω) t t.property
    intro j hj
    change |f ω (j * T / m) - g ω (j * T / m)| ≤
      ∑ i ∈ Finset.range (m + 1), |f ω (i * T / m) - g ω (i * T / m)|
    exact Finset.single_le_sum (s := Finset.range (m + 1)) (a := j)
      (f := fun i : ℕ => |f ω (i * T / m) - g ω (i * T / m)|)
      (fun i _ => abs_nonneg (f ω (i * T / m) - g ω (i * T / m)))
      (show j ∈ Finset.range (m + 1) from Finset.mem_range.mpr (by omega))
  calc
    _ ≤ ∫⁻ ω, (ENNReal.ofReal (D ω) + ENNReal.ofReal (K ω)) ∂μ :=
      lintegral_mono hpoint
    _ = (∫⁻ ω, ENNReal.ofReal (D ω) ∂μ) + ∫⁻ ω, ENNReal.ofReal (K ω) ∂μ :=
      lintegral_add_left (ENNReal.measurable_ofReal.comp hDm) _
    _ = _ := by
      congr 1
      simp only [D, ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _)]
      exact lintegral_finsetSum (Finset.range (m + 1))
        (f := fun j ω => ENNReal.ofReal |f ω (j * T / m) - g ω (j * T / m)|)
        (fun j _ => ENNReal.measurable_ofReal.comp (hgrid j))

end HarmonicBalls
