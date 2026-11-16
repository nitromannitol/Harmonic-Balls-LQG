import HarmonicBalls.Proofs.Potential.LQGClockAnnularAnnealedIncrement
import LatticeProb.Analysis.MonotoneGridApprox
import LatticeProb.LQG.LQGMassAlgebra

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

/-- The expected maximum of finitely many nonnegative variables is controlled by
 their summed moments of any order at least one. -/
theorem lintegral_iSup_le_rpow_sum_lintegral_rpow {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m : ℕ} (X : Fin m → Ω → ℝ≥0∞)
    (hX : ∀ j, Measurable (X j)) {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ ω, ⨆ j, X j ω ∂μ) ≤
      (∑ j, ∫⁻ ω, X j ω ^ p ∂μ) ^ (1 / p) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hq0 : 0 < 1 / p := one_div_pos.mpr hp0
  have hq1 : 1 / p ≤ 1 := (div_le_one hp0).2 hp
  let Y : Ω → ℝ≥0∞ := fun ω => (⨆ j, X j ω) ^ p
  have hYm : Measurable Y := (Measurable.iSup hX).pow_const p
  have hpoint (ω : Ω) : Y ω ≤ ∑ j, X j ω ^ p := by
    dsimp [Y]
    rw [(ENNReal.monotone_rpow_of_nonneg hp0.le).map_iSup_of_continuousAt
      (ENNReal.continuous_rpow_const (y := p)).continuousAt (by simp [hp0])]
    exact iSup_le fun j => Finset.single_le_sum (s := Finset.univ)
      (f := fun i : Fin m => X i ω ^ p) (fun _ _ => zero_le) (Finset.mem_univ j)
  calc
    _ = ∫⁻ ω, Y ω ^ (1 / p) ∂μ := by
      congr 1
      funext ω
      dsimp [Y]
      rw [← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one]
    _ ≤ (∫⁻ ω, Y ω ∂μ) ^ (1 / p) :=
      LatticeProb.lintegral_rpow_le_rpow_lintegral μ hq0 hq1 hYm.aemeasurable
    _ ≤ (∫⁻ ω, ∑ j, X j ω ^ p ∂μ) ^ (1 / p) :=
      ENNReal.rpow_le_rpow (lintegral_mono hpoint) hq0.le
    _ = _ := by
      congr 1
      exact lintegral_finsetSum _ (fun j _ => (hX j).pow_const p)

end HarmonicBalls
