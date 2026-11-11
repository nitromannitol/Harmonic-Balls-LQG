import HarmonicBalls.FirstPass.S11p.GreenMeasurable
import HarmonicBalls.FirstPass.S11q

/-!
# A.s. finiteness of the annular Green potential under a bounded density

Route (ii) for `hFin` in `FirstPass/S11p.lean`: the singular LQG measure of exponent `α₀` is the
base measure `μ₀` (exponent `0`) reweighted by `z ↦ |z|^{-γα₀}` (`singular_measure_identity`, `FirstPass/S11q.lean`).
On the annulus `𝔸_{3,6}` this weight is bounded, so `SG_{3,6}(μ) ≤ K · SG_{3,6}(μ₀)`. The finiteness of the base
potential `SG_{3,6}(μ₀)` is a NAMED HYPOTHESIS `hBase` here (it is the Green-potential clause of HB Proposition 2.5,
`GreenPotentialLiouvilleHolderStmt`, not yet bridged to `annulusGreenPotentialSup`).
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric
open scoped ENNReal

/-- Reweighting by a measurable density bounded by `K` on the annulus multiplies the annular Green potential
supremum by at most `K`. -/
theorem annulusGreenPotentialSup_withDensity_le (μ₀ : Measure ℂ) (g : ℂ → ℝ≥0∞) (hg : Measurable g)
    (x₀ : ℂ) (a b : ℝ) (K : ℝ≥0∞) (hK : ∀ y ∈ annulus x₀ a b, g y ≤ K) :
    annulusGreenPotentialSup (μ₀.withDensity g) x₀ a b ≤ K * annulusGreenPotentialSup μ₀ x₀ a b := by
  have hA : MeasurableSet (annulus x₀ a b) := (isOpen_annulus x₀ a b).measurableSet
  unfold annulusGreenPotentialSup
  simp only [ENNReal.mul_iSup]
  refine iSup₂_le fun x hx => ?_
  refine le_trans ?_ (le_iSup₂_of_le x hx le_rfl)
  have hxB : x ∈ ball x₀ b := hx.1
  have hkey : ∀ y ∈ annulus x₀ a b,
      (if y = x then ∞ else ENNReal.ofReal (greenFunction (ball x₀ b) x y)) =
        annulusKernelExt x₀ b (x, y) := by
    intro y hy
    rw [annulusKernelExt, indicator_of_mem (mk_mem_prod hxB hy.1)]
    rfl
  have hmeas : Measurable (fun y => annulusKernelExt x₀ b (x, y)) :=
    (lowerSemicontinuous_annulusKernel_section x₀ b x).measurable
  rw [setLIntegral_congr_fun hA hkey, setLIntegral_congr_fun hA hkey, restrict_withDensity hA,
    lintegral_withDensity_eq_lintegral_mul _ hg hmeas, ← lintegral_const_mul _ hmeas]
  refine lintegral_mono_ae ((ae_restrict_mem hA).mono fun y hy => ?_)
  simp only [Pi.mul_apply]
  gcongr
  exact hK y hy

/-- The singular weight `z ↦ |z|^{-γα₀}` is measurable (as an `ℝ≥0∞`-valued function). -/
theorem measurable_ofReal_LQGSingularWeight (γ α₀ : ℝ) :
    Measurable (fun z : ℂ => ENNReal.ofReal (LQGSingularWeight γ α₀ z)) := by
  unfold LQGSingularWeight
  exact (Real.measurable_exp.comp (measurable_const.mul (Real.measurable_log.comp measurable_norm))).ennreal_ofReal

/-- On the annulus `𝔸_{3,6}` the singular weight is at most `exp(|γα₀| log 6)`. -/
theorem ofReal_LQGSingularWeight_le_on_annulus (γ α₀ : ℝ) (y : ℂ) (hy : y ∈ annulus (0 : ℂ) 3 6) :
    ENNReal.ofReal (LQGSingularWeight γ α₀ y) ≤ ENNReal.ofReal (Real.exp (|γ * α₀| * Real.log 6)) := by
  have h6 : ‖y‖ < 6 := by simpa [mem_ball, dist_zero_right] using hy.1
  have h3 : 3 < ‖y‖ := by simpa [mem_closedBall, dist_zero_right, not_le] using hy.2
  have hL0 : 0 ≤ Real.log ‖y‖ := Real.log_nonneg (by linarith)
  have hL6 : Real.log ‖y‖ ≤ Real.log 6 := Real.log_le_log (by linarith) h6.le
  have hexp : -(γ * α₀) * Real.log ‖y‖ ≤ |γ * α₀| * Real.log 6 := by
    calc -(γ * α₀) * Real.log ‖y‖ ≤ |-(γ * α₀)| * Real.log ‖y‖ :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hL0
      _ = |γ * α₀| * Real.log ‖y‖ := by rw [abs_neg]
      _ ≤ |γ * α₀| * Real.log 6 := mul_le_mul_of_nonneg_left hL6 (abs_nonneg _)
  unfold LQGSingularWeight
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 hexp)

/-- Almost sure finiteness of the annular Green potential of the singular LQG measure `μ`, from the finiteness of the
base potential of `μ₀` (named hypothesis `hBase`, the Green clause of HB Prop. 2.5) and the singular identity
`μ = μ₀ · |z|^{-γα₀}` (named hypothesis `hSing`, `singular_measure_identity`). -/
theorem ae_annulusGreenPotentialSup_ne_top_of_withDensity {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (γ α₀ : ℝ) (μ₀ μ : Ω → Measure ℂ)
    (hBase : ∀ᵐ ω ∂P, annulusGreenPotentialSup (μ₀ ω) 0 3 6 ≠ ⊤)
    (hSing : ∀ᵐ ω ∂P, μ ω = (μ₀ ω).withDensity (fun z => ENNReal.ofReal (LQGSingularWeight γ α₀ z))) :
    ∀ᵐ ω ∂P, annulusGreenPotentialSup (μ ω) 0 3 6 ≠ ⊤ := by
  filter_upwards [hBase, hSing] with ω h1 h2
  rw [h2]
  refine ne_top_of_le_ne_top ?_ (annulusGreenPotentialSup_withDensity_le (μ₀ ω)
    (fun z => ENNReal.ofReal (LQGSingularWeight γ α₀ z)) (measurable_ofReal_LQGSingularWeight γ α₀)
    0 3 6 (ENNReal.ofReal (Real.exp (|γ * α₀| * Real.log 6)))
    (fun y hy => ofReal_LQGSingularWeight_le_on_annulus γ α₀ y hy))
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top h1

end HarmonicBalls

#print axioms HarmonicBalls.ae_annulusGreenPotentialSup_ne_top_of_withDensity
