import HarmonicBalls.Proofs.Sec6.WholePlaneNonatomic
import HarmonicBalls.Proofs.Sec6.LQGLimitComparison

/-! # Non-atomicity for nonpositive logarithmic singularities -/

namespace HarmonicBalls.Section6

open MeasureTheory Filter Metric Set
open scoped Topology ENNReal

universe u

/-- For a nonpositive logarithmic singularity the singular LQG measure has
no atom at zero. The whole-plane mass bound and existence are the inputs. -/
theorem ae_singular_origin_nonatomic_of_nonpositive
    (hS : WholePlaneScaledBallMassStep.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ ≤ 0)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hE : LQGMeasureExistence P γ 0 hC hcirc)
    (μ : Ω → Measure ℂ) (hG : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, μ ω {0} = 0 := by
  have hQ : 0 < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨μ₀, hμ₀⟩ := hE hG hγ hγ2 hQ
  have hc : ∀ᵐ ω ∂P, ∀ k, Continuous (fieldCircleAverage 0 (hcirc ω) (dyadicScale k)) :=
    ae_all_iff.mpr (fun k => hG.ae_continuous_fieldCircleAverage 0 (dyadicScale_pos k))
  filter_upwards [hμ, hμ₀, hc,
    ae_wholePlane_nonatomic_of_scaledBallMass hS P γ hγ hγ2 hC hcirc μ₀ hG hμ₀]
    with ω hm hm₀ hc hno
  have hloc : ∀ L : Set ℂ, IsCompact L → L ⊆ ball (0 : ℂ) 1 →
      ∀ᶠ k : ℕ in atTop, ∀ z ∈ L,
        fieldCircleAverage α₀ (hcirc ω) (dyadicScale k) z ≤
          fieldCircleAverage 0 (hcirc ω) (dyadicScale k) z := by
    intro L _ hL
    filter_upwards [] with k z hz
    have hr : 0 < dyadicScale k := dyadicScale_pos k
    have hr1 : dyadicScale k ≤ 1 := by
      unfold dyadicScale
      exact pow_le_one₀ (by norm_num) (by norm_num)
    have hz1 : ‖z‖ ≤ 1 := by
      have hz' : ‖z‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hL hz
      exact hz'.le
    have hlog : Real.log (max (dyadicScale k) ‖z‖) ≤ 0 :=
      Real.log_nonpos (le_of_lt (lt_max_of_lt_left hr)) (max_le hr1 hz1)
    have hprod : 0 ≤ α₀ * Real.log (max (dyadicScale k) ‖z‖) := mul_nonneg_of_nonpos_of_nonpos hα hlog
    rw [fieldCircleAverage_eq _ _ hr, fieldCircleAverage_eq _ _ hr]
    simp only [zero_mul, sub_zero]
    linarith
  have hle := isLQGLimit_measure_compact_le hγ.le hm hm₀ hc
    (U := ball (0 : ℂ) 1) (K := {0}) isOpen_ball isCompact_singleton
    (by simp) hloc
  rw [hno 0] at hle
  exact le_zero_iff.mp hle

/-- Nonpositive logarithmic singularities preserve non-atomicity under the
whole-plane mass bound and the existence of the whole-plane LQG measure. -/
theorem ae_singular_nonatomic_of_nonpositive
    (hS : WholePlaneScaledBallMassStep.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ ≤ 0)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hE : LQGMeasureExistence P γ 0 hC hcirc)
    (μ : Ω → Measure ℂ) (hG : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ z : ℂ, μ ω {z} = 0 := by
  have hQ : 0 < lqgQ γ := by unfold lqgQ; positivity
  filter_upwards [ae_singular_origin_nonatomic_of_nonpositive hS P γ α₀ hγ hγ2 hα hC hcirc hE μ hG hμ,
    ae_singular_nonatomic_off_origin_of_scaledBallMass hS P γ α₀ hγ hγ2 (hα.trans_lt hQ)
      hC hcirc hE μ hG hμ] with ω h0 hoff z
  by_cases hz : z = 0
  · simpa [hz] using h0
  · exact hoff z hz

end HarmonicBalls.Section6
