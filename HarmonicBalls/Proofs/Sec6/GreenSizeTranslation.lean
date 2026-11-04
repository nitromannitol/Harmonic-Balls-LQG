import HarmonicBalls.Proofs.Sec6.GreenTranslation
import HarmonicBalls.Proofs.Sec8.GreenPotentialScaling

/-! # Translation of annular Green-potential sizes -/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set
open scoped ENNReal

/-- Translation transports the annular Green potential at a fixed pole. -/
theorem annulusGreenPotential_map_sub (μ : Measure ℂ) (a b : ℝ) (x z : ℂ) :
    (∫⁻ y in annulus (0 : ℂ) a b,
      (if y = x then ∞ else ENNReal.ofReal (greenFunction (ball 0 b) x y))
        ∂(μ.map (fun w : ℂ => w - z))) =
    ∫⁻ y in annulus z a b,
      (if y = x + z then ∞ else ENNReal.ofReal (greenFunction (ball z b) (x + z) y)) ∂μ := by
  have hg : Measurable (fun w : ℂ => w - z) := by fun_prop
  have hf : Measurable (fun y : ℂ => if y = x then (∞ : ℝ≥0∞)
      else ENNReal.ofReal (greenFunction (ball 0 b) x y)) :=
    Measurable.ite (measurableSet_singleton x) measurable_const
      ((measurable_greenFunction isOpen_ball x).ennreal_ofReal)
  have hs : MeasurableSet (annulus (0 : ℂ) a b) :=
    (isOpen_ball.sdiff isClosed_closedBall).measurableSet
  rw [setLIntegral_map hs hf hg]
  have hp : (fun w : ℂ => w - z) ⁻¹' annulus (0 : ℂ) a b = annulus z a b := by
    ext w
    simp [annulus, mem_ball, mem_closedBall, dist_eq_norm]
  rw [hp]
  have himage : (fun w : ℂ => w + z) '' ball (0 : ℂ) b = ball z b := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      simpa [mem_ball, dist_eq_norm] using hv
    · intro hw
      refine ⟨w - z, ?_, by simp⟩
      simpa [mem_ball, dist_eq_norm] using hw
  apply lintegral_congr
  intro y
  have heq : y - z = x ↔ y = x + z := by constructor <;> intro h <;> linear_combination h
  by_cases h : y = x + z
  · simp [h]
  · simp only [h, heq.not.mpr h, ite_false]
    apply congrArg ENNReal.ofReal
    have ht := (greenFunction_translate (ball 0 b) z x (y - z)).symm
    simpa only [himage, sub_add_cancel] using ht

/-- Translation transports the annular Green-potential supremum. -/
theorem annulusGreenPotentialSup_map_sub (μ : Measure ℂ) (a b : ℝ) (z : ℂ) :
    annulusGreenPotentialSup (μ.map (fun w : ℂ => w - z)) 0 a b =
      annulusGreenPotentialSup μ z a b := by
  have hmem (x : ℂ) : x ∈ annulus (0 : ℂ) a b ↔ x + z ∈ annulus z a b := by
    simp [annulus, mem_ball, mem_closedBall, dist_eq_norm]
  unfold annulusGreenPotentialSup
  apply le_antisymm
  · refine iSup_le fun x => iSup_le fun hx => ?_
    rw [annulusGreenPotential_map_sub μ a b x z]
    exact le_iSup_of_le (x + z) (le_iSup_of_le ((hmem x).mp hx) le_rfl)
  · refine iSup_le fun x => iSup_le fun hx => ?_
    have hx' : x - z ∈ annulus (0 : ℂ) a b := by
      apply (hmem (x - z)).2
      simpa using hx
    have hi : (∫⁻ y in annulus (0 : ℂ) a b,
        (if y = x - z then ∞ else ENNReal.ofReal (greenFunction (ball 0 b) (x - z) y))
          ∂(μ.map (fun w : ℂ => w - z))) ≤
      ⨆ w ∈ annulus (0 : ℂ) a b, ∫⁻ y in annulus (0 : ℂ) a b,
        (if y = w then ∞ else ENNReal.ofReal (greenFunction (ball 0 b) w y))
          ∂(μ.map (fun w : ℂ => w - z)) :=
      le_iSup_of_le (x - z) (le_iSup_of_le hx' le_rfl)
    rw [annulusGreenPotential_map_sub μ a b (x - z) z] at hi
    simpa only [sub_add_cancel] using hi

end HarmonicBalls.Section6
