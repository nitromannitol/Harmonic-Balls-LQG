import HarmonicBalls.Proofs.Sec2.GraphDimensionComparableMeasures
import HarmonicBalls.Proofs.Sec6.LQGWeylScaling

/-!
# Graph dimension under bounded Weyl perturbations

We acknowledge Leonardo Bonanno's contributions to this formalization.
The global bounds apply to the entire plane, as required for unrestricted covers.
-/

namespace HarmonicBalls

open MeasureTheory Filter
open scoped ENNReal

/-- A globally bounded exponential density preserves graph dimension. -/
theorem isLiouvilleGraphDimension_iff_withDensity_exp
    (μ : Measure ℂ) (g : ℂ → ℝ) (a b : ℝ)
    (ha : ∀ z, a ≤ g z) (hb : ∀ z, g z ≤ b) (z w : ℂ) (d : ℝ) :
    IsLiouvilleGraphDimension
      (μ.withDensity fun z => ENNReal.ofReal (Real.exp (g z))) z w d ↔
      IsLiouvilleGraphDimension μ z w d := by
  apply isLiouvilleGraphDimension_iff_of_comparable (Real.exp_pos a) (Real.exp_pos b)
  · rw [← withDensity_const]
    apply withDensity_mono
    filter_upwards [] with x
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (ha x))
  · rw [← withDensity_const]
    apply withDensity_mono
    filter_upwards [] with x
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (hb x))

/-- On one full-measure event, every bounded continuous perturbation has the
Weyl-scaled LQG limit and preserves every graph-dimension exponent. -/
theorem ae_lqgLimit_addCircleAverage_graphDimension
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (hgff : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasure P γ (fun ω => fieldCircleAverage α (hcirc ω)) μ) :
    ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f →
      (∃ B : ℝ, ∀ z, |f z| ≤ B) →
      IsLQGLimit γ (addCircleAverage (fieldCircleAverage α (hcirc ω)) f)
        ((μ ω).withDensity fun z => ENNReal.ofReal (Real.exp (γ * f z))) ∧
      ∀ z w : ℂ, ∀ d : ℝ,
        (IsLiouvilleGraphDimension
          ((μ ω).withDensity fun z => ENNReal.ofReal (Real.exp (γ * f z))) z w d ↔
          IsLiouvilleGraphDimension (μ ω) z w d) := by
  have hc : ∀ᵐ ω ∂P, ∀ n, Continuous (fieldCircleAverage α (hcirc ω) (dyadicScale n)) :=
    ae_all_iff.mpr (fun n => hgff.ae_continuous_fieldCircleAverage α (dyadicScale_pos n))
  filter_upwards [hμ, hc] with ω hω hωc
  intro f hf ⟨B, hB⟩
  refine ⟨Section6.isLQGLimit_addCircleAverage hω hωc f hf, ?_⟩
  intro z w d
  apply isLiouvilleGraphDimension_iff_withDensity_exp (μ ω) (fun x => γ * f x)
    (- (|γ| * B)) (|γ| * B) _ _ z w d
  all_goals
    intro x
    have h := mul_le_mul_of_nonneg_left (hB x) (abs_nonneg γ)
    rw [← abs_mul] at h
    first | exact (abs_le.mp h).1 | exact (abs_le.mp h).2

#print axioms isLiouvilleGraphDimension_iff_withDensity_exp
#print axioms ae_lqgLimit_addCircleAverage_graphDimension

end HarmonicBalls
