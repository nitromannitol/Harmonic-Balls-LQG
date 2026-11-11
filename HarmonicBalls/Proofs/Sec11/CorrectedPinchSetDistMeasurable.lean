import HarmonicBalls.Steps.Sec11.PinchLocalSetDist
import HarmonicBalls.Steps.Sec11.InternalMetricMeasurable
import HarmonicBalls.Steps.Sec11.ProperMetricDyadic

/-! Measurability of set-to-set distances for random length metrics. -/

namespace HarmonicBalls

open Set MeasureTheory
open scoped ENNReal

/-- For nonempty fixed sets, the extended set distance is measurable for a
pointwise measurable family of Euclidean length metrics. -/
theorem measurable_ofReal_setDist_of_lengthMetric
    {Ω : Type*} [MeasurableSpace Ω] {D : Ω → ℂ → ℂ → ℝ}
    {A B : Set ℂ} (hA : A.Nonempty) (hB : B.Nonempty)
    (hD : ∀ x y, Measurable fun ω => D ω x y)
    (hmetric : ∀ ω, IsEuclideanLengthMetric (D ω)) :
    Measurable fun ω => ENNReal.ofReal (setDist (D ω) A B) := by
  let f : A × B → Ω → ℝ≥0∞ := fun p ω => ENNReal.ofReal (D ω p.1 p.2)
  have hf (ω : Ω) : Continuous (fun p : A × B => f p ω) := by
    have hp : Continuous (fun p : A × B => ((p.1 : ℂ), (p.2 : ℂ))) :=
      (continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)
    exact ENNReal.continuous_ofReal.comp ((hmetric ω).continuous_pair.comp hp)
  have hm : Measurable (⨅ p : A × B, f p) :=
    measurable_iInf_of_upperSemicontinuous (fun p => (hD p.1 p.2).ennreal_ofReal)
      (fun ω => (hf ω).upperSemicontinuous)
  convert hm using 1
  ext ω
  rw [ofReal_setDist_eq_iInf hA hB]
  simp only [iInf_apply, f, iInf_subtype, iInf_prod]


end HarmonicBalls
