import HarmonicBalls.Proofs.Sec6.BrownianScaling
import HarmonicBalls.Proofs.Brownian.PlanarHeatSemigroup
import HarmonicBalls.Defs.Brownian

/-! # Planar Brownian increments

The increments of planar Brownian motion have centered planar Gaussian laws.
-/

open MeasureTheory ProbabilityTheory MarkovProcess
open scoped NNReal

namespace HarmonicBalls

/-- Each planar Brownian increment has the centered Gaussian law with variance equal to
the time difference. -/
theorem planarBrownianMotion_map_increment (x : ℂ) (s t : ℝ≥0) :
    (planarBrownianMotion x).map (fun b => b t - b s) =
      planarGaussian 0 (nndist (t : ℝ) (s : ℝ)) := by
  let f : ContinuousPath ℝ → ℝ := fun b => b t - b s
  have hf : Measurable f := (ContinuousPath.measurable_coordinateProcess _).sub
    (ContinuousPath.measurable_coordinateProcess _)
  have hlaw (a : ℝ) : (brownianMotion a).map f = gaussianReal 0 (nndist (t : ℝ) (s : ℝ)) := by
    have h := (HarmonicBalls.Section6.isPreBrownianReal_brownianMotion a).hasLaw_sub t s
    change HasLaw (fun b : ContinuousPath ℝ => (b t - a) - (b s - a)) _ _ at h
    simpa [f, sub_sub_sub_cancel_right] using h.map_eq
  have hF : Measurable (fun b : ContinuousPath ℂ => b t - b s) :=
    (ContinuousPath.measurable_coordinateProcess _).sub (ContinuousPath.measurable_coordinateProcess _)
  have hp : ((brownianMotion x.re).prod (brownianMotion x.im)).map (Prod.map f f) =
      (gaussianReal 0 (nndist (t : ℝ) (s : ℝ))).prod
        (gaussianReal 0 (nndist (t : ℝ) (s : ℝ))) := by
    rw [← Measure.map_prod_map _ _ hf hf, hlaw x.re, hlaw x.im]
  have hff : Measurable (Prod.map f f) := (hf.comp measurable_fst).prodMk (hf.comp measurable_snd)
  rw [planarBrownianMotion_apply, Measure.map_map hF measurable_complexPathOfReIm,
    planarGaussian, Complex.zero_re, Complex.zero_im, ← hp,
    Measure.map_map Complex.measurableEquivRealProd.symm.measurable hff]
  congr 1
  funext p
  simp only [Function.comp_apply, complexPathOfReIm_apply, f]
  apply Complex.ext <;> simp [Complex.measurableEquivRealProd]

end HarmonicBalls
