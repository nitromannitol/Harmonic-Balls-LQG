import HarmonicBalls.Defs.Brownian
import HarmonicBalls.Proofs.Sec6.ExitTimeSpatialMap
import MarkovProcess.Examples.BrownianMotion
import MarkovProcess.Path.MeasureIdentification
import MarkovProcess.FiniteTime.MeasureFiniteRestrictionIdentification
import Mathlib.Probability.BrownianMotion.Basic

/-! # Brownian scaling

The centered canonical Brownian motion from MarkovProcess satisfies Mathlib's
finite-dimensional characterization, so Mathlib's scaling theorem applies.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory MarkovProcess

/-- Finite-dimensional distributions determine finite measures on real
continuous-path space. -/
theorem real_path_measure_eq_of_finite_dimensional_laws
    (μ ν : Measure (ContinuousPath ℝ)) [IsFiniteMeasure μ]
    (h : ∀ I : Finset NNReal,
      μ.map (fun ω : ContinuousPath ℝ => I.restrict (fun t => ω t)) =
        ν.map (fun ω : ContinuousPath ℝ => I.restrict (fun t => ω t))) : μ = ν := by
  let eval : ContinuousPath ℝ → NNReal → ℝ := fun ω t => ω t
  have heval : Measurable eval := Measurable.of_eval fun t =>
    ContinuousPath.measurable_coordinateProcess t
  have hfull : μ.map eval = ν.map eval := by
    apply MarkovProcess.Measure.eq_of_map_finiteRestriction_eq
    intro I
    have hI : Measurable (I.restrict : (NNReal → ℝ) → I → ℝ) :=
      Measurable.of_eval fun _ => measurable_pi_apply _
    rw [Measure.map_map hI heval, Measure.map_map hI heval]
    exact h I
  let restrict : (NNReal → ℝ) → DenseTime → ℝ := fun ω t => ω (DenseTime.castOrderEmbedding t)
  have hrestrict : Measurable restrict := Measurable.of_eval fun _ => measurable_pi_apply _
  have hdense := congrArg (fun ρ : Measure (NNReal → ℝ) => ρ.map restrict) hfull
  rw [Measure.map_map hrestrict heval, Measure.map_map hrestrict heval] at hdense
  apply MarkovProcess.Measure.map_denseRestriction_injective
  exact hdense

/-- The centered MarkovProcess Brownian motion has Mathlib's finite-dimensional
Brownian laws. -/
theorem isPreBrownianReal_brownianMotion (x : ℝ) :
    ProbabilityTheory.IsPreBrownianReal
      (fun (t : NNReal) (ω : ContinuousPath ℝ) => ω t - x) (brownianMotion x) := by
  apply ProbabilityTheory.HasIndepIncrements.isPreBrownianReal_of_hasLaw
  · exact (MarkovProcess.isBrownianReal_brownianMotion x).hasLaw_eval
  · exact (MarkovProcess.isBrownianReal_brownianMotion x).hasIndepIncrements

/-- Brownian scaling for the centered real canonical process. -/
theorem isPreBrownianReal_scaled_brownianMotion (x : ℝ) {c : NNReal} (hc : c ≠ 0) :
    ProbabilityTheory.IsPreBrownianReal
      (fun (t : NNReal) (ω : ContinuousPath ℝ) =>
        (Real.sqrt c)⁻¹ * (ω (c * t) - x)) (brownianMotion x) :=
  (isPreBrownianReal_brownianMotion x).smul hc

/-- All finite-dimensional laws of the scaled centered process coincide with
those of real Brownian motion started at zero. -/
theorem scaled_brownianMotion_finite_dimensional_law
    (x : ℝ) {c : NNReal} (hc : c ≠ 0) (I : Finset NNReal) :
    (brownianMotion x).map (fun ω => I.restrict (fun t =>
        (Real.sqrt c)⁻¹ * (ω (c * t) - x))) =
      (brownianMotion 0).map (fun ω => I.restrict (fun t => ω t)) := by
  calc
    _ = ProbabilityTheory.BrownianReal.projectiveFamily I :=
      ((isPreBrownianReal_scaled_brownianMotion x hc).hasLaw I).map_eq
    _ = _ := by
      simpa only [sub_zero] using (((isPreBrownianReal_brownianMotion 0).hasLaw I).map_eq).symm

/-- Recenter, rescale time, and normalize a real continuous path. -/
noncomputable def scaledCenteredRealPath (x : ℝ) (c : NNReal)
    (ω : ContinuousPath ℝ) : ContinuousPath ℝ :=
  ⟨fun t => (Real.sqrt c)⁻¹ * (ω (c * t) - x), by fun_prop⟩

theorem continuous_scaledCenteredRealPath (x : ℝ) (c : NNReal) :
    Continuous (scaledCenteredRealPath x c) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  show Continuous (fun q : ContinuousPath ℝ × NNReal =>
    (Real.sqrt c)⁻¹ * (q.1 (c * q.2) - x))
  fun_prop

/-- The scaled centered real Brownian path has the law of Brownian motion
started at zero. -/
theorem brownianMotion_map_scaledCenteredRealPath
    (x : ℝ) {c : NNReal} (hc : c ≠ 0) :
    (brownianMotion x).map (scaledCenteredRealPath x c) = brownianMotion 0 := by
  apply real_path_measure_eq_of_finite_dimensional_laws
  intro I
  have hI : Measurable (fun ω : ContinuousPath ℝ => I.restrict (fun t => ω t)) :=
    Measurable.of_eval fun _ => ContinuousPath.measurable_coordinateProcess _
  rw [Measure.map_map hI (continuous_scaledCenteredRealPath x c).measurable]
  exact scaled_brownianMotion_finite_dimensional_law x hc I

/-- Recenter, rescale time, and normalize a planar continuous path. -/
noncomputable def scaledCenteredPlanarPath (x : ℂ) (c : NNReal)
    (ω : ContinuousPath ℂ) : ContinuousPath ℂ :=
  ⟨fun t => (Real.sqrt c)⁻¹ • (ω (c * t) - x), by fun_prop⟩

theorem continuous_scaledCenteredPlanarPath (x : ℂ) (c : NNReal) :
    Continuous (scaledCenteredPlanarPath x c) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  show Continuous (fun q : ContinuousPath ℂ × NNReal =>
    (Real.sqrt c)⁻¹ • (q.1 (c * q.2) - x))
  fun_prop

/-- The scaled centered planar Brownian path has standard planar Brownian
law. -/
theorem planarBrownianMotion_map_scaledCenteredPlanarPath
    (x : ℂ) {c : NNReal} (hc : c ≠ 0) :
    (planarBrownianMotion x).map (scaledCenteredPlanarPath x c) = planarBrownianMotion 0 := by
  rw [planarBrownianMotion_apply, planarBrownianMotion_apply, Complex.zero_re, Complex.zero_im]
  have hp : ((brownianMotion x.re).prod (brownianMotion x.im)).map
      (Prod.map (scaledCenteredRealPath x.re c) (scaledCenteredRealPath x.im c)) =
      (brownianMotion 0).prod (brownianMotion 0) := by
    rw [← Measure.map_prod_map _ _ (continuous_scaledCenteredRealPath x.re c).measurable
      (continuous_scaledCenteredRealPath x.im c).measurable,
      brownianMotion_map_scaledCenteredRealPath x.re hc,
      brownianMotion_map_scaledCenteredRealPath x.im hc]
  rw [← hp]
  rw [Measure.map_map (continuous_scaledCenteredPlanarPath x c).measurable
      measurable_complexPathOfReIm,
    Measure.map_map measurable_complexPathOfReIm
      ((continuous_scaledCenteredRealPath x.re c).measurable.prodMap
        (continuous_scaledCenteredRealPath x.im c).measurable)]
  congr 1
  funext p
  ext t
  simp only [Function.comp_apply, complexPathOfReIm_apply, scaledCenteredPlanarPath,
    scaledCenteredRealPath, ContinuousMap.coe_mk, Prod.map_fst, Prod.map_snd,
    Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_inv]
  have hx : (x.re : ℂ) + (x.im : ℂ) * Complex.I = x := Complex.re_add_im x
  linear_combination (Real.sqrt c)⁻¹ * hx

/-- A spatial translation carries the planar Brownian law from zero to the
translated starting point. -/
theorem planarBrownianMotion_map_add (y : ℂ) :
    (planarBrownianMotion 0).map
        ((Homeomorph.refl NNReal).arrowCongr (Homeomorph.addRight y)) =
      planarBrownianMotion y := by
  let T := (Homeomorph.refl NNReal).arrowCongr (Homeomorph.addRight y)
  have h := congrArg (fun μ : Measure (ContinuousPath ℂ) => μ.map T)
    (planarBrownianMotion_map_scaledCenteredPlanarPath y (c := 1) one_ne_zero)
  rw [Measure.map_map T.measurable (continuous_scaledCenteredPlanarPath y 1).measurable] at h
  have hcomp : T ∘ scaledCenteredPlanarPath y 1 = id := by
    funext ω
    ext t
    simp [T, scaledCenteredPlanarPath, Homeomorph.arrowCongr]
  rw [hcomp, Measure.map_id] at h
  exact h.symm

/-- Translation carries planar Brownian motion to the translated starting
point. -/
theorem planarBrownianMotion_map_add_from (x y : ℂ) :
    (planarBrownianMotion x).map
        ((Homeomorph.refl NNReal).arrowCongr (Homeomorph.addRight y)) =
      planarBrownianMotion (x + y) := by
  rw [← planarBrownianMotion_map_add x,
    Measure.map_map ((Homeomorph.refl NNReal).arrowCongr (Homeomorph.addRight y)).measurable
      ((Homeomorph.refl NNReal).arrowCongr (Homeomorph.addRight x)).measurable,
    ← planarBrownianMotion_map_add (x + y)]
  congr 1
  funext ω
  ext t
  change (ω t + x) + y = ω t + (x + y)
  exact add_assoc _ _ _

/-- Brownian scaling as an identity for the spacetime path homeomorphism. -/
theorem planarBrownianMotion_map_spacetime_smul
    (x : ℂ) {k : ℝ} (hk : 0 < k) {c : NNReal} (hc : 0 < c)
    (hscale : (Real.sqrt c)⁻¹ = k) :
    (planarBrownianMotion x).map
      (spacetimePathHomeomorph (Homeomorph.smulOfNeZero k hk.ne') c hc) =
      planarBrownianMotion (k • x) := by
  let T := (Homeomorph.refl NNReal).arrowCongr (Homeomorph.addRight (k • x))
  have h := congrArg (fun μ : Measure (ContinuousPath ℂ) => μ.map T)
    (planarBrownianMotion_map_scaledCenteredPlanarPath x hc.ne')
  rw [Measure.map_map T.measurable (continuous_scaledCenteredPlanarPath x c).measurable,
    planarBrownianMotion_map_add] at h
  convert h using 1
  congr 1
  funext ω
  ext t
  simp only [Function.comp_apply, spacetimePathHomeomorph_apply, scaledCenteredPlanarPath, hscale]
  change k • ω (c * t) = k • (ω (c * t) - x) + k • x
  rw [smul_sub, sub_add_cancel]

end HarmonicBalls.Section6
