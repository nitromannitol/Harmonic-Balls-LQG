import HarmonicBalls.Proposed.MillerSheffieldIG4
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.CameronMartin

/-! # Cameron–Martin shifts of a Gaussian family on an inner product space

The path-space shift formula follows from the Gaussian process tilt identity.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

universe u

namespace HarmonicBalls

/-- The Cameron–Martin formula for a Gaussian family with inner-product covariance. -/
theorem millerSheffieldIG4Prop29_holds (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] : MillerSheffieldIG4Prop29.{u} H := by
  intro Ω _ P _ X hX g
  let σ : H →₀ ℝ := Finsupp.single g 1
  have hshift (f : H) :
      QuantumZipper.CameronMartin.covShift X P σ f = inner ℝ g f := by
    simp only [σ, QuantumZipper.CameronMartin.covShift, QuantumZipper.CameronMartin.covK,
      Finsupp.support_single _ one_ne_zero, Finset.sum_singleton,
      Finsupp.single_eq_same, one_mul]
    rw [hX.covariance_eq, real_inner_comm]
  have hcomb (ω : Ω) : QuantumZipper.CameronMartin.comb X σ ω = X g ω := by
    simp [σ, QuantumZipper.CameronMartin.comb]
  have hnorm : QuantumZipper.CameronMartin.covNorm X P σ = inner ℝ g g := by
    simp [σ, QuantumZipper.CameronMartin.covNorm, hshift]
  have hpath : Measurable (fun ω f => X f ω) := measurable_pi_iff.mpr hX.measurable
  have hshiftpath : Measurable (fun ω f => X f ω + inner ℝ g f) :=
    measurable_pi_iff.mpr fun f => (hX.measurable f).add_const _
  have hmap := QuantumZipper.CameronMartin.map_tiltMeasure_path
    hX.isGaussian hX.measurable hX.integral_eq_zero σ
  have hforward : QuantumZipper.CameronMartin.tiltMeasure X P σ ≪ P :=
    withDensity_absolutelyContinuous _ _
  have hback : P ≪ QuantumZipper.CameronMartin.tiltMeasure X P σ := by
    apply withDensity_absolutelyContinuous'
    · exact (ENNReal.measurable_ofReal.comp
        (QuantumZipper.CameronMartin.measurable_tiltDensity hX.isGaussian hX.measurable σ)).aemeasurable
    · exact ae_of_all _ fun ω => (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hf := hforward.map hpath
  have hb := hback.map hpath
  rw [hmap] at hf hb
  have hmap' : (QuantumZipper.CameronMartin.tiltMeasure X P σ).map (fun ω f => X f ω) =
      P.map (fun ω f => X f ω + inner ℝ g f) := by
    simpa only [hshift] using hmap
  refine ⟨Real.exp (inner ℝ g g / 2), Real.exp_pos _, ?_⟩
  intro A hA
  have hpre : MeasurableSet ((fun ω f => X f ω) ⁻¹' A) := hpath hA
  have heq := congrArg (fun μ : Measure (H → ℝ) => μ A) hmap'
  rw [Measure.map_apply hpath hA, Measure.map_apply hshiftpath hA,
    QuantumZipper.CameronMartin.tiltMeasure, withDensity_apply _ hpre] at heq
  constructor
  · rw [← heq]
    congr 1
    funext ω
    simp only [QuantumZipper.CameronMartin.tiltDensity, hcomb, hnorm, Real.exp_sub]
    rfl
  · have hf' : P.map (fun ω f => X f ω + inner ℝ g f) ≪
        P.map (fun ω f => X f ω) := by simpa only [hshift] using hf
    have hb' : P.map (fun ω f => X f ω) ≪
        P.map (fun ω f => X f ω + inner ℝ g f) := by simpa only [hshift] using hb
    rw [← Measure.map_apply hshiftpath hA, ← Measure.map_apply hpath hA]
    exact ⟨fun h => hb' h, fun h => hf' h⟩

end HarmonicBalls
