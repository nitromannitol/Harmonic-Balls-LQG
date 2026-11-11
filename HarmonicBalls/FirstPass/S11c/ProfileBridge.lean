import HarmonicBalls.FirstPass.S11c.Stationary
import HarmonicBalls.Proofs.GFF.ContinuousCircleDilationMixing

/-!
# Proposition 11.7, the repo's circle dilation as the normalized dilation of profiles

The ergodic dynamics on the continuous circle profiles (`continuousCircleDilation = continuousCircleAffine (1/2) 0`, ContinuousCircleDilationMixing.lean:19) coincide with the
normalized dilation `normalizedDilation` of the stationarity lemmas (Stationary.lean): on a profile `F` the point
`(r, z)` is sent to `F(r/2, z/2) - F(1/2, 0)`. Hence the ergodicity of the repo transfers to the iteration of
`normalizedDilation` on profiles, and `coneMassEvent_iterate_dilate` applies along the orbit.
-/

namespace HarmonicBalls

open MeasureTheory Set

/-- A continuous circle profile as a function of `(r, z)`, extended by zero to non-positive radii. -/
noncomputable def profileOf (F : C(CircleParameter, ℝ)) : ℝ → ℂ → ℝ :=
  fun e z => if h : 0 < e then F (⟨e, h⟩, z) else 0

/-- The repo's circle dilation is the normalized dilation of the profile. -/
theorem continuousCircleDilation_eq_normalizedDilation (F : C(CircleParameter, ℝ)) (p : CircleParameter) :
    continuousCircleDilation F p = normalizedDilation (profileOf F) (p.1 : ℝ) p.2 := by
  have hp : (0 : ℝ) < (p.1 : ℝ) := p.1.2
  have hn : ‖((1 / 2 : ℝ) : ℂ)‖ = 1 / 2 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by norm_num)]
  have hz : ((1 / 2 : ℝ) : ℂ) * p.2 + 0 = p.2 / 2 := by
    push_cast
    ring
  unfold continuousCircleDilation continuousCircleAffine normalizedDilation profileOf
  simp only [ContinuousMap.sub_apply, ContinuousMap.comp_apply, ContinuousMap.const_apply,
    ContinuousMap.coe_mk, affineCircleParameter, ContinuousMap.coe_mk]
  have h1 : (0 : ℝ) < (p.1 : ℝ) / 2 := by positivity
  have h2 : (0 : ℝ) < 1 / 2 := by norm_num
  simp only [h1, h2, dite_true]
  congr 1
  · congr 1
    refine Prod.ext (Subtype.ext ?_) hz
    simp only [hn]
    ring
  · congr 1
    exact Prod.ext (Subtype.ext hn) rfl

end HarmonicBalls
