import Mathlib.Analysis.ConstantSpeed

/-! # Natural parametrization on a closed interval

For a continuous curve of bounded variation, the natural parametrization
has unit speed on the interval from zero to its total variation.
-/

open Set
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- The image of the cumulative variation of a continuous bounded-variation
curve on a closed interval is the interval of its total length. -/
theorem variationOnFromTo_image_Icc {E : Type*} [PseudoMetricSpace E]
    (p : ℝ → E) {T : ℝ} (hT : 0 ≤ T)
    (hp : ContinuousOn p (Icc 0 T)) (hvar : BoundedVariationOn p (Icc 0 T)) :
    variationOnFromTo p (Icc 0 T) 0 '' Icc 0 T =
      Icc 0 (eVariationOn p (Icc 0 T)).toReal := by
  have hzero : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hcont : ContinuousOn (variationOnFromTo p (Icc 0 T) 0) (Icc 0 T) := by
    intro x hx
    exact (hvar.continuousWithinAt_variationOnFromTo_iff hzero hx).2 (hp x hx)
  have hmono := variationOnFromTo.monotoneOn hvar.locallyBoundedVariationOn hzero
  rw [hcont.image_Icc_of_monotoneOn hT hmono, variationOnFromTo.self,
    variationOnFromTo.eq_of_le p (Icc 0 T) hT, inter_self]

/-- Natural parametrization of a finite-length continuous curve has unit
speed on its full length interval and agrees with both endpoints. -/
theorem naturalParameterization_unitSpeed_Icc {E : Type*} [MetricSpace E]
    (p : ℝ → E) {T : ℝ} (hT : 0 ≤ T)
    (hp : ContinuousOn p (Icc 0 T)) (hvar : BoundedVariationOn p (Icc 0 T)) :
    HasUnitSpeedOn (naturalParameterization p (Icc 0 T) 0)
        (Icc 0 (eVariationOn p (Icc 0 T)).toReal) ∧
      naturalParameterization p (Icc 0 T) 0 0 = p 0 ∧
      naturalParameterization p (Icc 0 T) 0 (eVariationOn p (Icc 0 T)).toReal = p T := by
  have hzero : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hTmem : T ∈ Icc (0 : ℝ) T := ⟨hT, le_rfl⟩
  have hlocal := hvar.locallyBoundedVariationOn
  have himage := variationOnFromTo_image_Icc p hT hp hvar
  have hs := has_unit_speed_naturalParameterization p hlocal hzero
  rw [himage] at hs
  refine ⟨hs, ?_, ?_⟩
  · have h := edist_naturalParameterization_eq_zero hlocal hzero hzero
    rw [variationOnFromTo.self] at h
    exact edist_eq_zero.mp h
  · have h := edist_naturalParameterization_eq_zero hlocal hzero hTmem
    rw [variationOnFromTo.eq_of_le p (Icc 0 T) hT, inter_self] at h
    exact edist_eq_zero.mp h

/-- A unit-speed curve on an interval is one-Lipschitz on that interval. -/
theorem HasUnitSpeedOn.lipschitzOnWith_Icc {E : Type*} [PseudoMetricSpace E]
    {p : ℝ → E} {a b : ℝ} (hp : HasUnitSpeedOn p (Icc a b)) :
    LipschitzOnWith 1 p (Icc a b) := by
  intro x hx y hy
  change edist (p x) (p y) ≤ (1 : ℝ≥0∞) * edist x y
  simp only [one_mul]
  rcases le_total x y with hxy | hyx
  · have hv := eVariationOn.edist_le p
      (s := Icc a b ∩ Icc x y) (x := x) (y := y)
      ⟨hx, le_rfl, hxy⟩ ⟨hy, hxy, le_rfl⟩
    have hs : eVariationOn p (Icc a b ∩ Icc x y) = ENNReal.ofReal (y - x) := by
      simpa only [NNReal.coe_one, one_mul] using hp hx hy
    rw [hs] at hv
    have hdist : edist x y = ENNReal.ofReal (y - x) := by
      rw [edist_dist, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy)]
      congr 1
      ring
    exact hdist ▸ hv
  · have hv := eVariationOn.edist_le p
      (s := Icc a b ∩ Icc y x) (x := y) (y := x)
      ⟨hy, le_rfl, hyx⟩ ⟨hx, hyx, le_rfl⟩
    have hs : eVariationOn p (Icc a b ∩ Icc y x) = ENNReal.ofReal (x - y) := by
      simpa only [NNReal.coe_one, one_mul] using hp hy hx
    rw [hs] at hv
    have hdist : edist x y = ENNReal.ofReal (x - y) := by
      rw [edist_dist, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hyx)]
    rw [edist_comm] at hv
    exact hdist ▸ hv

end HarmonicBalls
