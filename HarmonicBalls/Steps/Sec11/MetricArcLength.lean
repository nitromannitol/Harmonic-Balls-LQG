import HarmonicBalls.Steps.Sec11.ArcLengthInterval
import HarmonicBalls.Steps.Sec11.WeylPathSegments

/-! # Arc-length parametrization for a Euclidean length metric -/

namespace HarmonicBalls

open MeasureTheory Set
open scoped ENNReal NNReal

private structure ArcLengthPoint where
  val : ℂ

/-- A continuous curve of finite length can be parametrized by metric
arc length, with its endpoints and total length preserved. -/
theorem IsEuclideanLengthMetric.exists_lengthParametrized_of_curveLength_lt_top
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {p : ℝ → ℂ} {T : ℝ} (hT : 0 ≤ T) (hp : ContinuousOn p (Icc 0 T))
    (hfinite : curveLength D p 0 T < ∞) :
    ∃ q : ℝ → ℂ, IsLengthParametrized D q (curveLength D p 0 T).toReal ∧
      q 0 = p 0 ∧ q (curveLength D p 0 T).toReal = p T := by
  let : MetricSpace ArcLengthPoint := {
    dist := fun x y => D x.val y.val
    dist_self := fun x => hD.self_eq_zero x.val
    dist_comm := fun x y => hD.symm x.val y.val
    dist_triangle := fun x y z => hD.triangle x.val y.val z.val
    eq_of_dist_eq_zero := by
      intro ⟨u⟩ ⟨v⟩ h
      exact congrArg ArcLengthPoint.mk (hD.eq_of_eq_zero u v h) }
  have hopen (U : Set ℂ) : IsOpen {z : ArcLengthPoint | z.val ∈ U} ↔ IsOpen U := by
    rw [Metric.isOpen_iff, hD.isOpen_iff]
    constructor
    · intro h x hx
      obtain ⟨ε, hε, hεx⟩ := h ⟨x⟩ hx
      refine ⟨ε, hε, ?_⟩
      intro y hy
      apply hεx
      change D y x < ε
      rw [hD.symm]
      exact hy
    · intro h ⟨x⟩ hx
      obtain ⟨ε, hε, hεx⟩ := h x hx
      refine ⟨ε, hε, ?_⟩
      intro ⟨y⟩ hy
      apply hεx y
      change D y x < ε at hy
      rwa [hD.symm] at hy
  have hmk : Continuous (fun z : ℂ => (⟨z⟩ : ArcLengthPoint)) := by
    rw [continuous_def]
    intro U hU
    apply (hopen _).mp
    convert hU using 1
    ext ⟨x⟩
    rfl
  have hval : Continuous (fun z : ArcLengthPoint => z.val) := by
    rw [continuous_def]
    intro U hU
    exact (hopen U).mpr hU
  let r : ℝ → ArcLengthPoint := fun t => ⟨p t⟩
  have hcurve (q : ℝ → ℂ) (a b : ℝ) :
      curveLength D q a b = eVariationOn (fun t => (⟨q t⟩ : ArcLengthPoint)) (Icc a b) := by
    simp only [curveLength, eVariationOn, edist_dist]
    rfl
  have hrcont : ContinuousOn r (Icc 0 T) := hmk.comp_continuousOn hp
  have hrvar : BoundedVariationOn r (Icc 0 T) := by
    change eVariationOn r (Icc 0 T) ≠ ∞
    rw [← hcurve]
    exact hfinite.ne
  obtain ⟨hspeed, hstart, hend⟩ := naturalParameterization_unitSpeed_Icc r hT hrcont hrvar
  let R := (curveLength D p 0 T).toReal
  have hs : HasUnitSpeedOn (naturalParameterization r (Icc 0 T) 0) (Icc 0 R) := by
    simpa only [R, hcurve] using hspeed
  let q : ℝ → ℂ := fun t => (naturalParameterization r (Icc 0 T) 0 t).val
  have hqcont : ContinuousOn q (Icc 0 R) :=
    hval.comp_continuousOn (HasUnitSpeedOn.lipschitzOnWith_Icc hs).continuousOn
  refine ⟨q, ⟨ENNReal.toReal_nonneg, hqcont, ?_⟩, ?_, ?_⟩
  · intro a b ha hab hb
    have ha' : a ∈ Icc 0 R := ⟨ha, hab.trans hb⟩
    have hb' : b ∈ Icc 0 R := ⟨ha.trans hab, hb⟩
    have hinter : Icc 0 R ∩ Icc a b = Icc a b := by
      apply inter_eq_right.mpr
      exact Icc_subset_Icc ha hb
    have h := hs ha' hb'
    simp only [NNReal.coe_one, one_mul, hinter] at h
    rw [hcurve]
    exact h
  · exact congrArg ArcLengthPoint.val hstart
  · have h := congrArg ArcLengthPoint.val hend
    simpa only [q, r, R, hcurve] using h

/-- Weyl scaling by zero recovers every Euclidean length metric. -/
theorem IsEuclideanLengthMetric.weylScaling_zero
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (ξ : ℝ) (x y : ℂ) :
    weylScaling D ξ 0 x y = ENNReal.ofReal (D x y) := by
  apply le_antisymm
  · rw [hD.ofReal_eq_internalMetric]
    refine le_iInf fun P => le_iInf fun _ => ?_
    by_cases hfin : pathLength D P = ∞
    · rw [hfin]
      exact le_top
    · have hfinite : curveLength D P.extend 0 1 < ∞ := lt_top_iff_ne_top.mpr hfin
      obtain ⟨q, hq, hq0, hqT⟩ :=
        hD.exists_lengthParametrized_of_curveLength_lt_top (by norm_num) P.continuous_extend.continuousOn hfinite
      have hq0' : q 0 = x := by simpa using hq0
      have hqT' : q (curveLength D P.extend 0 1).toReal = y := by simpa using hqT
      unfold weylScaling
      refine (iInf₂_le _ q).trans ((iInf₂_le hq hq0').trans ((iInf_le _ hqT').trans ?_))
      simp only [Pi.zero_apply, mul_zero, Real.exp_zero, ENNReal.ofReal_one,
        lintegral_const, one_mul, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero]
      exact (ENNReal.ofReal_toReal hfin).le
  · unfold weylScaling
    refine le_iInf fun T => le_iInf fun p => le_iInf fun hp => le_iInf fun hp0 =>
      le_iInf fun hpT => ?_
    obtain ⟨P, hP⟩ := exists_path_pathLength_le_curveLength (E := D) hp.1 hp.2.1
    have h := hD.ofReal_eq_internalMetric (p 0) (p T)
    have hle : ENNReal.ofReal (D (p 0) (p T)) ≤ pathLength D P := by
      rw [h]
      exact iInf_le_of_le P (iInf_le _ (fun _ => mem_univ _))
    have hbound : ENNReal.ofReal (D x y) ≤ ENNReal.ofReal T := by
      rw [← hp0, ← hpT]
      exact (hle.trans hP).trans_eq (by simpa using hp.2.2 0 T le_rfl hp.1 le_rfl)
    simpa only [Pi.zero_apply, mul_zero, Real.exp_zero, ENNReal.ofReal_one,
      lintegral_const, one_mul, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero] using hbound

end HarmonicBalls
