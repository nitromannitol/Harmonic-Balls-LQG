import HarmonicBalls.Steps.Sec11.InternalMetricPaths

/-! # Reversal of length-parametrized paths

Reversing time preserves length parametrization and weighted path costs.
Consequently Weyl scaling is symmetric for every weight.
-/

namespace HarmonicBalls

open MeasureTheory Set
open scoped ENNReal

private structure ReverseLengthPoint where
  val : ℂ

/-- Reversing time changes the interval of a curve length to its reflected
interval. -/
theorem IsEuclideanLengthMetric.curveLength_reverse
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (p : ℝ → ℂ) (T a b : ℝ) :
    curveLength D (fun t => p (T - t)) a b = curveLength D p (T - b) (T - a) := by
  let : MetricSpace ReverseLengthPoint := {
    dist := fun x y => D x.val y.val
    dist_self := fun x => hD.self_eq_zero x.val
    dist_comm := fun x y => hD.symm x.val y.val
    dist_triangle := fun x y z => hD.triangle x.val y.val z.val
    eq_of_dist_eq_zero := by
      intro ⟨u⟩ ⟨v⟩ h
      exact congrArg ReverseLengthPoint.mk (hD.eq_of_eq_zero u v h) }
  have hcurve (q : ℝ → ℂ) (s t : ℝ) :
      curveLength D q s t = eVariationOn (fun r => (⟨q r⟩ : ReverseLengthPoint)) (Icc s t) := by
    simp only [curveLength, eVariationOn, edist_dist]
    rfl
  let q : ℝ → ReverseLengthPoint := fun t => ⟨p t⟩
  have hanti : AntitoneOn (fun t : ℝ => T - t) (Icc a b) := by
    intro x hx y hy hxy
    linarith
  have himage : (fun t : ℝ => T - t) '' Icc a b = Icc (T - b) (T - a) := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      constructor <;> linarith [ht.1, ht.2]
    · intro hx
      refine ⟨T - x, ?_, by ring⟩
      constructor <;> linarith [hx.1, hx.2]
  calc
    curveLength D (fun t => p (T - t)) a b =
        eVariationOn (q ∘ fun t : ℝ => T - t) (Icc a b) := hcurve _ _ _
    _ = eVariationOn q (Icc (T - b) (T - a)) := by
      rw [eVariationOn.comp_eq_of_antitoneOn q _ hanti, himage]
    _ = curveLength D p (T - b) (T - a) := (hcurve _ _ _).symm

/-- Reversing a length-parametrized curve preserves its parametrization. -/
theorem IsEuclideanLengthMetric.isLengthParametrized_reverse
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {p : ℝ → ℂ} {T : ℝ} (hp : IsLengthParametrized D p T) :
    IsLengthParametrized D (fun t => p (T - t)) T := by
  refine ⟨hp.1, ?_, ?_⟩
  · apply hp.2.1.comp (continuous_const.sub continuous_id).continuousOn
    intro t ht
    change T - t ∈ Icc (0 : ℝ) T
    constructor <;> linarith [ht.1, ht.2]
  · intro s t hs hst ht
    rw [hD.curveLength_reverse, hp.2.2 (T - t) (T - s) (by linarith) (by linarith) (by linarith)]
    congr 1
    ring

/-- Reflection of a closed interval preserves Lebesgue integration. -/
theorem lintegral_Icc_reverse (F : ℝ → ℝ≥0∞) (T : ℝ) :
    (∫⁻ t in Icc (0 : ℝ) T, F (T - t)) = ∫⁻ t in Icc (0 : ℝ) T, F t := by
  have hpre : (fun t : ℝ => T - t) ⁻¹' Icc (0 : ℝ) T = Icc 0 T := by
    ext t
    simp only [mem_preimage, mem_Icc]
    constructor <;> intro ht <;> constructor <;> linarith [ht.1, ht.2]
  have hemb : MeasurableEmbedding (fun t : ℝ => T - t) :=
    (Homeomorph.subLeft T).measurableEmbedding
  have hm := ((volume : Measure ℝ).measurePreserving_sub_left T).restrict_preimage_emb
    hemb (Icc (0 : ℝ) T)
  rw [hpre] at hm
  exact hm.lintegral_comp_emb hemb F

/-- Weyl scaling is symmetric for arbitrary weights on a Euclidean length
metric. -/
theorem IsEuclideanLengthMetric.weylScaling_symm
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (ξ : ℝ) (f : ℂ → ℝ) (x y : ℂ) :
    weylScaling D ξ f x y = weylScaling D ξ f y x := by
  have hle (x y : ℂ) : weylScaling D ξ f x y ≤ weylScaling D ξ f y x := by
    unfold weylScaling
    refine le_iInf fun T => le_iInf fun p => le_iInf fun hp => le_iInf fun h0 =>
      le_iInf fun hT => ?_
    have hrev := hD.isLengthParametrized_reverse hp
    have hrev0 : (fun t => p (T - t)) 0 = x := by simpa using hT
    have hrevT : (fun t => p (T - t)) T = y := by simpa using h0
    calc
      _ ≤ ∫⁻ t in Icc (0 : ℝ) T, ENNReal.ofReal (Real.exp (ξ * f (p (T - t)))) :=
        (iInf₂_le T (fun t => p (T - t))).trans
          ((iInf₂_le hrev hrev0).trans (iInf_le _ hrevT))
      _ = _ := lintegral_Icc_reverse (fun t => ENNReal.ofReal (Real.exp (ξ * f (p t)))) T
  exact le_antisymm (hle x y) (hle y x)

end HarmonicBalls
