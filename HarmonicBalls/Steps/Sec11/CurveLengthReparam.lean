import HarmonicBalls.Steps.Sec11.MetricArcLength

/-! # Curve lengths under increasing reparametrization -/

namespace HarmonicBalls

open Set
open scoped ENNReal

private structure ReparamLengthPoint where
  val : ℂ

/-- A continuous increasing change of parameter preserves metric length. -/
theorem IsEuclideanLengthMetric.curveLength_comp_of_monotoneOn
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (p : ℝ → ℂ) (φ : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hφcont : ContinuousOn φ (Icc a b)) (hφmono : MonotoneOn φ (Icc a b)) :
    curveLength D (p ∘ φ) a b = curveLength D p (φ a) (φ b) := by
  let : MetricSpace ReparamLengthPoint := {
    dist := fun x y => D x.val y.val
    dist_self := fun x => hD.self_eq_zero x.val
    dist_comm := fun x y => hD.symm x.val y.val
    dist_triangle := fun x y z => hD.triangle x.val y.val z.val
    eq_of_dist_eq_zero := by
      intro ⟨u⟩ ⟨v⟩ h
      exact congrArg ReparamLengthPoint.mk (hD.eq_of_eq_zero u v h) }
  have hcurve (q : ℝ → ℂ) (s t : ℝ) :
      curveLength D q s t = eVariationOn (fun r => (⟨q r⟩ : ReparamLengthPoint)) (Icc s t) := by
    simp only [curveLength, eVariationOn, edist_dist]
    rfl
  let q : ℝ → ReparamLengthPoint := fun t => ⟨p t⟩
  have himage : φ '' Icc a b = Icc (φ a) (φ b) :=
    hφcont.image_Icc_of_monotoneOn hab hφmono
  calc
    _ = eVariationOn (q ∘ φ) (Icc a b) := hcurve _ _ _
    _ = eVariationOn q (Icc (φ a) (φ b)) := by
      rw [eVariationOn.comp_eq_of_monotoneOn q φ hφmono, himage]
    _ = _ := (hcurve _ _ _).symm

/-- For a continuous finite-length curve, cumulative length is continuous,
increasing and ranges over the whole interval of total length. -/
theorem IsEuclideanLengthMetric.cumulative_curveLength_properties
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {p : ℝ → ℂ} {T : ℝ} (hT : 0 ≤ T) (hp : ContinuousOn p (Icc 0 T))
    (hfinite : curveLength D p 0 T < ∞) :
    let L : ℝ → ℝ := fun t => (curveLength D p 0 t).toReal
    ContinuousOn L (Icc 0 T) ∧ MonotoneOn L (Icc 0 T) ∧ L 0 = 0 ∧
      L '' Icc 0 T = Icc 0 (L T) := by
  let : MetricSpace ReparamLengthPoint := {
    dist := fun x y => D x.val y.val
    dist_self := fun x => hD.self_eq_zero x.val
    dist_comm := fun x y => hD.symm x.val y.val
    dist_triangle := fun x y z => hD.triangle x.val y.val z.val
    eq_of_dist_eq_zero := by
      intro ⟨u⟩ ⟨v⟩ h
      exact congrArg ReparamLengthPoint.mk (hD.eq_of_eq_zero u v h) }
  have hopen (U : Set ℂ) : IsOpen {z : ReparamLengthPoint | z.val ∈ U} ↔ IsOpen U := by
    rw [Metric.isOpen_iff, hD.isOpen_iff]
    constructor
    · intro h x hx
      obtain ⟨ε, hε, hεx⟩ := h ⟨x⟩ hx
      refine ⟨ε, hε, ?_⟩
      intro y hy
      apply hεx
      change D y x < ε
      rwa [hD.symm]
    · intro h ⟨x⟩ hx
      obtain ⟨ε, hε, hεx⟩ := h x hx
      refine ⟨ε, hε, ?_⟩
      intro ⟨y⟩ hy
      apply hεx y
      change D y x < ε at hy
      rwa [hD.symm] at hy
  have hmk : Continuous (fun z : ℂ => (⟨z⟩ : ReparamLengthPoint)) := by
    rw [continuous_def]
    intro U hU
    apply (hopen _).mp
    convert hU using 1
    ext ⟨x⟩
    rfl
  let q : ℝ → ReparamLengthPoint := fun t => ⟨p t⟩
  have hcurve (s t : ℝ) : curveLength D p s t = eVariationOn q (Icc s t) := by
    simp only [curveLength, eVariationOn, edist_dist]
    rfl
  have hqcont : ContinuousOn q (Icc 0 T) := hmk.comp_continuousOn hp
  have hvar : BoundedVariationOn q (Icc 0 T) := by
    change eVariationOn q (Icc 0 T) ≠ ∞
    rw [← hcurve]
    exact hfinite.ne
  have hzero : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have heq : EqOn (variationOnFromTo q (Icc 0 T) 0)
      (fun t => (curveLength D p 0 t).toReal) (Icc 0 T) := by
    intro t ht
    rw [variationOnFromTo.eq_of_le q (Icc 0 T) ht.1,
      inter_eq_right.mpr (Icc_subset_Icc le_rfl ht.2), ← hcurve]
  have hcont : ContinuousOn (variationOnFromTo q (Icc 0 T) 0) (Icc 0 T) := by
    intro t ht
    exact (hvar.continuousWithinAt_variationOnFromTo_iff hzero ht).2 (hqcont t ht)
  have hmono := variationOnFromTo.monotoneOn hvar.locallyBoundedVariationOn hzero
  have hLzero : (curveLength D p 0 0).toReal = 0 := by
    have h := heq hzero
    rw [variationOnFromTo.self] at h
    exact h.symm
  have himage := variationOnFromTo_image_Icc q hT hqcont hvar
  refine ⟨hcont.congr heq.symm, ?_, hLzero, ?_⟩
  · intro x hx y hy hxy
    rw [← heq hx, ← heq hy]
    exact hmono hx hy hxy
  · rw [← image_congr heq, himage, ← hcurve]

/-- If an original curve is tracked by a continuous increasing parameter,
the shifted cumulative length of the tracked curve recovers the parameter
of a shifted unit-speed curve. -/
theorem IsEuclideanLengthMetric.cumulative_length_comp_of_tracking
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) {q p : ℝ → ℂ} {T : ℝ}
    (hq : IsLengthParametrized E q T) (hqD : curveLength D q 0 T < ∞)
    (htrack : ∀ t ∈ Icc 0 T, p (curveLength D q 0 t).toReal = q t)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    (curveLength E p 0 (curveLength D q 0 t).toReal).toReal = t := by
  let A : ℝ → ℝ := fun s => (curveLength D q 0 s).toReal
  obtain ⟨hcont, hmono, hzero, _⟩ := hD.cumulative_curveLength_properties hq.1 hq.2.1 hqD
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have heq : EqOn q (p ∘ A) (Icc 0 t) := by
    intro s hs
    exact (htrack s (hsub hs)).symm
  have hchange := hE.curveLength_comp_of_monotoneOn p A ht.1
    (hcont.mono hsub) (hmono.mono hsub)
  change A 0 = 0 at hzero
  have hcurve : curveLength E q 0 t = curveLength E p 0 (A t) := by
    rw [curveLength_eq_of_eqOn heq, hchange, hzero]
  have hunit := hq.2.2 0 t le_rfl ht.1 ht.2
  rw [hcurve] at hunit
  have hreal := congrArg ENNReal.toReal hunit
  simpa only [ENNReal.toReal_ofReal ht.1, sub_zero, A] using hreal

#print axioms IsEuclideanLengthMetric.cumulative_length_comp_of_tracking
#print axioms IsEuclideanLengthMetric.cumulative_curveLength_properties
#print axioms IsEuclideanLengthMetric.curveLength_comp_of_monotoneOn

end HarmonicBalls
