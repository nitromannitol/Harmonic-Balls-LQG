import Mathlib
import HarmonicBalls.LPStage.LengthMetric

/-!
# Weyl comparison of internal metrics on a closed set, with arclength reparametrization (staged for `LatticeProb.LQG`)

For a Euclidean length metric `D` on `ℂ` and the Weyl scaling `E = e^{ξ f} · D` (Gwynne-Miller, arXiv:1905.00383,
(1.7)-(1.8)), with `ξ f ≤ B` on a set `U`, the internal metric of `E` on `U` is at most `e^B` times the internal metric
of `D` on `U`. The statement is `LatticeProb.LQG.WeylInternalClosed`; `LatticeProb.LQG.weylInternalClosed_derived`
proves it with no hypothesis added. The argument: a path in `U` is reparametrized by its `D`-arclength (Burago-Burago-Ivanov);
each sub-arc is a competitor in the infimum defining `weylScaling`, with weighted cost at most `e^B` times its length;
telescoping over a partition bounds the `E`-length of the path. The proof uses only that the path lies in `U`.

Provenance (HarmonicBalls repository, branch main, commit da14a3bf): the arclength reparametrization lemmas are adapted from
`HarmonicBalls/Steps/Sec11/ArcLengthInterval.lean` (lines 14-81), `WeylPathConcatenation.lean` (14-62), `WeylPathSegments.lean` (14-36), `WeylPathReverse.lean`
(14-68), `MetricArcLength.lean` (11-100) and `CurveLengthReparam.lean` (10-110), with the namespace changed to
`LatticeProb.LQG` and the imports changed to Mathlib and `HarmonicBalls.LPStage.LengthMetric`. The Weyl comparison
lemmas are from `HarmonicBalls/FirstPass/Phase2/WeylInternalClosedDerived.lean`.
-/

namespace LatticeProb.LQG

open MeasureTheory Set
open scoped ENNReal NNReal

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


private structure ConcatLengthPoint where
  val : ℂ

/-- Curves agreeing on an interval have the same length there. -/
theorem curveLength_eq_of_eqOn {D : ℂ → ℂ → ℝ} {p q : ℝ → ℂ} {a b : ℝ}
    (h : EqOn p q (Icc a b)) : curveLength D p a b = curveLength D q a b := by
  unfold curveLength
  congr 1
  funext n
  apply Finset.sum_congr rfl
  intro i hi
  rw [h (n.2.2.2 (i + 1)), h (n.2.2.2 i)]

/-- Curve length is unchanged by translating the parameter. -/
theorem IsEuclideanLengthMetric.curveLength_translate
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (p : ℝ → ℂ) (c a b : ℝ) :
    curveLength D (fun t => p (t - c)) a b = curveLength D p (a - c) (b - c) := by
  let : MetricSpace ConcatLengthPoint := {
    dist := fun x y => D x.val y.val
    dist_self := fun x => hD.self_eq_zero x.val
    dist_comm := fun x y => hD.symm x.val y.val
    dist_triangle := fun x y z => hD.triangle x.val y.val z.val
    eq_of_dist_eq_zero := by
      intro ⟨u⟩ ⟨v⟩ h
      exact congrArg ConcatLengthPoint.mk (hD.eq_of_eq_zero u v h) }
  have hcurve (q : ℝ → ℂ) (s t : ℝ) :
      curveLength D q s t = eVariationOn (fun r => (⟨q r⟩ : ConcatLengthPoint)) (Icc s t) := by
    simp only [curveLength, eVariationOn, edist_dist]
    rfl
  let q : ℝ → ConcatLengthPoint := fun t => ⟨p t⟩
  have hmono : MonotoneOn (fun t : ℝ => t - c) (Icc a b) := by
    intro x hx y hy hxy
    linarith
  have himage : (fun t : ℝ => t - c) '' Icc a b = Icc (a - c) (b - c) := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      constructor <;> linarith [ht.1, ht.2]
    · intro hx
      refine ⟨x + c, ?_, by ring⟩
      constructor <;> linarith [hx.1, hx.2]
  calc
    curveLength D (fun t => p (t - c)) a b =
        eVariationOn (q ∘ fun t : ℝ => t - c) (Icc a b) := hcurve _ _ _
    _ = eVariationOn q (Icc (a - c) (b - c)) := by
      rw [eVariationOn.comp_eq_of_monotoneOn q _ hmono, himage]
    _ = curveLength D p (a - c) (b - c) := (hcurve _ _ _).symm


/-- Translating a subinterval to start at zero preserves length
parametrization. -/
theorem IsEuclideanLengthMetric.isLengthParametrized_subcurve
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {p : ℝ → ℂ} {T a b : ℝ} (hp : IsLengthParametrized D p T)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    IsLengthParametrized D (fun t => p (a + t)) (b - a) := by
  refine ⟨sub_nonneg.mpr hab, ?_, ?_⟩
  · apply hp.2.1.comp (continuous_const.add continuous_id).continuousOn
    intro t ht
    change 0 ≤ a + t ∧ a + t ≤ T
    constructor <;> linarith [ht.1, ht.2]
  · intro s t hs hst ht
    have heq : (fun t : ℝ => p (a + t)) = fun t => p (t - (-a)) := by
      funext t
      congr 1
      ring
    rw [heq, hD.curveLength_translate]
    have h := hp.2.2 (s - -a) (t - -a) (by linarith) (by linarith) (by linarith)
    rw [h]
    congr 1
    ring


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


private structure ArcLengthPoint where
  val : ℂ

/-- A continuous curve of finite length can be parametrized by metric
arc length, preserving its endpoints, total length and cumulative-length tracking. -/
theorem IsEuclideanLengthMetric.exists_lengthParametrized_with_tracking
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {p : ℝ → ℂ} {T : ℝ} (hT : 0 ≤ T) (hp : ContinuousOn p (Icc 0 T))
    (hfinite : curveLength D p 0 T < ∞) :
    ∃ q : ℝ → ℂ, IsLengthParametrized D q (curveLength D p 0 T).toReal ∧
      q 0 = p 0 ∧ q (curveLength D p 0 T).toReal = p T ∧
      ∀ t ∈ Icc 0 T, q (curveLength D p 0 t).toReal = p t := by
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
  refine ⟨q, ⟨ENNReal.toReal_nonneg, hqcont, ?_⟩, ?_, ?_, ?_⟩
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

  · intro t ht
    have h := edist_naturalParameterization_eq_zero hrvar.locallyBoundedVariationOn
      (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩) ht
    rw [variationOnFromTo.eq_of_le r (Icc 0 T) ht.1,
      inter_eq_right.mpr (Icc_subset_Icc le_rfl ht.2)] at h
    have heq := edist_eq_zero.mp h
    have hv := congrArg ArcLengthPoint.val heq
    simpa only [q, r, hcurve] using hv


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


/-- A `D`-arclength parametrized curve `q` on `[0, L]` with weight `ξ f ≤ B` along it: the sub-arc `r ↦ q (a + r)` is a
competitor in `weylScaling`, so `weylScaling D ξ f (q a) (q b) ≤ e^B (b - a)` for `0 ≤ a ≤ b ≤ L`. -/
theorem weylScaling_le_of_subarc {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {ξ B : ℝ} {f : ℂ → ℝ}
    {q : ℝ → ℂ} {L : ℝ} (hq : IsLengthParametrized D q L)
    (hw : ∀ x ∈ Icc 0 L, ξ * f (q x) ≤ B) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ L) :
    weylScaling D ξ f (q a) (q b) ≤ ENNReal.ofReal (Real.exp B) * ENNReal.ofReal (b - a) := by
  have hsub : IsLengthParametrized D (fun t => q (a + t)) (b - a) :=
    hD.isLengthParametrized_subcurve hq ha hab hb
  have h0 : (fun t => q (a + t)) 0 = q a := by simp
  have hT : (fun t => q (a + t)) (b - a) = q b := by simp
  refine iInf_le_of_le (b - a) (iInf_le_of_le (fun t => q (a + t)) (iInf_le_of_le hsub
    (iInf_le_of_le h0 (iInf_le_of_le hT ?_))))
  calc ∫⁻ t in Icc 0 (b - a), ENNReal.ofReal (Real.exp (ξ * f ((fun t => q (a + t)) t)))
      ≤ ∫⁻ _ in Icc 0 (b - a), ENNReal.ofReal (Real.exp B) := by
        refine setLIntegral_mono' measurableSet_Icc fun t ht => ?_
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        exact hw (a + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩
    _ = ENNReal.ofReal (Real.exp B) * ENNReal.ofReal (b - a) := by
        rw [setLIntegral_const, Real.volume_Icc, sub_zero]

/-- Both orientations: for `0 ≤ a ≤ b ≤ L`, `weylScaling (q a) (q b)` and `weylScaling (q b) (q a)` are at most
`e^B (b - a)`. The second follows from the first applied to the reversed curve `t ↦ q (L - t)`. -/
theorem weylScaling_le_of_subarc_both {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {ξ B : ℝ} {f : ℂ → ℝ}
    {q : ℝ → ℂ} {L : ℝ} (hq : IsLengthParametrized D q L)
    (hw : ∀ x ∈ Icc 0 L, ξ * f (q x) ≤ B) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ L) :
    weylScaling D ξ f (q a) (q b) ≤ ENNReal.ofReal (Real.exp B) * ENNReal.ofReal (b - a) ∧
      weylScaling D ξ f (q b) (q a) ≤ ENNReal.ofReal (Real.exp B) * ENNReal.ofReal (b - a) := by
  refine ⟨weylScaling_le_of_subarc hD hq hw ha hab hb, ?_⟩
  have hr : IsLengthParametrized D (fun t => q (L - t)) L := hD.isLengthParametrized_reverse hq
  have hwr : ∀ x ∈ Icc 0 L, ξ * f ((fun t => q (L - t)) x) ≤ B := fun x hx =>
    hw (L - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have h := weylScaling_le_of_subarc hD hr hwr (a := L - b) (b := L - a)
    (by linarith) (by linarith) (by linarith)
  simp only [sub_sub_cancel] at h
  rw [show L - a - (L - b) = b - a by ring] at h
  exact h

/-- Telescoping bound for partition sums: if `σ` is nondecreasing with `0 ≤ σ 0` and `σ N ≤ L`, and each term is at most
`c (σ (i+1) - σ i)`, the sum over `range N` is at most `c L`. -/
theorem sum_le_of_telescope {c : ℝ≥0∞} {σ : ℕ → ℝ} {L : ℝ} {d : ℕ → ℝ≥0∞} (N : ℕ)
    (hσ : ∀ i, σ i ≤ σ (i + 1)) (h0 : 0 ≤ σ 0) (hN : σ N ≤ L)
    (hd : ∀ i ∈ Finset.range N, d i ≤ c * ENNReal.ofReal (σ (i + 1) - σ i)) :
    ∑ i ∈ Finset.range N, d i ≤ c * ENNReal.ofReal L := by
  calc ∑ i ∈ Finset.range N, d i
      ≤ ∑ i ∈ Finset.range N, c * ENNReal.ofReal (σ (i + 1) - σ i) := Finset.sum_le_sum hd
    _ = c * ∑ i ∈ Finset.range N, ENNReal.ofReal (σ (i + 1) - σ i) := by rw [Finset.mul_sum]
    _ = c * ENNReal.ofReal (∑ i ∈ Finset.range N, (σ (i + 1) - σ i)) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => sub_nonneg.mpr (hσ i))]
    _ = c * ENNReal.ofReal (σ N - σ 0) := by rw [Finset.sum_range_sub σ N]
    _ ≤ c * ENNReal.ofReal L :=
        mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal (by linarith)) zero_le

/-- A partition bound for the `E`-length of a curve `p` on `[0, 1]` gives a bound for `curveLength E p 0 1`. -/
theorem curveLength_le_of_partition_bound {E : ℂ → ℂ → ℝ} {p : ℝ → ℂ} {M : ℝ≥0∞}
    (h : ∀ (N : ℕ) (u : ℕ → ℝ), Monotone u → (∀ i, u i ∈ Icc (0:ℝ) 1) →
      ∑ i ∈ Finset.range N, ENNReal.ofReal (E (p (u (i + 1))) (p (u i))) ≤ M) :
    curveLength E p 0 1 ≤ M := by
  unfold curveLength
  exact iSup_le fun ⟨N, u, hu, hI⟩ => h N u hu hI

/-- For a path `P` in `U`, with `E` the Weyl scaling of `D` by `f` and `ξ f ≤ B` on `U`, the `E`-length of `P` is at most
`e^B` times its `D`-length. The path is reparametrized by its `D`-arclength; each sub-arc is a competitor in `weylScaling`. -/
theorem pathLength_le_of_weylScaling {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {ξ B : ℝ} {f : ℂ → ℝ}
    {U : Set ℂ} (hscale : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y)
    (hweight : ∀ z ∈ U, ξ * f z ≤ B) {x y : ℂ} (P : Path x y) (hP : ∀ t, P t ∈ U) :
    pathLength E P ≤ ENNReal.ofReal (Real.exp B) * pathLength D P := by
  have hc0 : ENNReal.ofReal (Real.exp B) ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos B)).ne'
  unfold pathLength
  by_cases hfin : curveLength D P.extend 0 1 = ⊤
  · rw [hfin, ENNReal.mul_top hc0]
    exact le_top
  have hlt : curveLength D P.extend 0 1 < ⊤ := lt_top_iff_ne_top.mpr hfin
  have hcont : ContinuousOn P.extend (Icc 0 1) := P.continuous_extend.continuousOn
  have hPU : ∀ t ∈ Icc (0:ℝ) 1, P.extend t ∈ U := fun t ht => by
    rw [Path.extend_apply P ht]
    exact hP ⟨t, ht⟩
  obtain ⟨q, hq, -, -, htrack⟩ := hD.exists_lengthParametrized_with_tracking zero_le_one hcont hlt
  obtain ⟨-, hmono, -, himg⟩ := hD.cumulative_curveLength_properties zero_le_one hcont hlt
  have hmono' : ∀ a b : ℝ, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 → a ≤ b →
      (curveLength D P.extend 0 a).toReal ≤ (curveLength D P.extend 0 b).toReal :=
    fun a b ha hb hab => hmono ha hb hab
  -- the image of `q` on `[0, L]` is the image of `P` on `[0, 1]`, hence lies in `U`
  have hqU : ∀ x ∈ Icc (0:ℝ) (curveLength D P.extend 0 1).toReal, q x ∈ U := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := (Set.ext_iff.mp himg x).mpr hx
    show q (curveLength D P.extend 0 t).toReal ∈ U
    rw [htrack t ht]
    exact hPU t ht
  have hw : ∀ x ∈ Icc (0:ℝ) (curveLength D P.extend 0 1).toReal, ξ * f (q x) ≤ B :=
    fun x hx => hweight _ (hqU x hx)
  have hsum : ∀ (N : ℕ) (u : ℕ → ℝ), Monotone u → (∀ i, u i ∈ Icc (0:ℝ) 1) →
      ∑ i ∈ Finset.range N, ENNReal.ofReal (E (P.extend (u (i + 1))) (P.extend (u i))) ≤
        ENNReal.ofReal (Real.exp B) * ENNReal.ofReal (curveLength D P.extend 0 1).toReal := by
    intro N u hu hI
    have hσ : ∀ i, (curveLength D P.extend 0 (u i)).toReal ≤
        (curveLength D P.extend 0 (u (i + 1))).toReal :=
      fun i => hmono' _ _ (hI i) (hI (i + 1)) (hu (Nat.le_succ i))
    have hd : ∀ i ∈ Finset.range N, ENNReal.ofReal (E (P.extend (u (i + 1))) (P.extend (u i))) ≤
        ENNReal.ofReal (Real.exp B) *
          ENNReal.ofReal ((curveLength D P.extend 0 (u (i + 1))).toReal -
            (curveLength D P.extend 0 (u i)).toReal) := by
      intro i _
      have hL : (curveLength D P.extend 0 (u (i + 1))).toReal ≤
          (curveLength D P.extend 0 1).toReal :=
        hmono' _ _ (hI (i + 1)) (right_mem_Icc.mpr zero_le_one) (hI (i + 1)).2
      rw [hscale, ← htrack (u (i + 1)) (hI (i + 1)), ← htrack (u i) (hI i)]
      exact (weylScaling_le_of_subarc_both hD hq hw ENNReal.toReal_nonneg (hσ i) hL).2
    have hN : (curveLength D P.extend 0 (u N)).toReal ≤ (curveLength D P.extend 0 1).toReal :=
      hmono' _ _ (hI N) (right_mem_Icc.mpr zero_le_one) (hI N).2
    exact sum_le_of_telescope (σ := fun i => (curveLength D P.extend 0 (u i)).toReal) N hσ
      ENNReal.toReal_nonneg hN hd
  calc curveLength E P.extend 0 1
      ≤ ENNReal.ofReal (Real.exp B) * ENNReal.ofReal (curveLength D P.extend 0 1).toReal :=
        curveLength_le_of_partition_bound (fun N u hu hI => hsum N u hu hI)
    _ = ENNReal.ofReal (Real.exp B) * curveLength D P.extend 0 1 := by
        rw [ENNReal.ofReal_toReal hfin]


/-- The closed-set Weyl comparison of internal metrics: for a Euclidean length metric `D`, a function `E ≥ 0` with
`ENNReal.ofReal (E x y) = weylScaling D ξ f x y`, and a closed set `U` with `ξ f ≤ B` on `U`, the internal metric of `E`
on `U` is at most `e^B` times the internal metric of `D` on `U` (Gwynne-Miller, arXiv:1905.00383, (1.8)). -/
def WeylInternalClosed : Prop :=
  ∀ (D E : ℂ → ℂ → ℝ) (ξ B : ℝ) (f : ℂ → ℝ) (U : Set ℂ), IsEuclideanLengthMetric D →
    (∀ x y, 0 ≤ E x y) → (∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y) → IsClosed U →
    (∀ z ∈ U, ξ * f z ≤ B) → ∀ x y, internalMetric E U x y ≤ ENNReal.ofReal (Real.exp B) * internalMetric D U x y

/-- **Derived**: the closed-set Weyl comparison `WeylInternalClosed` holds, with no hypothesis added. -/
theorem weylInternalClosed_derived : WeylInternalClosed := by
  intro D E ξ B f U hD _hEnn hscale _hclosed hweight x y
  have hc0 : ENNReal.ofReal (Real.exp B) ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos B)).ne'
  have hctop : ENNReal.ofReal (Real.exp B) ≠ ⊤ := ENNReal.ofReal_ne_top
  unfold internalMetric
  calc ⨅ (P : Path x y) (_ : ∀ t, P t ∈ U), pathLength E P
      ≤ ⨅ (P : Path x y) (_ : ∀ t, P t ∈ U), ENNReal.ofReal (Real.exp B) * pathLength D P :=
        le_iInf₂ fun P hP => (iInf₂_le P hP).trans (pathLength_le_of_weylScaling hD hscale hweight P hP)
    _ = ENNReal.ofReal (Real.exp B) * ⨅ (P : Path x y) (_ : ∀ t, P t ∈ U), pathLength D P := by
        simp only [ENNReal.mul_iInf_of_ne hc0 hctop]


end LatticeProb.LQG
