import HarmonicBalls.Steps.Sec11.WeylPathReverse

/-! # Concatenation of length-parametrized curves

The identities below provide the variation calculations for joining two
length-parametrized curves at their common endpoint.
-/

namespace HarmonicBalls

open MeasureTheory Set
open scoped ENNReal

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

/-- Curve length is additive across adjacent intervals. -/
theorem IsEuclideanLengthMetric.curveLength_add
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (p : ℝ → ℂ) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    curveLength D p a b + curveLength D p b c = curveLength D p a c := by
  let : MetricSpace ConcatLengthPoint := {
    dist := fun x y => D x.val y.val
    dist_self := fun x => hD.self_eq_zero x.val
    dist_comm := fun x y => hD.symm x.val y.val
    dist_triangle := fun x y z => hD.triangle x.val y.val z.val
    eq_of_dist_eq_zero := by
      intro ⟨u⟩ ⟨v⟩ h
      exact congrArg ConcatLengthPoint.mk (hD.eq_of_eq_zero u v h) }
  have hcurve (s t : ℝ) :
      curveLength D p s t = eVariationOn (fun r => (⟨p r⟩ : ConcatLengthPoint)) (Icc s t) := by
    simp only [curveLength, eVariationOn, edist_dist]
    rfl
  rw [hcurve, hcurve, hcurve]
  simpa only [univ_inter] using eVariationOn.Icc_add_Icc
    (fun r => (⟨p r⟩ : ConcatLengthPoint)) (s := univ) hab hbc (mem_univ b)

/-- Joining two length-parametrized curves preserves length parametrization,
provided the joined curve is continuous at the junction. -/
theorem IsEuclideanLengthMetric.isLengthParametrized_concat
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {p q r : ℝ → ℂ} {T S : ℝ}
    (hp : IsLengthParametrized D p T) (hq : IsLengthParametrized D q S)
    (hr : ContinuousOn r (Icc 0 (T + S)))
    (hleft : EqOn r p (Icc 0 T))
    (hright : EqOn r (fun t => q (t - T)) (Icc T (T + S))) :
    IsLengthParametrized D r (T + S) := by
  refine ⟨add_nonneg hp.1 hq.1, hr, ?_⟩
  intro a b ha hab hb
  by_cases hbT : b ≤ T
  · rw [curveLength_eq_of_eqOn (hleft.mono (Icc_subset_Icc ha hbT))]
    exact hp.2.2 a b ha hab hbT
  · by_cases haT : T ≤ a
    · rw [curveLength_eq_of_eqOn (hright.mono (Icc_subset_Icc haT hb)),
        hD.curveLength_translate]
      have h := hq.2.2 (a - T) (b - T) (by linarith) (by linarith) (by linarith)
      convert h using 1; congr 1; ring
    · have haT' : a ≤ T := le_of_not_ge haT
      have hTb : T ≤ b := le_of_not_ge hbT
      rw [← hD.curveLength_add r haT' hTb,
        curveLength_eq_of_eqOn (hleft.mono (Icc_subset_Icc ha le_rfl)),
        curveLength_eq_of_eqOn (hright.mono (Icc_subset_Icc le_rfl hb)),
        hD.curveLength_translate,
        hp.2.2 a T ha haT' le_rfl]
      have h := hq.2.2 (T - T) (b - T) (by linarith) (by linarith) (by linarith)
      rw [h, ← ENNReal.ofReal_add (by linarith : 0 ≤ T - a)]
      congr 1
      ring
      all_goals linarith

/-- Two continuous curves with a common endpoint have a continuous
concatenation parametrized by the sum of their durations. -/
theorem continuousOn_length_concat {p q : ℝ → ℂ} {T S : ℝ}
    (hp : ContinuousOn p (Icc 0 T)) (hq : ContinuousOn q (Icc 0 S))
    (hT : 0 ≤ T) (hS : 0 ≤ S) (hjoin : p T = q 0) :
    ContinuousOn (fun t => if t ≤ T then p t else q (t - T)) (Icc 0 (T + S)) := by
  let r : ℝ → ℂ := fun t => if t ≤ T then p t else q (t - T)
  have hleft : EqOn r p (Icc 0 T) := by
    intro t ht
    simp only [r, ite_eq_left ht.2]
  have hright : EqOn r (fun t => q (t - T)) (Icc T (T + S)) := by
    intro t ht
    by_cases htT : t ≤ T
    · have heq : t = T := le_antisymm htT ht.1
      subst t
      simpa [r] using hjoin
    · simp only [r, ite_eq_right htT]
  have hleftcont : ContinuousOn r (Icc 0 T) := hp.congr hleft
  have hrightcont : ContinuousOn r (Icc T (T + S)) := by
    apply (hq.comp (continuous_id.sub continuous_const).continuousOn ?_).congr hright
    intro t ht
    change 0 ≤ t - T ∧ t - T ≤ S
    constructor <;> linarith [ht.1, ht.2]
  have hunion : Icc (0 : ℝ) T ∪ Icc T (T + S) = Icc 0 (T + S) :=
    Icc_union_Icc_eq_Icc hT (by linarith)
  rw [← hunion]
  exact hleftcont.union_of_isClosed hrightcont isClosed_Icc isClosed_Icc

/-- The usual time concatenation of two length-parametrized curves is
length-parametrized when their endpoints agree. -/
theorem IsEuclideanLengthMetric.isLengthParametrized_piecewise_concat
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {p q : ℝ → ℂ} {T S : ℝ}
    (hp : IsLengthParametrized D p T) (hq : IsLengthParametrized D q S)
    (hjoin : p T = q 0) :
    IsLengthParametrized D (fun t => if t ≤ T then p t else q (t - T)) (T + S) := by
  apply hD.isLengthParametrized_concat hp hq
    (continuousOn_length_concat hp.2.1 hq.2.1 hp.1 hq.1 hjoin)
  · intro t ht
    simp only [ite_eq_left ht.2]
  · intro t ht
    by_cases htT : t ≤ T
    · have heq : t = T := le_antisymm htT ht.1
      subst t
      simpa using hjoin
    · simp only [ite_eq_right htT]

/-- Lebesgue integration on an interval is invariant under translation. -/
theorem lintegral_Icc_translate (F : ℝ → ℝ≥0∞) (T S : ℝ) :
    (∫⁻ t in Icc T (T + S), F (t - T)) = ∫⁻ t in Icc (0 : ℝ) S, F t := by
  have hpre : (fun t : ℝ => t - T) ⁻¹' Icc (0 : ℝ) S = Icc T (T + S) := by
    ext t
    simp only [mem_preimage, mem_Icc]
    constructor <;> intro ht <;> constructor <;> linarith [ht.1, ht.2]
  have hemb : MeasurableEmbedding (fun t : ℝ => t - T) :=
    (Homeomorph.subRight T).measurableEmbedding
  have hpres : MeasurePreserving (fun t : ℝ => t - T) volume volume := by
    simpa only [sub_eq_add_neg] using measurePreserving_add_right (volume : Measure ℝ) (-T)
  have hm := hpres.restrict_preimage_emb hemb (Icc (0 : ℝ) S)
  rw [hpre] at hm
  exact hm.lintegral_comp_emb hemb F

/-- The weighted cost of a concatenation is bounded by the sum of the two
costs. No measurability assumption on the weight is required. -/
theorem lintegral_length_concat_le (F : ℂ → ℝ≥0∞) (p q : ℝ → ℂ) {T S : ℝ}
    (hT : 0 ≤ T) (hS : 0 ≤ S) (hjoin : p T = q 0) :
    (∫⁻ t in Icc 0 (T + S), F (if t ≤ T then p t else q (t - T))) ≤
      (∫⁻ t in Icc 0 T, F (p t)) + ∫⁻ t in Icc 0 S, F (q t) := by
  let r : ℝ → ℂ := fun t => if t ≤ T then p t else q (t - T)
  have hleft : ∀ t ∈ Icc (0 : ℝ) T, F (r t) = F (p t) := by
    intro t ht
    simp only [r, ite_eq_left ht.2]
  have hright : ∀ t ∈ Icc T (T + S), F (r t) = F (q (t - T)) := by
    intro t ht
    by_cases htT : t ≤ T
    · have heq : t = T := le_antisymm htT ht.1
      subst t
      simp only [r, le_refl, ite_true, sub_self, hjoin]
    · simp only [r, ite_eq_right htT]
  have hunion : Icc (0 : ℝ) T ∪ Icc T (T + S) = Icc 0 (T + S) :=
    Icc_union_Icc_eq_Icc hT (by linarith)
  change (∫⁻ t in Icc 0 (T + S), F (r t)) ≤ _
  rw [← hunion]
  calc
    (∫⁻ t in Icc (0 : ℝ) T ∪ Icc T (T + S), F (r t)) ≤
        (∫⁻ t in Icc 0 T, F (r t)) + ∫⁻ t in Icc T (T + S), F (r t) :=
      lintegral_union_le _ _ _
    _ = (∫⁻ t in Icc 0 T, F (p t)) + ∫⁻ t in Icc T (T + S), F (q (t - T)) := by
      rw [setLIntegral_congr_fun measurableSet_Icc hleft,
        setLIntegral_congr_fun measurableSet_Icc hright]
    _ = _ := by
      congr 1
      exact lintegral_Icc_translate (fun t => F (q t)) T S

/-- Weyl scaling of a length metric satisfies the triangle inequality for
arbitrary weights, including weights for which path costs can be infinite. -/
theorem IsEuclideanLengthMetric.weylScaling_triangle
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (ξ : ℝ) (f : ℂ → ℝ) (x y z : ℂ) :
    weylScaling D ξ f x z ≤ weylScaling D ξ f x y + weylScaling D ξ f y z := by
  simp only [weylScaling, ENNReal.iInf_add, ENNReal.add_iInf]
  refine le_iInf fun S => le_iInf fun q => le_iInf fun hq => le_iInf fun hq0 =>
    le_iInf fun hqS => le_iInf fun T => le_iInf fun p => le_iInf fun hp =>
    le_iInf fun hp0 => le_iInf fun hpT => ?_
  have hjoin : p T = q 0 := hpT.trans hq0.symm
  let r : ℝ → ℂ := fun t => if t ≤ T then p t else q (t - T)
  have hr := hD.isLengthParametrized_piecewise_concat hp hq hjoin
  have hr0 : r 0 = x := by
    simpa only [r, ite_eq_left hp.1] using hp0
  have hrend : r (T + S) = z := by
    by_cases hS : S = 0
    · subst S
      simpa [r] using hpT.trans (hq0.symm.trans hqS)
    · have hSpos : 0 < S := lt_of_le_of_ne hq.1 (Ne.symm hS)
      have hTS : ¬T + S ≤ T := by linarith
      simp only [r, ite_eq_right hTS, add_sub_cancel_left, hqS]
  calc
    _ ≤ ∫⁻ t in Icc 0 (T + S), ENNReal.ofReal (Real.exp (ξ * f (r t))) :=
      (iInf₂_le (T + S) r).trans ((iInf₂_le hr hr0).trans (iInf_le _ hrend))
    _ ≤ _ := lintegral_length_concat_le (fun u => ENNReal.ofReal (Real.exp (ξ * f u)))
      p q hp.1 hq.1 hjoin

end HarmonicBalls
