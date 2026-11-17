import HarmonicBalls.Proofs.GFF.PfefferCrossingJointMeasurable

/-! # Joint separation of annular boundaries

The exact separation relation is closed for nonnegative radii and measurable
for arbitrary radii, jointly in the path and annular parameters.
-/

namespace HarmonicBalls

open Set Filter MeasureTheory
open scoped unitInterval ENNReal

/-- Separation of two circles is closed jointly in the path and the center and
nonnegative radii. -/
theorem isClosed_setOf_pfefferSeparates_joint_nonneg :
    IsClosed {q : C(I, ℂ) × (ℂ × ℝ × ℝ) |
      0 ≤ q.2.2.1 ∧ 0 ≤ q.2.2.2 ∧
      ∀ (x y : ℂ) (γ : Path x y), x ∈ Metric.sphere q.2.1 q.2.2.1 →
        y ∈ Metric.sphere q.2.1 q.2.2.2 → ∃ t, γ t ∈ Set.range q.1} := by
  let S : Set (C(I, ℂ) × (ℂ × ℝ × ℝ)) := {q |
      0 ≤ q.2.2.1 ∧ 0 ≤ q.2.2.2 ∧
      ∀ (x y : ℂ) (γ : Path x y), x ∈ Metric.sphere q.2.1 q.2.2.1 →
        y ∈ Metric.sphere q.2.1 q.2.2.2 → ∃ t, γ t ∈ Set.range q.1}
  change IsClosed S
  apply isClosed_of_closure_subset
  intro q hq
  have ha : 0 ≤ q.2.2.1 :=
    (isClosed_le continuous_const (continuous_fst.comp (continuous_snd.comp continuous_snd))).closure_subset_iff.mpr
      (fun _ h => h.1) hq
  have hb : 0 ≤ q.2.2.2 :=
    (isClosed_le continuous_const (continuous_snd.comp (continuous_snd.comp continuous_snd))).closure_subset_iff.mpr
      (fun _ h => h.2.1) hq
  refine ⟨ha, hb, ?_⟩
  intro x y γ hx hy
  obtain ⟨f, hf, hfx, hfsphere⟩ := exists_continuous_sphere_selection hx
  obtain ⟨g, hg, hgy, hgsphere⟩ := exists_continuous_sphere_selection hy
  let F : (C(I, ℂ) × (ℂ × ℝ × ℝ)) × (I × I) → ℂ := fun v =>
    γ v.2.1 + (1 - (v.2.1 : ℝ)) • (f (v.1.2.1, v.1.2.2.1) - x) +
      (v.2.1 : ℝ) • (g (v.1.2.1, v.1.2.2.2) - y)
  have hF : Continuous F := by
    dsimp only [F]
    fun_prop
  have hclosed : IsClosed {v : (C(I, ℂ) × (ℂ × ℝ × ℝ)) × (I × I) |
      F v = v.1.1 v.2.2} := by
    apply isClosed_eq hF
    exact (continuous_fst.comp continuous_fst).eval (continuous_snd.comp continuous_snd)
  have hproj : IsClosed {v : C(I, ℂ) × (ℂ × ℝ × ℝ) |
      ∃ t s : I, F (v, (t, s)) = v.1 s} := by
    have h := isClosedMap_fst_of_compactSpace _ hclosed
    convert h using 1
    ext v
    constructor
    · rintro ⟨t, s, hs⟩
      exact ⟨(v, (t, s)), hs, rfl⟩
    · rintro ⟨⟨v', t, s⟩, hs, hv⟩
      cases hv
      exact ⟨t, s, hs⟩
  have hsub : S ⊆ {v : C(I, ℂ) × (ℂ × ℝ × ℝ) |
      ∃ t s : I, F (v, (t, s)) = v.1 s} := by
    intro v hv
    let X := f (v.2.1, v.2.2.1)
    let Y := g (v.2.1, v.2.2.2)
    let G : Path X Y := {
      toFun := fun t => γ t + (1 - (t : ℝ)) • (X - x) + (t : ℝ) • (Y - y)
      continuous_toFun := by fun_prop
      source' := by simp [X]
      target' := by simp [Y] }
    obtain ⟨t, s, hs⟩ := hv.2.2 X Y G (hfsphere _ _ hv.1) (hgsphere _ _ hv.2.1)
    exact ⟨t, s, hs.symm⟩
  obtain ⟨t, s, hs⟩ := hproj.closure_subset_iff.mpr hsub hq
  refine ⟨t, s, ?_⟩
  simpa only [F, hfx, hgy, sub_self, smul_zero, add_zero] using hs.symm

/-- Separation is jointly Borel measurable for arbitrary real radii. -/
theorem measurableSet_pfefferSeparates_joint :
    MeasurableSet {q : C(I, ℂ) × (ℂ × ℝ × ℝ) |
      ∀ (x y : ℂ) (γ : Path x y), x ∈ Metric.sphere q.2.1 q.2.2.1 →
        y ∈ Metric.sphere q.2.1 q.2.2.2 → ∃ t, γ t ∈ Set.range q.1} := by
  let N : Set (C(I, ℂ) × (ℂ × ℝ × ℝ)) :=
    {q | q.2.2.1 < 0 ∨ q.2.2.2 < 0}
  let S : Set (C(I, ℂ) × (ℂ × ℝ × ℝ)) := {q |
      0 ≤ q.2.2.1 ∧ 0 ≤ q.2.2.2 ∧
      ∀ (x y : ℂ) (γ : Path x y), x ∈ Metric.sphere q.2.1 q.2.2.1 →
        y ∈ Metric.sphere q.2.1 q.2.2.2 → ∃ t, γ t ∈ Set.range q.1}
  have hN : MeasurableSet N := by
    change MeasurableSet ({q : C(I, ℂ) × (ℂ × ℝ × ℝ) | q.2.2.1 < 0} ∪
      {q : C(I, ℂ) × (ℂ × ℝ × ℝ) | q.2.2.2 < 0})
    apply MeasurableSet.union <;> apply measurableSet_lt <;> fun_prop
  have hS : MeasurableSet S := isClosed_setOf_pfefferSeparates_joint_nonneg.measurableSet
  convert hN.union hS using 1
  ext q
  simp only [mem_union, mem_ofPred_eq, N, S]
  constructor
  · intro h
    by_cases ha : q.2.2.1 < 0
    · exact Or.inl (Or.inl ha)
    by_cases hb : q.2.2.2 < 0
    · exact Or.inl (Or.inr hb)
    · exact Or.inr ⟨le_of_not_gt ha, le_of_not_gt hb, h⟩
  · rintro ((ha | hb) | ⟨_, _, h⟩)
    · intro x y γ hx hy
      rw [Metric.sphere_eq_empty_of_neg ha] at hx
      exact hx.elim
    · intro x y γ hx hy
      rw [Metric.sphere_eq_empty_of_neg hb] at hy
      exact hy.elim
    · exact h

private def aroundJointRelation (c : ℝ≥0∞) :
    Set ((C(ℂ × ℂ, ℝ) × (ℂ × ℝ × ℝ)) × C(I, ℂ)) := {q |
    q.2 0 = q.2 1 ∧
    (∀ (x y : ℂ) (γ : Path x y), x ∈ Metric.sphere q.1.2.1 q.1.2.2.1 →
      y ∈ Metric.sphere q.1.2.1 q.1.2.2.2 → ∃ t, γ t ∈ Set.range q.2) ∧
    pathLength (fun x y => q.1.1 (x, y))
      (⟨q.2, rfl, rfl⟩ : Path (q.2 0) (q.2 1)) < c}

private theorem measurableSet_joint_pathLength_lt (c : ℝ≥0∞) :
    MeasurableSet {q : (C(ℂ × ℂ, ℝ) × (ℂ × ℝ × ℝ)) × C(I, ℂ) |
      pathLength (fun x y => q.1.1 (x, y))
        (⟨q.2, rfl, rfl⟩ : Path (q.2 0) (q.2 1)) < c} := by
  let g : ((C(ℂ × ℂ, ℝ) × (ℂ × ℝ × ℝ)) × C(I, ℂ)) →
      C(ℂ × ℂ, ℝ) × C(I, ℂ) := fun q => (q.1.1, q.2)
  have hg : Measurable g := (measurable_fst.comp measurable_fst).prodMk measurable_snd
  change MeasurableSet (g ⁻¹' {q : C(ℂ × ℂ, ℝ) × C(I, ℂ) |
      pathLength (fun x y => q.1 (x, y))
        (⟨q.2, rfl, rfl⟩ : Path (q.2 0) (q.2 1)) < c})
  exact (measurableSet_lt lowerSemicontinuous_pathLength.measurable measurable_const).preimage hg

private theorem measurableSet_aroundJointRelation (c : ℝ≥0∞) :
    MeasurableSet (aroundJointRelation c) := by
  have hloop : MeasurableSet {q : (C(ℂ × ℂ, ℝ) × (ℂ × ℝ × ℝ)) × C(I, ℂ) |
      q.2 0 = q.2 1} := isClosed_setOf_closedPaths.measurableSet.preimage measurable_snd
  have hsep : MeasurableSet {q : (C(ℂ × ℂ, ℝ) × (ℂ × ℝ × ℝ)) × C(I, ℂ) |
      ∀ (x y : ℂ) (γ : Path x y), x ∈ Metric.sphere q.1.2.1 q.1.2.2.1 →
        y ∈ Metric.sphere q.1.2.1 q.1.2.2.2 → ∃ t, γ t ∈ Set.range q.2} :=
    measurableSet_pfefferSeparates_joint.preimage (measurable_snd.prodMk
      (measurable_snd.comp measurable_fst))
  have hlen := measurableSet_joint_pathLength_lt c
  exact hloop.inter (hsep.inter hlen)

/-- Strict sublevels of the unrestricted around observable are universally
measurable jointly in the distance function, center and radii. -/
theorem uMeasurableSet_pfefferAround_joint_lt (c : ℝ≥0∞) :
    LQGMetric.UMeasurableSet {q : C(ℂ × ℂ, ℝ) × (ℂ × ℝ × ℝ) |
      pfefferAround (fun x y => q.1 (x, y)) q.2.1 q.2.2.1 q.2.2.2 < c} := by
  let : PolishSpace C(ℂ × ℂ, ℝ) := LQGMetric.polishSpace_continuousMap _ _
  let : PolishSpace C(I, ℂ) := LQGMetric.polishSpace_continuousMap _ _
  have hproj := LQGMetric.UMeasurableSet.setOf_exists (measurableSet_aroundJointRelation c)
  convert hproj using 1
  ext q
  change pfefferAround (fun x y => q.1 (x, y)) q.2.1 q.2.2.1 q.2.2.2 < c ↔
    ∃ p : C(I, ℂ), p 0 = p 1 ∧
      (∀ (x y : ℂ) (γ : Path x y), x ∈ Metric.sphere q.2.1 q.2.2.1 →
        y ∈ Metric.sphere q.2.1 q.2.2.2 → ∃ t, γ t ∈ Set.range p) ∧
      pathLength (fun x y => q.1 (x, y)) (⟨p, rfl, rfl⟩ : Path (p 0) (p 1)) < c
  constructor
  · intro h
    simp only [pfefferAround, iInf_lt_iff] at h
    obtain ⟨z, P, hsepP, hlenP⟩ := h
    refine ⟨P.toContinuousMap, ?_, hsepP, ?_⟩
    · exact P.source.trans P.target.symm
    · have hext : (⟨P.toContinuousMap, rfl, rfl⟩ :
          Path (P.toContinuousMap 0) (P.toContinuousMap 1)).extend = P.extend := rfl
      simpa only [pathLength, hext] using hlenP
  · rintro ⟨p, hp, hsep, hlen⟩
    let P : Path (p 0) (p 0) := ⟨p, rfl, hp.symm⟩
    have hsepP : PfefferSeparates P q.2.1 q.2.2.1 q.2.2.2 := hsep
    have hlenP : pathLength (fun x y => q.1 (x, y)) P < c := hlen
    exact ((iInf_le_of_le (p 0) (iInf_le_of_le P (iInf_le _ hsepP))).trans_lt hlenP)

/-- Pointwise almost everywhere measurable Euclidean length metrics have an
almost everywhere measurable unrestricted around observable jointly with the
center and radii. -/
theorem aemeasurable_pfefferAround_joint_of_ae_pointwise
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
    (ν : Measure (ℂ × ℝ × ℝ)) [SFinite ν] {D : Ω → ℂ → ℂ → ℝ}
    (hpoint : ∀ x y, AEMeasurable (fun ω => D ω x y) P)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω)) :
    AEMeasurable (fun q : Ω × (ℂ × ℝ × ℝ) =>
      pfefferAround (D q.1) q.2.1 q.2.2.1 q.2.2.2) (P.prod ν) := by
  obtain ⟨F, hF, _, hFeq⟩ := exists_measurable_continuousMap_of_ae_pointwise hpoint hmetric
  have hm : @Measurable (NullMeasurableSpace (Ω × (ℂ × ℝ × ℝ)) (P.prod ν)) ℝ≥0∞ _ _
      (fun q => pfefferAround (fun x y => F q.1 (x, y)) q.2.1 q.2.2.1 q.2.2.2) := by
    apply measurable_of_Iio
    intro c
    exact ((uMeasurableSet_pfefferAround_joint_lt c).preimage
      ((hF.comp measurable_fst).prodMk measurable_snd)).nullMeasurableSet (P.prod ν)
  have hae : AEMeasurable
      (fun q : Ω × (ℂ × ℝ × ℝ) =>
        pfefferAround (fun x y => F q.1 (x, y)) q.2.1 q.2.2.1 q.2.2.2) (P.prod ν) :=
    (show NullMeasurable _ (P.prod ν) from hm).aemeasurable
  apply hae.congr
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P) (ν := ν)).ae hFeq] with q hq
  have heq : (fun x y => F q.1 (x, y)) = D q.1 := by
    funext x y
    exact hq x y
  rw [heq]

end HarmonicBalls
