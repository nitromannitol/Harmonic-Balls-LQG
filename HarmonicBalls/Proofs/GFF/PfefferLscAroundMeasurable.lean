import HarmonicBalls.Proofs.GFF.PfefferAroundJointMeasurable

/-! # Around distances for lower semicontinuous distance fields

For a jointly measurable family of lower semicontinuous distance functions
on a Polish parameter space, the unrestricted around distance is universally
measurable jointly in the parameter and annular data.
-/

namespace HarmonicBalls

open Set MeasureTheory
open scoped unitInterval ENNReal

/-- Path length is jointly measurable in a distance field and a continuous path. -/
theorem measurable_pathLength_of_joint_lowerSemicontinuous
    {Ω : Type*} [MeasurableSpace Ω] {D : Ω → ℂ → ℂ → ℝ}
    (hD : Measurable fun q : Ω × (ℂ × ℂ) => D q.1 q.2.1 q.2.2)
    (hlsc : ∀ ω, LowerSemicontinuous fun q : ℂ × ℂ => D ω q.1 q.2) :
    Measurable fun q : Ω × C(I, ℂ) =>
      pathLength (D q.1) (⟨q.2, rfl, rfl⟩ : Path (q.2 0) (q.2 1)) := by
  let T := {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc (0 : ℝ) 1}
  have : SecondCountableTopology T :=
    TopologicalSpace.secondCountableTopology_induced T (ℕ → ℝ) Subtype.val
  have key : ∀ n : ℕ, Measurable (⨆ u : T, fun q : Ω × C(I, ℂ) =>
      ∑ i ∈ Finset.range n, ENNReal.ofReal
        (D q.1 (q.2 ⟨u.1 (i + 1), u.2.2 (i + 1)⟩) (q.2 ⟨u.1 i, u.2.2 i⟩))) := by
    intro n
    refine measurable_iSup_of_lowerSemicontinuous (fun u => ?_) (fun q => ?_)
    · refine Finset.measurable_sum _ fun i _ => ?_
      exact (hD.comp (measurable_fst.prodMk
        (((continuous_eval_const (⟨u.1 (i + 1), u.2.2 (i + 1)⟩ : I)).measurable.comp measurable_snd).prodMk
          ((continuous_eval_const (⟨u.1 i, u.2.2 i⟩ : I)).measurable.comp measurable_snd)))).ennreal_ofReal
    · let p : Path (q.2 0) (q.2 1) := ⟨q.2, rfl, rfl⟩
      have hp : ∀ (u : T) (i : ℕ), p.extend (u.1 i) = q.2 ⟨u.1 i, u.2.2 i⟩ :=
        fun u i => Path.extend_apply p (u.2.2 i)
      simp_rw [← hp]
      refine lowerSemicontinuous_sum fun i _ => ?_
      have hc : Continuous fun u : T => (p.extend (u.1 (i + 1)), p.extend (u.1 i)) :=
        (p.continuous_extend.comp ((continuous_apply (i + 1)).comp continuous_subtype_val)).prodMk
          (p.continuous_extend.comp ((continuous_apply i).comp continuous_subtype_val))
      exact ENNReal.continuous_ofReal.comp_lowerSemicontinuous ((hlsc q.1).comp hc)
        (fun _ _ h => ENNReal.ofReal_le_ofReal h)
  have heq : (fun q : Ω × C(I, ℂ) =>
      pathLength (D q.1) (⟨q.2, rfl, rfl⟩ : Path (q.2 0) (q.2 1))) =
      fun q => ⨆ n : ℕ, (⨆ u : T, fun q : Ω × C(I, ℂ) =>
        ∑ i ∈ Finset.range n, ENNReal.ofReal
          (D q.1 (q.2 ⟨u.1 (i + 1), u.2.2 (i + 1)⟩) (q.2 ⟨u.1 i, u.2.2 i⟩))) q := by
    funext q
    let p : Path (q.2 0) (q.2 1) := ⟨q.2, rfl, rfl⟩
    have hp : ∀ (u : T) (i : ℕ), p.extend (u.1 i) = q.2 ⟨u.1 i, u.2.2 i⟩ :=
      fun u i => Path.extend_apply p (u.2.2 i)
    simp only [iSup_apply]
    change (⨆ v : ℕ × T, ∑ i ∈ Finset.range v.1, ENNReal.ofReal
      (D q.1 (p.extend (v.2.1 (i + 1))) (p.extend (v.2.1 i)))) = _
    simp_rw [hp]
    exact iSup_prod
  rw [heq]
  exact Measurable.iSup key

/-- Strict sublevels of the unrestricted around distance are universally
measurable for jointly measurable lower semicontinuous distance fields. -/
theorem uMeasurableSet_pfefferAround_joint_of_lowerSemicontinuous
    {Ω : Type*} [TopologicalSpace Ω] [PolishSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    {D : Ω → ℂ → ℂ → ℝ}
    (hD : Measurable fun q : Ω × (ℂ × ℂ) => D q.1 q.2.1 q.2.2)
    (hlsc : ∀ ω, LowerSemicontinuous fun q : ℂ × ℂ => D ω q.1 q.2)
    (c : ℝ≥0∞) :
    LQGMetric.UMeasurableSet {q : Ω × (ℂ × ℝ × ℝ) |
      pfefferAround (D q.1) q.2.1 q.2.2.1 q.2.2.2 < c} := by
  let : PolishSpace C(I, ℂ) := LQGMetric.polishSpace_continuousMap _ _
  let R : Set ((Ω × (ℂ × ℝ × ℝ)) × C(I, ℂ)) := {q |
    q.2 0 = q.2 1 ∧
    (∀ (x y : ℂ) (γ : Path x y), x ∈ Metric.sphere q.1.2.1 q.1.2.2.1 →
      y ∈ Metric.sphere q.1.2.1 q.1.2.2.2 → ∃ t, γ t ∈ Set.range q.2) ∧
    pathLength (D q.1.1) (⟨q.2, rfl, rfl⟩ : Path (q.2 0) (q.2 1)) < c}
  have hloop : MeasurableSet {q : (Ω × (ℂ × ℝ × ℝ)) × C(I, ℂ) |
      q.2 0 = q.2 1} := isClosed_setOf_closedPaths.measurableSet.preimage measurable_snd
  have hsep : MeasurableSet {q : (Ω × (ℂ × ℝ × ℝ)) × C(I, ℂ) |
      ∀ (x y : ℂ) (γ : Path x y), x ∈ Metric.sphere q.1.2.1 q.1.2.2.1 →
        y ∈ Metric.sphere q.1.2.1 q.1.2.2.2 → ∃ t, γ t ∈ Set.range q.2} :=
    measurableSet_pfefferSeparates_joint.preimage (measurable_snd.prodMk
      (measurable_snd.comp measurable_fst))
  have hlen : MeasurableSet {q : (Ω × (ℂ × ℝ × ℝ)) × C(I, ℂ) |
      pathLength (D q.1.1) (⟨q.2, rfl, rfl⟩ : Path (q.2 0) (q.2 1)) < c} := by
    let g : ((Ω × (ℂ × ℝ × ℝ)) × C(I, ℂ)) → Ω × C(I, ℂ) :=
      fun q => (q.1.1, q.2)
    have hg : Measurable g := (measurable_fst.comp measurable_fst).prodMk measurable_snd
    change MeasurableSet (g ⁻¹' {q : Ω × C(I, ℂ) |
      pathLength (D q.1) (⟨q.2, rfl, rfl⟩ : Path (q.2 0) (q.2 1)) < c})
    exact (measurableSet_lt (measurable_pathLength_of_joint_lowerSemicontinuous hD hlsc)
      measurable_const).preimage hg
  have hR : MeasurableSet R := hloop.inter (hsep.inter hlen)
  have hproj := LQGMetric.UMeasurableSet.setOf_exists hR
  convert hproj using 1
  ext q
  change pfefferAround (D q.1) q.2.1 q.2.2.1 q.2.2.2 < c ↔
    ∃ p : C(I, ℂ), p 0 = p 1 ∧
      (∀ (x y : ℂ) (γ : Path x y), x ∈ Metric.sphere q.2.1 q.2.2.1 →
        y ∈ Metric.sphere q.2.1 q.2.2.2 → ∃ t, γ t ∈ Set.range p) ∧
      pathLength (D q.1) (⟨p, rfl, rfl⟩ : Path (p 0) (p 1)) < c
  constructor
  · intro h
    simp only [pfefferAround, iInf_lt_iff] at h
    obtain ⟨z, P, hsepP, hlenP⟩ := h
    refine ⟨P.toContinuousMap, P.source.trans P.target.symm, hsepP, ?_⟩
    have hext : (⟨P.toContinuousMap, rfl, rfl⟩ :
        Path (P.toContinuousMap 0) (P.toContinuousMap 1)).extend = P.extend := rfl
    simpa only [pathLength, hext] using hlenP
  · rintro ⟨p, hp, hsep, hlen⟩
    let P : Path (p 0) (p 0) := ⟨p, rfl, hp.symm⟩
    have hsepP : PfefferSeparates P q.2.1 q.2.2.1 q.2.2.2 := hsep
    have hlenP : pathLength (D q.1) P < c := hlen
    exact ((iInf_le_of_le (p 0) (iInf_le_of_le P (iInf_le _ hsepP))).trans_lt hlenP)

/-- The unrestricted around distance is almost everywhere measurable for any
s-finite measure on the parameter and annular-data space. -/
theorem aemeasurable_pfefferAround_joint_of_lowerSemicontinuous
    {Ω : Type*} [TopologicalSpace Ω] [PolishSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    {D : Ω → ℂ → ℂ → ℝ}
    (hD : Measurable fun q : Ω × (ℂ × ℂ) => D q.1 q.2.1 q.2.2)
    (hlsc : ∀ ω, LowerSemicontinuous fun q : ℂ × ℂ => D ω q.1 q.2)
    (μ : Measure (Ω × (ℂ × ℝ × ℝ))) [SFinite μ] :
    AEMeasurable (fun q : Ω × (ℂ × ℝ × ℝ) =>
      pfefferAround (D q.1) q.2.1 q.2.2.1 q.2.2.2) μ := by
  have hm : @Measurable (NullMeasurableSpace (Ω × (ℂ × ℝ × ℝ)) μ) ℝ≥0∞ _ _
      (fun q => pfefferAround (D q.1) q.2.1 q.2.2.1 q.2.2.2) := by
    apply measurable_of_Iio
    intro c
    exact (uMeasurableSet_pfefferAround_joint_of_lowerSemicontinuous hD hlsc c).nullMeasurableSet μ
  exact (show NullMeasurable _ μ from hm).aemeasurable

end HarmonicBalls
