import HarmonicBalls.Proposed.PfefferMetricScaling
import Mathlib.Topology.Maps.Proper.Basic
import HarmonicBalls.Steps.Sec11.ProperMetricDyadic
import HarmonicBalls.Steps.Sec11.CurveLengthReparam
import LatticeProb.Bonanno.LQGMetric.Meas.UM
import LatticeProb.Bonanno.LQGMetric.Prob.PolishContinuousMap

/-! # Measurability of distances around annuli

The separation condition is closed in the space of continuous paths. The
unrestricted around observable has universally measurable strict sublevels,
so it is almost everywhere measurable for random continuous metrics.
-/

namespace HarmonicBalls

open Set Filter
open scoped unitInterval Topology ENNReal

/-- Continuous maps whose ranges meet a fixed closed set form a closed set. -/
theorem isClosed_setOf_range_inter_nonempty (F : Set ℂ) (hF : IsClosed F) :
    IsClosed {p : C(I, ℂ) | ∃ t, p t ∈ F} := by
  have hclosed : IsClosed {q : C(I, ℂ) × I | q.1 q.2 ∈ F} :=
    hF.preimage continuous_eval
  have hproj := isClosedMap_fst_of_compactSpace _ hclosed
  convert hproj using 1
  ext p
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨(p, t), ht, rfl⟩
  · rintro ⟨⟨q, t⟩, ht, hq⟩
    cases hq
    exact ⟨t, ht⟩

/-- The exact separation condition is closed among continuous maps. -/
theorem isClosed_setOf_pfefferSeparates (center : ℂ) (a b : ℝ) :
    IsClosed {p : C(I, ℂ) | ∀ (x y : ℂ) (γ : Path x y),
      x ∈ Metric.sphere center a → y ∈ Metric.sphere center b →
        ∃ t, γ t ∈ Set.range p} := by
  simp_rw [Set.ofPred_forall]
  apply isClosed_iInter
  intro x
  apply isClosed_iInter
  intro y
  apply isClosed_iInter
  intro γ
  apply isClosed_iInter
  intro hx
  apply isClosed_iInter
  intro hy
  have hγ : IsClosed (Set.range γ) := (isCompact_range γ.continuous).isClosed
  convert isClosed_setOf_range_inter_nonempty (Set.range γ) hγ using 1
  ext p
  simp only [mem_ofPred_eq, mem_range]
  constructor
  · rintro ⟨t, s, h⟩
    exact ⟨s, t, h.symm⟩
  · rintro ⟨t, s, h⟩
    exact ⟨s, t, h.symm⟩

/-- A limit of separating loops separates, even when their basepoints vary. -/
theorem pfefferSeparates_of_tendsto
    {ι : Type*} {l : Filter ι} [NeBot l] {z : ι → ℂ}
    {p : ∀ i, Path (z i) (z i)} {z₀ : ℂ} {p₀ : Path z₀ z₀}
    {center : ℂ} {a b : ℝ}
    (hp : Tendsto (fun i => (p i).toContinuousMap) l (𝓝 p₀.toContinuousMap))
    (hsep : ∀ᶠ i in l, PfefferSeparates (p i) center a b) :
    PfefferSeparates p₀ center a b := by
  exact (isClosed_setOf_pfefferSeparates center a b).mem_of_tendsto hp hsep

/-- The closed maps in the path space form a closed set. -/
theorem isClosed_setOf_closedPaths : IsClosed {p : C(I, ℂ) | p 0 = p 1} :=
  isClosed_eq (continuous_eval_const 0) (continuous_eval_const 1)

/-- Path length is lower semicontinuous jointly in a continuous distance
function and a continuous path. -/
theorem lowerSemicontinuous_pathLength :
    LowerSemicontinuous (fun q : C(ℂ × ℂ, ℝ) × C(I, ℂ) =>
      pathLength (fun x y => q.1 (x, y))
        (⟨q.2, rfl, rfl⟩ : Path (q.2 0) (q.2 1))) := by
  change LowerSemicontinuous (fun q : C(ℂ × ℂ, ℝ) × C(I, ℂ) =>
    ⨆ v : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc (0 : ℝ) 1},
      ∑ i ∈ Finset.range v.1, ENNReal.ofReal
        (q.1 ((⟨q.2, rfl, rfl⟩ : Path (q.2 0) (q.2 1)).extend (v.2.1 (i + 1)),
          (⟨q.2, rfl, rfl⟩ : Path (q.2 0) (q.2 1)).extend (v.2.1 i))))
  apply lowerSemicontinuous_iSup
  intro v
  apply Continuous.lowerSemicontinuous
  apply continuous_finsetSum
  intro i hi
  simp only [Path.extend_apply _ (v.2.2.2 (i + 1)), Path.extend_apply _ (v.2.2.2 i)]
  apply ENNReal.continuous_ofReal.comp
  exact continuous_fst.eval
    (((continuous_eval_const (⟨v.2.1 (i + 1), v.2.2.2 (i + 1)⟩ : I)).comp continuous_snd).prodMk
      ((continuous_eval_const (⟨v.2.1 i, v.2.2.2 i⟩ : I)).comp continuous_snd))

/-- For a compact family of paths, the existence of a separating closed path
of bounded length is a closed condition on the distance function. -/
theorem isClosed_setOf_exists_separating_pathLength_le
    (K : Set C(I, ℂ)) (hK : IsCompact K) (center : ℂ) (a b : ℝ) (c : ℝ≥0∞) :
    IsClosed {d : C(ℂ × ℂ, ℝ) | ∃ p ∈ K, p 0 = p 1 ∧
      (∀ (x y : ℂ) (γ : Path x y), x ∈ Metric.sphere center a →
        y ∈ Metric.sphere center b → ∃ t, γ t ∈ Set.range p) ∧
      pathLength (fun x y => d (x, y)) (⟨p, rfl, rfl⟩ : Path (p 0) (p 1)) ≤ c} := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let g : C(ℂ × ℂ, ℝ) × K → C(ℂ × ℂ, ℝ) × C(I, ℂ) :=
    fun q => (q.1, q.2.1)
  have hg : Continuous g := continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hlen := (lowerSemicontinuous_pathLength.isClosed_preimage c).preimage hg
  have hloop : IsClosed {q : C(ℂ × ℂ, ℝ) × K | q.2.1 0 = q.2.1 1} :=
    isClosed_setOf_closedPaths.preimage (continuous_subtype_val.comp continuous_snd)
  have hsep : IsClosed {q : C(ℂ × ℂ, ℝ) × K | ∀ (x y : ℂ) (γ : Path x y),
      x ∈ Metric.sphere center a → y ∈ Metric.sphere center b →
        ∃ t, γ t ∈ Set.range q.2.1} :=
    (isClosed_setOf_pfefferSeparates center a b).preimage
      (continuous_subtype_val.comp continuous_snd)
  have hproj := isClosedMap_fst_of_compactSpace _ (hloop.inter (hsep.inter hlen))
  convert hproj using 1
  ext d
  constructor
  · rintro ⟨p, hpK, hpl, hps, hpb⟩
    exact ⟨(d, ⟨p, hpK⟩), ⟨hpl, hps, hpb⟩, rfl⟩
  · rintro ⟨⟨d', p⟩, ⟨hpl, hps, hpb⟩, hd⟩
    cases hd
    exact ⟨p.1, p.2, hpl, hps, hpb⟩

/-- A pointwise measurable almost surely Euclidean length metric has a
measurable continuous-map representative that is everywhere a Euclidean length
metric and agrees with the original at every pair of points almost surely. -/
theorem exists_measurable_continuousMap_of_ae_euclideanLengthMetric
    {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} {D : Ω → ℂ → ℂ → ℝ}
    (hD : ∀ x y, Measurable fun ω => D ω x y)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω)) :
    ∃ F : Ω → C(ℂ × ℂ, ℝ), Measurable F ∧
      (∀ ω, IsEuclideanLengthMetric fun x y => F ω (x, y)) ∧
      ∀ᵐ ω ∂P, ∀ x y, F ω (x, y) = D ω x y := by
  classical
  let H : Set Ω := {ω | IsEuclideanLengthMetric (D ω)}
  have hH : MeasureTheory.NullMeasurableSet H P := by
    apply (MeasureTheory.nullMeasurableSet_univ (μ := P)).congr
    filter_upwards [hmetric] with ω hω
    simp only [mem_univ, H, mem_ofPred_eq, hω]
  obtain ⟨G, hsub, hG, hGeq⟩ := hH.exists_measurable_subset_ae_eq
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    filter_upwards [hGeq, hmetric] with ω heq hω
    exact Eq.mpr heq hω
  let D' : Ω → ℂ → ℂ → ℝ := fun ω x y => if ω ∈ G then D ω x y else dist x y
  have hD'metric : ∀ ω, IsEuclideanLengthMetric (D' ω) := by
    intro ω
    by_cases hω : ω ∈ G
    · have hωmetric : IsEuclideanLengthMetric (D ω) := hsub hω
      simpa only [D', hω, ↓reduceIte] using hωmetric
    · simpa only [D', hω, ↓reduceIte] using isEuclideanLengthMetric_dist
  let F : Ω → C(ℂ × ℂ, ℝ) := fun ω => ⟨fun p => D' ω p.1 p.2, (hD'metric ω).continuous_pair⟩
  refine ⟨F, ?_, hD'metric, ?_⟩
  · apply ContinuousMap.measurable_iff_eval.mpr
    intro p
    exact Measurable.ite hG (hD p.1 p.2) measurable_const
  · filter_upwards [hGae] with ω hω
    intro x y
    simp only [F, D', hω, ↓reduceIte, ContinuousMap.coe_mk]

/-- Arc-length parametrization preserves the full range of a finite-length
continuous curve. -/
theorem IsEuclideanLengthMetric.exists_lengthParametrized_with_range
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {p : ℝ → ℂ} {T : ℝ} (hT : 0 ≤ T) (hp : ContinuousOn p (Icc 0 T))
    (hfinite : curveLength D p 0 T < ∞) :
    ∃ q : ℝ → ℂ, IsLengthParametrized D q (curveLength D p 0 T).toReal ∧
      q 0 = p 0 ∧ q (curveLength D p 0 T).toReal = p T ∧
      q '' Icc 0 (curveLength D p 0 T).toReal = p '' Icc 0 T := by
  obtain ⟨q, hq, hq0, hqT, htrack⟩ :=
    hD.exists_lengthParametrized_with_tracking hT hp hfinite
  have himage := (hD.cumulative_curveLength_properties hT hp hfinite).2.2.2
  refine ⟨q, hq, hq0, hqT, ?_⟩
  rw [← himage, image_image]
  exact image_congr htrack

/-- Every strict sublevel of the unrestricted around observable is
universally measurable on the space of continuous distance functions. -/
theorem uMeasurableSet_pfefferAround_lt (center : ℂ) (a b : ℝ) (c : ℝ≥0∞) :
    LQGMetric.UMeasurableSet {d : C(ℂ × ℂ, ℝ) |
      pfefferAround (fun x y => d (x, y)) center a b < c} := by
  let : PolishSpace C(ℂ × ℂ, ℝ) := LQGMetric.polishSpace_continuousMap _ _
  let : PolishSpace C(I, ℂ) := LQGMetric.polishSpace_continuousMap _ _
  let R : Set (C(ℂ × ℂ, ℝ) × C(I, ℂ)) := {q |
    q.2 0 = q.2 1 ∧
    (∀ (x y : ℂ) (γ : Path x y), x ∈ Metric.sphere center a →
      y ∈ Metric.sphere center b → ∃ t, γ t ∈ Set.range q.2) ∧
    pathLength (fun x y => q.1 (x, y))
      (⟨q.2, rfl, rfl⟩ : Path (q.2 0) (q.2 1)) < c}
  have hloop : MeasurableSet {q : C(ℂ × ℂ, ℝ) × C(I, ℂ) | q.2 0 = q.2 1} :=
    isClosed_setOf_closedPaths.measurableSet.preimage measurable_snd
  have hsep : MeasurableSet {q : C(ℂ × ℂ, ℝ) × C(I, ℂ) |
      ∀ (x y : ℂ) (γ : Path x y), x ∈ Metric.sphere center a →
        y ∈ Metric.sphere center b → ∃ t, γ t ∈ Set.range q.2} :=
    (isClosed_setOf_pfefferSeparates center a b).measurableSet.preimage measurable_snd
  have hlen : MeasurableSet {q : C(ℂ × ℂ, ℝ) × C(I, ℂ) |
      pathLength (fun x y => q.1 (x, y))
        (⟨q.2, rfl, rfl⟩ : Path (q.2 0) (q.2 1)) < c} :=
    measurableSet_lt lowerSemicontinuous_pathLength.measurable measurable_const
  have hR : MeasurableSet R := hloop.inter (hsep.inter hlen)
  have hproj := LQGMetric.UMeasurableSet.setOf_exists hR
  convert hproj using 1
  ext d
  change pfefferAround (fun x y => d (x, y)) center a b < c ↔
    ∃ p : C(I, ℂ), p 0 = p 1 ∧
      (∀ (x y : ℂ) (γ : Path x y), x ∈ Metric.sphere center a →
        y ∈ Metric.sphere center b → ∃ t, γ t ∈ Set.range p) ∧
      pathLength (fun x y => d (x, y)) (⟨p, rfl, rfl⟩ : Path (p 0) (p 1)) < c
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
    have hsepP : PfefferSeparates P center a b := hsep
    have hlenP : pathLength (fun x y => d (x, y)) P < c := hlen
    exact ((iInf_le_of_le (p 0) (iInf_le_of_le P (iInf_le _ hsepP))).trans_lt hlenP)

/-- The unrestricted around observable is almost everywhere measurable for a
pointwise measurable almost surely Euclidean length metric. -/
theorem aemeasurable_pfefferAround_of_ae_euclideanLengthMetric
    {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.SFinite P]
    {D : Ω → ℂ → ℂ → ℝ} (center : ℂ) (a b : ℝ)
    (hD : ∀ x y, Measurable fun ω => D ω x y)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω)) :
    AEMeasurable (fun ω => pfefferAround (D ω) center a b) P := by
  obtain ⟨F, hF, _, hFeq⟩ :=
    exists_measurable_continuousMap_of_ae_euclideanLengthMetric hD hmetric
  have hm : @Measurable (MeasureTheory.NullMeasurableSpace Ω P) ℝ≥0∞ _ _
      (fun ω => pfefferAround (fun x y => F ω (x, y)) center a b) := by
    apply measurable_of_Iio
    intro c
    exact ((uMeasurableSet_pfefferAround_lt center a b c).preimage hF).nullMeasurableSet P
  have hae : AEMeasurable
      (fun ω => pfefferAround (fun x y => F ω (x, y)) center a b) P :=
    (show MeasureTheory.NullMeasurable _ P from hm).aemeasurable
  apply hae.congr
  filter_upwards [hFeq] with ω hω
  have heq : (fun x y => F ω (x, y)) = D ω := by
    funext x y
    exact hω x y
  rw [heq]

/-- On a whole-plane GFF probability space, the unrestricted around observable
is almost everywhere measurable under pointwise metric measurability. -/
theorem IsWholePlaneGFF.aemeasurable_pfefferAround_of_ae_euclideanLengthMetric
    {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc) {D : Ω → ℂ → ℂ → ℝ}
    (center : ℂ) (a b : ℝ) (hD : ∀ x y, Measurable fun ω => D ω x y)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω)) :
    AEMeasurable (fun ω => pfefferAround (D ω) center a b) P := by
  let : MeasureTheory.IsProbabilityMeasure P := hgff.isProbabilityMeasure
  exact HarmonicBalls.aemeasurable_pfefferAround_of_ae_euclideanLengthMetric center a b hD hmetric

end HarmonicBalls
