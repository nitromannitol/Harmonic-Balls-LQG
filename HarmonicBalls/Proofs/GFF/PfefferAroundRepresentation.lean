import HarmonicBalls.Proposed.PfefferMetricScaling
import Mathlib.Topology.Maps.Proper.Basic

/-! # Closedness of separating loops

The separation condition is closed in the space of continuous paths with the
compact-open topology.
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

end HarmonicBalls
