import HarmonicBalls.Proposed.PfefferMetricScaling
import Mathlib.Topology.Maps.Proper.Basic

/-! # Closedness of separating loops

The separation condition is closed in the space of continuous paths with the
compact-open topology.
-/

namespace HarmonicBalls

open Set Filter
open scoped unitInterval Topology

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

end HarmonicBalls
