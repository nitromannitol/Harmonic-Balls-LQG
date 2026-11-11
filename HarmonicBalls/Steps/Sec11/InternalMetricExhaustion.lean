import HarmonicBalls.Defs.LQGMetric

/-! # Internal metrics on increasing open domains -/

namespace HarmonicBalls

open Set
open scoped ENNReal

/-- Internal distance on an increasing union of open sets is the infimum of
its internal distances on those sets. Compactness of a path ensures it lies
in one member of the cover. No metric assumptions on `D` are needed. -/
theorem internalMetric_iUnion_of_monotone_isOpen
    (D : ℂ → ℂ → ℝ) (U : ℕ → Set ℂ)
    (hUopen : ∀ n, IsOpen (U n)) (hUmono : Monotone U) (x y : ℂ) :
    internalMetric D (⋃ n, U n) x y = ⨅ n, internalMetric D (U n) x y := by
  apply le_antisymm
  · exact le_iInf fun n => internalMetric_anti D (subset_iUnion U n) x y
  · unfold internalMetric
    refine le_iInf fun p => le_iInf fun hp => ?_
    have hcover : range p ⊆ ⋃ n, U n := by
      rintro z ⟨t, rfl⟩
      exact hp t
    obtain ⟨n, hn⟩ := (isCompact_range p.continuous).elim_directed_cover U hUopen
      hcover (fun i j => ⟨max i j, hUmono (le_max_left _ _), hUmono (le_max_right _ _)⟩)
    have hpath : ∀ t, p t ∈ U n := fun t => hn ⟨t, rfl⟩
    exact (iInf_le (fun n => ⨅ (q : Path x y) (_ : ∀ t, q t ∈ U n),
      pathLength D q) n).trans (iInf_le_of_le p (iInf_le_of_le hpath le_rfl))


end HarmonicBalls
