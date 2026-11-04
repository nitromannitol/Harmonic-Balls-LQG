import HarmonicBalls.Draft.Section1

/-! # Closure continuity of an increasing harmonic-ball family -/

namespace HarmonicBalls

open Set Filter Topology Metric

/-- An increasing Hausdorff-continuous family has right-continuous closures. -/
theorem closure_eq_iInter_of_hausdorffContinuousOn
    (Λ : ℝ → Set ℂ) (hmono : MonotoneOn Λ (Ioi (0 : ℝ)))
    (hcont : HausdorffContinuousOn Λ (Ioi (0 : ℝ)))
    (t : ℝ) (ht : 0 < t) :
    closure (Λ t) = ⋂ s ∈ Ioi t, closure (Λ s) := by
  apply Subset.antisymm
  · intro x hx
    simp only [mem_iInter, mem_Ioi]
    intro s hs
    exact closure_mono (hmono ht (lt_trans ht hs) hs.le) hx
  · intro x hx
    simp only [mem_iInter, mem_Ioi] at hx
    apply mem_closure_iff_infEDist_zero.mpr
    by_contra hne
    have hpos : 0 < infEDist x (Λ t) := pos_iff_ne_zero.mpr hne
    have hdist : ∀ᶠ s in 𝓝[>] t,
        hausdorffEDist (Λ s) (Λ t) < infEDist x (Λ t) :=
      (nhdsWithin_mono _ (Ioi_subset_Ioi ht.le)) (hcont t ht _ hpos)
    have hs : ∀ᶠ s in 𝓝[>] t, t < s := self_mem_nhdsWithin
    obtain ⟨s, hst, hclose⟩ := (hs.and hdist).exists
    have hz : infEDist x (Λ s) = 0 := mem_closure_iff_infEDist_zero.mp (hx s hst)
    have hle : infEDist x (Λ t) ≤ hausdorffEDist (Λ s) (Λ t) := by
      simpa [hz] using (infEDist_le_infEDist_add_hausdorffEDist (x := x) (s := Λ s) (t := Λ t))
    exact (not_lt_of_ge hle) hclose

/-- The closure-continuity hypothesis in the entry-frontier argument follows
from the conditions of Theorem 1.1. -/
theorem SatisfiesHarmonicBallConditions.closure_eq_iInter
    {μ : MeasureTheory.Measure ℂ} {Λ : ℝ → Set ℂ} {z : ℂ}
    (h : SatisfiesHarmonicBallConditions μ Λ z) (t : ℝ) (ht : 0 < t) :
    closure (Λ t) = ⋂ s ∈ Ioi t, closure (Λ s) :=
  closure_eq_iInter_of_hausdorffContinuousOn Λ h.monotoneOn h.hausdorffContinuousOn t ht

end HarmonicBalls
