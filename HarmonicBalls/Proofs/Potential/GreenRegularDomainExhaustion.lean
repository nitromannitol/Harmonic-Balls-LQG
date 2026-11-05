import HarmonicBalls.Proofs.Sec6.RelativelyCompactExhaustion

/-! # Relatively compact open exhaustions with a fixed pole

This is the topological part of a Green-regular exhaustion. The boundary
regularity of the resulting domains is a separate question.
-/

namespace HarmonicBalls

open Set

/-- An open subset of the plane admits an increasing relatively compact open
exhaustion containing any prescribed point at every stage. -/
theorem exists_open_relativelyCompact_exhaustion {U : Set ℂ} (hU : IsOpen U)
    {z : ℂ} (hz : z ∈ U) :
    ∃ V : ℕ → Set ℂ, (∀ n, IsOpen (V n)) ∧ Monotone V ∧
      (⋃ n, V n) = U ∧ (∀ n, closure (V n) ⊆ U) ∧ ∀ n, z ∈ V n := by
  obtain ⟨D, hopen, hmono, -, hnext, hunion⟩ :=
    Section6.exists_relativelyCompact_open_exhaustion hU
  obtain ⟨k, hk⟩ := mem_iUnion.mp (hunion.symm ▸ hz)
  let V (n : ℕ) := D (k + n)
  refine ⟨V, fun n => hopen _, ?_, ?_, ?_, ?_⟩
  · intro m n hmn
    exact hmono (by omega)
  · apply Subset.antisymm
    · rw [← hunion]
      exact iUnion_subset fun n => subset_iUnion D _
    · rw [← hunion]
      refine iUnion_subset fun n => ?_
      exact (hmono (show n ≤ k + n by omega)).trans (subset_iUnion V n)
  · intro n
    rw [← hunion]
    exact (hnext _).trans (subset_iUnion D _)
  · intro n
    exact hmono (show k ≤ k + n by omega) hk

#print axioms exists_open_relativelyCompact_exhaustion

end HarmonicBalls
