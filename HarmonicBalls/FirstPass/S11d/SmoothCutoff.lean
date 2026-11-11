import HarmonicBalls.FirstPass.S11d.ShiftBound

/-!
# Proposition 11.9, smooth cutoff for the shift

FIRST-PASS NEW. The smooth function `φ` of the shift `h~ = h - (φ/ξ) log(2A/ε)` (paper proof of `prop:mass-diam-gen`,
lines 3125-3131): `φ = 1` on the compact set `K = closure(V \ S₂)` (through the open set `O`), `0 ≤ φ ≤ 1`, and compact
support inside the bounded open set `U = W \ S₁`. Built from Mathlib's `exists_contDiff_support_eq_eq_one_iff`
(Geometry/Manifold/PartitionOfUnity.lean) and `exists_open_between_of_compact` (ShiftBound.lean).
-/

namespace HarmonicBalls

open Set

/-- A smooth cutoff equal to `1` on a compact `K`, with values in `[0,1]` and compact support whose closure lies in a
bounded open `U ⊇ K`. -/
theorem exists_smooth_cutoff {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hUb : Bornology.IsBounded U) :
    ∃ φ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U ∧
      (∀ z, 0 ≤ φ z ∧ φ z ≤ 1) ∧ ∀ z ∈ K, φ z = 1 := by
  obtain ⟨O, hOo, hKO, hclO⟩ := exists_open_between_of_compact hK hU hKU
  obtain ⟨f, hf, hrange, hsupp, hiff⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hOo hK.isClosed hKO
  have htsupp : tsupport f = closure O := by rw [tsupport, hsupp]
  have hcompact : IsCompact (closure O) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure (hUb.subset hclO)
  refine ⟨f, hf, ?_, ?_, ?_, ?_⟩
  · unfold HasCompactSupport
    rw [htsupp]
    exact hcompact
  · rw [htsupp]
    exact hclO
  · intro z
    exact ⟨(hrange (Set.mem_range_self z)).1, (hrange (Set.mem_range_self z)).2⟩
  · intro z hz
    exact (hiff z).mp hz

end HarmonicBalls
