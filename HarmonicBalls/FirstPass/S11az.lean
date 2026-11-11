import HarmonicBalls.FirstPass.S11am

/-!
# Countable dense index sets of the pinch geometry

Every subset `A` of `ℂ` has a countable subset `S ⊆ A` with `A ⊆ closure S` (`IsCountDenseIn S A` of
`FirstPass/S11am.lean:36`). This is the separability of `ℂ` (Mathlib `TopologicalSpace.IsSeparable.of_separableSpace`
and `TopologicalSpace.IsSeparable.exists_countable_dense_subset`), needing no hypothesis on `A`. Applying it to each
of the eleven sets of the structure `S11am.PinchCountSets` (spheres `∂B_5`, `∂B_δ`, `∂B_{2δ}`, `∂B_{3δ}`, the closures
of `Q'`, `T \ B_{3δ}(W)`, `V`, `B_{3δ}(W) \ V`, and the frontier `∂Q`) gives a nonempty type, and the chosen element is
the count-set family used by the countable form of the decoded local rule.
-/

namespace HarmonicBalls.S11az

open Metric

/-- Every subset of `ℂ` has a countable subset `S` with `S ⊆ A` and `A ⊆ closure S`: `ℂ` is separable, so every
subspace is, and a countable dense subset of the subspace `A` lies in `A`. -/
theorem exists_isCountDenseIn (A : Set ℂ) : ∃ S : Set ℂ, S.Countable ∧ S ⊆ A ∧ A ⊆ closure S := by
  obtain ⟨t, ht, hc, hcl⟩ :=
    TopologicalSpace.IsSeparable.exists_countable_dense_subset (TopologicalSpace.IsSeparable.of_separableSpace A)
  exact ⟨t, hc, ht, hcl⟩

/-- The count sets of the pinch geometry `(V, W, T, Q', Q, δ)` exist (no hypotheses on the sets). -/
theorem pinchCountSets_nonempty (V W T Q' Q : Set ℂ) (δ : ℝ) :
    Nonempty (S11am.PinchCountSets V W T Q' Q δ) := by
  obtain ⟨sp, hspc, hsp, hspd⟩ := exists_isCountDenseIn (sphere (0 : ℂ) 5)
  obtain ⟨qp, hqpc, hqp, hqpd⟩ := exists_isCountDenseIn (closure Q')
  obtain ⟨fp, hfpc, hfp, hfpd⟩ := exists_isCountDenseIn (frontier Q)
  obtain ⟨cp, hcpc, hcp, hcpd⟩ := exists_isCountDenseIn (closure (T \ thickening (3 * δ) W))
  obtain ⟨ep, hepc, hep, hepd⟩ := exists_isCountDenseIn (sphere (0 : ℂ) δ)
  obtain ⟨s2, hs2c, hs2, hs2d⟩ := exists_isCountDenseIn (sphere (0 : ℂ) δ)
  obtain ⟨s3, hs3c, hs3, hs3d⟩ := exists_isCountDenseIn (sphere (0 : ℂ) (2 * δ))
  obtain ⟨cv, hcvc, hcv, hcvd⟩ := exists_isCountDenseIn (closure V)
  obtain ⟨t2, ht2c, ht2, ht2d⟩ := exists_isCountDenseIn (sphere (0 : ℂ) (2 * δ))
  obtain ⟨t3, ht3c, ht3, ht3d⟩ := exists_isCountDenseIn (sphere (0 : ℂ) (3 * δ))
  obtain ⟨ct, hctc, hct, hctd⟩ := exists_isCountDenseIn (closure (thickening (3 * δ) W \ V))
  exact ⟨⟨sp, ⟨hsp, hspd, hspc⟩, qp, ⟨hqp, hqpd, hqpc⟩, fp, ⟨hfp, hfpd, hfpc⟩,
    cp, ⟨hcp, hcpd, hcpc⟩, ep, ⟨hep, hepd, hepc⟩, s2, ⟨hs2, hs2d, hs2c⟩,
    s3, ⟨hs3, hs3d, hs3c⟩, cv, ⟨hcv, hcvd, hcvc⟩, t2, ⟨ht2, ht2d, ht2c⟩,
    t3, ⟨ht3, ht3d, ht3c⟩, ct, ⟨hct, hctd, hctc⟩⟩⟩

/-- A count-set family for the pinch geometry, chosen by `Classical.choice` (`pinchCountSets_nonempty`). -/
noncomputable def pinchCountSets (V W T Q' Q : Set ℂ) (δ : ℝ) : S11am.PinchCountSets V W T Q' Q δ :=
  Classical.choice (pinchCountSets_nonempty V W T Q' Q δ)

end HarmonicBalls.S11az
