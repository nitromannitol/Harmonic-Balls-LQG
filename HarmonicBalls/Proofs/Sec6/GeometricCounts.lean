import HarmonicBalls.Proofs.Sec6.Localization

/-!
# Counting geometric annulus scales

A finite collection of indexed good scales injects into the set of all good geometric radii.
This deterministic step applies equally to good and very good annuli.
-/

namespace HarmonicBalls.Section6

open Set

/-- Count selected geometric scales in a bounded interval. The positive stride permits taking
subsequences, as needed for disjoint annuli in the very good annulus argument. -/
theorem geometric_scale_count_le {q lo hi : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hlo : 0 < lo) (P : ℝ → Prop) [DecidablePred P] (n₀ stride K : ℕ) (hstride : 0 < stride)
    (hrange : ∀ k ∈ Finset.range K, q ^ (n₀ + stride * k) ∈ Icc lo hi) :
    ((Finset.range K).filter fun k => P (q ^ (n₀ + stride * k))).card ≤
      {r : ℝ | r ∈ Icc lo hi ∧ (∃ n : ℕ, r = q ^ n) ∧ P r}.ncard := by
  classical
  let F := (Finset.range K).filter fun k => P (q ^ (n₀ + stride * k))
  let f : ℕ → ℝ := fun k => q ^ (n₀ + stride * k)
  let T : Set ℝ := {r | r ∈ Icc lo hi ∧ (∃ n : ℕ, r = q ^ n) ∧ P r}
  have hfin : T.Finite := finite_of_geometric (A := 1) hq0.le hq1 hlo fun r hr =>
    ⟨hr.1.1, by obtain ⟨n, hn⟩ := hr.2.1; exact ⟨n, by simpa using hn⟩⟩
  have hinj : Function.Injective f := by
    intro i j hij
    have h := (pow_right_injective₀ hq0 (ne_of_lt hq1)) hij
    change n₀ + stride * i = n₀ + stride * j at h
    exact Nat.mul_left_cancel hstride (Nat.add_left_cancel h)
  have hsub : f '' (F : Set ℕ) ⊆ T := by
    rintro r ⟨k, hk, rfl⟩
    have hk' := Finset.mem_filter.mp hk
    exact ⟨hrange k hk'.1, ⟨n₀ + stride * k, rfl⟩, hk'.2⟩
  calc
    F.card = (f '' (F : Set ℕ)).ncard := by rw [hinj.injOn.ncard_image, Set.ncard_coe_finset]
    _ ≤ T.ncard := Set.ncard_le_ncard hsub hfin

end HarmonicBalls.Section6
