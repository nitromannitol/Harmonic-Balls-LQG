import Mathlib

/-!
# Step 4 (geometry): the cutoff of the local certificate sequence
(fp-S11ah-11-13-steps-4-5, owner n4; Step 4 of `notes/fp-gaps/CHATGPT-n3-Q1-eq34.md` section 5.)

For `n : ℕ` the certificate scale is `r_n = 2^{-n}` and the cutoff radius is `7 r_n` (the buffered domain `O_* ⊆ B_7`,
Step 1). The local certificate (J) is used at a centre `z` only when `closedBall z (7 r_n) ⊆ D_loc`. This file proves two
facts about this cutoff: it is an open condition on `z`, hence measurable, and for a bounded `A` with `closure A ⊆ D_loc`
it holds for every `z ∈ A` once `n` is large (the uniform finite cutoff of Step 4).
-/

open Metric Set Filter Topology

namespace FirstPassS11ah

/-- The scale `r_n = 2^{-n}` of the `n`-th certificate of the local sequence (Step 4). -/
noncomputable def certScale (n : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ n

/-- The cutoff radius `7 r_n` of the `n`-th local certificate (Step 4, (J)). -/
noncomputable def cutRadius (n : ℕ) : ℝ := 7 * certScale n

lemma certScale_pos (n : ℕ) : 0 < certScale n := pow_pos (by norm_num) n

lemma certScale_antitone {m n : ℕ} (h : m ≤ n) : certScale n ≤ certScale m :=
  pow_le_pow_of_le_one (by norm_num) (by norm_num) h

/-- The centres `z` whose closed cutoff ball `closedBall z ρ` lies in the open set `D`: this set is open, hence
measurable (Step 4, measurability of the cutoff in `z`). -/
lemma isOpen_setOf_closedBall_subset {D : Set ℂ} (hD : IsOpen D) (ρ : ℝ) :
    IsOpen {z : ℂ | closedBall z ρ ⊆ D} := by
  rw [Metric.isOpen_iff]
  intro z0 hz0
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_closedBall z0 ρ).exists_thickening_subset_open hD hz0
  refine ⟨δ, hδ, ?_⟩
  intro z hz
  show closedBall z ρ ⊆ D
  intro w hw
  apply hsub
  rw [Metric.mem_thickening_iff]
  refine ⟨w - z + z0, ?_, ?_⟩
  · rw [mem_closedBall, dist_eq_norm, show w - z + z0 - z0 = w - z by ring, ← dist_eq_norm]
    exact mem_closedBall.1 hw
  · rw [dist_eq_norm, show w - (w - z + z0) = z - z0 by ring, ← dist_eq_norm]
    exact mem_ball.1 hz

lemma measurableSet_setOf_closedBall_subset {D : Set ℂ} (hD : IsOpen D) (ρ : ℝ) :
    MeasurableSet {z : ℂ | closedBall z ρ ⊆ D} :=
  (isOpen_setOf_closedBall_subset hD ρ).measurableSet

/-- **Uniform finite cutoff (Step 4).** If `A` is bounded with `closure A ⊆ D` and `D` is open (`A ⋐ D_loc`), then for
all `n` beyond some `n₀` and every `z ∈ A` the cutoff ball `closedBall z (7 r_n)` lies in `D`. -/
lemma exists_cutoff_of_closure_subset {A D : Set ℂ} (hA : Bornology.IsBounded A) (hD : IsOpen D)
    (hAD : closure A ⊆ D) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ z ∈ A, closedBall z (cutRadius n) ⊆ D := by
  obtain ⟨δ, hδ, hsub⟩ := hA.isCompact_closure.exists_thickening_subset_open hD hAD
  obtain ⟨n₀, hn₀⟩ := exists_pow_lt_of_lt_one (by positivity : (0 : ℝ) < δ / 7) (by norm_num : (2 : ℝ)⁻¹ < 1)
  refine ⟨n₀, fun n hn z hz w hw => hsub ?_⟩
  rw [Metric.mem_thickening_iff]
  refine ⟨z, subset_closure hz, ?_⟩
  have h1 : dist w z ≤ cutRadius n := mem_closedBall.1 hw
  have h2 : certScale n ≤ certScale n₀ := certScale_antitone hn
  have h3 : certScale n₀ < δ / 7 := hn₀
  have h4 : cutRadius n = 7 * certScale n := rfl
  linarith

end FirstPassS11ah
