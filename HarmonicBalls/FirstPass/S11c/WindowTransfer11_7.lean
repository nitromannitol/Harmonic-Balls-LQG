import HarmonicBalls.FirstPass.S11c.ScaleCone11_7
import HarmonicBalls.FirstPass.S11c.ConeTranslate11_7
import HarmonicBalls.FirstPass.S11c.IdentifyBad11_7

/-!
# Lemma 11.7, window transfer (B2 sec 5.1 and sec 7; deterministic)

Two deterministic facts used to pass the origin window bound (`origin_window_visits`, Origin11_7.lean:192) to the window
sum `globalWindowSum` (IdentifyBad11_7.lean:23) of a rooted measure:

* `globalWindowSum_smul_map_add_right`: for `c ∈ (0, ∞)`, the window sum at root `z` of the measure `c • ν.map (· + z)`
  equals the window sum at the origin of `ν` (scale invariance ScaleCone11_7 and translation ConeTranslate11_7).
* `window_shift_ge`: a window bound at the shifted indices `N₀ + n`, `n ∈ [N'+1, 2N']`, gives the bound `(p/8) N` on
  `[N+1, 2N]` (B2 sec 1: the constant `δ = p/8`, from `N = N' + N₀`).
-/

open MeasureTheory Filter Set
open scoped ENNReal

namespace HarmonicBalls.S11c

/-- The window sum at root `z` of `c • ν.map (· + z)` is the origin window sum of `ν` (`c ∈ (0, ∞)`). -/
theorem globalWindowSum_smul_map_add_right (Q : Set ℂ) (M : ℝ) (z : ℂ) (ν : Measure ℂ)
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ⊤) (N : ℕ) :
    globalWindowSum Q M z (c • ν.map (fun w => w + z)) N = globalWindowSum Q M 0 ν N := by
  classical
  unfold globalWindowSum
  refine Finset.sum_congr rfl fun n _ => ?_
  have key : coneMassEvent (c • ν.map (fun w => w + z)) Q M ((2 : ℝ)⁻¹ ^ n) z ↔
      coneMassEvent ν Q M ((2 : ℝ)⁻¹ ^ n) 0 :=
    (coneMassEvent_smul_iff _ Q M _ z hc0 hc).trans (coneMassEvent_map_add_right ν Q M _ z)
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, key]

/-- Index shift (B2 sec 1, `δ = p/8`): a window bound at the indices `N₀ + n`, `n ∈ [N'+1, 2N']`, yields the window bound
`(p/8) N` on `[N+1, 2N]` for all large `N`. For `N = N' + N₀` one has `N' ≥ N₀` and `N ≤ 2N'`. -/
lemma window_shift_ge (g : ℕ → ℝ) (hg : ∀ m, 0 ≤ g m) (N0 : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (h : ∀ᶠ N' : ℕ in atTop, p / 4 * (N' : ℝ) ≤ ∑ n ∈ Finset.Icc (N' + 1) (2 * N'), g (N0 + n)) :
    ∀ᶠ N : ℕ in atTop, p / 8 * (N : ℝ) ≤ ∑ m ∈ Finset.Icc (N + 1) (2 * N), g m := by
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp h
  refine eventually_atTop.mpr ⟨2 * N0 + N1, fun N hN => ?_⟩
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + N0 := ⟨N - N0, by omega⟩
  have hA : p / 4 * (N' : ℝ) ≤ ∑ n ∈ Finset.Icc (N' + 1) (2 * N'), g (N0 + n) := hN1 N' (by omega)
  have hsub : (Finset.Icc (N' + 1) (2 * N')).image (fun n => N0 + n) ⊆
      Finset.Icc (N' + N0 + 1) (2 * (N' + N0)) := by
    intro m hm
    simp only [Finset.mem_image, Finset.mem_Icc] at hm ⊢
    obtain ⟨n, ⟨h1, h2⟩, rfl⟩ := hm
    omega
  have hsum : ∑ n ∈ Finset.Icc (N' + 1) (2 * N'), g (N0 + n) =
      ∑ m ∈ (Finset.Icc (N' + 1) (2 * N')).image (fun n => N0 + n), g m := by
    rw [Finset.sum_image]
    intro x _ y _ hxy
    simpa using hxy
  have hle : ∑ m ∈ (Finset.Icc (N' + 1) (2 * N')).image (fun n => N0 + n), g m ≤
      ∑ m ∈ Finset.Icc (N' + N0 + 1) (2 * (N' + N0)), g m :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => hg m)
  have hcast : ((N' + N0 : ℕ) : ℝ) ≤ 2 * (N' : ℝ) := by
    have : N' + N0 ≤ 2 * N' := by omega
    exact_mod_cast this
  calc p / 8 * ((N' + N0 : ℕ) : ℝ) ≤ p / 8 * (2 * (N' : ℝ)) :=
        mul_le_mul_of_nonneg_left hcast (by positivity)
    _ = p / 4 * (N' : ℝ) := by ring
    _ ≤ ∑ n ∈ Finset.Icc (N' + 1) (2 * N'), g (N0 + n) := hA
    _ = ∑ m ∈ (Finset.Icc (N' + 1) (2 * N')).image (fun n => N0 + n), g m := hsum
    _ ≤ ∑ m ∈ Finset.Icc (N' + N0 + 1) (2 * (N' + N0)), g m := hle

end HarmonicBalls.S11c
