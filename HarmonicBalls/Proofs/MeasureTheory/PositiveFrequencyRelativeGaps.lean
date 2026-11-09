import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Set.Card

/-!
# Positive-frequency good indices with relative gaps tending to one

A deterministic consequence of a positive counting frequency. Let `S ⊆ ℕ` satisfy
`(1 / N) * #{1 ≤ n ≤ N : n ∈ S} → p` as `N → ∞`, with `p > 0`. Let `n₁ < n₂ < ⋯` be the
increasing enumeration of the good positive indices, that is of `{n ∈ S : 0 < n}`. Then

* `#{1 ≤ n ≤ nᵢ : n ∈ S} = i` for every `i`, hence `i / nᵢ → p`;
* `nᵢ / i → p⁻¹`;
* `nᵢ₊₁ / nᵢ → 1`.

No bound on the absolute gaps `nᵢ₊₁ - nᵢ` is assumed. This is the relative-gap step of
`notes/sec11-proof/sec11-proof-r10.tex`, lines 491–510. There the frequency is obtained from the
ergodic theorem (Walters, Theorem 1.14); that input is not used here, only the frequency
hypothesis is.

Indexing. `goodEnum S k` is the zero-indexed enumeration (`Nat.nth`), so the paper's `nᵢ` is
`goodEnum S (i - 1)`. Only positive integers are counted and enumerated: an element `0 ∈ S` never
enters the enumeration, and every denominator `goodEnum S k` is positive. Shifting the index by
one does not change the limits.
-/

open Filter Topology Set

namespace HarmonicBalls.PositiveFrequencyRelativeGaps

open scoped Classical

noncomputable section

/-- A good positive index: `0 < n` and `n ∈ S`. -/
def IsGoodPos (S : Set ℕ) (n : ℕ) : Prop :=
  0 < n ∧ n ∈ S

/-- The counting function `N ↦ #{1 ≤ n ≤ N : n ∈ S}`. The index `0` is never counted. -/
def goodCount (S : Set ℕ) (N : ℕ) : ℕ :=
  (S ∩ Icc 1 N).ncard

/-- The increasing enumeration `n₀ < n₁ < ⋯` of the good positive indices (zero-indexed). -/
def goodEnum (S : Set ℕ) (k : ℕ) : ℕ :=
  Nat.nth (IsGoodPos S) k

/-- The counting function is the `Nat.count` of good positive indices below `N + 1`. -/
lemma goodCount_eq_count (S : Set ℕ) (N : ℕ) :
    goodCount S N = Nat.count (IsGoodPos S) (N + 1) := by
  rw [Nat.count_eq_card_filter_range, goodCount, ← Set.ncard_coe_finset]
  congr 1
  ext n
  constructor
  · intro h
    obtain ⟨hS, hIcc⟩ := h
    obtain ⟨h1, h2⟩ := Set.mem_Icc.mp hIcc
    exact Finset.mem_coe.mpr (Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), by omega, hS⟩)
  · intro h
    obtain ⟨hr, hgood⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp h)
    obtain ⟨h0, hS⟩ := hgood
    have h2 : n < N + 1 := Finset.mem_range.mp hr
    exact ⟨hS, Set.mem_Icc.mpr ⟨by omega, by omega⟩⟩

/-- The good positive indices are infinite when the frequency is positive: a finite set has
bounded counting function, so `#{1 ≤ n ≤ N : n ∈ S} / N → 0`, contradicting the limit `p > 0`. -/
lemma goodSet_infinite {S : Set ℕ} {p : ℝ} (hp : 0 < p)
    (hfreq : Tendsto (fun N : ℕ => (goodCount S N : ℝ) / N) atTop (𝓝 p)) :
    (Set.ofPred (IsGoodPos S)).Infinite := by
  intro hfin
  have hbound : ∀ N : ℕ, goodCount S N ≤ (Set.ofPred (IsGoodPos S)).ncard := by
    intro N
    refine Set.ncard_le_ncard (fun n hn => ?_) hfin
    have h1 : 1 ≤ n := hn.2.1
    show 0 < n ∧ n ∈ S
    exact ⟨by omega, hn.1⟩
  have hzero : Tendsto (fun N : ℕ => ((Set.ofPred (IsGoodPos S)).ncard : ℝ) / N) atTop
      (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hle : p ≤ 0 := by
    refine le_of_tendsto_of_tendsto' hfreq hzero (fun N => ?_)
    gcongr
    exact_mod_cast hbound N
  linarith

/-- Enumeration identity: the `k`-th good positive index has exactly `k + 1` good positive
indices in `[1, goodEnum S k]`. -/
lemma goodCount_goodEnum {S : Set ℕ} (hinf : (Set.ofPred (IsGoodPos S)).Infinite) (k : ℕ) :
    goodCount S (goodEnum S k) = k + 1 := by
  have hk : IsGoodPos S (Nat.nth (IsGoodPos S) k) := Nat.nth_mem_of_infinite hinf k
  rw [goodCount_eq_count, goodEnum, Nat.count_succ, Nat.count_nth_of_infinite hinf k]
  simp [hk]

/-- Positive-frequency relative gaps. If `#{1 ≤ n ≤ N : n ∈ S} / N → p > 0`, then the increasing
enumeration `goodEnum S` of the good positive indices is strictly increasing, enumerates exactly
`{n : 0 < n ∧ n ∈ S}`, satisfies `#{1 ≤ n ≤ goodEnum S k : n ∈ S} = k + 1`, and has
`(k + 1) / nₖ → p`, `k / nₖ → p`, `nₖ / k → p⁻¹` and `nₖ₊₁ / nₖ → 1`. No bound on the
absolute gaps is assumed. -/
theorem positive_frequency_relative_gaps (S : Set ℕ) {p : ℝ} (hp : 0 < p)
    (hfreq : Tendsto (fun N : ℕ => (goodCount S N : ℝ) / N) atTop (𝓝 p)) :
    StrictMono (goodEnum S) ∧ Set.range (goodEnum S) = {n | IsGoodPos S n} ∧
      (∀ k : ℕ, goodCount S (goodEnum S k) = k + 1) ∧
      Tendsto (fun k : ℕ => ((k : ℝ) + 1) / goodEnum S k) atTop (𝓝 p) ∧
      Tendsto (fun k : ℕ => (k : ℝ) / goodEnum S k) atTop (𝓝 p) ∧
      Tendsto (fun k : ℕ => (goodEnum S k : ℝ) / k) atTop (𝓝 p⁻¹) ∧
      Tendsto (fun k : ℕ => (goodEnum S (k + 1) : ℝ) / goodEnum S k) atTop (𝓝 1) := by
  have hinf : (Set.ofPred (IsGoodPos S)).Infinite := goodSet_infinite hp hfreq
  have hmono : StrictMono (goodEnum S) := Nat.nth_strictMono hinf
  have hrange : Set.range (goodEnum S) = {n | IsGoodPos S n} :=
    Nat.range_nth_of_infinite hinf
  have hcount : ∀ k : ℕ, goodCount S (goodEnum S k) = k + 1 := goodCount_goodEnum hinf
  have hgood : ∀ k : ℕ, IsGoodPos S (goodEnum S k) := fun k => Nat.nth_mem_of_infinite hinf k
  have hpos : ∀ k : ℕ, (0 : ℝ) < goodEnum S k := fun k => by
    exact_mod_cast (hgood k).1
  have hgrow : Tendsto (goodEnum S) atTop atTop :=
    tendsto_atTop_mono (fun k => hmono.id_le k) tendsto_id
  -- Frequency along the enumeration: `(k + 1) / nₖ → p`, from the count identity.
  have hA : Tendsto (fun k : ℕ => ((k : ℝ) + 1) / goodEnum S k) atTop (𝓝 p) := by
    refine (hfreq.comp hgrow).congr (fun k => ?_)
    simp only [Function.comp_apply, hcount k, Nat.cast_add, Nat.cast_one]
  -- `1 / nₖ → 0`, hence `k / nₖ = (k + 1) / nₖ - 1 / nₖ → p`.
  have hinv : Tendsto (fun k : ℕ => 1 / (goodEnum S k : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hgrow)
  have hB : Tendsto (fun k : ℕ => (k : ℝ) / goodEnum S k) atTop (𝓝 p) := by
    have h := hA.sub hinv
    rw [sub_zero] at h
    exact h.congr (fun k => by ring)
  -- Inversion, legitimate since `p ≠ 0`: `nₖ / k → p⁻¹`.
  have hC : Tendsto (fun k : ℕ => (goodEnum S k : ℝ) / k) atTop (𝓝 p⁻¹) :=
    (hB.inv₀ hp.ne').congr (fun k => inv_div _ _)
  -- `(k + 2) / (k + 1) → 1`.
  have hc : Tendsto (fun k : ℕ => ((k : ℝ) + 2) / ((k : ℝ) + 1)) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [add_zero] at h
    refine h.congr (fun k => ?_)
    have hne : (k : ℝ) + 1 ≠ 0 := by positivity
    rw [show ((k : ℝ) + 2) / ((k : ℝ) + 1)
        = ((k : ℝ) + 1) / ((k : ℝ) + 1) + 1 / ((k : ℝ) + 1) by ring, div_self hne]
  -- Shifted inverse: `n_{k+1} / (k + 2) → p⁻¹`.
  have hb : Tendsto (fun k : ℕ => (goodEnum S (k + 1) : ℝ) / ((k : ℝ) + 2)) atTop
      (𝓝 p⁻¹) := by
    have h := (hA.comp (tendsto_add_atTop_nat 1)).inv₀ hp.ne'
    refine h.congr (fun k => ?_)
    simp only [Function.comp_apply, inv_div]
    push_cast
    ring
  -- Consecutive ratio: `n_{k+1} / nₖ = (n_{k+1} / (k + 2)) * ((k + 1) / nₖ) * ((k + 2) / (k + 1))`.
  have hD : Tendsto (fun k : ℕ => (goodEnum S (k + 1) : ℝ) / goodEnum S k) atTop (𝓝 1) := by
    have h := (hb.mul hA).mul hc
    rw [inv_mul_cancel₀ hp.ne', mul_one] at h
    refine h.congr (fun k => ?_)
    have h1 : (goodEnum S k : ℝ) ≠ 0 := (hpos k).ne'
    have h2 : (k : ℝ) + 1 ≠ 0 := by positivity
    have h3 : (k : ℝ) + 2 ≠ 0 := by positivity
    field_simp
  exact ⟨hmono, hrange, hcount, hA, hB, hC, hD⟩

end

end HarmonicBalls.PositiveFrequencyRelativeGaps
