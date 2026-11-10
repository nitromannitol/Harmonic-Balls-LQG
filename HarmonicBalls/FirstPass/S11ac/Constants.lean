import HarmonicBalls.FirstPass.S11ac.ChainGlue

/-! # Overlap chains and telescoping products (fp-S11ac, owner z6)

Pieces `Dp j` (open) cover a preconnected set `X`. A list `L` is an overlap chain from `a` when consecutive pieces
intersect (`OvChain`). The product of the local ratios along a chain telescopes to the ratio of the endpoint
constants (`ratioProd_eq_of_chain`). Every piece is reached from piece `0` by an overlap chain (`exists_ovChain`).
-/

namespace HarmonicBalls.S11ac

open Set Filter Topology
open scoped ENNReal

/-- Consecutive pieces of the list chain `a :: L` intersect. -/
def OvChain (Dp : ℕ → Set ℂ) : ℕ → List ℕ → Prop
  | _, [] => True
  | a, b :: L => (Dp a ∩ Dp b).Nonempty ∧ OvChain Dp b L

/-- The last index of the chain `a :: L` (the value `a` for the empty list). -/
def lastOr : ℕ → List ℕ → ℕ
  | a, [] => a
  | _, b :: L => lastOr b L

/-- Product of the ratios along the list chain `a :: L`. -/
noncomputable def ratioProd (R : ℕ → ℕ → ℝ≥0∞) : ℕ → List ℕ → ℝ≥0∞
  | _, [] => 1
  | a, b :: L => R a b * ratioProd R b L

theorem lastOr_append_single (a : ℕ) (L : List ℕ) (l : ℕ) : lastOr a (L ++ [l]) = l := by
  induction L generalizing a with
  | nil => rfl
  | cons b L ih => simpa [lastOr] using ih b

theorem ovChain_append (Dp : ℕ → Set ℂ) (a : ℕ) (L : List ℕ) (j : ℕ) :
    OvChain Dp a (L ++ [j]) ↔ OvChain Dp a L ∧ (Dp (lastOr a L) ∩ Dp j).Nonempty := by
  induction L generalizing a with
  | nil => simp [OvChain, lastOr]
  | cons b L ih =>
    simp only [List.cons_append, OvChain, lastOr, ih]
    tauto

/-- **Telescoping.** If the local ratios are the ratios of positive constants `β` on overlapping pieces, the
product along an overlap chain is the ratio of the constants at the endpoints. -/
theorem ratioProd_eq_of_chain (Dp : ℕ → Set ℂ) {R : ℕ → ℕ → ℝ≥0∞} {β : ℕ → ℝ} (hβ : ∀ a, 0 < β a)
    (hR : ∀ a b, (Dp a ∩ Dp b).Nonempty → R a b = ENNReal.ofReal (β a / β b)) :
    ∀ (L : List ℕ) (a : ℕ), OvChain Dp a L →
      ratioProd R a L = ENNReal.ofReal (β a / β (lastOr a L)) := by
  intro L
  induction L with
  | nil =>
    intro a _
    simp [ratioProd, lastOr, div_self (hβ a).ne']
  | cons b L ih =>
    intro a h
    obtain ⟨hab, hL⟩ := h
    simp only [ratioProd, lastOr]
    rw [hR a b hab, ih b hL, ← ENNReal.ofReal_mul (div_nonneg (hβ a).le (hβ b).le)]
    congr 1
    have := (hβ b).ne'
    have := (hβ (lastOr b L)).ne'
    have := (hβ a).ne'
    field_simp

/-- **Existence of overlap chains.** If the open pieces `Dp j` (nonempty, inside `X`) cover the preconnected set `X`,
every piece is reached from piece `0` by an overlap chain. -/
theorem exists_ovChain (Dp : ℕ → Set ℂ) {X : Set ℂ} (hXpre : IsPreconnected X)
    (hopen : ∀ j, IsOpen (Dp j)) (hDX : ∀ j, Dp j ⊆ X) (hcov : X ⊆ ⋃ j, Dp j) (hne : ∀ j, (Dp j).Nonempty)
    (j : ℕ) : ∃ L : List ℕ, OvChain Dp 0 L ∧ lastOr 0 L = j := by
  classical
  set S : Set ℕ := {j | ∃ L : List ℕ, OvChain Dp 0 L ∧ lastOr 0 L = j} with hS
  have step : ∀ k l, k ∈ S → (Dp k ∩ Dp l).Nonempty → l ∈ S := by
    rintro k l ⟨L, hL, hlast⟩ hkl
    refine ⟨L ++ [l], ?_, lastOr_append_single 0 L l⟩
    rw [ovChain_append, hlast]
    exact ⟨hL, hkl⟩
  set U : Set ℂ := ⋃ k ∈ S, Dp k with hU
  set V : Set ℂ := ⋃ k ∈ Sᶜ, Dp k with hV
  have hUo : IsOpen U := isOpen_biUnion fun k _ => hopen k
  have hVo : IsOpen V := isOpen_biUnion fun k _ => hopen k
  have hdisj : Disjoint U V := by
    rw [Set.disjoint_left]
    intro z hzU hzV
    obtain ⟨k, hkS, hzk⟩ := mem_iUnion₂.1 hzU
    obtain ⟨l, hlS, hzl⟩ := mem_iUnion₂.1 hzV
    exact hlS (step k l hkS ⟨z, hzk, hzl⟩)
  have hcovUV : X ⊆ U ∪ V := by
    intro z hz
    obtain ⟨k, hk⟩ := mem_iUnion.1 (hcov hz)
    by_cases hkS : k ∈ S
    · exact Or.inl (mem_biUnion hkS hk)
    · exact Or.inr (mem_biUnion hkS hk)
  have h0S : (0 : ℕ) ∈ S := ⟨[], trivial, rfl⟩
  have hne0 : (X ∩ U).Nonempty := by
    obtain ⟨z, hz⟩ := hne 0
    exact ⟨z, hDX 0 hz, mem_biUnion h0S hz⟩
  have hXU : X ⊆ U := hXpre.subset_left_of_subset_union hUo hVo hdisj hcovUV hne0
  obtain ⟨z, hz⟩ := hne j
  obtain ⟨k, hkS, hzk⟩ := mem_iUnion₂.1 (hXU (hDX j hz))
  exact step k j hkS ⟨z, hzk, hz⟩

end HarmonicBalls.S11ac
