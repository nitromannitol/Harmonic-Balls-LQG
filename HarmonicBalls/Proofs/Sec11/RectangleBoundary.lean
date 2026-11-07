import HarmonicBalls.Proofs.Sec11.ConnectedCoreNeighborhood

/-! # Connected boundary of a rectangle -/

namespace HarmonicBalls
open Set

/-- The boundary of a nonempty closed rectangle is connected. -/
theorem isConnected_frontier_rectangle {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    IsConnected (frontier (Icc a b ×ˢ Icc c d)) := by
  let B : Set (ℝ × ℝ) := Icc a b ×ˢ {c}
  let L : Set (ℝ × ℝ) := {a} ×ˢ Icc c d
  let T : Set (ℝ × ℝ) := Icc a b ×ˢ {d}
  let R : Set (ℝ × ℝ) := {b} ×ˢ Icc c d
  have hB : IsConnected B := (isConnected_Icc hab).prod isConnected_singleton
  have hL : IsConnected L := isConnected_singleton.prod (isConnected_Icc hcd)
  have hT : IsConnected T := (isConnected_Icc hab).prod isConnected_singleton
  have hR : IsConnected R := isConnected_singleton.prod (isConnected_Icc hcd)
  have hBL : IsConnected (B ∪ L) := hB.union ⟨(a,c), by simp [B, L, hab, hcd]⟩ hL
  have hBLT : IsConnected (B ∪ L ∪ T) :=
    hBL.union ⟨(a,d), by simp [B, L, T, hab, hcd]⟩ hT
  have hall : IsConnected (B ∪ L ∪ T ∪ R) :=
    hBLT.union ⟨(b,c), by simp [B, L, T, R, hab, hcd]⟩ hR
  have heq : frontier (Icc a b ×ˢ Icc c d) = B ∪ L ∪ T ∪ R := by
    rw [frontier_prod_eq, isClosed_Icc.closure_eq, isClosed_Icc.closure_eq,
      frontier_Icc hab, frontier_Icc hcd]
    ext ⟨x,y⟩
    simp only [B, L, T, R, mem_union, mem_prod, mem_Icc, mem_insert_iff,
      mem_singleton_iff]
    aesop
  exact heq ▸ hall

/-- The boundary of each positive-side intermediate square is connected. -/
theorem isConnected_frontier_complexIntermediateGridSquare {N : ℕ} (a : ℂ)
    (r : ℝ) (hr : 0 < r) (i : Fin N × Fin N) :
    IsConnected (frontier (complexIntermediateGridSquare a r i)) := by
  let l₁ := a.re + ((i.1.val : ℝ) - 1 / 4) * r
  let u₁ := a.re + ((i.1.val : ℝ) + 5 / 4) * r
  let l₂ := a.im + ((i.2.val : ℝ) - 1 / 4) * r
  let u₂ := a.im + ((i.2.val : ℝ) + 5 / 4) * r
  have h₁ : l₁ ≤ u₁ := by dsimp [l₁, u₁]; nlinarith
  have h₂ : l₂ ≤ u₂ := by dsimp [l₂, u₂]; nlinarith
  let e := Complex.equivRealProdCLM.toHomeomorph
  have hs : complexIntermediateGridSquare a r i = e ⁻¹' (Icc l₁ u₁ ×ˢ Icc l₂ u₂) := by
    ext z
    change (((i.1.val : ℝ) - 1 / 4) * r ≤ z.re - a.re ∧
      z.re - a.re ≤ ((i.1.val : ℝ) + 5 / 4) * r ∧
      ((i.2.val : ℝ) - 1 / 4) * r ≤ z.im - a.im ∧
      z.im - a.im ≤ ((i.2.val : ℝ) + 5 / 4) * r) ↔ _
    simp only [mem_preimage, mem_prod, mem_Icc]
    change _ ↔ (l₁ ≤ z.re ∧ z.re ≤ u₁) ∧ l₂ ≤ z.im ∧ z.im ≤ u₂
    dsimp [l₁, u₁, l₂, u₂]
    constructor
    · rintro ⟨h1,h2,h3,h4⟩
      exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
    · rintro ⟨⟨h1,h2⟩,h3,h4⟩
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  rw [hs, ← e.preimage_frontier]
  exact e.isConnected_preimage.mpr (isConnected_frontier_rectangle h₁ h₂)

#print axioms isConnected_frontier_rectangle
#print axioms isConnected_frontier_complexIntermediateGridSquare
end HarmonicBalls
