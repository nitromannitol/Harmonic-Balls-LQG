import HarmonicBalls.Proofs.Sec11.ConnectedRemoval

/-! # Geometry of the intermediate-square core -/

namespace HarmonicBalls
open Set

/-- The protected squares are exactly the selected parity class used in the
mass estimate. -/
theorem union_complexGridSquare_eq_class {N : ℕ} (a : ℂ) (r : ℝ) (j : Fin 4) :
    (⋃ i : {i : Fin N × Fin N // squareParity i = j},
      complexGridSquare a r i.1) =
      squareCoordinates a ⁻¹' gridSquareClass (N := N) r j := by
  classical
  ext x
  simp only [mem_iUnion, mem_preimage, gridSquareClass, complexGridSquare]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i.1, by simpa [i.2] using hi⟩
  · rintro ⟨i, hi⟩
    by_cases hj : squareParity i = j
    · exact ⟨⟨i, hj⟩, by simpa [hj] using hi⟩
    · simp [hj] at hi

/-- Removing the interiors of one parity class yields a connected compact
core and shift neighborhoods avoiding the protected mass class and the closed
observation set. Each removed intermediate square remains attached to the
core. -/
theorem dyadic_intermediate_connected_core_geometry {N : ℕ} (a : ℂ) (r : ℝ)
    (hr : 0 < r) (j : Fin 4) (K W F : Set ℂ) (hKc : IsCompact K)
    (hK : IsConnected K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hF : IsClosed F) (hKF : Disjoint K F)
    (hHK : ∀ i : {i : Fin N × Fin N // squareParity i = j},
      complexIntermediateGridSquare a r i.1 ⊆ K) :
    let H := fun i : {i : Fin N × Fin N // squareParity i = j} =>
      complexIntermediateGridSquare a r i.1
    let C := K \ ⋃ i, interior (H i)
    IsCompact C ∧ IsConnected C ∧
      (∀ x ∈ K, x ∈ C ∨ ∃ i, x ∈ H i) ∧
      (∀ i, (H i ∩ C).Nonempty) ∧
      Disjoint (squareCoordinates a ⁻¹' gridSquareClass (N := N) r j) C ∧
      ∃ V T : Set ℂ, IsOpen V ∧ IsConnected V ∧ C ⊆ V ∧
        IsCompact (closure V) ∧ IsOpen T ∧ closure V ⊆ T ∧ T ⊆ W ∧
        Disjoint T F ∧ Disjoint T (squareCoordinates a ⁻¹' gridSquareClass (N := N) r j) := by
  have hconn := isConnected_dyadic_intermediate_core a r hr j K hKc hK hHK
  obtain ⟨hc, hcover, hattach, hd⟩ := dyadic_intermediate_compact_core a r hr j K hKc hHK
  obtain ⟨V, T, hVo, hVc, hCV, hVcompact, hTo, hVT, hTW, hTF, hTS⟩ :=
    dyadic_intermediate_core_shift_neighborhoods a r hr j K W F hKc hW hKW hF hKF hHK hconn
  rw [union_complexGridSquare_eq_class] at hd hTS
  exact ⟨hc, hconn, hcover, hattach, hd, V, T, hVo, hVc, hCV, hVcompact,
    hTo, hVT, hTW, hTF, hTS⟩

end HarmonicBalls
