import HarmonicBalls.Proofs.Sec11.DyadicIntermediateSquare

/-! # A mass-carrying dyadic class with small internal distances -/

namespace HarmonicBalls
open Set Filter Topology MeasureTheory
open scoped ENNReal BigOperators

/-- A uniform diameter tail and conditional mass positivity give a fixed
dyadic parity class whose enlarged squares are disjoint and lie in the given
open neighborhood.  With positive probability the class carries mass and
every tile has uniformly small internal distances. -/
theorem IsWholePlaneGFF.exists_dyadic_intermediate_square_seed
    {Ω : Type*} [m₀ : MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (ξ : ℝ) (m : MeasurableSpace Ω)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ)
    (a : ℂ) (L : ℝ) (hL : 0 < L)
    {U : Set ℂ} (hU : IsOpen U) (hsub : closedSquare a L ⊆ U)
    (b : ℕ → ℝ≥0∞) (c d : ℝ≥0∞) (p : ℝ) (hp : 2 < p)
    (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (hcond : ∀ᵐ ω ∂P, 0 < (P[({ω | (8 : ℝ≥0∞) * c < μ ω (closedSquare a L)}).indicator
      (fun _ => (1 : ℝ)) | m]) ω)
    (hmargin : ∀ᶠ n in atTop, b n < d)
    (hbound : ∀ᶠ n in atTop, ∀ i, P {ω | b n * ENNReal.ofReal
      (Real.exp (ξ * hcirc ω 1 0)) < dyadicIntermediateInternalDiameter D a L n i ω} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ ((p + e n) * n))) :
    ∃ n j, (∀ i : Fin (2 ^ n) × Fin (2 ^ n),
      complexOpenEnlargedGridSquare a (L / (2 : ℝ) ^ n) i ⊆ U) ∧
      (∀ i k : Fin (2 ^ n) × Fin (2 ^ n), squareParity i = j → squareParity k = j →
        i ≠ k → Disjoint (complexOpenEnlargedGridSquare a (L / (2 : ℝ) ^ n) i)
          (complexOpenEnlargedGridSquare a (L / (2 : ℝ) ^ n) k)) ∧
      0 < P {ω | (∀ i : Fin (2 ^ n) × Fin (2 ^ n), ∀ x ∈
        complexIntermediateGridSquare a (L / (2 : ℝ) ^ n) i, ∀ y ∈
        complexIntermediateGridSquare a (L / (2 : ℝ) ^ n) i,
          internalMetric (D ω) (complexOpenEnlargedGridSquare a (L / (2 : ℝ) ^ n) i) x y ≤ d) ∧
        (2 : ℝ≥0∞) * c < μ ω
          (squareCoordinates a ⁻¹' gridSquareClass (N := 2 ^ n) (L / 2 ^ n) j)} := by
  let : MeasurableSpace Ω := m₀
  obtain ⟨n, j, hU', hpos⟩ := h.exists_complex_square_mass_class_inside_open ξ m μ a L hL
    hU hsub (dyadicIntermediateInternalDiameter D a L) b c d p hp e he hcond hmargin hbound
  have hr : 0 < L / (2 : ℝ) ^ n := by positivity
  refine ⟨n, j, ?_, ?_, hpos.trans_le (measure_mono ?_)⟩
  · intro i
    exact (complexOpenEnlargedGridSquare_subset a _ i).trans (hU' i)
  · intro i k hi hk hik
    exact (complex_enlarged_grid_squares_disjoint a _ hr i k (hi.trans hk.symm) hik).mono
      (complexOpenEnlargedGridSquare_subset a _ i)
      (complexOpenEnlargedGridSquare_subset a _ k)
  · intro ω hω
    refine ⟨?_, hω.2⟩
    intro i x hx y hy
    have hle : internalMetric (D ω)
        (complexOpenEnlargedGridSquare a (L / (2 : ℝ) ^ n) i) x y ≤
        dyadicIntermediateInternalDiameter D a L n i ω := by
      exact le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le y (le_iSup_of_le hy le_rfl)))
    exact hle.trans (hω.1 i).le

#print axioms IsWholePlaneGFF.exists_dyadic_intermediate_square_seed
end HarmonicBalls
