import HarmonicBalls.Proofs.Sec11.DyadicSquareBuffer
import HarmonicBalls.Proofs.Sec11.DyadicSquareMassSelection

/-! # Enlarged dyadic squares inside an open neighborhood -/

namespace HarmonicBalls
open Set Filter Topology Metric MeasureTheory
open scoped ENNReal BigOperators

/-- A rectangular enlargement lies in a metric thickening of the original
square, with twice the coordinate buffer as radius. -/
theorem closedSquare_buffer_subset_thickening (a : ℂ) (L ε : ℝ)
    (hL : 0 ≤ L) (hε : 0 < ε) :
    closedSquare (a - ⟨ε, ε⟩) (L + 2 * ε) ⊆
      thickening (3 * ε) (closedSquare a L) := by
  intro z hz
  simp only [closedSquare, Complex.mem_reProdIm, mem_Icc, Complex.sub_re,
    Complex.sub_im] at hz
  let x := min (max z.re a.re) (a.re + L)
  let y := min (max z.im a.im) (a.im + L)
  let w : ℂ := ⟨x, y⟩
  have hxl : a.re ≤ x := le_min (le_max_right _ _) (by linarith)
  have hxu : x ≤ a.re + L := min_le_right _ _
  have hyl : a.im ≤ y := le_min (le_max_right _ _) (by linarith)
  have hyu : y ≤ a.im + L := min_le_right _ _
  have hxlo : z.re - ε ≤ x := by
    apply le_min
    · exact le_trans (by linarith) (le_max_left _ _)
    · linarith [hz.1.2]
  have hxhi : x ≤ z.re + ε := by
    apply le_trans (min_le_left _ _)
    exact max_le (by linarith) (by linarith [hz.1.1])
  have hylo : z.im - ε ≤ y := by
    apply le_min
    · exact le_trans (by linarith) (le_max_left _ _)
    · linarith [hz.2.2]
  have hyhi : y ≤ z.im + ε := by
    apply le_trans (min_le_left _ _)
    exact max_le (by linarith) (by linarith [hz.2.1])
  apply mem_thickening_iff.mpr
  refine ⟨w, ?_, ?_⟩
  · simpa [closedSquare, w, Complex.mem_reProdIm, mem_Icc] using And.intro (And.intro hxl hxu) (And.intro hyl hyu)
  · have hn := Complex.norm_le_abs_re_add_abs_im (z - w)
    have hx : |z.re - x| ≤ ε := abs_le.mpr ⟨by linarith, by linarith⟩
    have hy : |z.im - y| ≤ ε := abs_le.mpr ⟨by linarith, by linarith⟩
    rw [dist_eq_norm]
    simp only [Complex.sub_re, Complex.sub_im] at hn
    change ‖z - w‖ < 3 * ε
    change ‖z - w‖ ≤ |z.re - x| + |z.im - y| at hn
    linarith

/-- If a closed square is compactly contained in an open set, every enlarged
square of a sufficiently fine dyadic subdivision is contained in that set. -/
theorem complex_enlarged_dyadic_square_eventually_subset_open
    (a : ℂ) (L : ℝ) (hL : 0 < L) {U : Set ℂ} (hU : IsOpen U)
    (hsub : closedSquare a L ⊆ U) :
    ∀ᶠ n : ℕ in atTop, ∀ i : Fin (2 ^ n) × Fin (2 ^ n),
      complexEnlargedGridSquare a (L / (2 : ℝ) ^ n) i ⊆ U := by
  have hcompact : IsCompact (closedSquare a L) :=
    IsCompact.reProdIm isCompact_Icc isCompact_Icc
  obtain ⟨δ, hδ, hδU⟩ := hcompact.exists_thickening_subset_open hU hsub
  have hε : 0 < δ / 4 := by positivity
  have hbuf := closedSquare_buffer_subset_thickening a L (δ / 4) hL.le hε
  have hmono : thickening (3 * (δ / 4)) (closedSquare a L) ⊆
      thickening δ (closedSquare a L) := by
    apply thickening_mono
    linarith
  filter_upwards [complex_enlarged_dyadic_square_subset_buffer a L (δ / 4) hL hε]
    with n hn i
  exact (hn i).trans (hbuf.trans (hmono.trans hδU))

/-- A mass-carrying dyadic parity class can be selected with all its enlarged
squares contained in the prescribed open neighborhood. -/
theorem IsWholePlaneGFF.exists_complex_square_mass_class_inside_open
    {Ω : Type*} [m₀ : MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (ξ : ℝ) (m : MeasurableSpace Ω)
    (μ : Ω → Measure ℂ) (a : ℂ) (L : ℝ) (hL : 0 < L)
    {U : Set ℂ} (hU : IsOpen U) (hsub : closedSquare a L ⊆ U)
    (X : ∀ n, Fin (2 ^ n) × Fin (2 ^ n) → Ω → ℝ≥0∞)
    (b : ℕ → ℝ≥0∞) (c d : ℝ≥0∞) (p : ℝ) (hp : 2 < p)
    (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (hcond : ∀ᵐ ω ∂P, 0 < (P[({ω | (8 : ℝ≥0∞) * c < μ ω (closedSquare a L)}).indicator
      (fun _ => (1 : ℝ)) | m]) ω)
    (hmargin : ∀ᶠ n in atTop, b n < d)
    (hbound : ∀ᶠ n in atTop, ∀ i, P {ω | b n * ENNReal.ofReal
      (Real.exp (ξ * hcirc ω 1 0)) < X n i ω} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ ((p + e n) * n))) :
    ∃ n j, (∀ i : Fin (2 ^ n) × Fin (2 ^ n),
      complexEnlargedGridSquare a (L / (2 : ℝ) ^ n) i ⊆ U) ∧
      0 < P {ω | (∀ i : Fin (2 ^ n) × Fin (2 ^ n), X n i ω < d) ∧
        (2 : ℝ≥0∞) * c < μ ω
          (squareCoordinates a ⁻¹' gridSquareClass (N := 2 ^ n) (L / 2 ^ n) j)} := by
  let : MeasurableSpace Ω := m₀
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (complex_enlarged_dyadic_square_eventually_subset_open a L hL hU hsub)
  obtain ⟨n, hn, j, hj⟩ := h.exists_complex_square_mass_class_after ξ m μ a L hL N
    X b c d p hp e he hcond hmargin hbound
  exact ⟨n, j, hN n hn, hj⟩

end HarmonicBalls
