import HarmonicBalls.Proofs.Sec11.DyadicClosedGridCover

/-! # Mass selection on complex dyadic parity classes -/

namespace HarmonicBalls
open MeasureTheory Set Filter Topology
open scoped ENNReal BigOperators

/-- Conditional mass positivity and a uniform dyadic power estimate select
one of the concrete complex parity classes at a deterministic scale. -/
theorem IsWholePlaneGFF.exists_complex_square_mass_class_of_power_error
    {Ω : Type*} [m₀ : MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (ξ : ℝ) (m : MeasurableSpace Ω)
    (μ : Ω → Measure ℂ) (z : ℂ) (L : ℝ) (hL : 0 < L)
    (X : ∀ n, Fin (2 ^ n) × Fin (2 ^ n) → Ω → ℝ≥0∞)
    (a : ℕ → ℝ≥0∞) (c d : ℝ≥0∞) (p : ℝ) (hp : 2 < p)
    (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (hcond : ∀ᵐ ω ∂P, 0 < (P[({ω | (8 : ℝ≥0∞) * c < μ ω (closedSquare z L)}).indicator
      (fun _ => (1 : ℝ)) | m]) ω)
    (hmargin : ∀ᶠ n in atTop, a n < d)
    (hbound : ∀ᶠ n in atTop, ∀ i, P {ω | a n * ENNReal.ofReal
      (Real.exp (ξ * hcirc ω 1 0)) < X n i ω} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ ((p + e n) * n))) :
    ∃ n j, 0 < P {ω | (∀ i : Fin (2 ^ n) × Fin (2 ^ n), X n i ω < d) ∧
      (2 : ℝ≥0∞) * c < μ ω
        (squareCoordinates z ⁻¹' gridSquareClass (N := 2 ^ n) (L / 2 ^ n) j)} := by
  let : MeasurableSpace Ω := m₀
  apply h.exists_mass_class_of_dyadic_power_error ξ m μ (closedSquare z L)
    (fun n j => squareCoordinates z ⁻¹' gridSquareClass (N := 2 ^ n) (L / 2 ^ n) j)
    X a c d p hp e he
  · exact complex_closed_square_subset_dyadic_classes z L hL
  · exact hcond
  · exact hmargin
  · exact hbound

/-- The mass-carrying class can be chosen at an arbitrarily fine dyadic
scale, allowing additional eventual geometric conditions to be imposed. -/
theorem IsWholePlaneGFF.exists_complex_square_mass_class_after
    {Ω : Type*} [m₀ : MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (ξ : ℝ) (m : MeasurableSpace Ω)
    (μ : Ω → Measure ℂ) (z : ℂ) (L : ℝ) (hL : 0 < L) (N : ℕ)
    (X : ∀ n, Fin (2 ^ n) × Fin (2 ^ n) → Ω → ℝ≥0∞)
    (a : ℕ → ℝ≥0∞) (c d : ℝ≥0∞) (p : ℝ) (hp : 2 < p)
    (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (hcond : ∀ᵐ ω ∂P, 0 < (P[({ω | (8 : ℝ≥0∞) * c < μ ω (closedSquare z L)}).indicator
      (fun _ => (1 : ℝ)) | m]) ω)
    (hmargin : ∀ᶠ n in atTop, a n < d)
    (hbound : ∀ᶠ n in atTop, ∀ i, P {ω | a n * ENNReal.ofReal
      (Real.exp (ξ * hcirc ω 1 0)) < X n i ω} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ ((p + e n) * n))) :
    ∃ n ≥ N, ∃ j, 0 < P {ω | (∀ i : Fin (2 ^ n) × Fin (2 ^ n), X n i ω < d) ∧
      (2 : ℝ≥0∞) * c < μ ω
        (squareCoordinates z ⁻¹' gridSquareClass (N := 2 ^ n) (L / 2 ^ n) j)} := by
  classical
  let : MeasurableSpace Ω := m₀
  let X' : ∀ n, Fin (2 ^ n) × Fin (2 ^ n) → Ω → ℝ≥0∞ :=
    fun n i ω => if N ≤ n then X n i ω else ∞
  have hb : ∀ᶠ n in atTop, ∀ i, P {ω | a n * ENNReal.ofReal
      (Real.exp (ξ * hcirc ω 1 0)) < X' n i ω} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ ((p + e n) * n)) := by
    filter_upwards [hbound, eventually_ge_atTop N] with n hn hN i
    simpa only [X', ite_eq_left hN] using hn i
  obtain ⟨n, j, hj⟩ := h.exists_complex_square_mass_class_of_power_error
    ξ m μ z L hL X' a c d p hp e he hcond hmargin hb
  have hN : N ≤ n := by
    by_contra hN
    have hempty : {ω | (∀ i : Fin (2 ^ n) × Fin (2 ^ n), X' n i ω < d) ∧
      (2 : ℝ≥0∞) * c < μ ω
        (squareCoordinates z ⁻¹' gridSquareClass (N := 2 ^ n) (L / 2 ^ n) j)} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro hall
      let i : Fin (2 ^ n) := ⟨0, by positivity⟩
      have hh := hall (i, i)
      simp only [X', ite_eq_right hN] at hh
      exact False.elim ((not_lt_of_ge le_top) hh)
    rw [hempty, measure_empty] at hj
    exact (lt_irrefl _ hj)
  refine ⟨n, hN, j, ?_⟩
  simpa only [X', ite_eq_left hN] using hj

end HarmonicBalls
