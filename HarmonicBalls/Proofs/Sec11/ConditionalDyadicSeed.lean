import HarmonicBalls.Proofs.Sec11.DyadicIntermediateSeed
import HarmonicBalls.Proofs.Sec11.ConditionalNullIntersection

/-! # Conditional dyadic mass and diameter seeds -/

namespace HarmonicBalls
open MeasureTheory Set Filter Topology
open scoped ENNReal

/-- Conditional mass positivity and convergence of the simultaneous tile
failure probability select a scale and parity class inside any positive
outside event. The scale may be required to exceed a prescribed index. -/
theorem exists_conditional_mass_tile_seed_after
    {Ω X : Type*} [m₀ : MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] (m : MeasurableSpace Ω) (hm : m ≤ m₀)
    (μ : Ω → Measure X) (S : Set X) (C : ℕ → Fin 4 → Set X)
    (E : ℕ → Set Ω) (c : ℝ≥0∞) (N : ℕ)
    (hcover : ∀ n, S ⊆ ⋃ j, C n j)
    (hH : @NullMeasurableSet Ω m₀ {ω | (8 : ℝ≥0∞) * c < μ ω S} P)
    (hcond : ∀ᵐ ω ∂P, 0 < (P[({ω | (8 : ℝ≥0∞) * c < μ ω S}).indicator
      (fun _ => (1 : ℝ)) | m]) ω)
    (hfail : Tendsto (fun n => P (E n)ᶜ) atTop (𝓝 0))
    (F : Set Ω) (hF : MeasurableSet[m] F) (hFp : 0 < P F) :
    ∃ n ≥ N, ∃ j, 0 < P {ω | ω ∈ F ∧ ω ∈ E n ∧
      (2 : ℝ≥0∞) * c < μ ω (C n j)} := by
  let : MeasurableSpace Ω := m₀
  have hp : 0 < P {ω | ω ∈ F ∧ (8 : ℝ≥0∞) * c < μ ω S} := by
    exact measure_inter_pos_of_condExp_indicator_pos_nullMeasurable P m hm hF hH hFp hcond
  have he : ∀ᶠ n in atTop, P (E n)ᶜ <
      P {ω | ω ∈ F ∧ (8 : ℝ≥0∞) * c < μ ω S} :=
    (tendsto_order.1 hfail).2 _ hp
  classical
  let E' : ℕ → Set Ω := fun n => if N ≤ n then E n else ∅
  obtain ⟨n, hn, hs⟩ := (he.and (eventually_ge_atTop N)).exists
  have hsmall : ∃ n, P (E' n)ᶜ <
      P {ω | ω ∈ F ∧ (8 : ℝ≥0∞) * c < μ ω S} := by
    exact ⟨n, by simpa [E', hs] using hn⟩
  obtain ⟨k, j, hj⟩ := exists_positive_measure_scale_and_four_tile_class_of_failure_bound
    P μ F S C E' c hcover hsmall
  have hk : N ≤ k := by
    by_contra hk
    have hz : {ω | ω ∈ F ∧ ω ∈ E' k ∧
        (2 : ℝ≥0∞) * c < μ ω (C k j)} = ∅ := by
      simp [E', hk]
    rw [hz, measure_empty] at hj
    exact (lt_irrefl _ hj)
  exact ⟨k, hk, j, by simpa [E', hk] using hj⟩

/-- A prescribed outside event contains a positive mass-carrying dyadic seed
with fixed small intermediate-square internal distances, provided the uniform
power estimate and conditional mass positivity hold. -/
theorem IsWholePlaneGFF.exists_conditional_intermediate_seed
    {Ω : Type*} [m₀ : MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (ξ : ℝ) (m : MeasurableSpace Ω) (hm : m ≤ m₀)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ)
    (a : ℂ) (L : ℝ) (hL : 0 < L) {U : Set ℂ}
    (hU : IsOpen U) (hsub : closedSquare a L ⊆ U)
    (b : ℕ → ℝ≥0∞) (c d : ℝ≥0∞) (p : ℝ) (hp : 2 < p)
    (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (hH : @NullMeasurableSet Ω m₀ {ω | (8 : ℝ≥0∞) * c < μ ω (closedSquare a L)} P)
    (hcond : ∀ᵐ ω ∂P, 0 < (P[({ω | (8 : ℝ≥0∞) * c < μ ω (closedSquare a L)}).indicator
      (fun _ => (1 : ℝ)) | m]) ω)
    (hmargin : ∀ᶠ n in atTop, b n < d)
    (hbound : ∀ᶠ n in atTop, ∀ i, P {ω | b n * ENNReal.ofReal
      (Real.exp (ξ * hcirc ω 1 0)) < dyadicIntermediateInternalDiameter D a L n i ω} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ ((p + e n) * n)))
    (F : Set Ω) (hF : MeasurableSet[m] F) (hFp : 0 < P F) :
    ∃ n j, (∀ i : Fin (2 ^ n) × Fin (2 ^ n),
      complexOpenEnlargedGridSquare a (L / (2 : ℝ) ^ n) i ⊆ U) ∧
      0 < P {ω | ω ∈ F ∧ (∀ i : Fin (2 ^ n) × Fin (2 ^ n), ∀ x ∈
        complexIntermediateGridSquare a (L / (2 : ℝ) ^ n) i, ∀ y ∈
        complexIntermediateGridSquare a (L / (2 : ℝ) ^ n) i,
          internalMetric (D ω) (complexOpenEnlargedGridSquare a (L / (2 : ℝ) ^ n) i) x y ≤ d) ∧
        (2 : ℝ≥0∞) * c < μ ω
          (squareCoordinates a ⁻¹' gridSquareClass (N := 2 ^ n) (L / 2 ^ n) j)} := by
  let : MeasurableSpace Ω := m₀
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (complex_enlarged_dyadic_square_eventually_subset_open a L hL hU hsub)
  have hfail := h.tendsto_dyadic_square_diameters_of_power_error ξ
    (dyadicIntermediateInternalDiameter D a L) b d p hp e he hmargin hbound
  obtain ⟨n, hn, j, hj⟩ := exists_conditional_mass_tile_seed_after P m hm μ
    (closedSquare a L)
    (fun n j => squareCoordinates a ⁻¹' gridSquareClass (N := 2 ^ n) (L / 2 ^ n) j)
    (fun n => {ω | ∀ i, dyadicIntermediateInternalDiameter D a L n i ω < d}) c N
    (complex_closed_square_subset_dyadic_classes a L hL) hH hcond hfail F hF hFp
  refine ⟨n, j, ?_, hj.trans_le (measure_mono ?_)⟩
  · intro i
    exact (complexOpenEnlargedGridSquare_subset a _ i).trans (hN n hn i)
  · intro ω hω
    refine ⟨hω.1, ?_, hω.2.2⟩
    intro i x hx y hy
    have hle : internalMetric (D ω)
        (complexOpenEnlargedGridSquare a (L / (2 : ℝ) ^ n) i) x y ≤
        dyadicIntermediateInternalDiameter D a L n i ω := by
      exact le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le y (le_iSup_of_le hy le_rfl)))
    exact hle.trans (hω.2.1 i).le

#print axioms IsWholePlaneGFF.exists_conditional_intermediate_seed

#print axioms exists_conditional_mass_tile_seed_after
end HarmonicBalls
