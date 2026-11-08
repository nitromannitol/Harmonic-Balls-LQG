import HarmonicBalls.Proofs.Sec11.Closure.FixedMassDiameter

/-!
# Fixed-geometry instance with the pinned set outside a neighbourhood of `W` (Section 11, draft lines 376–446)

`Closure/FixedMassDiameter.lean` instantiates `hinside_of_square_dyadic_tail` with the pinned set
`O = B_{6/5}(0)`. The pinned σ-algebra `comap (localModConstPairings 0 hC O)` is the largest one allowed by the
hypotheses of the dyadic-core producer when `O` is the complement of a neighbourhood of `W = B_{.04}(1.5)`:
the producer needs only `sphere 0 1 ⊆ O` and `Disjoint (closure V) (closure O)`. This module uses the
pinned set `O = ℂ \ cl B_{3/100}(3/2)`, which is the field outside a neighbourhood of `W`, as in the written
argument ("measurable outside `W`", tex lines 490–491; the measurability claim is under review, see F3 in the
status note). The leftover premises are those of `FixedMassDiameter.lean`.
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

/-- The pinned set `O = ℂ \ cl B_{3/100}(3/2)`, the field outside a neighbourhood of `W = B_{.04}(1.5)`. -/
noncomputable def fixedOutside : Set ℂ := (closedBall pinchCentreA (3 / 100))ᶜ

/-- The unit circle lies outside the closed disc of radius `3/100` about `3/2`. -/
lemma fixed_sphere_subset_outside : sphere (0 : ℂ) 1 ⊆ fixedOutside := by
  intro z hz
  rw [mem_sphere_zero_iff_norm] at hz
  unfold fixedOutside
  intro hcl
  rw [mem_closedBall] at hcl
  have h := fixed_abs_norm_sub_le_dist z pinchCentreA
  rw [norm_pinchCentreA, hz] at h
  have h2 := (abs_le.1 (h.trans hcl)).1
  linarith

/-- The closure of `V` is disjoint from the closure of the pinned set `O`. -/
lemma fixed_closure_outside_disjoint : Disjoint (closure fixedV) (closure fixedOutside) := by
  rw [Set.disjoint_left]
  intro x hxV hxO
  have hO : closure fixedOutside ⊆ {x : ℂ | 3 / 100 ≤ dist x pinchCentreA} := by
    apply closure_minimal _ (isClosed_le continuous_const (continuous_id.dist continuous_const))
    intro y hy
    show 3 / 100 ≤ dist y pinchCentreA
    unfold fixedOutside at hy
    by_contra hlt
    exact hy (mem_closedBall.2 (le_of_lt (not_le.1 hlt)))
  have h1 : dist x pinchCentreA ≤ 1 / 50 := mem_closedBall.1 (fixed_closure_V_sub hxV)
  have h2 : 3 / 100 ≤ dist x pinchCentreA := hO hxO
  linarith

/-- The fixed-geometry instance of `hinside` with the pinned set `O = ℂ \ cl B_{3/100}(3/2)`: for every `n > 0`
and mass threshold `k`, the conditional positivity given the field outside a neighbourhood of `W`. The leftover
premises are those of `fixed_hinside_of_square_dyadic_tail`. -/
theorem fixed_outside_hinside_of_square_dyadic_tail {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {α γ ξ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hγ : 0 < γ) (hξ : 0 < ξ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hfull : ∀ᵐ ω ∂P, ∀ W : Set ℂ, IsOpen W → W.Nonempty → 0 < μ ω W)
    (hfront : ∀ᵐ ω ∂P, μ ω (frontier (closedSquare fixedSquareCorner fixedSquareSide)) = 0)
    (hdata : SquareDyadicTailInput P ξ hC hcirc 𝔇 fixedSquareCorner fixedSquareSide) :
    ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∀ᵐ ω ∂P, 0 < (P[({ω | internalDiam (𝔇 (hC ω)) fixedDelta fixedV < (n : ℝ≥0∞)⁻¹ ∧
        (k : ℝ≥0∞) < μ ω fixedU}).indicator (fun _ => (1 : ℝ)) |
          MeasurableSpace.comap (localModConstPairings 0 hC fixedOutside) inferInstance]) ω :=
  hinside_of_square_dyadic_tail h hμ hγ hξ fixedSquareCorner fixedSquareSide fixedSquareSide_pos
    fixedU fixedV fixedOutside isOpen_ball.measurableSet fixed_square_subset_U fixed_buffer_square
    hfront fixedDelta_pos fixed_sphere_subset_outside 𝔇 h𝔇 fixed_closure_V_compact fixed_V_connected
    fixed_closure_outside_disjoint fixed_square_subset_interior_closure hfull hdata

#print axioms fixed_outside_hinside_of_square_dyadic_tail

end HarmonicBalls
