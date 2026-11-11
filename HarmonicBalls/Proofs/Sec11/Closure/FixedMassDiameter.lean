import HarmonicBalls.Proofs.Sec11.Closure.MassDiameterInside
import HarmonicBalls.Proofs.Sec11.Closure.CorrectedFixedGeometry

/-!
# Fixed-geometry instance of the conditional mass-diameter positivity (Section 11)

`Closure/MassDiameterInside.lean` gives the hypothesis `hinside` of the conditional chain for any square
`closedSquare z L ⊆ U`, any pinned set `O` with `sphere 0 1 ⊆ O` and `Disjoint (closure V) (closure O)`.
This module chooses the data of the fixed corrected configuration (`Closure/CorrectedFixedGeometry.lean`):
the square with corner `3/2 - 1/400 - i/400` and side `1/200`, which lies in `U = B_{.01}(1.5)`; the pinned set
`O = B_{6/5}(0)`; and `δ = 10⁻⁴`. It proves the geometric hypotheses of the dyadic-core producer.

The hypotheses that remain explicit are the GFF and LQG data, the full-support hypothesis `hfull` (from
`LQGVolumeGrowthAllScalesStmt`), `0 < ξ`, the boundary-null hypothesis `hfront` of the square, and the square
tail premise `SquareDyadicTailInput`. The measurable clause of `hinside` is not included.
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

/-- The lower-left corner `3/2 - 1/400 - i/400` of the fixed test square. -/
noncomputable def fixedSquareCorner : ℂ := ⟨3 / 2 - 1 / 400, -(1 / 400)⟩

/-- The side `1/200` of the fixed test square. -/
noncomputable def fixedSquareSide : ℝ := 1 / 200

/-- The pinned outer set `O = B_{6/5}(0)`, which contains the unit circle. -/
noncomputable def fixedPinned : Set ℂ := ball (0 : ℂ) (6 / 5)

lemma fixedSquareCorner_re : fixedSquareCorner.re = 3 / 2 - 1 / 400 := rfl

lemma fixedSquareCorner_im : fixedSquareCorner.im = -(1 / 400) := rfl

lemma fixedSquareSide_eq : fixedSquareSide = 1 / 200 := rfl

lemma fixedSquareSide_pos : 0 < fixedSquareSide := by
  rw [fixedSquareSide_eq]
  norm_num

lemma fixedDelta_pos : 0 < fixedDelta := by
  rw [fixedDelta_eq]
  norm_num

/-- Real and imaginary parts of the points of the fixed square. -/
lemma fixed_square_re_im {x : ℂ} (hx : x ∈ closedSquare fixedSquareCorner fixedSquareSide) :
    3 / 2 - 1 / 400 ≤ x.re ∧ x.re ≤ 3 / 2 + 1 / 400 ∧ -(1 / 400) ≤ x.im ∧ x.im ≤ 1 / 400 := by
  have h := hx
  simp only [closedSquare, Complex.mem_reProdIm, mem_Icc, fixedSquareCorner_re,
    fixedSquareCorner_im, fixedSquareSide_eq] at h
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
  exact ⟨h1, by linarith, h3, by linarith⟩

lemma pinchCentreA_im' : pinchCentreA.im = 0 := by simp [pinchCentreA]

lemma fixed_square_subset_U : closedSquare fixedSquareCorner fixedSquareSide ⊆ fixedU := by
  intro x hx
  obtain ⟨h1, h2, h3, h4⟩ := fixed_square_re_im hx
  unfold fixedU
  rw [mem_ball, dist_eq_norm]
  have h := Complex.norm_le_abs_re_add_abs_im (x - pinchCentreA)
  rw [Complex.sub_re, Complex.sub_im, pinchCentreA_re, pinchCentreA_im'] at h
  have hr : |x.re - 3 / 2| ≤ 1 / 400 := abs_le.2 ⟨by linarith, by linarith⟩
  have hi : |x.im - 0| ≤ 1 / 400 := abs_le.2 ⟨by linarith, by linarith⟩
  linarith

/-- The norm of a point of the fixed square is at most `2`. -/
lemma fixed_square_norm_le {x : ℂ} (hx : x ∈ closedSquare fixedSquareCorner fixedSquareSide) :
    ‖x‖ ≤ 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := fixed_square_re_im hx
  have h := Complex.norm_le_abs_re_add_abs_im x
  have hr : |x.re| ≤ 3 / 2 + 1 / 400 := abs_le.2 ⟨by linarith, by linarith⟩
  have hi : |x.im| ≤ 1 / 400 := abs_le.2 ⟨by linarith, by linarith⟩
  linarith

/-- The dyadic buffer of the square lies in `B_4(0)`, as required by `hbufferS`. -/
lemma fixed_buffer_square :
    ∀ (n : ℕ) (x : ℂ), x ∈ closedSquare fixedSquareCorner fixedSquareSide →
      closedBall x (dyadicScale n) ⊆ ball (0 : ℂ) 4 := by
  intro n x hx y hy
  have hx2 := fixed_square_norm_le hx
  have hn : dyadicScale n ≤ 1 := by
    unfold dyadicScale
    exact pow_le_one₀ (by norm_num) (by norm_num)
  rw [mem_closedBall, dist_eq_norm] at hy
  rw [mem_ball, dist_zero_right]
  have h1 := norm_sub_norm_le y x
  linarith

lemma fixed_square_subset_interior_closure :
    closedSquare fixedSquareCorner fixedSquareSide ⊆ interior (closure fixedV) := by
  have hUV : fixedU ⊆ fixedV := ball_subset_ball (by norm_num)
  have hVint : fixedV ⊆ interior (closure fixedV) := interior_maximal subset_closure isOpen_ball
  exact fixed_square_subset_U.trans (hUV.trans hVint)

lemma fixed_sphere_subset_pinned : sphere (0 : ℂ) 1 ⊆ fixedPinned := by
  intro z hz
  rw [mem_sphere_zero_iff_norm] at hz
  unfold fixedPinned
  rw [mem_ball, dist_zero_right, hz]
  norm_num

lemma fixed_closure_V_compact : IsCompact (closure fixedV) :=
  (isCompact_closedBall pinchCentreA (1 / 50)).of_isClosed_subset isClosed_closure
    fixed_closure_V_sub

lemma fixed_V_connected : IsConnected (closure fixedV) := by
  have hV : IsConnected fixedV :=
    ⟨⟨pinchCentreA, mem_ball_self (by norm_num)⟩, (convex_ball _ _).isPreconnected⟩
  exact hV.closure

lemma fixed_V_pinned_disjoint : Disjoint (closure fixedV) (closure fixedPinned) := by
  rw [Set.disjoint_left]
  intro x hxV hxO
  unfold fixedPinned at hxO
  have h1 : dist x pinchCentreA ≤ 1 / 50 := mem_closedBall.1 (fixed_closure_V_sub hxV)
  have h2 : dist x 0 ≤ 6 / 5 := mem_closedBall.1 (closure_ball_subset_closedBall hxO)
  rw [dist_zero_right] at h2
  have h3 := fixed_abs_norm_sub_le_dist x pinchCentreA
  rw [norm_pinchCentreA] at h3
  have h4 := (abs_le.1 (h3.trans h1)).1
  linarith

/-- The fixed-geometry instance of `hinside`: for every `n > 0` and mass threshold `k`, the conditional
positivity of `{internalDiam(D_h) V < 1/n, k < μ U}` given the pinned outside σ-algebra, almost surely, from
the dyadic-core producer. The leftover premises are the GFF and LQG data, the full-support `hfull`, `0 < ξ`,
the boundary-null `hfront` of the square, and the square tail `SquareDyadicTailInput`. -/
theorem fixed_hinside_of_square_dyadic_tail {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
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
          MeasurableSpace.comap (localModConstPairings 0 hC fixedPinned) inferInstance]) ω :=
  hinside_of_square_dyadic_tail h hμ hγ hξ fixedSquareCorner fixedSquareSide fixedSquareSide_pos
    fixedU fixedV fixedPinned isOpen_ball.measurableSet fixed_square_subset_U fixed_buffer_square
    hfront fixedDelta_pos fixed_sphere_subset_pinned 𝔇 h𝔇 fixed_closure_V_compact fixed_V_connected
    fixed_V_pinned_disjoint fixed_square_subset_interior_closure hfull hdata


end HarmonicBalls
