import HarmonicBalls.Proofs.Sec8.CircleDensity

/-! # Local circle-density approximations

A disk around the origin inherits the local containment of a disk of the same
radius, and both disks can be enlarged by a common positive amount. The
imported Section 8 argument uses Leonardo Bonanno's LatticeProb formalization
of the ergodic theorem.
-/

open MeasureTheory Set Metric Filter
open scoped Topology

namespace HarmonicBalls

/-- If a disk is contained in a centered ball, then the concentric disk of the
same radius is contained in that ball as well. -/
theorem closedBall_zero_subset_of_closedBall_subset {r ε : ℝ} (z : ℂ)
    (hz : closedBall z r ⊆ ball 0 ε) : closedBall (0 : ℂ) r ⊆ ball 0 ε := by
  intro x hx
  have hxnorm : ‖x‖ ≤ r := by simpa [mem_closedBall, dist_zero_right] using hx
  have hp : z + x ∈ ball (0 : ℂ) ε := hz (by
    rw [mem_closedBall, dist_eq_norm]
    simpa using hxnorm)
  have hm : z - x ∈ ball (0 : ℂ) ε := hz (by
    rw [mem_closedBall, dist_eq_norm]
    simpa using hxnorm)
  have hp' : ‖z + x‖ < ε := by simpa [mem_ball, dist_zero_right] using hp
  have hm' : ‖z - x‖ < ε := by simpa [mem_ball, dist_zero_right] using hm
  have h := norm_sub_le (z + x) (z - x)
  have heq : (z + x) - (z - x) = (2 : ℂ) * x := by ring
  rw [heq, norm_mul] at h
  have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [htwo] at h
  rw [mem_ball, dist_zero_right]
  nlinarith

/-- A compact disk contained in an open set can be enlarged slightly while
remaining in the open set. -/
theorem exists_enlarged_closedBall_subset_open {r : ℝ} (hr : 0 ≤ r) (z : ℂ)
    {U : Set ℂ} (hU : IsOpen U) (hz : closedBall z r ⊆ U) :
    ∃ η > 0, closedBall z (r + η) ⊆ U := by
  obtain ⟨η, hη, hsub⟩ := (isCompact_closedBall z r).exists_cthickening_subset_open hU hz
  refine ⟨η, hη, ?_⟩
  simpa [cthickening_closedBall hη.le hr, add_comm] using hsub

/-- Both circles admit a common buffer inside the field's local domain. -/
theorem exists_common_circle_buffer {r ε : ℝ} (hr : 0 ≤ r) (z : ℂ)
    (hz : closedBall z r ⊆ ball 0 ε) :
    ∃ η > 0, closedBall z (r + η) ⊆ ball 0 ε ∧
      closedBall (0 : ℂ) (r + η) ⊆ ball 0 ε := by
  obtain ⟨ηz, hηz, hz'⟩ := exists_enlarged_closedBall_subset_open hr z isOpen_ball hz
  obtain ⟨η0, hη0, h0'⟩ := exists_enlarged_closedBall_subset_open hr 0 isOpen_ball
    (closedBall_zero_subset_of_closedBall_subset z hz)
  refine ⟨min ηz η0, lt_min hηz hη0, ?_, ?_⟩
  · exact (closedBall_subset_closedBall (by linarith [min_le_left ηz η0])).trans hz'
  · have hsub : closedBall (0 : ℂ) (r + min ηz η0) ⊆ closedBall 0 (r + η0) :=
      closedBall_subset_closedBall (by linarith [min_le_right ηz η0])
    exact hsub.trans h0'

/-- The annular widths used to approximate a circle. -/
noncomputable def circleDensityWidth (r η : ℝ) (n : ℕ) : ℝ :=
  r * η / ((n : ℝ) + 1)

theorem circleDensityWidth_pos {r η : ℝ} (hr : 0 < r) (hη : 0 < η) (n : ℕ) :
    0 < circleDensityWidth r η n := by
  unfold circleDensityWidth
  positivity

theorem circleDensityWidth_tendsto_zero (r η : ℝ) :
    Tendsto (circleDensityWidth r η) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => r * η / ((n : ℝ) + 1)) atTop (𝓝 0)
  simpa [div_eq_mul_inv] using
    (tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))

/-- Explicit local zero-integral tests built from annular densities, with widths
converging to zero. This leaves convergence of their logarithmic energy open. -/
theorem exists_local_circleDensity_tests {r ε : ℝ} (hr : 0 < r) (z : ℂ)
    (hz : closedBall z r ⊆ ball 0 ε) :
    ∃ (η : ℝ) (hη : 0 < η),
      let δ := circleDensityWidth r η
      let hδ := circleDensityWidth_pos hr hη
      let φ := fun n x =>
        (∫ y, circleDensity r (δ n) (hδ n) 0 y)⁻¹ * circleDensity r (δ n) (hδ n) z x -
        (∫ y, circleDensity r (δ n) (hδ n) 0 y)⁻¹ * circleDensity r (δ n) (hδ n) 0 x
      Tendsto δ atTop (𝓝 0) ∧
      (∀ n, IsTestFunction (ball 0 ε) (φ n) ∧ ∫ x, φ n x = 0) ∧
      (∀ n x, x ∈ Function.support (circleDensity r (δ n) (hδ n) z) →
        |‖x - z‖ - r| < η / ((n : ℝ) + 1)) ∧
      (∀ n x, x ∈ Function.support (circleDensity r (δ n) (hδ n) 0) →
        |‖x‖ - r| < η / ((n : ℝ) + 1)) := by
  obtain ⟨η, hη, hz', h0'⟩ := exists_common_circle_buffer hr.le z hz
  refine ⟨η, hη, circleDensityWidth_tendsto_zero r η, ?_, ?_, ?_⟩
  · intro n
    have hwidth : circleDensityWidth r η n ≤ r * η := by
      unfold circleDensityWidth
      apply div_le_self (mul_nonneg hr.le hη.le)
      exact le_add_of_nonneg_left (Nat.cast_nonneg n)
    exact circleDensity_normalized_difference_test hr (circleDensityWidth_pos hr hη n)
      hwidth z (ball 0 ε) hz' h0'
  · intro n x hx
    apply circleDensity_support_radius hr (circleDensityWidth_pos hr hη n) _ z x hx
    simp only [circleDensityWidth]
    ring_nf
    exact le_rfl
  · intro n x hx
    have h := circleDensity_support_radius hr (circleDensityWidth_pos hr hη n)
      (η := η / ((n : ℝ) + 1)) (by simp [circleDensityWidth, div_eq_mul_inv, mul_assoc]) 0 x hx
    simpa using h

/-- Difference of the normalized annular densities at `z` and at the origin. -/
noncomputable def circleDensityDifference (r η : ℝ) (hr : 0 < r) (hη : 0 < η)
    (z : ℂ) (n : ℕ) (x : ℂ) : ℝ :=
  let δ := circleDensityWidth r η n
  let hδ := circleDensityWidth_pos hr hη n
  (∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ z x -
    (∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ 0 x

/-- The local centered circle version follows once the logarithmic covariance
error of the explicit annular densities tends to zero. -/
theorem IsWholePlaneGFF.exists_joint_centered_circle_version_of_circleDensity_limit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) {ε r : ℝ} (hr : 0 < r)
    (hkernel : ∀ z, closedBall z r ⊆ ball 0 ε → ∀ η (hη : 0 < η),
      Tendsto (fun n =>
        wholePlaneGFFCov (.pairing (circleDensityDifference r η hr hη z n))
          (.pairing (circleDensityDifference r η hr hη z n)) +
        wholePlaneGFFCov (.circle r z) (.circle r z) +
        wholePlaneGFFCov (.circle r 0) (.circle r 0) -
        2 * wholePlaneGFFCov (.circle r z) (.circle r 0) -
        2 * wholePlaneGFFCov (.pairing (circleDensityDifference r η hr hη z n)) (.circle r z) +
        2 * wholePlaneGFFCov (.pairing (circleDensityDifference r η hr hη z n)) (.circle r 0))
        atTop (𝓝 0)) :
    ∃ d : Ω → ℂ → ℝ,
      @Measurable (Ω × ℂ) ℝ
        ((Section6.fieldSigmaAlgebraModConst α₀ hC (ball 0 ε)).prod inferInstance) _
        (Function.uncurry d) ∧
      ∀ᵐ ω ∂P, ∀ z, closedBall z r ⊆ ball 0 ε →
        d ω z = fieldCircleAverage α₀ (hcirc ω) r z -
          fieldCircleAverage α₀ (hcirc ω) r 0 := by
  apply hGFF.exists_joint_centered_circle_version_of_covariance_limit hr
  intro z hz
  obtain ⟨η, hη, _, htests, _, _⟩ := exists_local_circleDensity_tests hr z hz
  refine ⟨circleDensityDifference r η hr hη z, ?_, hkernel z hz η hη⟩
  intro n
  exact htests n

end HarmonicBalls
