import HarmonicBalls.Proofs.Sec2.PolyHighProb

/-!
# A uniform ball inside an annulus

A ball-volume lower bound supplies the annulus mass needed by the Harnack
cover in Proposition 7.1, uniformly for all larger annulus radii.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

/-- A ball of radius at most `ρ/8`, centred at distance `3ρ/4` from `w`,
lies in the annulus `𝔸_{ρ/2,ρ}(w)`. -/
theorem ball_subset_half_annulus (w : ℂ) {ρ s : ℝ} (hρ : 0 < ρ) (hs : s ≤ ρ / 8) :
    ball (w + ((3 * ρ / 4 : ℝ) : ℂ)) s ⊆ annulus w (ρ / 2) ρ := by
  let x : ℂ := w + ((3 * ρ / 4 : ℝ) : ℂ)
  have hdist : dist x w = 3 * ρ / 4 := by
    dsimp [x]
    rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  intro y hy
  have hyx : dist y x < s := mem_ball.1 hy
  have houter := dist_triangle y x w
  have hinner := dist_triangle x y w
  rw [dist_comm x y] at hinner
  have hyouter : dist y w < ρ := by linarith
  have hyinner : ρ / 2 < dist y w := by linarith
  exact ⟨hyouter, not_le_of_gt hyinner⟩

/-- If the closed Harnack ball lies in the unit ball, the centre of the
inscribed ball is an admissible centre for the volume-growth estimate. -/
theorem annulus_innerBall_center_mem_unitBall (w : ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hunit : closedBall w ρ ⊆ ball (0 : ℂ) 1) :
    w + ((3 * ρ / 4 : ℝ) : ℂ) ∈ ball (0 : ℂ) 1 := by
  apply hunit
  rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  linarith

/-- The annulus contains at least the mass of the inscribed ball. -/
theorem measure_ball_le_half_annulus (μ : Measure ℂ) (w : ℂ) {ρ s : ℝ}
    (hρ : 0 < ρ) (hs : s ≤ ρ / 8) :
    μ (ball (w + ((3 * ρ / 4 : ℝ) : ℂ)) s) ≤ μ (annulus w (ρ / 2) ρ) :=
  measure_mono (ball_subset_half_annulus w hρ hs)

/-- A uniform ball-volume lower bound gives the same lower bound for each
half-annulus whose outer radius is at least the selected scale. -/
theorem lower_mass_half_annulus_of_ball_volume (μ : Measure ℂ) {β ε : ℝ} (hε : 0 < ε)
    (hvol : ∀ x ∈ ball (0 : ℂ) 1,
      ENNReal.ofReal ((ε / 8) ^ β) ≤ μ (ball x (ε / 8)))
    {w : ℂ} {ρ : ℝ} (hρ : ε ≤ ρ)
    (hunit : closedBall w ρ ⊆ ball (0 : ℂ) 1) :
    ENNReal.ofReal ((ε / 8) ^ β) ≤ μ (annulus w (ρ / 2) ρ) := by
  have hρpos : 0 < ρ := lt_of_lt_of_le hε hρ
  exact (hvol _ (annulus_innerBall_center_mem_unitBall w hρpos hunit)).trans
    (measure_ball_le_half_annulus μ w hρpos (by linarith))

/-- A polynomially likely uniform ball-volume lower bound supplies the
uniform annulus-mass bound used in the Harnack cover. -/
theorem polyHighProb_uniform_annulus_lower_of_ball_lower
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {μ : Ω → Measure ℂ} {β : ℝ}
    (h : PolyHighProb P (fun s => {ω | ∀ x ∈ ball (0 : ℂ) 1,
      ENNReal.ofReal (s ^ β) ≤ μ ω (ball x s)})) :
    PolyHighProb P (fun ε => {ω | ∀ w ρ, ε ≤ ρ →
      closedBall w ρ ⊆ ball (0 : ℂ) 1 →
      ENNReal.ofReal ((ε / 8) ^ β) ≤ μ ω (annulus w (ρ / 2) ρ)}) := by
  have hh := h.comp_mul (c := (1 : ℝ) / 8) (by norm_num)
  apply hh.mono_of_small one_pos
  intro ε hε _ ω hω w ρ hερ hunit
  apply lower_mass_half_annulus_of_ball_volume (μ ω) hε _ hερ hunit
  simpa only [mem_ofPred_eq, one_div, div_eq_mul_inv, one_mul, mul_comm] using hω

end HarmonicBalls
