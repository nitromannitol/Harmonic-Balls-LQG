import HarmonicBalls.Proposed.PfefferMetricScaling
import HarmonicBalls.FirstPass.S11m.E1Bounds
import HarmonicBalls.Steps.Sec11.LocalPathLength

/-! # Annular comparison for a quadratic Weyl shift

A quadratic Weyl shift increases the distance across an annulus by at least
the exponential of its minimum on a smaller outer annulus.
-/

namespace HarmonicBalls
open Set Metric
open scoped ENNReal

/-- A quadratic Weyl shift compares the distance across the annulus with radii
`r` and `2r` to the original distance across the annulus with radii `1.9r`
and `2r`. -/
theorem pfefferAcross_quadratic_weyl_lower {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {ξ r : ℝ} (hξ : 0 < ξ) (hr : 0 < r)
    (hscale : ∀ x y, ENNReal.ofReal (E x y) =
      weylScaling D ξ (fun z => ‖z‖ ^ 2) x y) :
    ENNReal.ofReal (Real.exp (ξ * ((19 / 10 : ℝ) * r) ^ 2)) *
      pfefferAcross D 0 ((19 / 10 : ℝ) * r) (2 * r) ≤
      pfefferAcross E 0 r (2 * r) := by
  let a : ℝ := (19 / 10 : ℝ) * r
  let b : ℝ := 2 * r
  have ha : 0 < a := by dsimp [a]; positivity
  have har : r < a := by dsimp [a]; linarith
  have hneA : (sphere (0 : ℂ) a).Nonempty := NormedSpace.sphere_nonempty.mpr ha.le
  have hneB : (sphere (0 : ℂ) b).Nonempty := NormedSpace.sphere_nonempty.mpr (by dsimp [b]; positivity)
  let d := setDist D (sphere (0 : ℂ) a) (sphere (0 : ℂ) b)
  have hd : ∀ x ∈ sphere (0 : ℂ) b, ∀ y ∈ sphere (0 : ℂ) a, d ≤ D x y := by
    intro x hx y hy
    rw [hD.symm x y]
    unfold d setDist
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro _ ⟨u, _, v, _, rfl⟩
      exact S11m.E1Bounds.nonneg_of_isEuclideanLengthMetric hD u v
    · exact ⟨y, hy, x, hx, rfl⟩
  have hcross : pfefferAcross D 0 a b = ENNReal.ofReal d := by
    rw [ofReal_setDist_eq_iInf hneA hneB]
    rfl
  have hweight : ∀ z ∈ closure ((ball (0 : ℂ) a)ᶜ), a ^ 2 ≤ ‖z‖ ^ 2 := by
    intro z hz
    rw [closure_compl, isOpen_ball.interior_eq] at hz
    have hz' : a ≤ ‖z‖ := by simpa [mem_ball, dist_zero_right, not_lt] using hz
    nlinarith [norm_nonneg z]
  have hpoint (x y : ℂ) (hx : x ∈ sphere (0 : ℂ) b) (hy : y ∈ sphere (0 : ℂ) r) :
      ENNReal.ofReal (Real.exp (ξ * a ^ 2) * d) ≤ ENNReal.ofReal (E y x) := by
    rw [hscale]
    have hx' : x ∈ closure ((ball (0 : ℂ) a)ᶜ) := by
      rw [closure_compl, isOpen_ball.interior_eq]
      have hxb : ‖x‖ = b := by simpa [mem_sphere, dist_zero_right] using hx
      simp only [mem_compl_iff, mem_ball, dist_zero_right, not_lt]
      dsimp [a,b] at *
      linarith
    have hy' : y ∉ interior ((ball (0 : ℂ) a)ᶜ) := by
      rw [interior_compl, closure_ball 0 ha.ne']
      have hyr : ‖y‖ = r := by simpa [mem_sphere, dist_zero_right] using hy
      simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le, not_lt]
      linarith
    have h := S11m.E1Bounds.weylScaling_ge_of_exit hD hξ.le hweight hx' hy'
      (fun w hw => by
        rw [frontier_compl, frontier_ball 0 ha.ne'] at hw
        exact hd x hx w hw)
    have hs := hD.weylScaling_symm ξ (fun z : ℂ => ‖z‖ ^ 2) y x
    rw [hs]
    exact h
  change ENNReal.ofReal (Real.exp (ξ * a ^ 2)) * pfefferAcross D 0 a b ≤ pfefferAcross E 0 r b
  rw [hcross, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  unfold pfefferAcross
  exact le_iInf fun y => le_iInf fun hy => le_iInf fun x => le_iInf fun hx => hpoint x y hx hy
end HarmonicBalls
