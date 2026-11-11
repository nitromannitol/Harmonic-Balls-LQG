import HarmonicBalls.Defs.Annuli
import HarmonicBalls.Proofs.Potential.FiniteDiscGreenReciprocity
import HarmonicBalls.Proofs.Potential.GreenPositivity

/-!
# Lemma 11.17: the Green kernel of the annulus potential is lower semicontinuous

Coordinate 6 of `pinchScalars` is `M * SG_{3,6}(0)`, where `SG` is `annulusGreenPotentialSup` (Defs/Annuli.lean:65): the
supremum over `x` in the annulus of `∫_A κ(x, y) dμ(y)`, with the extended kernel `κ(x, y) = +∞` on the diagonal and
`G_{B_6(0)}(x, y)` off it. This file proves the deterministic lower semicontinuity of `κ` on `B_b(x₀) × B_b(x₀)`:
off the diagonal `κ` is `ofReal ∘ G_{B_b}` and `G` is jointly continuous there (`continuousAt_greenFunction_uncurry`,
FiniteDiscGreenReciprocity.lean:363); on the diagonal `κ = +∞` and `G(x, y) ≥ (2π)⁻¹ log(r/|x-y|)` when `closedBall y r ⊆ O`
(`log_div_le_greenFunction`, GreenPositivity.lean:78), so `κ → +∞` at the diagonal.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric Topology
open scoped ENNReal

/-- The extended Green kernel of the annulus potential `annulusGreenPotentialSup` (Defs/Annuli.lean:65): `+∞` on the
diagonal, `ofReal G_{B_b(x₀)}(x, y)` off it (the paper's value `G(x, x) = +∞`). -/
noncomputable def annulusKernel (x₀ : ℂ) (b : ℝ) (x y : ℂ) : ℝ≥0∞ :=
  if y = x then ∞ else ENNReal.ofReal (greenFunction (ball x₀ b) x y)

/-- Off the diagonal, the extended kernel is continuous at `(z, y)`: `κ` agrees near `(z, y)` with `ofReal ∘ G`. -/
theorem annulusKernel_continuousAt_of_ne (x₀ : ℂ) {b : ℝ} {z y : ℂ} (hz : z ∈ ball x₀ b) (hy : y ∈ ball x₀ b)
    (hzy : z ≠ y) :
    ContinuousAt (fun p : ℂ × ℂ => annulusKernel x₀ b p.1 p.2) (z, y) := by
  have hG := continuousAt_greenFunction_uncurry isOpen_ball isBounded_ball hz hy hzy
  have hev : ∀ᶠ p : ℂ × ℂ in 𝓝 (z, y), p.2 ≠ p.1 := by
    have hopen : IsOpen {p : ℂ × ℂ | p.2 ≠ p.1} := isOpen_ne_fun continuous_snd continuous_fst
    exact hopen.mem_nhds (show y ≠ z from fun h => hzy h.symm)
  have hcont : ContinuousAt (fun p : ℂ × ℂ => ENNReal.ofReal (greenFunction (ball x₀ b) p.1 p.2)) (z, y) :=
    ENNReal.continuous_ofReal.continuousAt.comp hG
  refine hcont.congr ?_
  filter_upwards [hev] with p hp
  simp [annulusKernel, hp]

/-- Lower semicontinuity of the extended Green kernel on the ball `B_b(x₀)` (on the diagonal, the pole bound). -/
theorem annulusKernel_lowerSemicontinuousOn (x₀ : ℂ) {b : ℝ} :
    LowerSemicontinuousOn (fun p : ℂ × ℂ => annulusKernel x₀ b p.1 p.2) (ball x₀ b ×ˢ ball x₀ b) := by
  rintro ⟨z, y⟩ hp
  rw [mem_prod] at hp
  obtain ⟨hz, hy⟩ := hp
  by_cases hzy : z = y
  · subst hzy
    -- diagonal: the value is `⊤`
    intro t ht
    have ht' : t < ⊤ := by simpa [annulusKernel] using ht
    have hzb : ‖z - x₀‖ < b := by simpa [mem_ball, dist_eq_norm] using hz
    set a := ‖z - x₀‖ with ha
    set R := (b - a) / 2 with hR
    have hRpos : 0 < R := by rw [hR]; linarith
    -- a real level `M ≥ 0` strictly above `t`
    set M := t.toReal + 1 with hM
    have hMpos : 0 < M := by rw [hM]; linarith [ENNReal.toReal_nonneg (a := t)]
    have htM : t < ENNReal.ofReal M := by
      rw [← ENNReal.ofReal_toReal ht'.ne_top]
      exact (ENNReal.ofReal_lt_ofReal_iff hMpos).2 (by rw [hM]; linarith)
    set ε := R * Real.exp (-(2 * Real.pi * M)) with hε
    have hεpos : 0 < ε := by rw [hε]; positivity
    have hεR : ε ≤ R := by
      rw [hε]
      have : Real.exp (-(2 * Real.pi * M)) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos]
      nlinarith
    -- eventually (near the diagonal point) the difference is small and `y` is close to `z`
    have hd : ∀ᶠ q : ℂ × ℂ in 𝓝 (z, z), ‖q.1 - q.2‖ < ε := by
      have hc : Continuous fun q : ℂ × ℂ => ‖q.1 - q.2‖ := by fun_prop
      have h0 : ‖z - z‖ < ε := by simpa using hεpos
      exact hc.continuousAt.eventually_lt continuousAt_const h0
    have hdz : ∀ᶠ q : ℂ × ℂ in 𝓝 (z, z), ‖q.2 - x₀‖ < a + R / 2 := by
      have hc : Continuous fun q : ℂ × ℂ => ‖q.2 - x₀‖ := by fun_prop
      have h0 : ‖z - x₀‖ < a + R / 2 := by rw [ha]; linarith
      exact hc.continuousAt.eventually_lt continuousAt_const h0
    have hball : ∀ᶠ q : ℂ × ℂ in 𝓝[ball x₀ b ×ˢ ball x₀ b] (z, z),
        ‖q.1 - q.2‖ < ε ∧ ‖q.2 - x₀‖ < a + R / 2 :=
      eventually_nhdsWithin_of_eventually_nhds (hd.and hdz)
    filter_upwards [hball] with q hq
    obtain ⟨hq1, hq2⟩ := hq
    by_cases hqe : q.2 = q.1
    · show t < annulusKernel x₀ b q.1 q.2
      rw [show annulusKernel x₀ b q.1 q.2 = ⊤ by simp [annulusKernel, hqe]]
      exact ht'
    · have hdpos : 0 < ‖q.1 - q.2‖ := by
        rw [norm_pos_iff, sub_ne_zero]; exact fun h => hqe h.symm
      have hdR : ‖q.1 - q.2‖ < R := lt_of_lt_of_le hq1 hεR
      have hcb : closedBall q.2 R ⊆ ball x₀ b := by
        intro w hw
        rw [mem_closedBall, dist_eq_norm] at hw
        rw [mem_ball, dist_eq_norm]
        have htri : ‖w - x₀‖ ≤ ‖w - q.2‖ + ‖q.2 - x₀‖ := by
          have := norm_add_le (w - q.2) (q.2 - x₀)
          simpa using this
        linarith
      have hlog := log_div_le_greenFunction isBounded_ball hRpos hcb hdpos hdR
      have hkey : M < (2 * Real.pi)⁻¹ * Real.log (R / ‖q.1 - q.2‖) := by
        have hexp : 2 * Real.pi * M < Real.log (R / ‖q.1 - q.2‖) := by
          rw [Real.lt_log_iff_exp_lt (by positivity)]
          have hdiv : ‖q.1 - q.2‖ < R * Real.exp (-(2 * Real.pi * M)) := hq1
          rw [lt_div_iff₀ hdpos]
          have : R * Real.exp (-(2 * Real.pi * M)) * Real.exp (2 * Real.pi * M) = R := by
            rw [mul_assoc, ← Real.exp_add]; simp
          nlinarith [Real.exp_pos (2 * Real.pi * M)]
        have hpi : 0 < (2 * Real.pi)⁻¹ := by positivity
        calc M = (2 * Real.pi)⁻¹ * (2 * Real.pi * M) := by field_simp
          _ < (2 * Real.pi)⁻¹ * Real.log (R / ‖q.1 - q.2‖) := mul_lt_mul_of_pos_left hexp hpi
      show t < annulusKernel x₀ b q.1 q.2
      rw [show annulusKernel x₀ b q.1 q.2 = ENNReal.ofReal (greenFunction (ball x₀ b) q.1 q.2) by
        simp [annulusKernel, hqe]]
      exact lt_of_lt_of_le htM (ENNReal.ofReal_le_ofReal (le_of_lt (lt_of_lt_of_le hkey hlog)))
  · have hc := annulusKernel_continuousAt_of_ne x₀ hz hy hzy
    exact fun t ht => eventually_nhdsWithin_of_eventually_nhds (hc.tendsto.eventually_const_lt ht)

end HarmonicBalls
