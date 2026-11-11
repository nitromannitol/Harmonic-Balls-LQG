import HarmonicBalls.Defs.LQGMetric

/-!
# Constant shifts and monotonicity of the Weyl scaling

Deterministic facts about `weylScaling D ξ f u v` (`HarmonicBalls/Defs/LQGMetric.lean`, the infimum over length
parametrised paths of `∫ exp (ξ f (p t)) dt`) used by the route of Lemma 11.12:

* a constant shift multiplies the Weyl scaling by `e^{ξ c}`: this is the random normalisation `N_ρ` of Step 3.3 (6), since
  `N_ρ h = h - ⟨h, ρ⟩` subtracts a random constant;
* pointwise monotonicity in the weight, and a bump bounded by a constant, give the one-sided comparisons of Step 4.3.

No external input. The Weyl scaling property (Fact 2.2 III, `HarmonicBalls/Proposed/LQG.lean`) is the only place where the
metric of the field is related to the Weyl scaling of the base metric; these lemmas are purely about the infimum.
-/

namespace HarmonicBalls.S11m

open MeasureTheory Set
open scoped ENNReal

/-- A constant shift of the weight multiplies the Weyl scaling by `e^{ξ c}` (Step 3.3 (6): the normalisation
`N_ρ h = h - ⟨h, ρ⟩` changes the metric by a deterministic factor). -/
theorem weylScaling_add_const (D : ℂ → ℂ → ℝ) (ξ : ℝ) (f : ℂ → ℝ) (c : ℝ) (u v : ℂ) :
    weylScaling D ξ (fun x => f x + c) u v =
      ENNReal.ofReal (Real.exp (ξ * c)) * weylScaling D ξ f u v := by
  have key : ∀ (T : ℝ) (p : ℝ → ℂ),
      ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * (f (p t) + c))) =
        ENNReal.ofReal (Real.exp (ξ * c)) * ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * f (p t))) := by
    intro T p
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun t => ?_
    rw [mul_add, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
    ring
  have h0 : ENNReal.ofReal (Real.exp (ξ * c)) ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have htop : ENNReal.ofReal (Real.exp (ξ * c)) ≠ ∞ := ENNReal.ofReal_ne_top
  unfold weylScaling
  simp only [key, ← ENNReal.mul_iInf_of_ne h0 htop]

/-- The Weyl scaling is monotone in the weight for `ξ ≥ 0` (pointwise comparison of the integrands). -/
theorem weylScaling_mono {D : ℂ → ℂ → ℝ} {ξ : ℝ} (hξ : 0 ≤ ξ) {f g : ℂ → ℝ} (h : ∀ x, f x ≤ g x) (u v : ℂ) :
    weylScaling D ξ f u v ≤ weylScaling D ξ g u v := by
  unfold weylScaling
  refine iInf_mono fun T => iInf_mono fun p => iInf_mono fun _ => iInf_mono fun _ => iInf_mono fun _ =>
    lintegral_mono fun t => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (h _) hξ))

/-- A bump bounded above by a constant `c` raises the Weyl scaling at most by `e^{ξ c}` (Step 4.3, the upper comparison
`A_new ≤ b A`, with `b = e^{ξ c}`). -/
theorem weylScaling_add_le_const_mul {D : ℂ → ℂ → ℝ} {ξ : ℝ} (hξ : 0 ≤ ξ) (f u : ℂ → ℝ) (c : ℝ)
    (hu : ∀ x, u x ≤ c) (x y : ℂ) :
    weylScaling D ξ (fun z => f z + u z) x y ≤
      ENNReal.ofReal (Real.exp (ξ * c)) * weylScaling D ξ f x y := by
  have hle : ∀ z, f z + u z ≤ f z + c := fun z => by linarith [hu z]
  rw [← weylScaling_add_const D ξ f c x y]
  exact weylScaling_mono hξ hle x y

end HarmonicBalls.S11m
