import HarmonicBalls.FirstPass.S11j.PositiveWeylBump
import HarmonicBalls.Steps.Sec11.SingularWeylBumpInverse
import HarmonicBalls.Steps.Sec11.WeylMetricConstantScaling
import HarmonicBalls.Steps.Sec11.PinchNormalizedLocalEvent

/-!
# First pass, Section 11: inverse Weyl identity after a nonnegative bump (fp-S11j, owner n4)

Positive counterpart (F6c) of the inverse identity `IsEuclideanLengthMetric.inverse_weylScaling`
(`Steps/Sec11/WeylInverse.lean:71`), which is stated for nonpositive weights. For a nonnegative compactly supported
continuous weight `f` and the bumped metric `E = e^{ξ f} D`, the identity `ofReal (D x y) = weylScaling E ξ (-f) x y`
holds. No path analysis is repeated: with `g = f - M` for a constant `M ≥ sup f`, the negative identity applies to `g`,
and the two constant factors `e^{ξ M}` and `e^{-ξ M}` cancel by `weylScaling_add_const` and
`IsEuclideanLengthMetric.weylScaling_const_mul`.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set
open scoped ENNReal

/-- A constant shift of the weight multiplies the Weyl scaling by `e^{ξ M}`: if `f = g + M` pointwise, then
`weylScaling D ξ f = e^{ξ M} · weylScaling D ξ g`. -/
theorem weylScaling_eq_exp_mul_of_shift (D : ℂ → ℂ → ℝ) (ξ M : ℝ) (f g : ℂ → ℝ)
    (hfg : ∀ z, f z = g z + M) (x y : ℂ) :
    weylScaling D ξ f x y = ENNReal.ofReal (Real.exp (ξ * M)) * weylScaling D ξ g x y := by
  have hf : f = fun z => g z + M := funext hfg
  rw [hf]
  exact weylScaling_add_const D ξ M g x y

/-- Deterministic inverse identity after a nonnegative compactly supported bump of a Euclidean length metric:
`D x y = weylScaling (e^{ξ f} D) ξ (-f) x y` as `ENNReal` values. -/
theorem IsEuclideanLengthMetric.inverse_weylScaling_nonneg
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {ξ : ℝ} (hξ : 0 ≤ ξ)
    (f : ℂ → ℝ) (hf : Continuous f) (hc : HasCompactSupport f) (hl : ∀ z, 0 ≤ f z)
    (hzero : ∀ x y, weylScaling D ξ 0 x y = ENNReal.ofReal (D x y)) (x y : ℂ) :
    ENNReal.ofReal (D x y) =
      weylScaling (fun u v => (weylScaling D ξ f u v).toReal) ξ (fun z => -f z) x y := by
  obtain ⟨c', hc'⟩ := exists_lower_bound_of_continuous_compactSupport (fun z => -f z) hf.neg hc.neg
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ z, f z ≤ M :=
    ⟨-c', fun z => by
      have h : c' ≤ -f z := hc' z
      linarith⟩
  obtain ⟨g, hgdef⟩ : ∃ g : ℂ → ℝ, ∀ z, g z = f z + -M := ⟨fun z => f z + -M, fun z => rfl⟩
  have hfg : ∀ z, f z = g z + M := fun z => by rw [hgdef z]; ring
  have hg_cont : Continuous g := by
    have hgfun : g = fun z => f z + -M := funext hgdef
    rw [hgfun]
    exact hf.add continuous_const
  have hg_le : ∀ z, g z ≤ 0 := fun z => by rw [hgdef z]; linarith [hM z]
  have hg_low : ∀ z, -M ≤ g z := fun z => by rw [hgdef z]; linarith [hl z]
  -- the bumped metric of `f` is `e^{ξ M}` times the bumped metric of `g`
  have hEf : ∀ x y, (weylScaling D ξ f x y).toReal =
      Real.exp (ξ * M) * (weylScaling D ξ g x y).toReal := fun x y => by
    rw [weylScaling_eq_exp_mul_of_shift D ξ M f g hfg x y, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.exp_pos _).le]
  have hEfun : (fun u v => (weylScaling D ξ f u v).toReal) =
      fun u v => Real.exp (ξ * M) * (weylScaling D ξ g u v).toReal :=
    funext fun u => funext fun v => hEf u v
  -- the bumped metric of `g` is a length metric: a constant multiple of the bumped metric of `f`
  have hEf_len : IsEuclideanLengthMetric (fun u v => (weylScaling D ξ f u v).toReal) :=
    hD.weylScaling_nonneg_bump_isLengthMetric hξ f hf hc hl hzero
  have hEg : IsEuclideanLengthMetric (fun u v => (weylScaling D ξ g u v).toReal) := by
    have hfun : (fun u v => (weylScaling D ξ g u v).toReal) =
        fun u v => Real.exp (-(ξ * M)) * (weylScaling D ξ f u v).toReal :=
      funext fun u => funext fun v => by
        rw [hEf u v, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    rw [hfun]
    exact hEf_len.const_mul (Real.exp_pos _)
  -- the negated weight of `f` is the negated weight of `g` shifted by `-M`
  have hneg : (fun z => -f z) = fun z => (fun z => -g z) z + -M :=
    funext fun z => by
      show -f z = -g z + -M
      rw [hfg z]
      ring
  have hstep1 : weylScaling (fun u v => (weylScaling D ξ f u v).toReal) ξ (fun z => -f z) x y =
      ENNReal.ofReal (Real.exp (ξ * M)) *
        weylScaling (fun u v => (weylScaling D ξ g u v).toReal) ξ (fun z => -f z) x y := by
    rw [hEfun]
    exact hEg.weylScaling_const_mul (Real.exp_pos _) ξ (fun z => -f z) x y
  have hstep2 : weylScaling (fun u v => (weylScaling D ξ g u v).toReal) ξ (fun z => -f z) x y =
      ENNReal.ofReal (Real.exp (ξ * (-M))) *
        weylScaling (fun u v => (weylScaling D ξ g u v).toReal) ξ (fun z => -g z) x y := by
    rw [hneg]
    exact weylScaling_add_const _ ξ (-M) (fun z => -g z) x y
  have hone : ENNReal.ofReal (Real.exp (ξ * M)) * ENNReal.ofReal (Real.exp (ξ * (-M))) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
      show ξ * M + ξ * (-M) = 0 by ring, Real.exp_zero, ENNReal.ofReal_one]
  have hinv : ENNReal.ofReal (D x y) =
      weylScaling (fun u v => (weylScaling D ξ g u v).toReal) ξ (fun z => -g z) x y :=
    hD.inverse_weylScaling hξ g hg_cont hg_low hg_le hEg x y
  rw [hstep1, hstep2, ← mul_assoc, hone, one_mul]
  exact hinv

/-- Almost surely, the inverse identity holds for the bumped metric of the singular field, for every continuous
compactly supported weight `f ≥ 0`. Positive counterpart of `ae_singularField_weylBump_identities_of_metricFieldAxioms`
(`Steps/Sec11/SingularWeylBumpInverse.lean:17`). -/
theorem ae_singularField_nonneg_weylBump_inverse_of_metricFieldAxioms
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ ξ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ)
    (haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α₀ < lqgQ γ) (hD : IsLQGMetricOfField P γ ξ α₀ hC D)
    (hξ : 0 ≤ ξ) :
    ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → (∀ z, 0 ≤ f z) → ∀ x y,
      ENNReal.ofReal (D ω x y) =
        weylScaling (fun u v => (weylScaling (D ω) ξ f u v).toReal) ξ (fun z => -f z) x y := by
  filter_upwards [ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α₀ hC hcirc D
      haxioms hgff hγ hγ₂ hα hD,
    ae_weylScaling_zero_of_metricFieldAxioms P γ ξ α₀ hC hcirc D
      haxioms hgff hγ hγ₂ hα hD] with ω hm hz
  intro f hf hc hl x y
  exact hm.inverse_weylScaling_nonneg hξ f hf hc hl hz x y

end HarmonicBalls
