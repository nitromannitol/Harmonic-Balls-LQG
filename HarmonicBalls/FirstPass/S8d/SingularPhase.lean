import HarmonicBalls.FirstPass.S8d.RegularPhase
import HarmonicBalls.FirstPass.S8d.TranslatedDensity

/-! # FIRST-PASS helper (fp-S8d, owner n4): the singular translated very-good event, probability bound (route d2 + d1)

For the singular LQG measure `ν` (`α = γ`) of a whole-plane GFF and the regular measure `lam` (`α = 0`) of the same field,
the Weyl relation off the origin (`hW`, the frozen `LocalLQGInsertionWeylOffOrigin` of FirstPass/Frozen/S8c.lean:59 in its
per-measure form) gives, for almost every `ω`, the two-sided density bounds on the annulus `𝔸_{1/4,2}(-q)`
(`translated_density_bounds`, TranslatedDensity.lean). Then `isVeryGoodAnnulus_of_density` (CriterionThreeTransfer.lean)
says that the regular very-good event of the translated measure implies the singular one, with constants
`a·k₁/k₂`, `C₁m·k₁/k₂`, `C₁p·k₂/k₁`, `C₂m·k₁/k₂`, `C₂p·k₂/k₁`, where `k₁ = (2^{γ²})⁻¹`, `k₂ = ((1/4)^{γ²})⁻¹`.
Hence the singular failure event is almost surely contained in the regular failure event, whose probability is bounded
by `regular_phase_probability` (RegularPhase.lean). No new mathematics: the monotonicity of the probability and the
almost sure inclusion. -/

open MeasureTheory Metric Set Filter
open scoped ENNReal

namespace HarmonicBalls

universe u

/-- The singular translated very-good failure event has probability at most `1 - p`, for a translation `q` with
`‖q‖ ≤ 1/5`, when the regular one does, with the constants of Draft Lemma 6.7 at `α₀ = 0`. -/
theorem singular_translated_failure_le {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (γ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : (0 : ℝ) < lqgQ γ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (ν lam : Ω → Measure ℂ) (hlam : IsLQGMeasureOfField P γ 0 hcirc lam)
    (hW : ∀ᵐ ω ∂P, ∀ s : Set ℂ, MeasurableSet s → (0 : ℂ) ∉ s →
      lam ω s = ∫⁻ z in s, ENNReal.ofReal (‖z‖ ^ (γ * γ)) ∂(ν ω))
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (βminus : ℝ) (N₀ : ℕ) (hN₀ : 9 ≤ N₀) (a b C₁m C₁p C₂m C₂p C₃ p : ℝ)
    (ha : 0 ≤ a) (hC₁m : 0 < C₁m) (hC₁p : 0 ≤ C₁p) (hC₂m : 0 < C₂m) (hC₂p : 0 ≤ C₂p)
    (h67 : ∀ (Ω' : Type u) [MeasurableSpace Ω'] (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ)
      (hcirc' : Ω' → ℝ → ℂ → ℝ) (μ : Ω' → Measure ℂ),
      IsWholePlaneGFF P' hC' hcirc' → IsLQGMeasureOfField P' γ 0 hcirc' μ →
      ∀ ρ : ℝ, 0 < ρ → ∀ x₀ : ℂ, ρ / 100 ≤ infDist (0 : ℂ) (annulus x₀ (ρ / 4) (2 * ρ)) →
        P' {ω | ¬ IsVeryGoodAnnulus (μ ω) βminus ρ x₀ N₀ a b C₁m C₁p C₂m C₂p C₃} ≤ ENNReal.ofReal (1 - p))
    (q : ℂ) (hq : ‖q‖ ≤ 1 / 5) :
    P {ω | ¬ IsVeryGoodAnnulus ((ν ω).map (fun w : ℂ => w - q)) βminus 1 (-q) N₀
        (a * (((2 : ℝ) ^ (γ * γ))⁻¹ / (((1 : ℝ) / 4) ^ (γ * γ))⁻¹))
        b (C₁m * (((2 : ℝ) ^ (γ * γ))⁻¹ / (((1 : ℝ) / 4) ^ (γ * γ))⁻¹))
        (C₁p * ((((1 : ℝ) / 4) ^ (γ * γ))⁻¹ / ((2 : ℝ) ^ (γ * γ))⁻¹))
        (C₂m * (((2 : ℝ) ^ (γ * γ))⁻¹ / (((1 : ℝ) / 4) ^ (γ * γ))⁻¹))
        (C₂p * ((((1 : ℝ) / 4) ^ (γ * γ))⁻¹ / ((2 : ℝ) ^ (γ * γ))⁻¹)) C₃} ≤
      ENNReal.ofReal (1 - p) := by
  have hreg := regular_phase_probability P γ hγ0 hγ2 hα hC hcirc hGFF lam hlam hAff hCC βminus N₀ a b C₁m C₁p
    C₂m C₂p C₃ p h67 q hq
  have hk₁ : (0 : ℝ) < ((2 : ℝ) ^ (γ * γ))⁻¹ := by positivity
  have hk₁₂ : ((2 : ℝ) ^ (γ * γ))⁻¹ ≤ (((1 : ℝ) / 4) ^ (γ * γ))⁻¹ := by
    have h1 : (0 : ℝ) < ((1 : ℝ) / 4) ^ (γ * γ) := Real.rpow_pos_of_pos (by norm_num) _
    have h2 : (0 : ℝ) < (2 : ℝ) ^ (γ * γ) := Real.rpow_pos_of_pos (by norm_num) _
    exact (inv_le_inv₀ h2 h1).2 (Real.rpow_le_rpow (by norm_num) (by norm_num) (mul_self_nonneg γ))
  have hae : {ω | ¬ IsVeryGoodAnnulus ((ν ω).map (fun w : ℂ => w - q)) βminus 1 (-q) N₀
        (a * (((2 : ℝ) ^ (γ * γ))⁻¹ / (((1 : ℝ) / 4) ^ (γ * γ))⁻¹))
        b (C₁m * (((2 : ℝ) ^ (γ * γ))⁻¹ / (((1 : ℝ) / 4) ^ (γ * γ))⁻¹))
        (C₁p * ((((1 : ℝ) / 4) ^ (γ * γ))⁻¹ / ((2 : ℝ) ^ (γ * γ))⁻¹))
        (C₂m * (((2 : ℝ) ^ (γ * γ))⁻¹ / (((1 : ℝ) / 4) ^ (γ * γ))⁻¹))
        (C₂p * ((((1 : ℝ) / 4) ^ (γ * γ))⁻¹ / ((2 : ℝ) ^ (γ * γ))⁻¹)) C₃} ≤ᵐ[P]
      {ω | ¬ IsVeryGoodAnnulus ((lam ω).map (fun w : ℂ => w - q)) βminus 1 (-q) N₀ a b C₁m C₁p C₂m C₂p C₃} :=
    hW.mono fun ω hωW hs hr => hs (isVeryGoodAnnulus_of_density ((lam ω).map (fun w : ℂ => w - q))
      ((ν ω).map (fun w : ℂ => w - q)) (-q) 1 βminus one_pos N₀ hN₀ _ _ hk₁ hk₁₂ a b C₁m C₁p C₂m C₂p C₃ ha
      hC₁m hC₁p hC₂m hC₂p (translated_density_bounds (ν ω) (lam ω) γ q hωW).1
      (translated_density_bounds (ν ω) (lam ω) γ q hωW).2 hr)
  exact (measure_mono_ae hae).trans hreg

#print axioms singular_translated_failure_le

end HarmonicBalls
