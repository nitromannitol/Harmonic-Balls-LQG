import HarmonicBalls.Draft.Section6

/-!
# Section 6 steps for Lemma 6.13: decay across one good annulus, and the maximum principle on discs

The proof of Lemma 6.13 (lines 1725-1810 of paper/lqg_harmonic_ball-corrected.tex) has a potential-theoretic core
and a combinatorial part (the choice of radii, the covering of the shell, the iteration; proved in
`HarmonicBalls/Proofs/Sec6/LowMass.lean`). The core is carved into two steps. In both, `Λ̃_t` is a connected
component of `Λ^z_t ∩ B_ρ(x₀)` with `closure B_ρ(x₀) ⊂ B_1 \ {z}`, and the statements hold on one event of
probability one (the event of Lemmas 3.1-3.2 and 6.9).

* `GoodAnnulusOdometerDecayStep` (Step 2, lines 1752-1781): if `E_r(w; a, b)` occurs, `closure B_{5r}(w) ⊂ B_ρ(x₀)` and
  `μ_h(Λ̃_t ∩ 𝔸_{3r,5r}(w)) ≤ a μ_h(𝔸_{3r,5r}(w))`, then
  `sup_{Λ̃_t ∩ B_{4r}(w)} v^z_t ≤ b sup_{Λ̃_t ∩ 𝔸_{3r,5r}(w)} v^z_t`. Proof route: for `x ∈ Λ̃_t ∩ ∂B_{4r}(w)`, Lemma 6.9
  with `A = 𝔸_{3r,5r}(w)` and the component `Λ^x_t ⊆ Λ̃_t` of `A ∩ Λ^z_t` containing `x` (open by Lemma 3.2, so
  admissible as `Y` in eq:good-annulus-harmonic, with `μ_h(Λ^x_t) ≤ a μ_h(A)`), the inclusion of events
  `{τ_A ≤ τ^{A \ Λ^x_t}} ⊆ {τ_A ≤ τ_{Λ^x_t}}` and the continuity of `v^z_t` off `z`; then the maximum principle for the
  subharmonic function `v^z_t 1_{Λ̃_t}` on `B_{4r}(w)` (line 1776).
* `ComponentOdometerDiscMaxStep` (lines 1776, 1801-1804): for `closure B_s(c) ⊂ B_ρ(x₀)`,
  `sup_{Λ̃_t ∩ B_s(c)} v^z_t ≤ sup_{Λ̃_t ∩ ∂B_s(c)} v^z_t`: `v^z_t 1_{Λ̃_t}` is subharmonic in `B_ρ(x₀)` (`Δv^z_t = μ_h`
  on `Λ^z_t \ {z}`, `v^z_t = 0` on `∂Λ^z_t`, Lemmas 3.1-3.2), and the maximum principle. When `Λ̃_t` misses
  `∂B_s(c)` both sides vanish (as in `component_inter_closedBall_eq_empty`).
-/

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped ENNReal

open Section6

universe u

/-- Step 2 of the proof of Lemma 6.13 (lines 1752-1781): decay of the odometer across one good annulus. -/
def GoodAnnulusOdometerDecayStep : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t → ∀ ρ : ℝ, 0 < ρ → ∀ x₀ : ℂ,
    closedBall x₀ ρ ⊆ ball 0 1 \ {z} →
    ∀ Λ ∈ connectedComponentsIn (cluster (μ ω) 1 z t ∩ ball x₀ ρ), ∀ a b r : ℝ, 0 < r → ∀ w : ℂ,
      closedBall w (5 * r) ⊆ ball x₀ ρ → IsGoodAnnulus (μ ω) r w a b →
      μ ω (Λ ∩ annulus w (3 * r) (5 * r)) ≤ ENNReal.ofReal a * μ ω (annulus w (3 * r) (5 * r)) →
      ⨆ x ∈ Λ ∩ ball w (4 * r), odometerExt (μ ω) z t x ≤
        ENNReal.ofReal b * ⨆ x ∈ Λ ∩ annulus w (3 * r) (5 * r), odometerExt (μ ω) z t x

/-- The maximum principle for `v^z_t 1_{Λ̃_t}` on discs inside `B_ρ(x₀)` (lines 1776, 1801-1804). -/
def ComponentOdometerDiscMaxStep : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t → ∀ ρ : ℝ, 0 < ρ → ∀ x₀ : ℂ,
    closedBall x₀ ρ ⊆ ball 0 1 \ {z} →
    ∀ Λ ∈ connectedComponentsIn (cluster (μ ω) 1 z t ∩ ball x₀ ρ), ∀ (c : ℂ) (s : ℝ), 0 < s →
      closedBall c s ⊆ ball x₀ ρ →
      ⨆ x ∈ Λ ∩ ball c s, odometerExt (μ ω) z t x ≤ ⨆ x ∈ Λ ∩ sphere c s, odometerExt (μ ω) z t x

end HarmonicBalls
