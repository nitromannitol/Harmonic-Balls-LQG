import HarmonicBalls.Draft.Section6

/-!
# Section 6 steps for Lemma 6.11: the maximum principle on components and domain monotonicity

The proof of Lemma 6.11 (lines 1828-1949 of paper/lqg_harmonic_ball-corrected.tex) is deterministic given `h`. It
iterates Lemma 6.13 and Lemma 6.8 over the shells of Lemma 6.12, starting from Lemma 6.10, and concludes with the
maximum principle (lines 1876-1883). Besides Lemmas 6.8, 6.10, 6.12 and 6.13 it uses two facts, carved here:

* `ClusterComponentInnerBallStep` (line 1877, "`v^z_t 1_{Λ̃_t}` is subharmonic in `B_ρ(x₀)`"; GRAPH G25 fix: `Λ̃_t`
  is the statement's component of `Λ^z_t ∩ B_ρ(x₀)`). A component of `Λ^z_t ∩ B_ρ(x₀)` that misses an annulus
  `𝔸_{ρ/2,d}(x₀)`, `d ∈ (ρ/2, ρ)`, misses `closure B_{ρ/2}(x₀)`. Proof route: otherwise, being connected, it lies in
  `closure B_{ρ/2}(x₀)`, so it is a connected component of the open set `Λ^z_t` (Lemma 3.2) not containing `z`,
  compactly inside `B_1 \ {z}`; the odometer is positive and subharmonic there (`Δv^z_t = μ_h` on `Λ^z_t \ {z}`,
  Lemmas 3.1-3.2), continuous, and zero on its boundary, against the maximum principle.
* `GreenPotentialSupMonoStep` (GRAPH G22 fix: the base case uses Lemma 6.10 with `(s₁,s₂,s₃,s₄) = (1/4,1/2,7/8,1)`
  and then `SG_ρ(x₀; 1/4, 1) ≤ SG_ρ(x₀)`): `SG(x₀; s₁, s₂) ≤ SG(x₀; s₁, s₃)` for `s₂ ≤ s₃`, by domain monotonicity
  of the Green function, `G_{B_{s₂}(x₀)} ≤ G_{B_{s₃}(x₀)}` on `B_{s₂}(x₀)` (the greatest harmonic minorant of
  `log (1/|x - ·|)` on the larger ball restricts to a harmonic minorant on the smaller one).
-/

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped ENNReal

open Section6

universe u

/-- Step (maximum principle on components, line 1877). A.s., for `z ∈ B_1`, `t > 0` and `closure B_ρ(x₀) ⊂ B_1 \ {z}`:
a connected component of `Λ^z_t ∩ B_ρ(x₀)` which misses `𝔸_{ρ/2,d}(x₀)` for some `d ∈ (ρ/2, ρ)` misses
`closure B_{ρ/2}(x₀)`. -/
def ClusterComponentInnerBallStep : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t → ∀ ρ : ℝ, 0 < ρ → ∀ x₀ : ℂ,
    closedBall x₀ ρ ⊆ ball 0 1 \ {z} →
    ∀ Λ ∈ connectedComponentsIn (cluster (μ ω) 1 z t ∩ ball x₀ ρ), ∀ d ∈ Ioo (ρ / 2) ρ,
      Λ ∩ annulus x₀ (ρ / 2) d = ∅ → Λ ∩ closedBall x₀ (ρ / 2) = ∅

/-- Step (domain monotonicity of `SG`, GRAPH G22): `SG(x₀; s₁, s₂) ≤ SG(x₀; s₁, s₃)` for `0 ≤ s₁ < s₂ ≤ s₃`. -/
def GreenPotentialSupMonoStep : Prop :=
  ∀ (μ : Measure ℂ) (x₀ : ℂ) (s₁ s₂ s₃ : ℝ), 0 ≤ s₁ → s₁ < s₂ → s₂ ≤ s₃ →
    annulusGreenPotentialSup μ x₀ s₁ s₂ ≤ annulusGreenPotentialSup μ x₀ s₁ s₃

end HarmonicBalls
