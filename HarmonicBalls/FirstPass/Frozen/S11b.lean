import HarmonicBalls.Draft.Section11

/-! # FIRST-PASS frozen external inputs for Section 11, ergodic and rooted parts (worker n1, fp-S11b)

Two EXTERNAL Props used by the first-pass proof of Lemma 11.7 (`lemma:mu_h-bad-and-harnack`, printed proof at
`paper/lqg_harmonic_ball-corrected.tex`, the paragraph after the proof of `lemma:positive-probability`, and [C39]).
Both are stated about the whole-plane GFF and its LQG measures only. Neither mentions clusters, odometers, harmonic
balls or IDLA processes. The event `coneMassEvent μ Q M r z` is the Draft predicate of `Draft/Section11.lean`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HarmonicBalls

universe u

/-- RETIRED (NOT-EXTERNAL, truth check 2026-11-09): this states the frequency of the paper's `coneMassEvent`, not
general mathematics. Do not use. Replaced by the internal ergodic argument of `FirstPass/S11c.lean`.
(Former FIRST-PASS FROZEN text, kept for the record.) Dilation ergodicity of the whole-plane GFF modulo additive constants, in the form it is used for
the origin-rooted field `h^γ = g - γ log|·|` (LQG measure `μ0 ω`, `IsLQGMeasureOfField P γ γ hcirc μ0`), for the
dyadic scales. For each scale index `n₀`, almost surely the Cesàro frequency of the events
`coneMassEvent (μ0 ω) Q M (2⁻¹)^n 0` over `n ∈ {1, …, N}` tends to the expectation of the event at scale `n₀`.
Why it holds: the events are invariant under additive constants (both sides scale by `e^{γc}`) and under the
dilation `z ↦ 2z` (the cone and the annuli are scale invariant, and the 2D Green function is dilation invariant), so
the sequence of events is stationary in `n`; dyadic dilation acts ergodically on the whole-plane GFF modulo constants,
and the pointwise ergodic theorem gives the limit.

Source: the paper's proof of Lemma 11.7 (lines 2936-2951 of the corrected copy), which cites the ergodicity of dyadic
dilation of the whole-plane GFF modulo constants and the pointwise ergodic theorem. Standard; locator pending.
Used by: firstPass_11_7. -/
def OriginRootedConeFrequencyFrozen : Prop :=
  ∀ (γ : ℝ) (Q : Set ℂ) (M : ℝ), 0 < γ → γ < 2 → IsCone Q → 0 < M →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ0 : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ γ hcirc μ0 →
  ∀ n₀ : ℕ, ∀ᵐ ω ∂P,
    Tendsto (fun N : ℕ => ({n : ℕ | 0 < n ∧ n ≤ N ∧ coneMassEvent (μ0 ω) Q M ((2 : ℝ)⁻¹ ^ n) 0}.ncard : ℝ) / (N : ℝ))
      atTop (𝓝 (∫⁻ ω, Set.indicator {ω' : Ω | coneMassEvent (μ0 ω') Q M ((2 : ℝ)⁻¹ ^ n₀) 0}
        (fun _ => (1 : ℝ≥0∞)) ω ∂P).toReal)

/-- RETIRED (NOT-EXTERNAL, truth check 2026-11-09): this states the rooted transfer of the paper's `coneMassEvent`
frequency, not general mathematics. Do not use. Replaced by the local Palm transfer in `FirstPass/Frozen/S11c.lean`.
(Former FIRST-PASS FROZEN text, kept for the record.) Rooted transfer from the origin to `μ_h`-almost every point, for the frequency of good
scales in the window `[N+1, 2N]` (the statement of Lemma 11.7 at a fixed `δ`). Let `μ0` be the LQG measure with
`α = γ` (rooted at `0`) and `μ` the LQG measure with the given `α₀`, both of the same whole-plane GFF `g`. If almost
surely the window frequency at the origin for `μ0` is at least `δ` for all large `N`, then almost surely, for
`μ`-a.e. `z`, the window frequency at `z` for `μ` is at least `δ` for all large `N`.
Why it holds: the local field of `μ` at a `μ`-typical point `z ≠ 0` (Palm/rooted identity) is the `γ`-log-singular
field at `z` plus the smooth drift `-α₀ log|·|`, which is a Cameron-Martin shift on a small disk, and the event is
translation covariant (the whole-plane GFF modulo constants is stationary) and invariant under additive constants.
Source: the paper's proof of `lemma:mu_h-bad-and-harnack` (Lemma 11.7; corrected copy, the paragraph beginning "The
rooted-field change of measure used in the proof of Lemma \ref{lemma:mu_h-doubling-and-harnack}"), correction [C39].
Standard; locator pending.
Used by: firstPass_11_7. -/
def RootedConeFrequencyTransferFrozen : Prop :=
  ∀ (γ α₀ : ℝ) (Q : Set ℂ) (M δ : ℝ), 0 < γ → γ < 2 → α₀ < lqgQ γ → IsCone Q → 0 < M → 0 < δ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ0 μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ γ hcirc μ0 →
    IsLQGMeasureOfField P γ α₀ hcirc μ →
    (∀ᵐ ω ∂P, ∀ᶠ N in atTop,
      δ * N ≤ ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ coneMassEvent (μ0 ω) Q M ((2 : ℝ)⁻¹ ^ n) 0}.ncard : ℝ)) →
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), ∀ᶠ N in atTop,
      δ * N ≤ ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ coneMassEvent (μ ω) Q M ((2 : ℝ)⁻¹ ^ n) z}.ncard : ℝ)

end HarmonicBalls
