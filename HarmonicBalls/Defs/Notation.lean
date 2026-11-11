import Mathlib

/-! # Notation and conventions

Shared notation of Bou-Rabee and Gwynne, *Harmonic balls in Liouville quantum gravity* (arXiv:2208.11795),
Section 1.6 (paper/lqg_harmonic_ball-corrected.tex, lines 323-342), and the constant `Q` of eq. (Q) (line 371).
The ambient plane is `ℂ` with Lebesgue measure `volume`; `B_r(z)` is `Metric.ball z r`.
-/

namespace HarmonicBalls

open MeasureTheory

/-- The open annulus `𝔸_{r₁,r₂}(z) = B_{r₂}(z) \ closure (B_{r₁}(z))` (eq:annulus, line 334). -/
def annulus (z : ℂ) (r₁ r₂ : ℝ) : Set ℂ :=
  Metric.ball z r₂ \ Metric.closedBall z r₁

/-- The LQG constant `Q = 2/γ + γ/2` (eq:Q, line 371). -/
noncomputable def lqgQ (γ : ℝ) : ℝ :=
  2 / γ + γ / 2

/-- A one-parameter family of events `E r` occurs *with polynomially high probability as `r → 0`* if there is
real `p > 0` with `P[E^r] ≥ 1 - O(r^p)` (line 336). We bound the (outer) probability of the complement, so the good
event need not be measurable: `P[(E r)ᶜ] ≤ C r^p` for all `0 < r < r₀`. The exponent `p` is REAL (`r ^ p` is `Real.rpow`):
an earlier version let `p` elaborate as a natural number, which forced `p ≥ 1` and made every statement using this
predicate stronger than the paper. -/
def PolyHighProb {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (E : ℝ → Set Ω) : Prop :=
  ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ, ∃ r₀ > 0, ∀ r : ℝ, 0 < r → r < r₀ → P (E r)ᶜ ≤ ENNReal.ofReal (C * r ^ p)

end HarmonicBalls
