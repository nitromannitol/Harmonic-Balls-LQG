import Mathlib
import HarmonicBalls.Defs.Notation
import HarmonicBalls.Defs.GFF
import HarmonicBalls.Defs.LQGMetric

/-! # Pfeffer's weak LQG metrics: Definition 1.6 and the background scaling (1.10) (proposed)

Source: Pfeffer, *Weak Liouville quantum gravity metrics with matter central charge up to 25*, arXiv:2104.04020v3.
* Section 1 definitions, p. 5: length space, internal metric (1.5), `D`-distance across and around an annulus,
  and `h_r(0)`, the average of `h` over `∂B_r(0)`.
* (1.4), p. 4: the background charge `Q = Q(ξ)` (cited there from Ding–Gwynne, DG18 Theorem 1.5 and DG20 Proposition 1.1).
* Definition 1.6, p. 6: a weak LQG metric with parameter `ξ > 0`; Axioms I–V and the bound (1.7).
* Proposition 1.9, equation (1.10), p. 8: `c_{δr}/c_r = δ^{ξQ + o_δ(1)}` as `δ → 0`, uniformly over `r > 0`.

Each input is a `def ... : Prop`, taken as an explicit hypothesis. Nothing here is a derived conclusion. The membership of the LQG metric
`IsLQGMetric` in the class `IsPfefferWeakLQGMetric`, the tightness of its normalized distances, and the identification
of the background charge with `lqgQ γ` are proof targets, not assumptions. The background charge enters only as the
real parameter `Q` of `PfefferBackgroundScaling`; the value of (1.4) is not staged here.

Credit: the whole-plane GFF carriers `IsWholePlaneGFF`, the pairing functionals and their σ-algebras come from
`HarmonicBalls.Defs.GFF` and `HarmonicBalls.Defs.LQGMetric`. Their whole-plane GFF construction is due to Leonardo Bonanno.

Deviations from the printed statement, flagged for the source check:
1. Metrics are real-valued `D : ℂ → ℂ → ℝ`, as in `IsLQGMetric`. The printed metrics may take the value `∞`
   (internal metrics, p. 5). Such values enter through `ENNReal.ofReal` and the `ℝ≥0∞`-valued `internalMetric`,
   `curveLength`, `pathLength`.
2. Measurability of `h ↦ D_h` is the pointwise convention `Measurable[distributionMeasurableSpace]`, not the
   measurability into the space of lower semicontinuous metrics stated in Definition 1.6.
3. "The D-distances of closed paths" (p. 5, around `A`) is read as the `D`-lengths `len(P; D)` of the closed paths.
   "Separate the inner and outer boundaries" is read as: every path in `ℂ` from the inner circle to the outer circle
   meets the range of the closed path.
4. Axiom V is stated for every Euclidean annulus `A(z₀; a, b)` with `0 < a < b`. The printed "if `A` is a fixed
   annulus" is read as universal in `A`. The constants `c_r` precede `A`, as printed.
5. The random continuous function `f` in "a whole-plane GFF plus a continuous function" is random, as in `IsLQGMetric`.
6. The printed codomain (lower semicontinuous metrics, Definition 1.6) is imposed almost surely on the field instances
   `h = h^ℂ + f` only, not for every pairing functional `T`; the repository's `IsLQGMetric` uses the same domain.
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

/-- The circle average `(2π)⁻¹ ∫₀^{2π} f(z + r e^{iθ}) dθ` of a continuous `f : ℂ → ℝ` over `∂B_r(z)`
(normalized arc length). This is the circle-average part of the field `h = h^ℂ + f` in Axiom V (`h_r(0)`, p. 5). -/
noncomputable def pfefferCircleAverage (f : ℂ → ℝ) (r : ℝ) (z : ℂ) : ℝ :=
  (2 * Real.pi)⁻¹ * (∫ θ in (0 : ℝ)..(2 * Real.pi), f (z + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))

/-- The `D`-distance across the annulus `A(z₀; a, b) = {a < |z - z₀| < b}` (p. 5): the distance between its inner
boundary `∂B_a(z₀)` and its outer boundary `∂B_b(z₀)`, namely `inf {D x y : x ∈ ∂B_a(z₀), y ∈ ∂B_b(z₀)}`. -/
noncomputable def pfefferAcross (D : ℂ → ℂ → ℝ) (z₀ : ℂ) (a b : ℝ) : ℝ≥0∞ :=
  ⨅ x ∈ Metric.sphere z₀ a, ⨅ y ∈ Metric.sphere z₀ b, ENNReal.ofReal (D x y)

/-- The closed path `P` separates the inner circle `∂B_a(z₀)` from the outer circle `∂B_b(z₀)` (reading of p. 5):
every path in `ℂ` from a point of the inner circle to a point of the outer circle meets the range of `P`. -/
def PfefferSeparates {z : ℂ} (P : Path z z) (z₀ : ℂ) (a b : ℝ) : Prop :=
  ∀ (x y : ℂ) (γ : Path x y), x ∈ Metric.sphere z₀ a → y ∈ Metric.sphere z₀ b → ∃ t, γ t ∈ Set.range ⇑P

/-- The `D`-distance around the annulus `A(z₀; a, b)` (p. 5): the infimum of the `D`-lengths `len(P; D)` of the closed
paths `P` that separate the inner and outer boundaries of `A`. -/
noncomputable def pfefferAround (D : ℂ → ℂ → ℝ) (z₀ : ℂ) (a b : ℝ) : ℝ≥0∞ :=
  ⨅ (z : ℂ) (P : Path z z) (_ : PfefferSeparates P z₀ a b), pathLength D P

/-- Axiom I of Definition 1.6 (p. 5): `(ℂ, D)` is a length space, that is, `D(z, w)` is the infimum of the
`D`-lengths of all paths in `ℂ` from `z` to `w`. -/
def PfefferIsLengthSpace (D : ℂ → ℂ → ℝ) : Prop :=
  ∀ z w : ℂ, ENNReal.ofReal (D z w) = internalMetric D univ z w

/-- A lower semicontinuous metric on `ℂ` (the codomain in Definition 1.6, p. 6), with real values: symmetric, nonnegative,
vanishing exactly on the diagonal, satisfying the triangle inequality, and lower semicontinuous on `ℂ × ℂ`. -/
def PfefferIsLscMetric (D : ℂ → ℂ → ℝ) : Prop :=
  (∀ z, D z z = 0) ∧ (∀ z w, 0 ≤ D z w) ∧ (∀ z w, D z w = D w z) ∧ (∀ x y z, D x z ≤ D x y + D y z) ∧
    (∀ z w, D z w = 0 → z = w) ∧ LowerSemicontinuous (fun p : ℂ × ℂ => D p.1 p.2)

/-- The pairing functional `h = h^ℂ + f` of the field, as a function of `ω` (`addFunPairing`). -/
noncomputable def pfefferField {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ) (f : Ω → ℂ → ℝ) : Ω → (ℂ → ℝ) → ℝ :=
  fun ω => addFunPairing (hC ω) (f ω)

/-- The normalizing factor `c_r⁻¹ e^{-ξ h_r(0)}` of Axiom V, where `h_r(0) = hcirc ω r 0 + (average of f over ∂B_r(0))`. -/
noncomputable def pfefferNormalization {Ω : Type*} (ξ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (f : Ω → ℂ → ℝ) (c : ℝ → ℝ)
    (r : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal ((c r)⁻¹ * Real.exp (-(ξ * (hcirc ω r 0 + pfefferCircleAverage (f ω) r 0))))

/-- Tightness over scales, in the form used in Axiom V (p. 6): for every `ε ∈ (0, 1)` there is `M > 0` with
`P(M⁻¹ ≤ X_r ≤ M) ≥ 1 - ε` for all `r > 0`. The event is invariant under `X ↦ X⁻¹`, so this is tightness of the laws
of `X_r` and of their inverses in `(0, ∞)`. -/
def PfefferTightAcrossScales {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ → Ω → ℝ≥0∞) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ M : ℝ, 0 < M ∧ ∀ r : ℝ, 0 < r →
    ENNReal.ofReal (1 - ε) ≤ P {ω | ENNReal.ofReal M⁻¹ ≤ X r ω ∧ X r ω ≤ ENNReal.ofReal M}

/-- Axiom V of Definition 1.6 (p. 6) for the field `h = h^ℂ + f`, with scaling constants `c` (`c r = c_r`):
(a) `c_r > 0` for `r > 0`;
(b) for every Euclidean annulus `A(z₀; a, b)` with `0 < a < b`, the normalized distances across and around the scaled
annulus `rA = A(r z₀; r a, r b)`, `c_r⁻¹ e^{-ξ h_r(0)} D(across rA)` and `c_r⁻¹ e^{-ξ h_r(0)} D(around rA)`, are tight
over `r > 0` (together with their inverses);
(c) the bound (1.7): there is `Λ > 1` with `Λ⁻¹ δ^Λ ≤ c_{δr}/c_r ≤ Λ δ^{-Λ}` for all `δ ∈ (0, 1)` and all rational
`r > 0`. -/
def PfefferAxiomVScale {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ξ : ℝ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (f : Ω → ℂ → ℝ)
    (c : ℝ → ℝ) : Prop :=
  (∀ r : ℝ, 0 < r → 0 < c r) ∧
  (∀ (z₀ : ℂ) (a b : ℝ), 0 < a → a < b →
    PfefferTightAcrossScales P (fun r ω => pfefferNormalization ξ hcirc f c r ω *
        pfefferAcross (𝔇 (pfefferField hC f ω)) ((r : ℂ) * z₀) (r * a) (r * b)) ∧
    PfefferTightAcrossScales P (fun r ω => pfefferNormalization ξ hcirc f c r ω *
        pfefferAround (𝔇 (pfefferField hC f ω)) ((r : ℂ) * z₀) (r * a) (r * b))) ∧
  (∃ Λ : ℝ, 1 < Λ ∧ ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ q : ℚ, 0 < (q : ℝ) →
    Λ⁻¹ * δ ^ Λ ≤ c (δ * q) / c q ∧ c (δ * q) / c q ≤ Λ * δ ^ (-Λ))

/-- Axioms I–V of Definition 1.6 (p. 6) for the field `h = h^ℂ + f` on `(Ω, P)`, where `hC`, `hcirc` describe a
whole-plane GFF `h^ℂ` and `f` is a random continuous function. Axioms I–IV hold almost surely. -/
def PfefferWeakAxioms {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ξ : ℝ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (f : Ω → ℂ → ℝ) : Prop :=
  -- Codomain: each `D_h` is a lower semicontinuous metric (Definition 1.6, p. 6; see deviation 1).
  (∀ᵐ ω ∂P, PfefferIsLscMetric (𝔇 (pfefferField hC f ω))) ∧
  -- I. Length space.
  (∀ᵐ ω ∂P, PfefferIsLengthSpace (𝔇 (pfefferField hC f ω))) ∧
  -- II. Locality: `D_h(·, ·; U)` is determined a.s. by `h|_U`, for each deterministic open `U`.
  (∀ U : Set ℂ, IsOpen U → ∃ G : Ω → ℂ → ℂ → ℝ≥0∞,
    (∀ z w, Measurable[pairingSigmaAlgebra (pfefferField hC f) U] fun ω => G ω z w) ∧
      ∀ᵐ ω ∂P, ∀ z ∈ U, ∀ w ∈ U, internalMetric (𝔇 (pfefferField hC f ω)) U z w = G ω z w) ∧
  -- III. Weyl scaling: for each continuous `g`, `D_{h+g} = e^{ξ g} · D_h` a.s. (printed order: `g` before a.s.).
  (∀ g : ℂ → ℝ, Continuous g → ∀ᵐ ω ∂P, ∀ u v : ℂ,
    ENNReal.ofReal (𝔇 (addFunPairing (pfefferField hC f ω) g) u v) =
      weylScaling (𝔇 (pfefferField hC f ω)) ξ g u v) ∧
  -- IV. Translation invariance: `D_{h(· + z)}(u, v) = D_h(u + z, v + z)` a.s. for each deterministic `z`.
  (∀ z : ℂ, ∀ᵐ ω ∂P, ∀ u v : ℂ,
    𝔇 (affinePullbackPairing (pfefferField hC f ω) 1 z) u v = 𝔇 (pfefferField hC f ω) (u + z) (v + z)) ∧
  -- V. Tightness across scales, with some scaling constants.
  (∃ c : ℝ → ℝ, PfefferAxiomVScale P ξ 𝔇 hC hcirc f c)

/-- A weak LQG metric with parameter `ξ > 0` (Definition 1.6, p. 6): `ξ > 0`, `h ↦ D_h` is measurable (pointwise, see
deviation 2), and for every whole-plane GFF `h^ℂ` plus a random continuous function `f` on the same probability space,
the Axioms I–V hold. -/
def IsPfefferWeakLQGMetric (ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) : Prop :=
  0 < ξ ∧ (∀ z w : ℂ, Measurable[distributionMeasurableSpace] fun T => 𝔇 T z w) ∧
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (f : Ω → ℂ → ℝ), IsWholePlaneGFF P hC hcirc → (∀ ω, Continuous (f ω)) →
      (∀ x, Measurable fun ω => f ω x) → PfefferWeakAxioms P ξ 𝔇 hC hcirc f

/-- Proposition 1.9, equation (1.10) (p. 8) of Pfeffer. Let `Q = Q(ξ)` be the background charge of (1.4). For every
weak LQG metric `𝔇` with parameter `ξ`, every instance of the field `h = h^ℂ + f` and every family `c` of scaling
constants of Axiom V for that instance, `c_{δr}/c_r = δ^{ξQ + o_δ(1)}` as `δ → 0`, uniformly over `r > 0`. Written out:
for every `η > 0`, for all sufficiently small `δ > 0`, for all `r > 0`,
`|log (c_{δr}/c_r) / log δ - ξ Q| ≤ η`. -/
def PfefferBackgroundScaling (ξ Q : ℝ) : Prop :=
  ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsPfefferWeakLQGMetric ξ 𝔇 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (f : Ω → ℂ → ℝ), IsWholePlaneGFF P hC hcirc → (∀ ω, Continuous (f ω)) →
      (∀ x, Measurable fun ω => f ω x) →
      ∀ c : ℝ → ℝ, PfefferAxiomVScale P ξ 𝔇 hC hcirc f c →
        ∀ η : ℝ, 0 < η → ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ r : ℝ, 0 < r →
          |Real.log (c (δ * r) / c r) / Real.log δ - ξ * Q| ≤ η

end HarmonicBalls
