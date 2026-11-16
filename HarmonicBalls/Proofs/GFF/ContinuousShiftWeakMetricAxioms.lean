import HarmonicBalls.Proofs.GFF.PureGFFPfefferWeakAxioms
import HarmonicBalls.Proofs.GFF.LQGMetricExistence

/-! # Pfeffer's weak LQG metric Axioms I–IV for a whole-plane GFF plus a continuous function

Sources: Pfeffer, *Weak Liouville quantum gravity metrics with matter central charge up to 25*, arXiv:2104.04020v3,
Definition 1.6 (p. 6), the codomain of lower semicontinuous metrics and Axioms I–IV for the field `h = h^ℂ + f`;
Gwynne–Miller, *Existence and uniqueness of the Liouville quantum gravity metric for `γ ∈ (0, 2)`*,
arXiv:1905.00383v3, Section 1.2 (p. 6), the axioms of a `γ`-LQG metric for a whole-plane GFF plus a continuous
function, and Theorem 1.2 (p. 6).

Setting. `𝔇` is a `γ`-LQG metric with Weyl exponent `ξ` (`IsLQGMetric γ ξ 𝔇`), `h^ℂ` is a whole-plane GFF
(`IsWholePlaneGFF P hC hcirc`) and `f` is a random continuous function on the same probability space, measurable in
`ω` at every point. The field of Definition 1.6 is `h^ℂ + f` (`pfefferField hC f`).

Results.
* `IsLQGMetric.continuousShift_pfefferWeakAxioms_one_to_four`: the codomain condition and Axioms I–IV of
  `PfefferWeakAxioms` hold for `h^ℂ + f`. They follow from the axioms of `IsLQGMetric` applied to this same field:
  Axiom I of `IsLQGMetric` (Euclidean length metric) gives the codomain and the length space property; locality is
  the same statement; the almost sure Weyl scaling for all continuous functions at once gives Axiom III; the
  coordinate change with scale `r = 1` gives the translation invariance of Axiom IV.
* `IsLQGMetric.deterministicShift_pfefferWeakAxioms_one_to_four`: the case of a deterministic continuous `f`.
* `IsLQGMetric.continuousShift_pfefferWeakAxioms_of_axiomVScale`: Axiom V for `h^ℂ + f`, with some scaling
  constants, completes `PfefferWeakAxioms` for `h^ℂ + f`.
* `exists_isLQGMetric_continuousShift_pfefferWeakAxioms_one_to_four`: for `γ ∈ (0, 2)` the `γ`-LQG metric with Weyl
  exponent `ξ = γ / d_γ` of Gwynne–Miller, Theorem 1.2, satisfies the codomain condition and Axioms I–IV for every
  whole-plane GFF plus a random continuous function.

Scope. Axiom V for `h^ℂ + f` with `f ≠ 0` is not treated here; for `f = 0` it is
`IsLQGMetric.pureGFF_pfefferAxiomVScale`.

Credit: the whole-plane GFF `h^ℂ` is due to Leonardo Bonanno.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set
open scoped ENNReal

/-- **Pfeffer's weak LQG metric Axioms I–IV for a whole-plane GFF plus a continuous function.** For a `γ`-LQG metric
`𝔇` with Weyl exponent `ξ`, a whole-plane GFF `h^ℂ` and a random continuous function `f` on the same probability
space, measurable in `ω` at every point, the field `h^ℂ + f` satisfies the codomain condition and Axioms I–IV of
Definition 1.6, exactly as the first five clauses of `PfefferWeakAxioms`. -/
theorem IsLQGMetric.continuousShift_pfefferWeakAxioms_one_to_four {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇) {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc) {f : Ω → ℂ → ℝ} (hf : ∀ ω, Continuous (f ω))
    (hfm : ∀ x, Measurable fun ω => f ω x) :
    (∀ᵐ ω ∂P, PfefferIsLscMetric (𝔇 (pfefferField hC f ω))) ∧
    (∀ᵐ ω ∂P, PfefferIsLengthSpace (𝔇 (pfefferField hC f ω))) ∧
    (∀ U : Set ℂ, IsOpen U → ∃ G : Ω → ℂ → ℂ → ℝ≥0∞,
      (∀ z w, Measurable[pairingSigmaAlgebra (pfefferField hC f) U] fun ω => G ω z w) ∧
        ∀ᵐ ω ∂P, ∀ z ∈ U, ∀ w ∈ U, internalMetric (𝔇 (pfefferField hC f ω)) U z w = G ω z w) ∧
    (∀ g : ℂ → ℝ, Continuous g → ∀ᵐ ω ∂P, ∀ u v : ℂ,
      ENNReal.ofReal (𝔇 (addFunPairing (pfefferField hC f ω) g) u v) =
        weylScaling (𝔇 (pfefferField hC f ω)) ξ g u v) ∧
    (∀ z : ℂ, ∀ᵐ ω ∂P, ∀ u v : ℂ,
      𝔇 (affinePullbackPairing (pfefferField hC f ω) 1 z) u v = 𝔇 (pfefferField hC f ω) (u + z) (v + z)) := by
  have hax : SatisfiesLQGMetricAxioms P γ ξ 𝔇 (pfefferField hC f) :=
    h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc f h hf hfm
  refine ⟨?_, ?_, hax.locality, ?_, ?_⟩
  · filter_upwards [hax.ae_isEuclideanLengthMetric] with ω hω using hω.pfefferIsLscMetric
  · filter_upwards [hax.ae_isEuclideanLengthMetric] with ω hω using hω.pfefferIsLengthSpace
  · intro g hg
    filter_upwards [hax.ae_weylScaling] with ω hω using hω g hg
  · intro z
    filter_upwards [hax.coordChange 1 one_pos z] with ω hω u v
    have huv := hω u v
    simp only [Complex.ofReal_one, one_mul, Real.log_one, mul_zero, addFunPairing_const_zero] at huv
    exact huv.symm

/-- **Axioms I–IV for a whole-plane GFF plus a deterministic continuous function.** For a `γ`-LQG metric `𝔇` with
Weyl exponent `ξ`, a whole-plane GFF `h^ℂ` and a deterministic continuous function `φ`, the field `h^ℂ + φ` satisfies
the codomain condition and Axioms I–IV of Definition 1.6. -/
theorem IsLQGMetric.deterministicShift_pfefferWeakAxioms_one_to_four {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc) {φ : ℂ → ℝ}
    (hφ : Continuous φ) :
    (∀ᵐ ω ∂P, PfefferIsLscMetric (𝔇 (pfefferField hC (fun _ => φ) ω))) ∧
    (∀ᵐ ω ∂P, PfefferIsLengthSpace (𝔇 (pfefferField hC (fun _ => φ) ω))) ∧
    (∀ U : Set ℂ, IsOpen U → ∃ G : Ω → ℂ → ℂ → ℝ≥0∞,
      (∀ z w, Measurable[pairingSigmaAlgebra (pfefferField hC fun _ => φ) U] fun ω => G ω z w) ∧
        ∀ᵐ ω ∂P, ∀ z ∈ U, ∀ w ∈ U, internalMetric (𝔇 (pfefferField hC (fun _ => φ) ω)) U z w = G ω z w) ∧
    (∀ g : ℂ → ℝ, Continuous g → ∀ᵐ ω ∂P, ∀ u v : ℂ,
      ENNReal.ofReal (𝔇 (addFunPairing (pfefferField hC (fun _ => φ) ω) g) u v) =
        weylScaling (𝔇 (pfefferField hC (fun _ => φ) ω)) ξ g u v) ∧
    (∀ z : ℂ, ∀ᵐ ω ∂P, ∀ u v : ℂ,
      𝔇 (affinePullbackPairing (pfefferField hC (fun _ => φ) ω) 1 z) u v =
        𝔇 (pfefferField hC (fun _ => φ) ω) (u + z) (v + z)) :=
  h𝔇.continuousShift_pfefferWeakAxioms_one_to_four h (fun _ => hφ) fun _ => measurable_const

/-- Axiom V for a whole-plane GFF plus a random continuous function, with some scaling constants, completes
`PfefferWeakAxioms` for that field: the codomain condition and Axioms I–IV hold for every `γ`-LQG metric. -/
theorem IsLQGMetric.continuousShift_pfefferWeakAxioms_of_axiomVScale {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc) {f : Ω → ℂ → ℝ}
    (hf : ∀ ω, Continuous (f ω)) (hfm : ∀ x, Measurable fun ω => f ω x)
    (hV : ∃ c : ℝ → ℝ, PfefferAxiomVScale P ξ 𝔇 hC hcirc f c) :
    PfefferWeakAxioms P ξ 𝔇 hC hcirc f := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := h𝔇.continuousShift_pfefferWeakAxioms_one_to_four h hf hfm
  exact ⟨h0, h1, h2, h3, h4, hV⟩

/-- **Axioms I–IV for the `γ`-LQG metric.** For `γ ∈ (0, 2)` the Weyl exponent `ξ = γ / d_γ` is positive and the
`γ`-LQG metric with Weyl exponent `ξ` of Gwynne–Miller, Theorem 1.2, satisfies the codomain condition and Axioms I–IV
of Definition 1.6 for every whole-plane GFF plus a random continuous function. -/
theorem exists_isLQGMetric_continuousShift_pfefferWeakAxioms_one_to_four {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    0 < LQGMetric.xiGamma γ ∧ ∃ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ (LQGMetric.xiGamma γ) 𝔇 ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
        (f : Ω → ℂ → ℝ), IsWholePlaneGFF P hC hcirc → (∀ ω, Continuous (f ω)) →
        (∀ x, Measurable fun ω => f ω x) →
        (∀ᵐ ω ∂P, PfefferIsLscMetric (𝔇 (pfefferField hC f ω))) ∧
        (∀ᵐ ω ∂P, PfefferIsLengthSpace (𝔇 (pfefferField hC f ω))) ∧
        (∀ U : Set ℂ, IsOpen U → ∃ G : Ω → ℂ → ℂ → ℝ≥0∞,
          (∀ z w, Measurable[pairingSigmaAlgebra (pfefferField hC f) U] fun ω => G ω z w) ∧
            ∀ᵐ ω ∂P, ∀ z ∈ U, ∀ w ∈ U, internalMetric (𝔇 (pfefferField hC f ω)) U z w = G ω z w) ∧
        (∀ g : ℂ → ℝ, Continuous g → ∀ᵐ ω ∂P, ∀ u v : ℂ,
          ENNReal.ofReal (𝔇 (addFunPairing (pfefferField hC f ω) g) u v) =
            weylScaling (𝔇 (pfefferField hC f ω)) (LQGMetric.xiGamma γ) g u v) ∧
        (∀ z : ℂ, ∀ᵐ ω ∂P, ∀ u v : ℂ,
          𝔇 (affinePullbackPairing (pfefferField hC f ω) 1 z) u v =
            𝔇 (pfefferField hC f ω) (u + z) (v + z)) := by
  obtain ⟨hξ, 𝔇, h𝔇⟩ := exists_isLQGMetric hγ hγ2
  refine ⟨hξ, 𝔇, h𝔇, ?_⟩
  intro Ω _ P hC hcirc f h hf hfm
  exact h𝔇.continuousShift_pfefferWeakAxioms_one_to_four h hf hfm

end HarmonicBalls
