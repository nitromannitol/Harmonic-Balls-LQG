import HarmonicBalls.Proofs.GFF.PureGFFPfefferCrossingTightness
import HarmonicBalls.Steps.Sec11.ProperMetricDyadic

/-! # Pfeffer's weak LQG metric axioms for the pure whole-plane GFF (Definition 1.6)

Sources: Pfeffer, *Weak Liouville quantum gravity metrics with matter central charge up to 25*, arXiv:2104.04020v3,
Definition 1.6 (p. 6), Axioms I–V and the codomain of lower semicontinuous metrics; Gwynne–Miller, *Existence and
uniqueness of the Liouville quantum gravity metric for `γ ∈ (0, 2)`*, arXiv:1905.00383v3, Section 1.2 (p. 6), the
axioms of a `γ`-LQG metric, and (1.13), (1.15).

Setting. `𝔇` is a `γ`-LQG metric with Weyl exponent `ξ` (`IsLQGMetric γ ξ 𝔇`) and `h^ℂ` is a whole-plane GFF
(`IsWholePlaneGFF P hC hcirc`). The field of Definition 1.6 is `h^ℂ + f` with `f = 0`.

Results.
* `IsEuclideanLengthMetric.nonneg`, `IsEuclideanLengthMetric.pfefferIsLscMetric`,
  `IsEuclideanLengthMetric.pfefferIsLengthSpace`: a length metric inducing the Euclidean topology is a nonnegative
  lower semicontinuous metric and a length space in the sense of Axiom I.
* `IsLQGMetric.pureGFF_pfefferWeakAxioms`: `PfefferWeakAxioms` for `f = 0`. The codomain and Axioms I–IV follow from
  the axioms of `IsLQGMetric` applied to the field `h^ℂ + 0`: Axiom I (Euclidean length metric) gives the codomain and
  the length space property; locality is the same statement; the almost sure Weyl scaling for all continuous functions
  at once gives Axiom III; the coordinate change with scale `r = 1` gives the translation invariance of Axiom IV.
  Axiom V holds with `c_r = r^{ξQ}`, `Q = 2/γ + γ/2` (`IsLQGMetric.pureGFF_pfefferAxiomVScale`).

Scope. Only the pure field (`f = 0`) is treated. Nothing here concerns `h^ℂ + f` for nonzero `f` or the class
`IsPfefferWeakLQGMetric`.

Credit: the whole-plane GFF `h^ℂ` is due to Leonardo Bonanno.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set
open scoped ENNReal

/-- A metric which induces the Euclidean topology and is a length metric takes nonnegative values. -/
theorem IsEuclideanLengthMetric.nonneg {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (z w : ℂ) :
    0 ≤ D z w := by
  have h := hD.triangle z w z
  rw [hD.self_eq_zero, hD.symm w z] at h
  linarith

/-- A metric which induces the Euclidean topology and is a length metric is a lower semicontinuous metric on `ℂ`
(the codomain of Definition 1.6). -/
theorem IsEuclideanLengthMetric.pfefferIsLscMetric {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) :
    PfefferIsLscMetric D :=
  ⟨hD.self_eq_zero, hD.nonneg, hD.symm, hD.triangle, hD.eq_of_eq_zero, hD.continuous_pair.lowerSemicontinuous⟩

/-- A metric which induces the Euclidean topology and is a length metric satisfies Axiom I of Definition 1.6. -/
theorem IsEuclideanLengthMetric.pfefferIsLengthSpace {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) :
    PfefferIsLengthSpace D :=
  hD.ofReal_eq_internalMetric

/-- **Pfeffer's weak LQG metric axioms for the pure whole-plane GFF.** For a `γ`-LQG metric `𝔇` with Weyl exponent
`ξ` and a whole-plane GFF `h^ℂ`, the field `h^ℂ + f` with `f = 0` satisfies the codomain condition and Axioms I–V of
Definition 1.6, Axiom V with the scaling constants `c_r = r^{ξQ}`, `Q = 2/γ + γ/2`. -/
theorem IsLQGMetric.pureGFF_pfefferWeakAxioms {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇) {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc) :
    PfefferWeakAxioms P ξ 𝔇 hC hcirc 0 := by
  have hax : SatisfiesLQGMetricAxioms P γ ξ 𝔇 (pfefferField hC fun _ _ => 0) :=
    h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc (fun _ _ => 0) h (fun _ => continuous_const)
      (fun _ => measurable_const)
  refine ⟨?_, ?_, hax.locality, ?_, ?_, ⟨_, h𝔇.pureGFF_pfefferAxiomVScale h⟩⟩
  · filter_upwards [hax.ae_isEuclideanLengthMetric] with ω hω using hω.pfefferIsLscMetric
  · filter_upwards [hax.ae_isEuclideanLengthMetric] with ω hω using hω.pfefferIsLengthSpace
  · intro g hg
    filter_upwards [hax.ae_weylScaling] with ω hω using hω g hg
  · intro z
    filter_upwards [hax.coordChange 1 one_pos z] with ω hω u v
    have huv := hω u v
    simp only [Complex.ofReal_one, one_mul, Real.log_one, mul_zero, addFunPairing_const_zero] at huv
    exact huv.symm

end HarmonicBalls
