import HarmonicBalls.FirstPass.S11n

/-!
# Frozen existence of common canonical LQG decoders

One EXTERNAL input for the pull-back of the canonical statement to an arbitrary whole-plane GFF model. Its witnesses
are the common decoders `Dμ`, `Dd` on the canonical field space, used in `LQGCanonicalIdentificationStmt`
(`FirstPass/S11n.lean`).
-/

namespace HarmonicBalls

open MeasureTheory

universe u

/-- DERIVED INTERFACE. Audit l.188: "Canonical simultaneous
measure/metric decoders are assembled from construction, measurability, locality, and uniqueness. There is no single printed
theorem with this exact Lean type."
FROZEN, EXTERNAL (truth check TRUE, Verdict and section 1). For every `γ ∈ (0, 2)`, every `ξ ∈ ℝ` and
every `α₀ < Q_γ`, there are common canonical decoders `Dμ : CanonSpace → Measure ℂ` and `Dd : CanonSpace → ℂ → ℂ → ℝ`
for which `LQGCanonicalIdentificationStmt` holds: for every whole-plane GFF model, every LQG measure `μ` and every LQG
metric `D` of the field `h^ℂ - α₀ log|·|`, almost surely `μ = a • Dμ (alphaCanon α₀ hC)` and
`D = b * Dd (alphaCanon α₀ hC)` for constants `a, b > 0`.

Sources: the measure decoder from the mean-zero local decoders, Duplantier-Sheffield arXiv:0808.1560v2; the metric
uniqueness up to a deterministic factor, Gwynne-Miller arXiv:1905.00383v3, Theorem 1.2, p. 6; the inserted metric,
DFGPS arXiv:1905.00380v2; the reconstruction of the normalised field from mean-zero observations.
The parameter `ξ` is free: Gwynne-Miller Theorem 1.2 is displayed at `ξ = γ/d_γ`, and the reduction of the
free-`ξ` form to that value (for a value with no metric the metric clause is vacuous).
Used by: `correctedLemma11_13_of_existence` (`HarmonicBalls/FirstPass/S11n/Existence.lean`). -/
def LQGCanonicalDecodersExistStmt : Prop :=
  ∀ (γ ξ α₀ : ℝ), 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∃ (Dμ : S11n.CanonSpace → Measure ℂ) (Dd : S11n.CanonSpace → ℂ → ℂ → ℝ),
      S11n.LQGCanonicalIdentificationStmt.{u} γ ξ α₀ Dμ Dd

/-- FROZEN, EXTERNAL (truth check TRUE).
The measurable strengthening of `LQGCanonicalDecodersExistStmt`, which
is kept unchanged. For every `γ ∈ (0, 2)`, every `ξ ∈ ℝ` and every `α₀ < Q_γ` there are

* a kernel `K : CanonSpace → Measure ℂ`, measurable and s-finite (`IsSFiniteKernel K`), whose values are locally finite
  Radon measures on `ℂ` (`IsFiniteMeasureOnCompacts`), the measure decoder;
* a map `d : CanonSpace → C(ℂ × ℂ, ℝ)`, Borel for the compact-open topology, which is local uniform convergence on
  `ℂ × ℂ`, the metric decoder;

such that

1. the identification clause `LQGCanonicalIdentificationStmt` holds with `Dμ := K` and `Dd L x y := d L (x, y)`, with the
   same quantification over arbitrary whole-plane GFF models and the same two positive scalar factors as the old
   statement (retained verbatim in the sense of that clause);
2. the measure map is a measurable kernel with locally finite Radon values (the type of `K` and item 2 of the source);
3. the metric map is Borel into continuous functions for local uniform convergence (`Measurable d`);
4. there is a measurable set `G` of canonical fields, `P_α`-conull for every whole-plane GFF model
   (`alphaCanon α₀ hC ω ∈ G` almost surely), on which `K L` has full support and `d L` is a length metric inducing the
   Euclidean topology (`IsEuclideanLengthMetric`).

Sources: Duplantier-Sheffield arXiv:0808.1560v2, Proposition 1.1, printed p. 5 (measure construction) and Proposition 2.1,
printed p. 13 (coordinate change); Gwynne-Miller arXiv:1905.00383v3, section 1.2, printed pp. 5-6 (the metric as a measurable
map from distributions to continuous metrics) and Theorem 1.2, printed p. 6 (existence and uniqueness); Gwynne-Miller
Remark 1.5, printed p. 8, and Dubedat-Falconet-Gwynne-Pfeffer-Sun arXiv:1905.00380v2, Proposition 3.17, printed p. 43
(continuity through an insertion of strength `α₀ < Q`). Free-`ξ` source (the unrestricted `ξ` quantifier, which
Gwynne-Miller Theorem 1.2 alone does not give, their Weyl exponent being fixed at `γ/d_γ`): Ding-Gwynne
arXiv:2108.12060v1, Definition 1.5, printed pp. 5-6, and Theorem 1.9, printed p. 7, (1.13); subcritical parameter
correspondence arXiv:2005.13576v2, Proposition 1.1, printed p. 3, and Section 1.3, printed p. 9, (1.9)-(1.10).
Clause 4 is required also when no LQG metric exists at the given `ξ`; this is harmless, since fixed defaults satisfy
that branch (a fixed locally finite measure replaces unsuccessful inputs). Used by: the measurable covariance proposition of
`HarmonicBalls/FirstPass/S11s.lean` and, through it, the certified-decoder bridge of Step 13. -/
def LQGCanonicalDecodersMeasurableExistStmt : Prop :=
  ∀ (γ ξ α₀ : ℝ), 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∃ (K : ProbabilityTheory.Kernel S11n.CanonSpace ℂ) (d : S11n.CanonSpace → ContinuousMap (ℂ × ℂ) ℝ),
      ProbabilityTheory.IsSFiniteKernel K ∧ (∀ L, MeasureTheory.IsFiniteMeasureOnCompacts (K L)) ∧
      Measurable d ∧
      S11n.LQGCanonicalIdentificationStmt.{u} γ ξ α₀ (fun L => K L) (fun L x y => d L (x, y)) ∧
      ∃ G : Set S11n.CanonSpace, MeasurableSet G ∧
        (∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
          (hcirc : Ω → ℝ → ℂ → ℝ),
          IsWholePlaneGFF P hC hcirc → ∀ᵐ ω ∂P, alphaCanon α₀ hC ω ∈ G) ∧
        ∀ L ∈ G, (K L).support = Set.univ ∧ IsEuclideanLengthMetric (fun x y => d L (x, y))

end HarmonicBalls
