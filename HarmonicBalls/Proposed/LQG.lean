import Mathlib
import HarmonicBalls.Defs.LQG
import HarmonicBalls.Defs.LQGMetric

/-! # Literature inputs on the GFF, the LQG measure and the LQG metric (proposed)

Section 2 of Bou-Rabee and Gwynne, *Harmonic balls in Liouville quantum gravity* (arXiv:2208.11795),
paper/lqg_harmonic_ball-corrected.tex, lines 355-466. Each input is a `def ... : Prop` (never an axiom), to be taken
as an explicit hypothesis; the operator admits it into `HarmonicBalls/External`.

Each Prop is parametrized by the probability space and the field (`hC` the pairings, `hcirc` the circle averages
of the whole-plane GFF `h^ℂ`, `IsWholePlaneGFF`), and assumes `IsWholePlaneGFF P hC hcirc` itself, so that it is a
true statement for every choice of the parameters. The field of the paper is `h = h^ℂ - α₀ log |·|` (eq:gff,
line 380), with `γ ∈ (0, 2)` and `α₀ < Q = lqgQ γ`.

* `WholePlaneGFFAffineInvariance`: eq:gff-scaling (line 369).
* `LQGMeasureExistence`: existence of `μ_h` (eq:measure-lim, line 396).
* `LQGMeasureNonatomic`, `LQGMeasureLocality`, `LQGMeasureWeylScaling`, `LQGMeasureCoordChange`:
  Fact 2.1 I-IV (lines 401-416).
* `WholePlaneLQGBallMassBounds`: LQG mass of Euclidean balls for the whole-plane GFF (Ding-Gwynne 2020, Lemma 3.8),
  the single published estimate from which Lemma 2.4 and the unnumbered inputs I1 (full support) and I2 (volume
  growth at all small scales) of HarmonicBalls/Draft/Section2.lean are derived.
* `LQGMetricExistenceUniqueness`: existence and uniqueness of the γ-LQG metric (lines 418-421, 455).
* `LQGMetricFieldAxioms`: Fact 2.2 I-IV (lines 432-453) for the metric `D_h` of the field of the paper.

Some of these are consequences of the definitions (the paper says Fact 2.1 I-III are "immediate from the
definition", line 418); they are staged here so that downstream proofs can proceed, and each such docstring says so.
-/

namespace HarmonicBalls

open MeasureTheory Set
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The whole-plane GFF -/

/-- **Affine invariance of the whole-plane GFF modulo additive constant** (eq:gff-scaling, line 369):
`h^ℂ =d h^ℂ(a · + b) - h^ℂ_{|a|}(b)` for `a ∈ ℂ ∖ {0}`, `b ∈ ℂ`. Stated as: the field with pairings
`(h^ℂ(a · + b), φ) - h^ℂ_{|a|}(b) ∫ φ = |a|⁻² (h^ℂ, φ((· - b) / a)) - h^ℂ_{|a|}(b) ∫ φ` and circle averages
`h^ℂ_{|a| r}(a z + b) - h^ℂ_{|a|}(b)` is again a whole-plane GFF (`IsWholePlaneGFF` determines the joint law of all
pairings and circle averages). Source: the law of the whole-plane GFF modulo additive constant is invariant under
complex affine maps (paper, line 367): Gwynne-Holden-Sun, *Mating of trees for random planar maps and Brownian
motions* (arXiv:1910.04713v2), Section 3.2.2, p. 16; Berestycki-Powell, *Gaussian free field and Liouville quantum
gravity* (arXiv:2404.16642v2), Corollary 5.7 and Remark 5.8 (p. 169) with Lemma 6.26 (p. 220). It also follows from
the covariance kernel (eq:cov-kernel, line 359), `-log |z - w|` being affine invariant up to additive terms, so it
is expected to be provable from `IsWholePlaneGFF`. Each deterministic affine map is treated separately.
Berestycki-Powell initially uses log coefficient `1/(2π)` and rescales by `√(2π)` for LQG;
the present kernel already has log coefficient one. -/
def WholePlaneGFFAffineInvariance (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) : Prop :=
  IsWholePlaneGFF P hC hcirc → ∀ a : ℂ, a ≠ 0 → ∀ b : ℂ,
    IsWholePlaneGFF P
      (fun ω φ => (‖a‖ ^ 2)⁻¹ * hC ω (fun y => φ ((y - b) / a)) - hcirc ω ‖a‖ b * ∫ x, φ x)
      (fun ω r z => hcirc ω (‖a‖ * r) (a * z + b) - hcirc ω ‖a‖ b)

/-! ### The LQG measure: existence and Fact 2.1 -/

/-- **Existence of the γ-LQG measure** `μ_h` of `h = h^ℂ - α₀ log |·|` (eq:measure-lim, line 396): for
`γ ∈ (0, 2)` and `α₀ < Q`, there is a random measure `μ` with `IsLQGMeasureOfField P γ α₀ hcirc μ`, i.e. a.s. the
measures `ε^{γ²/2} e^{γ h_ε(z)} dz` converge vaguely along `ε = 2^{-k}` to a Radon measure.
Source: Bou-Rabee-Gwynne (arXiv:2208.11795v3), Section 2.2, p. 9, states existence for this singular
whole-plane field. Duplantier-Sheffield (arXiv:0808.1560v2), Proposition 1.1, p. 5, and Berestycki-Powell
(arXiv:2404.16642v2), Theorem 2.1, p. 62, treat bounded-domain Dirichlet fields; transfer near the pole
requires more than the domain Markov property. Local finiteness near the singularity uses `α₀ < Q`. -/
def LQGMeasureExistence (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) : Prop :=
  IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∃ μ : Ω → Measure ℂ, IsLQGMeasureOfField P γ α₀ hcirc μ

/-- **Fact 2.1 I (Radon measure)** (line 404): a.s. `μ_h` is a non-atomic Radon measure. Radon (locally finite)
is part of `IsLQGMeasureOfField`; this Prop is the non-atomicity. Source: paper, line 418 ("immediate from the
definition"), Fact 2.1 I, p. 9. The assertion holds simultaneously for all points; uniqueness of the locally
finite vague limit makes the choice of `μ` immaterial. Berestycki-Powell (arXiv:2404.16642v2), Theorems 2.1
and 3.2 (pp. 62 and 81), require transfer to this whole-plane singular field. -/
def LQGMeasureNonatomic (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) : Prop :=
  IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → α₀ < lqgQ γ → ∀ μ : Ω → Measure ℂ,
    IsLQGMeasureOfField P γ α₀ hcirc μ → ∀ᵐ ω ∂P, ∀ x : ℂ, μ ω {x} = 0

/-- **Fact 2.1 II (locality)** (line 405): for every deterministic open `U`, `μ_h(U)` is given by a measurable
function of `h|_U`, i.e. it is a.s. equal to a `σ(h|_U)`-measurable random variable (`fieldSigmaAlgebra`).
Source: paper, line 418 ("immediate from the definition", the circle averages over circles in `U` being
`σ(h|_U)`-measurable up to null sets). -/
def LQGMeasureLocality (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) : Prop :=
  IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → α₀ < lqgQ γ → ∀ μ : Ω → Measure ℂ,
    IsLQGMeasureOfField P γ α₀ hcirc μ → ∀ U : Set ℂ, IsOpen U →
      ∃ Y : Ω → ℝ≥0∞, Measurable[fieldSigmaAlgebra α₀ hC U] Y ∧ ∀ᵐ ω ∂P, μ ω U = Y ω

/-- **Fact 2.1 III (Weyl scaling)** (line 406): a.s., `e^{γ f} · μ_h = μ_{h+f}` for every continuous `f : ℂ → ℝ`,
where `μ_{h+f}` is the vague limit of `ε^{γ²/2} e^{γ (h + f)_ε(z)} dz` along `ε = 2^{-k}` (`addCircleAverage`).
Source: paper, line 418 ("immediate from the definition"). This is a deterministic consequence of `IsLQGLimit`
(the circle averages `f_ε` converge to `f` locally uniformly); it is expected to be proved rather than admitted.
All continuous functions share the same almost-sure event, as in Fact 2.1 III, p. 9. -/
def LQGMeasureWeylScaling (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) : Prop :=
  IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → α₀ < lqgQ γ → ∀ μ : Ω → Measure ℂ,
    IsLQGMeasureOfField P γ α₀ hcirc μ → ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f →
      IsLQGLimit γ (addCircleAverage (fieldCircleAverage α₀ (hcirc ω)) f)
        ((μ ω).withDensity fun x => ENNReal.ofReal (Real.exp (γ * f x)))

/-- **Fact 2.1 IV (conformal covariance), for complex affine maps** (eq:measure-coord, line 412): a.s., for all
`a ∈ ℂ ∖ {0}` and `b ∈ ℂ`, with `φ(x) = a x + b` (so `Q log |φ'| = Q log |a|`),
`μ_{h ∘ φ + Q log |φ'|}(A) = μ_h(φ(A))` for all Borel `A`. The circle averages of `h ∘ φ + Q log |a|` are
`(ε, z) ↦ h_{|a| ε}(a z + b) + Q log |a|`, and `A ↦ μ_h(φ(A))` is the push-forward of `μ_h` by `φ⁻¹`.
Since the pulled-back approximations at scale `2^{-k}` are those of `h` at scale `|a| 2^{-k}`, the simultaneous
statement uses a.s. convergence along all `ε → 0`. Source: Duplantier-Sheffield 2011, Proposition 2.1 (p. 13; a.s.
for a fixed conformal map); Sheffield-Wang 2016 (*Field-measure correspondence in Liouville quantum gravity almost
surely commutes with all conformal maps simultaneously*, arXiv:1605.06171v2), Theorem 1.1 (a.s. convergence as
`ε → 0`) and Theorem 1.4 (p. 3; all conformal maps simultaneously). Sheffield-Wang starts with a bounded-domain
Dirichlet field; Fact 2.1 IV, p. 9 of Bou-Rabee-Gwynne, is the direct background statement for this singular field.

Scope: only complex affine maps, which is how the paper uses Fact 2.1 IV (rescalings, lines 904-916 and 2164).
For a general conformal `φ : Ũ → U` the field `h ∘ φ` lives on `Ũ` and its circle averages are not circle
averages of `h`, so they are not expressible through the
interface of `Defs/GFF.lean`. -/
def LQGMeasureCoordChange (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) : Prop :=
  IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → α₀ < lqgQ γ → ∀ μ : Ω → Measure ℂ,
    IsLQGMeasureOfField P γ α₀ hcirc μ → ∀ᵐ ω ∂P, ∀ a : ℂ, a ≠ 0 → ∀ b : ℂ,
      IsLQGLimit γ (fun ε z => fieldCircleAverage α₀ (hcirc ω) (‖a‖ * ε) (a * z + b) + lqgQ γ * Real.log ‖a‖)
        ((μ ω).map fun x => (x - b) / a)

/-! ### The LQG measure of Euclidean balls (base estimate for Lemma 2.4, I1 and I2) -/

/-- **LQG mass of Euclidean balls for the whole-plane GFF.** For the γ-LQG measure `μ` of a whole-plane GFF `h^ℂ`
normalized so that `h^ℂ_1(0) = 0` (the field of the paper with `α₀ = 0`), for each `β̲ ∈ (0, 2/(2+γ)²)` and each
`β̄ > 2/(2-γ)²`, with polynomially high probability as `ε → 0` (`PolyHighProb`, the convention of both papers):
`μ(B_{ε^β̲}(z)) ≥ ε` and `μ(B_{ε^β̄}(z)) ≤ ε` for all `z` in the unit square `𝕊 = [0,1]²`.

Source: J. Ding and E. Gwynne, *The fractal dimension of Liouville quantum gravity: universality, monotonicity, and
bounds*, Comm. Math. Phys. 374 (2020), arXiv:1807.01072, Lemma 3.8 (p. 25), verbatim (whole-plane case used):
"Lemma 3.8. Suppose that h is either a whole-plane GFF normalized so that h_1(0) = 0, a zero-boundary GFF on 𝕊(1),
or one of the white noise fields ĥ or ĥ^tr defined above. For each β̲ ∈ (0, 2/(2+γ)²) and each β̄ > 2/(2−γ)², it
holds with polynomially high probability as ε → 0 that
inf_{z∈𝕊} μ_h(B_{ε^β̲}(z)) ≥ ε and sup_{z∈𝕊} μ_h(B_{ε^β̄}(z)) ≤ ε. (3.14)"
Here `𝕊 = [0,1]²` (loc. cit., Theorem 1.1: "Let 𝕊 = [0,1]² be the unit square"). This is the estimate on which
Berestycki-Gwynne (arXiv:2003.10320, Lemma A.1, p. 66, eq. (A.2)) build the argument that the paper cites for
Lemma 2.4 ("exactly the same argument as in [BG20, Lemma A.1]", line 510).

How the paper's unnumbered inputs and Lemma 2.4 follow from this single estimate (none of them is a separate input):
1. Put `δ = ε^β`: the bounds read `δ^{β⁻} ≤ μ(B_δ(z)) ≤ δ^{β⁺}` on `𝕊` for `β⁻ = 1/β̲ > (2+γ)²/2` and
   `β⁺ = 1/β̄ < (2-γ)²/2`, with polynomially high probability as `δ → 0`.
2. By `WholePlaneGFFAffineInvariance` and `LQGMeasureCoordChange`, the same holds on any fixed square, hence on
   `B_R`: the additive constants `h^ℂ_{|a|}(b)` are Gaussian, so `e^{γ h^ℂ_{|a|}(b)} ∈ [δ^ζ, δ^{-ζ}]` with
   superpolynomially high probability, absorbed by the slack in the open exponent ranges.
3. The log singularity `-α₀ log |·|` (Draft/Section2 `LiouvilleVolumeGrowthStmt`, Lemma 2.4 with [C1]): the proof of
   BG20 Lemma A.1 (scale invariance modulo additive constant on the annuli `B_{e^{-k}} \ B_{e^{-k-1}}`, the coordinate
   change formula, and a union bound over `k ≤ (1-ζ) log δ⁻¹`), with `-γ log |·|` replaced by `-α₀ log |·|`
   (`LQGMeasureWeylScaling`, `LQGMeasureLocality` on each annulus); at `|z| ≍ δ^s` the exponent interpolates linearly
   between `(2∓γ)²/2` (`s = 0`) and `γ(Q-α₀)` (`s = 1`).
4. I2 (Draft/Section2 `LQGVolumeGrowthAllScalesStmt`): Borel-Cantelli over `δ = 2^{-k}` (the failure probabilities
   `O(2^{-kp})` are summable), monotonicity of `r ↦ μ(B_r(z))` and the slack in the exponent ranges.
5. I1 (Draft/Section2 `LQGMeasureFullSupportStmt`): the lower bound of I2, since every nonempty open set contains a
   ball `B_r(z)` with `z ∈ B_R` and `r` small. -/
def WholePlaneLQGBallMassBounds (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) : Prop :=
  IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → ∀ μ : Ω → Measure ℂ, IsLQGMeasureOfField P γ 0 hcirc μ →
    ∀ βlower βupper : ℝ, 0 < βlower → βlower < 2 / (2 + γ) ^ 2 → 2 / (2 - γ) ^ 2 < βupper →
      PolyHighProb P fun ε => {ω | (∀ z ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1,
          ENNReal.ofReal ε ≤ μ ω (Metric.ball z (ε ^ βlower))) ∧
        ∀ z ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1, μ ω (Metric.ball z (ε ^ βupper)) ≤ ENNReal.ofReal ε}

/-! ### The LQG metric: existence, uniqueness and Fact 2.2 -/

/-- **Existence and uniqueness of the γ-LQG metric** (lines 418-421 and 455): for each `γ ∈ (0, 2)` there is
`ξ > 0` (namely `ξ = γ / d_γ`, eq:xi, line 440) such that a γ-LQG metric `𝔇` with Weyl exponent `ξ`
(`IsLQGMetric`) exists, and any two such metrics agree up to a deterministic positive constant: there is `C > 0`
such that a.s. `D'_h = C D_h` whenever `h` is a whole-plane GFF plus a (measurable) random continuous function.
Source: Gwynne-Miller 2021 (*Existence and uniqueness of the Liouville quantum gravity metric for γ ∈ (0, 2)*,
Invent. Math. 223, arXiv:1905.00383), Theorem 1.2 (p. 6), building on Ding-Dubédat-Dunlap-Falconet 2020
(*Tightness of Liouville first passage percolation for γ ∈ (0, 2)*, Publ. IHES 132, arXiv:1904.08021), Theorem 1
(p. 3) and Dubédat-Falconet-Gwynne-Pfeffer-Sun 2020 (*Weak LQG metrics and Liouville first passage percolation*,
PTRF 178, arXiv:1905.00380), Theorem 1.2 (p. 6).

The exponent is existentially quantified, exactly as in GM21, where `ξ = γ / d_γ` with `d_γ` the LFPP exponent
of Ding-Gwynne 2018; this Prop asserts nothing for other values of `ξ`. -/
def LQGMetricExistenceUniqueness : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ ξ : ℝ, 0 < ξ ∧ (∃ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇) ∧
    ∀ 𝔇 𝔇' : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 → IsLQGMetric γ ξ 𝔇' →
      ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
        (hcirc : Ω → ℝ → ℂ → ℝ) (f : Ω → ℂ → ℝ), IsWholePlaneGFF P hC hcirc → (∀ ω, Continuous (f ω)) →
        (∀ x, Measurable fun ω => f ω x) → ∀ᵐ ω ∂P, ∀ u v : ℂ,
          𝔇' (addFunPairing (hC ω) (f ω)) u v = C * 𝔇 (addFunPairing (hC ω) (f ω)) u v

/-- **Fact 2.2 for the field of the paper** (lines 432-453). Let `𝔇` be a γ-LQG metric with Weyl exponent `ξ`, and
`h = h^ℂ - α₀ log |·|` with `α₀ < Q`. The metric of `h + f` (`f` continuous, possibly `0`) is the Weyl scaling
`e^{ξ (f - α₀ log |·|)} · D_{h^ℂ}` (`IsLQGMetricOfField`); write `D_h` for the case `f = 0`. Then:
* I: a.s. `D_h` is finite, and it is a length metric inducing the Euclidean topology;
* II: for each deterministic open `U`, `D_h(·, ·; U)` is a.s. equal to a `σ(h|_U)`-measurable random function;
* III: a.s., for every continuous `f`, `D_{h+f} = e^{ξ f} · D_h`;
* IV: for each `r > 0`, `z ∈ ℂ`, a.s. `D_h(r u + z, r v + z) = D_{h(r · + z) + Q log r}(u, v)` for all `u, v`, where
  `h(r · + z) + Q log r = h^ℂ(r · + z) + Q log r - α₀ log |r · + z|` has metric
  `e^{-ξ α₀ log |r · + z|} · D_{h^ℂ(r · + z) + Q log r}`.
Source: for a whole-plane GFF plus a continuous function these are the axioms of Gwynne-Miller 2021,
Section 1.2 (p. 6), verified in DDDF20, DFGPS20 and GM21 (paper, line 455). For the log singularity
`-α₀ log |·|`: Dubédat-Falconet-Gwynne-Pfeffer-Sun 2020 (arXiv:1905.00380), definition p. 9, Theorem 1.10
(p. 10; finiteness for `α₀ < Q`) and Proposition 3.17 (p. 43; Euclidean topology); Gwynne-Miller 2021,
Remark 1.5 (p. 8). III and IV for `h` follow from those for `h^ℂ` and the composition rule of Weyl scalings.

Caveat on `ξ`: the Prop quantifies over every `ξ` for which `IsLQGMetric γ ξ 𝔇` holds. The literature
constructs γ-LQG metrics only for `ξ = γ / d_γ`; if the axioms admitted another exponent, this Prop would assert
Fact 2.2 for it as well. -/
def LQGMetricFieldAxioms (P : Measure Ω) (γ ξ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) : Prop :=
  IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → α₀ < lqgQ γ → ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ,
    IsLQGMetric γ ξ 𝔇 →
    let Dh : Ω → ℂ → ℂ → ℝ≥0∞ := fun ω => weylScaling (𝔇 (hC ω)) ξ fun x => -α₀ * Real.log ‖x‖
    -- I. Finiteness, Euclidean topology and length metric.
    (∀ᵐ ω ∂P, (∀ u v, Dh ω u v < ∞) ∧ IsEuclideanLengthMetric fun u v => (Dh ω u v).toReal) ∧
    -- II. Locality.
    (∀ U : Set ℂ, IsOpen U → ∃ G : Ω → ℂ → ℂ → ℝ≥0∞,
      (∀ z w, Measurable[fieldSigmaAlgebra α₀ hC U] fun ω => G ω z w) ∧
        ∀ᵐ ω ∂P, ∀ z ∈ U, ∀ w ∈ U, internalMetric (fun u v => (Dh ω u v).toReal) U z w = G ω z w) ∧
    -- III. Weyl scaling.
    (∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → ∀ u v,
      weylScaling (𝔇 (hC ω)) ξ (fun x => f x - α₀ * Real.log ‖x‖) u v =
        weylScaling (fun u v => (Dh ω u v).toReal) ξ f u v) ∧
    -- IV. Coordinate change for scaling and translation.
    (∀ r : ℝ, 0 < r → ∀ z : ℂ, ∀ᵐ ω ∂P, ∀ u v : ℂ,
      Dh ω (r * u + z) (r * v + z) =
        weylScaling (𝔇 (addFunPairing (affinePullbackPairing (hC ω) r z) fun _ => lqgQ γ * Real.log r)) ξ
          (fun x => -α₀ * Real.log ‖(r : ℂ) * x + z‖) u v)

end HarmonicBalls
