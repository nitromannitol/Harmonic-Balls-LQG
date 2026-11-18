import HarmonicBalls.Proposed.LQG
import HarmonicBalls.FirstPass.S11v.AffineCore

/-! # Cited facts of Section 2: the LQG measure (Fact 2.1) and the LQG metric (Fact 2.2)

Bou-Rabee and Gwynne, *Harmonic balls in Liouville quantum gravity* (arXiv:2208.11795),
paper/lqg_harmonic_ball-corrected.tex, Section 2.2 (lines 397-468). The two facts are stated here in their printed
forms, as literature inputs (`def ... : Prop`, never axioms), on the field `h = h^ℂ - α₀ log |·|` of the paper
(eq:gff, line 387) with `γ ∈ (0, 2)` and `α₀ < Q = 2/γ + γ/2` (lines 377-380):

* `lqgMeasureFactCited`: Fact 2.1 (`fact:lqg-measure`, lines 407-422) together with the definition of `μ_h` as the
  a.s. limit eq:measure-lim (lines 401-406): the limit as `ε → 0` along all radii, and conformal covariance for
  general conformal maps `φ : Ũ → U`, as printed.
* `lqgMetricFactCited`: Fact 2.2 (`fact:lqg-metric`, lines 438-459) for the LQG metric `D_h` of lines 426-436, with
  the Weyl exponent `ξ = γ / d_γ` (eq:xi, line 446), `d_γ` the a.s. Hausdorff dimension of `(ℂ, D_h)` (line 428).

Both docstrings carry PENDING TRUTH CHECK: the Props are statements of cited results, recorded for a truth check.

## Vocabulary (deterministic, defined here)

* `TendstoLQGApproxOn γ hε V m`: `ε^{γ²/2} e^{γ hε ε z} dz → m` vaguely on the open set `V` as `ε → 0⁺`.
* `imageCircleTestEnergy φ ε z ψ`: the variance of `(h^ℂ, ν) - (h^ℂ, ψ)` for `ν` the push-forward by `φ` of the
  uniform probability measure on `∂B_ε(z)`.
* `IsImageCircleAverageProcess P hC hcirc hcurve`: `hcurve ω φ ε z` is the average of `h^ℂ` over the image curve
  `φ(∂B_ε(z))` (the circle average of `h^ℂ ∘ φ` over `∂B_ε(z)`), used for the circle averages of
  `h ∘ φ + Q log |φ'|` in Fact 2.1 IV.

## Projections to the Proposed Props bound by the counted theorems

| Proposed Prop (`Proposed/LQG.lean`) | from the cited fact |
|---|---|
| `LQGMeasureExistence` (:74) | `lqgMeasureExistence_of_cited` |
| `LQGMeasureNonatomic` (:86) | `lqgMeasureNonatomic_of_cited` |
| `LQGMeasureLocality` (:97) | `lqgMeasureLocality_of_cited` |
| `LQGMeasureWeylScaling` (:107) | `lqgMeasureWeylScaling_of_cited` |
| `LQGMeasureCoordChange` (:131) | `lqgMeasureCoordChange_of_cited` |
| `LQGMetricFieldAxioms` (:225-:245) at `ξ = γ / d_γ` | `lqgMetricFieldAxioms_of_cited` |
| `LQGMetricFieldAxioms` at any other `ξ` | not a direct consequence (below) |
| `LQGMetricExistenceUniqueness` (:196), existence half | `lqgMetricExistence_of_cited` |
| `LQGMetricExistenceUniqueness`, uniqueness half | not a direct consequence (below) |

The measure projections use, besides projection, only the a.s. uniqueness of the vague limit
(`IsLQGMeasure.ae_eq`, `Defs/LQG.lean:116`): the Proposed Props quantify over every `μ` with the dyadic limit
`IsLQGMeasureOfField`, which a.s. agrees with the `μ_h` of the cited fact.

Not a direct consequence:
* `LQGMetricFieldAxioms P γ ξ α₀ hC hcirc` for `ξ ≠ γ / d_γ`: the Proposed Prop quantifies over every exponent `ξ`
  admitting a metric with `IsLQGMetric γ ξ 𝔇`; Fact 2.2 concerns the exponent `ξ = γ / d_γ` only.
* the uniqueness half of `LQGMetricExistenceUniqueness`: uniqueness up to a deterministic constant (line 461, "these
  properties uniquely characterize `D_h`", Gwynne-Miller 2021) is stated after the Fact environment, not in it.

## Which parts are proved in the repository

Fact 2.1 (all with the dyadic definition `IsLQGMeasureOfField`, `Defs/LQG.lean:73`):
* existence of `μ_h`: `lqgMeasureExistence_derived` (`FirstPass/Phase2/LQGMeasureExistenceDerived.lean:25`); the
  limit along all radii `ε → 0` for the same `μ` (eq:measure-lim as printed):
  `ae_tendsto_integral_singular_lqgApprox_continuum_all` (`Proofs/GFF/LQGMeasureContinuumConvergence.lean:432`);
* I (non-atomic; Radon is part of `IsLQGLimit`): `lqgMeasureNonatomic_holds` (`FirstPass/Phase2/NonatomicHolds.lean:25`);
* II: `lqgMeasureLocality_derived` (`FirstPass/Phase2/CircleAverageLocalityLinkDerived.lean:181`);
* III along dyadic radii: `Section6.lqgMeasureWeylScaling` (`Proofs/Sec6/LQGWeylScaling.lean:124`);
* IV for complex affine maps, one event for all `(a, b)`, dyadic radii: `lqgMeasureCoordChange_holds`
  (`FirstPass/Phase2/CoordChangeHolds.lean:31`).
Supplied only by the cited statement: IV for non-affine conformal maps `φ : Ũ → U` (general conformal covariance,
Duplantier-Sheffield 2011 Prop. 2.1 for a fixed map, Sheffield-Wang 2016 for all maps), and III along all radii.

Fact 2.2:
* existence of a γ-LQG metric with some exponent `ξ > 0`, unique up to a deterministic constant:
  `lqgMetricExistenceUniqueness_derived` (`Proofs/GFF/LQGMetricUniquenessDerived.lean:40`);
* I-IV for `D_h`, for every `ξ` and every `𝔇` with `IsLQGMetric γ ξ 𝔇`: `lqgMetricFieldAxioms_forall_derived`
  (`FirstPass/Phase2/FieldAxiomsConsequencesDerived.lean:37`).
Supplied only by the cited statement: the identification `ξ = γ / d_γ` with `d_γ > 2` the a.s. Hausdorff dimension
of `(ℂ, D_h)` (eq:xi, line 446; line 428).
-/

universe u

namespace HarmonicBalls

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

/-! ### Vocabulary for the printed statements -/

/-- `ε^{γ²/2} e^{γ hε ε z} dz → m` vaguely on the open set `V` as `ε → 0` along all positive radii (eq:measure-lim,
line 403): for every continuous `f` with compact support contained in `V`,
`∫ f d(lqgApprox γ hε ε) → ∫ f dm` as `ε → 0⁺`. The paper's "weak limit" is read in this vague sense, the limits
being infinite Radon measures. -/
def TendstoLQGApproxOn (γ : ℝ) (hε : ℝ → ℂ → ℝ) (V : Set ℂ) (m : Measure ℂ) : Prop :=
  ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ V →
    Tendsto (fun ε : ℝ => ∫ z, f z ∂(lqgApprox γ hε ε)) (𝓝[>] 0) (𝓝 (∫ z, f z ∂m))

/-- The energy `∬ K d(ν - ψ dx) d(ν - ψ dx)` of the whole-plane GFF kernel `K = wholePlaneCov` (eq:cov-kernel,
line 363), where `ν` is the push-forward by `φ` of the uniform probability measure on `∂B_ε(z)`. It is the variance
of `(h^ℂ, ν) - (h^ℂ, ψ)`, i.e. of the average of `h^ℂ` over the image curve `φ(∂B_ε(z))` minus the pairing with `ψ`. -/
noncomputable def imageCircleTestEnergy (φ : ℂ → ℂ) (ε : ℝ) (z : ℂ) (ψ : ℂ → ℝ) : ℝ :=
  Real.circleAverage (fun x => Real.circleAverage (fun y => wholePlaneCov (φ x) (φ y)) z ε) z ε
    - 2 * Real.circleAverage (fun x => ∫ y, ψ y * wholePlaneCov (φ x) y) z ε
    + wholePlaneGFFCov (GFFObservable.pairing ψ) (GFFObservable.pairing ψ)

/-- `hcurve ω φ ε z` is the average of the whole-plane GFF `h^ℂ` (pairings `hC`, circle averages `hcirc`) over the
image curve `φ(∂B_ε(z))`, with respect to the push-forward by `φ` of the uniform measure on `∂B_ε(z)`; equivalently
the circle average `(h^ℂ ∘ φ)_ε(z)` of the composed field. Here `φ` is holomorphic and injective on an open set `V`
containing `closedBall z ε`, `ε > 0`.
* For a complex affine map `x ↦ a x + b` the image curve is the circle `∂B_{|a| ε}(a z + b)`, and the average is the
  circle average `h^ℂ_{|a| ε}(a z + b)` itself, for every sample.
* In general it is a random variable which is the `L²(P)` limit of pairings `(h^ℂ, ψ)` with test functions: for
  every test function `ψ`, `E[(hcurve φ ε z - (h^ℂ, ψ))²]` is the energy of `ν - ψ dx` (`imageCircleTestEnergy`).
  This determines `hcurve ω φ ε z` up to a `P`-null set.
* For each map, a.s. the process `(ε, z) ↦ hcurve ω φ ε z` is continuous where it is defined (as for circle
  averages, Duplantier-Sheffield 2011, Prop. 3.1); this determines it up to indistinguishability, map by map. -/
structure IsImageCircleAverageProcess {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (hcurve : Ω → (ℂ → ℂ) → ℝ → ℂ → ℝ) : Prop where
  /-- Affine maps: the image curve is a circle and the average is the circle average. -/
  affine_eq : ∀ (ω : Ω) (a b : ℂ), a ≠ 0 → ∀ (ε : ℝ) (z : ℂ), 0 < ε →
    hcurve ω (fun x => a * x + b) ε z = hcirc ω (‖a‖ * ε) (a * z + b)
  /-- Each image-curve average is a random variable (up to null sets). -/
  aemeasurable : ∀ V : Set ℂ, IsOpen V → ∀ φ : ℂ → ℂ, DifferentiableOn ℂ φ V → InjOn φ V →
    ∀ (ε : ℝ) (z : ℂ), 0 < ε → closedBall z ε ⊆ V → AEMeasurable (fun ω => hcurve ω φ ε z) P
  /-- The `L²(P)` distance to the pairings with test functions is that of the average of `h^ℂ` over the curve. -/
  integral_sq_sub : ∀ V : Set ℂ, IsOpen V → ∀ φ : ℂ → ℂ, DifferentiableOn ℂ φ V → InjOn φ V →
    ∀ (ε : ℝ) (z : ℂ), 0 < ε → closedBall z ε ⊆ V → ∀ ψ : ℂ → ℝ, IsTestFunction univ ψ →
      ∫ ω, (hcurve ω φ ε z - hC ω ψ) ^ 2 ∂P = imageCircleTestEnergy φ ε z ψ
  /-- For each map, a.s. continuity in the radius and the centre. -/
  ae_continuousOn : ∀ V : Set ℂ, IsOpen V → ∀ φ : ℂ → ℂ, DifferentiableOn ℂ φ V → InjOn φ V →
    ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hcurve ω φ p.1 p.2) {p | 0 < p.1 ∧ closedBall p.2 p.1 ⊆ V}

/-! ### Fact 2.1: the LQG measure -/

/-- **Fact 2.1 (LQG measure), printed form**, with the definition of `μ_h` (eq:measure-lim).

Source: paper/lqg_harmonic_ball-corrected.tex, eq:measure-lim (lines 401-405), line 406, Fact `fact:lqg-measure`
(lines 407-422), and line 424. Citation as printed: eq:measure-lim is followed by
`\cite{duplantier2011liouville, sheffield2016field}` (line 405), and line 424 reads "The first three properties in
Fact 2.1 are immediate from the definition (eq:measure-lim). The conformal covariance property was proven to hold
a.s. for a fixed conformal map in [DS11, Proposition 2.1] and extended to all conformal maps simultaneously in
[SW16]." Bibliography: [DS11] B. Duplantier and S. Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math.
185(2):333-393, 2011 (arXiv:0808.1560); [SW16] S. Sheffield and M. Wang, *Field-measure correspondence in Liouville
quantum gravity almost surely commutes with all conformal maps simultaneously*, arXiv:1605.06171, 2016.

Statement. For every whole-plane GFF `h^ℂ` (`IsWholePlaneGFF P hC hcirc`, normalized so that `h^ℂ_1(0) = 0`), every
`γ ∈ (0, 2)` and `α₀ < Q`, and `h = h^ℂ - α₀ log |·|` (eq:gff, line 387; circle averages `fieldCircleAverage`),
there is a random measure `μ = μ_h` such that:
* eq:measure-lim: a.s. `μ_h = lim_{ε → 0} ε^{γ²/2} e^{γ h_ε(z)} dz`, the limit along all `ε → 0` in the vague
  sense (`TendstoLQGApproxOn ... univ`);
* I (Radon measure): a.s. `μ_h` is a non-atomic Radon (locally finite) measure;
* II (locality): for every deterministic open `U`, `μ_h(U)` is a.s. equal to a `σ(h|_U)`-measurable random variable
  (`fieldSigmaAlgebra`);
* III (Weyl scaling): a.s., for every continuous `f : ℂ → ℝ`, `e^{γ f} · μ_h = μ_{h+f}`, where `μ_{h+f}` is the
  limit eq:measure-lim for the field `h + f` (line 406), with circle averages `h_ε + f_ε` (`addCircleAverage`);
* IV (conformal covariance): a.s., for all open `U, Ũ` and every conformal map `φ : Ũ → U` (holomorphic and
  injective on `Ũ`, `φ(Ũ) = U`; here `Ũ` is `V`), `μ_{h∘φ + Q log |φ'|}(A) = μ_h(φ(A))` for all Borel `A ⊆ Ũ`
  (eq:measure-coord), where `μ_{h∘φ + Q log |φ'|}` is the limit eq:measure-lim on `Ũ` for the field
  `h ∘ φ + Q log |φ'|`, whose circle average over `∂B_ε(z)` is
  `(h^ℂ ∘ φ)_ε(z) - α₀ (log |φ|)_ε(z) + Q (log |φ'|)_ε(z)`.

Reading of IV. The circle averages `(h^ℂ ∘ φ)_ε(z)` are averages of `h^ℂ` over the image curves `φ(∂B_ε(z))`; they
are given by a process `hcurve` with `IsImageCircleAverageProcess`. For complex affine `φ` they are the circle
averages `hcirc` themselves, for every sample. For other maps the image curve is not a circle, and its average is
determined by the field up to a `P`-null set depending on the map; the simultaneous statement over these maps is made
for the chosen process `hcurve`.

PENDING TRUTH CHECK. -/
def lqgMeasureFactCited : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∃ μ : Ω → Measure ℂ,
      -- eq:measure-lim: `μ_h` is the a.s. limit of `ε^{γ²/2} e^{γ h_ε(z)} dz` as `ε → 0`.
      (∀ᵐ ω ∂P, TendstoLQGApproxOn γ (fieldCircleAverage α₀ (hcirc ω)) univ (μ ω)) ∧
      -- I. Radon measure: a.s. `μ_h` is a non-atomic Radon measure.
      (∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) ∧ ∀ x : ℂ, μ ω {x} = 0) ∧
      -- II. Locality.
      (∀ U : Set ℂ, IsOpen U → ∃ Y : Ω → ℝ≥0∞,
        Measurable[fieldSigmaAlgebra α₀ hC U] Y ∧ ∀ᵐ ω ∂P, μ ω U = Y ω) ∧
      -- III. Weyl scaling.
      (∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f →
        TendstoLQGApproxOn γ (addCircleAverage (fieldCircleAverage α₀ (hcirc ω)) f) univ
          ((μ ω).withDensity fun x => ENNReal.ofReal (Real.exp (γ * f x)))) ∧
      -- IV. Conformal covariance (`V` is the domain `Ũ` of the conformal map `φ : Ũ → U`).
      ∃ hcurve : Ω → (ℂ → ℂ) → ℝ → ℂ → ℝ, IsImageCircleAverageProcess P hC hcirc hcurve ∧
        ∀ᵐ ω ∂P, ∀ U V : Set ℂ, IsOpen U → IsOpen V → ∀ φ : ℂ → ℂ, DifferentiableOn ℂ φ V →
          InjOn φ V → φ '' V = U → ∃ m : Measure ℂ,
            TendstoLQGApproxOn γ (fun ε z => hcurve ω φ ε z
                - α₀ * Real.circleAverage (fun x => Real.log ‖φ x‖) z ε
                + lqgQ γ * Real.circleAverage (fun x => Real.log ‖deriv φ x‖) z ε) V m ∧
              ∀ A : Set ℂ, MeasurableSet A → A ⊆ V → m A = μ ω (φ '' A)

/-! ### Fact 2.2: the LQG metric -/

/-- **Fact 2.2 (LQG metric), printed form**, for the LQG metric `D_h` of lines 426-436.

Source: paper/lqg_harmonic_ball-corrected.tex, lines 426-436 (the LQG metric `D_h` and the metric `D_{h+f}`), line 428
(`d_γ`), Fact `fact:lqg-metric` (lines 438-459), and line 461. Citation as printed: line 426, "It was shown in
\cite{ding2020tightness, gwynne2021existence} that one can define also the LQG metric `D_h`"; line 428, "the
Hausdorff dimension of the metric space `(ℂ, D_h)` is a.s. given by a deterministic number `d_γ > 2`
\cite[Corollary 1.7]{gp-kpz}"; line 461, "The properties listed in Fact 2.2 were verified for the LQG metric in
\cite{ding2020tightness, dubedat2020weak, gwynne2021existence}." Bibliography: [DDDF20] J. Ding, J. Dubédat,
A. Dunlap and H. Falconet, *Tightness of Liouville first passage percolation for γ ∈ (0,2)*, Publ. Math. IHÉS
132:353-403, 2020; [DFGPS20] J. Dubédat, H. Falconet, E. Gwynne, J. Pfeffer and X. Sun, *Weak LQG metrics and
Liouville first passage percolation*, Probab. Theory Related Fields 178(1-2):369-436, 2020; [GM21] E. Gwynne and
J. Miller, *Existence and uniqueness of the Liouville quantum gravity metric for γ ∈ (0,2)*, Invent. Math.
223(1):213-333, 2021; [GP19] E. Gwynne and J. Pfeffer, *KPZ formulas for the Liouville quantum gravity metric*,
Trans. Amer. Math. Soc. (to appear), 2019.

Statement. For every `γ ∈ (0, 2)` there is a deterministic `d_γ > 2` such that, with `ξ = γ / d_γ` (eq:xi), a γ-LQG
metric `𝔇 : h ↦ D_h` with Weyl exponent `ξ` exists (`IsLQGMetric`, Gwynne-Miller 2021, Section 1.2), and for every
such `𝔇`, every whole-plane GFF `h^ℂ` and every `α₀ < Q`, the metric `D_h` of `h = h^ℂ - α₀ log |·|`, i.e. the Weyl
scaling `e^{-ξ α₀ log |·|} · D_{h^ℂ}` (`Defs/LQGMetric.lean`, `IsLQGMetricOfField`), satisfies:
* `d_γ`: a.s. the Hausdorff dimension of the metric space `(ℂ, D_h)` is `d_γ` (line 428);
* I: a.s. `D_h` is finite, induces the Euclidean topology on `ℂ` and is a length metric;
* II: for every deterministic open `U`, the internal metric `D_h(·, ·; U)` is a.s. equal to a random function whose
  values are `σ(h|_U)`-measurable;
* III: a.s., for every continuous `f : ℂ → ℝ` and all `u, v`,
  `D_{h+f}(u, v) = inf_{P : u → v} ∫_0^{len(P; D_h)} e^{ξ f(P(t))} dt`, with `D_{h+f} = e^{ξ (f - α₀ log |·|)} · D_{h^ℂ}`;
* IV: for each `r > 0` and `z ∈ ℂ`, a.s. `D_h(r u + z, r v + z) = D_{h(r · + z) + Q log r}(u, v)` for all `u, v`.
The bodies of I-IV are those of `LQGMetricFieldAxioms` (`Proposed/LQG.lean:225-245`) at `ξ = γ / d_γ`.

PENDING TRUTH CHECK. -/
def lqgMetricFactCited : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ dγ : ℝ, 2 < dγ ∧
    (∃ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ (γ / dγ) 𝔇) ∧
    ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ (γ / dγ) 𝔇 →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    let Dh : Ω → ℂ → ℂ → ℝ≥0∞ := fun ω => weylScaling (𝔇 (hC ω)) (γ / dγ) fun x => -α₀ * Real.log ‖x‖
    -- `d_γ` is a.s. the Hausdorff dimension of `(ℂ, D_h)`.
    (∀ᵐ ω ∂P, ∃ M : EMetricSpace ℂ,
      (∀ u v : ℂ, @edist ℂ M.toPseudoEMetricSpace.toEDist u v = Dh ω u v) ∧
        @dimH ℂ M univ = ENNReal.ofReal dγ) ∧
    -- I. Finiteness, Euclidean topology and length metric.
    (∀ᵐ ω ∂P, (∀ u v, Dh ω u v < ∞) ∧ IsEuclideanLengthMetric fun u v => (Dh ω u v).toReal) ∧
    -- II. Locality.
    (∀ U : Set ℂ, IsOpen U → ∃ G : Ω → ℂ → ℂ → ℝ≥0∞,
      (∀ z w, Measurable[fieldSigmaAlgebra α₀ hC U] fun ω => G ω z w) ∧
        ∀ᵐ ω ∂P, ∀ z ∈ U, ∀ w ∈ U, internalMetric (fun u v => (Dh ω u v).toReal) U z w = G ω z w) ∧
    -- III. Weyl scaling.
    (∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → ∀ u v,
      weylScaling (𝔇 (hC ω)) (γ / dγ) (fun x => f x - α₀ * Real.log ‖x‖) u v =
        weylScaling (fun u v => (Dh ω u v).toReal) (γ / dγ) f u v) ∧
    -- IV. Coordinate change for scaling and translation.
    (∀ r : ℝ, 0 < r → ∀ z : ℂ, ∀ᵐ ω ∂P, ∀ u v : ℂ,
      Dh ω (r * u + z) (r * v + z) =
        weylScaling (𝔇 (addFunPairing (affinePullbackPairing (hC ω) r z) fun _ => lqgQ γ * Real.log r))
          (γ / dγ) (fun x => -α₀ * Real.log ‖(r : ℂ) * x + z‖) u v)

/-! ### Projections -/

namespace Section2Cited

/-- The dyadic scales `2^{-k}` tend to `0` from the right. -/
theorem tendsto_dyadicScale_nhdsGT : Tendsto dyadicScale atTop (𝓝[>] (0 : ℝ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun k => dyadicScale_pos k⟩
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- A locally finite vague limit along all radii is in particular the dyadic limit `IsLQGLimit`. -/
theorem isLQGLimit_of_tendstoLQGApproxOn {γ : ℝ} {hε : ℝ → ℂ → ℝ} {m : Measure ℂ}
    (hm : IsLocallyFiniteMeasure m) (h : TendstoLQGApproxOn γ hε univ m) : IsLQGLimit γ hε m where
  isLocallyFiniteMeasure := hm
  tendsto_integral f hf hfs := (h f hf hfs (subset_univ _)).comp tendsto_dyadicScale_nhdsGT

/-- The measure `μ_h` of the cited fact is an `IsLQGMeasureOfField`. -/
theorem isLQGMeasureOfField_of_tendsto {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hlim : ∀ᵐ ω ∂P, TendstoLQGApproxOn γ (fieldCircleAverage α₀ (hcirc ω)) univ (μ ω))
    (hfin : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω)) : IsLQGMeasureOfField P γ α₀ hcirc μ := by
  show ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α₀ (hcirc ω)) (μ ω)
  filter_upwards [hlim, hfin] with ω h1 h2
  exact isLQGLimit_of_tendstoLQGApproxOn h2 h1

end Section2Cited

open Section2Cited

/-- Fact 2.1 (cited) gives the existence Prop `LQGMeasureExistence` (`Proposed/LQG.lean:74`). -/
theorem lqgMeasureExistence_of_cited (hF : lqgMeasureFactCited.{u}) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) :
    LQGMeasureExistence P γ α₀ hC hcirc := by
  intro hh hγ0 hγ2 hα
  obtain ⟨μ, hlim, hI, -⟩ := hF Ω P hC hcirc hh γ α₀ hγ0 hγ2 hα
  exact ⟨μ, isLQGMeasureOfField_of_tendsto hlim (hI.mono fun _ h => h.1)⟩

/-- Fact 2.1 I (cited) gives `LQGMeasureNonatomic` (`Proposed/LQG.lean:86`). -/
theorem lqgMeasureNonatomic_of_cited (hF : lqgMeasureFactCited.{u}) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) :
    LQGMeasureNonatomic P γ α₀ hC hcirc := by
  intro hh hγ0 hγ2 hα μ' hμ'
  obtain ⟨μ, hlim, hI, -⟩ := hF Ω P hC hcirc hh γ α₀ hγ0 hγ2 hα
  have hμ := isLQGMeasureOfField_of_tendsto hlim (hI.mono fun _ h => h.1)
  filter_upwards [IsLQGMeasure.ae_eq hμ hμ', hI] with ω heq hω x
  rw [← heq]
  exact hω.2 x

/-- Fact 2.1 II (cited) gives `LQGMeasureLocality` (`Proposed/LQG.lean:97`). -/
theorem lqgMeasureLocality_of_cited (hF : lqgMeasureFactCited.{u}) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) :
    LQGMeasureLocality P γ α₀ hC hcirc := by
  intro hh hγ0 hγ2 hα μ' hμ' U hU
  obtain ⟨μ, hlim, hI, hII, -⟩ := hF Ω P hC hcirc hh γ α₀ hγ0 hγ2 hα
  have hμ := isLQGMeasureOfField_of_tendsto hlim (hI.mono fun _ h => h.1)
  obtain ⟨Y, hY, hYae⟩ := hII U hU
  refine ⟨Y, hY, ?_⟩
  filter_upwards [IsLQGMeasure.ae_eq hμ hμ', hYae] with ω heq hω
  rw [← heq]
  exact hω

/-- Fact 2.1 III (cited) gives `LQGMeasureWeylScaling` (`Proposed/LQG.lean:107`). -/
theorem lqgMeasureWeylScaling_of_cited (hF : lqgMeasureFactCited.{u}) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) :
    LQGMeasureWeylScaling P γ α₀ hC hcirc := by
  intro hh hγ0 hγ2 hα μ' hμ'
  obtain ⟨μ, hlim, hI, -, hIII, -⟩ := hF Ω P hC hcirc hh γ α₀ hγ0 hγ2 hα
  have hμ := isLQGMeasureOfField_of_tendsto hlim (hI.mono fun _ h => h.1)
  filter_upwards [IsLQGMeasure.ae_eq hμ hμ', hI, hIII] with ω heq hω hW f hf
  rw [← heq]
  have hfin : IsLocallyFiniteMeasure (μ ω) := hω.1
  exact isLQGLimit_of_tendstoLQGApproxOn
    (IsLocallyFiniteMeasure.withDensity_ofReal (Real.continuous_exp.comp (continuous_const.mul hf)))
    (hW f hf)

/-- Fact 2.1 IV (cited), specialized to the complex affine maps `x ↦ a x + b` on `Ũ = U = ℂ`, gives
`LQGMeasureCoordChange` (`Proposed/LQG.lean:131`). -/
theorem lqgMeasureCoordChange_of_cited (hF : lqgMeasureFactCited.{u}) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) :
    LQGMeasureCoordChange P γ α₀ hC hcirc := by
  intro hh hγ0 hγ2 hα μ' hμ'
  obtain ⟨μ, hlim, hI, -, -, hcurve, hproc, hIV⟩ := hF Ω P hC hcirc hh γ α₀ hγ0 hγ2 hα
  have hμ := isLQGMeasureOfField_of_tendsto hlim (hI.mono fun _ h => h.1)
  filter_upwards [IsLQGMeasure.ae_eq hμ hμ', hI, hIV] with ω heq hω hcov a ha b
  rw [← heq]
  have hfin : IsLocallyFiniteMeasure (μ ω) := hω.1
  have hsurj : (fun x => a * x + b) '' univ = univ := by
    refine Set.image_univ_of_surjective fun y => ⟨(y - b) / a, ?_⟩
    show a * ((y - b) / a) + b = y
    rw [mul_div_assoc', mul_div_cancel_left₀ _ ha, sub_add_cancel]
  obtain ⟨m, hm, hmA⟩ := hcov univ univ isOpen_univ isOpen_univ (fun x => a * x + b) (by fun_prop)
    (fun x _ y _ hxy => by simpa [ha] using hxy) hsurj
  have himg : ∀ A : Set ℂ, (fun x => a * x + b) '' A = (fun x => (x - b) / a) ⁻¹' A := by
    intro A
    ext x
    simp only [mem_image, mem_preimage]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rwa [add_sub_cancel_right, mul_div_cancel_left₀ _ ha]
    · intro hx
      exact ⟨(x - b) / a, hx, by rw [mul_div_assoc', mul_div_cancel_left₀ _ ha, sub_add_cancel]⟩
  have hmfin : IsLocallyFiniteMeasure m := by
    refine ⟨fun x => ⟨ball x 1, ball_mem_nhds x one_pos, ?_⟩⟩
    rw [hmA _ measurableSet_ball (subset_univ _)]
    have hK : IsCompact ((fun y => a * y + b) '' closedBall x 1) :=
      (isCompact_closedBall x 1).image (by fun_prop)
    exact (measure_mono (image_mono ball_subset_closedBall)).trans_lt hK.measure_lt_top
  have hmap : m = (μ ω).map (fun x => (x - b) / a) := by
    ext A hA
    rw [hmA A hA (subset_univ A),
      Measure.map_apply (by fun_prop : Continuous fun x : ℂ => (x - b) / a).measurable hA, himg]
  have hd : ∀ x : ℂ, deriv (fun x => a * x + b) x = a := fun x => by
    have h1 := (((hasDerivAt_id' x).const_mul a).add_const b).deriv
    rw [mul_one] at h1
    exact h1
  have hfun : ∀ ε : ℝ, 0 < ε → ∀ z : ℂ,
      hcurve ω (fun x => a * x + b) ε z - α₀ * Real.circleAverage (fun x => Real.log ‖a * x + b‖) z ε
          + lqgQ γ * Real.circleAverage (fun x => Real.log ‖deriv (fun x => a * x + b) x‖) z ε
        = fieldCircleAverage α₀ (hcirc ω) (‖a‖ * ε) (a * z + b) + lqgQ γ * Real.log ‖a‖ := by
    intro ε hε z
    have hlog : Real.circleAverage (fun x => Real.log ‖a * x + b‖) z ε =
        Real.circleAverage (fun x => Real.log ‖x‖) (a * z + b) (‖a‖ * ε) :=
      (circleAverage_affine_comp b (fun x => Real.log ‖x‖) z ε).symm
    simp only [hd, Real.circleAverage_const]
    rw [hproc.affine_eq ω a b ha ε z hε, hlog]
    rfl
  subst hmap
  refine ⟨hmfin, fun f hf hfs => ?_⟩
  refine Tendsto.congr (fun k => ?_) ((hm f hf hfs (subset_univ _)).comp tendsto_dyadicScale_nhdsGT)
  simp only [Function.comp_apply, lqgApprox, hfun (dyadicScale k) (dyadicScale_pos k)]

/-- Fact 2.2 (cited) gives `LQGMetricFieldAxioms` (`Proposed/LQG.lean:225-245`) at the Weyl exponent `ξ = γ / d_γ`,
for every probability space, insertion `α₀` and field. -/
theorem lqgMetricFieldAxioms_of_cited (hF : lqgMetricFactCited.{u}) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) :
    ∃ dγ : ℝ, 2 < dγ ∧ ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms P γ (γ / dγ) α₀ hC hcirc := by
  obtain ⟨dγ, hd, -, hall⟩ := hF γ hγ0 hγ2
  refine ⟨dγ, hd, ?_⟩
  intro Ω _ P α₀ hC hcirc hh _ _ hα 𝔇 h𝔇
  exact (hall 𝔇 h𝔇 Ω P hC hcirc hh α₀ hα).2

/-- Fact 2.2 (cited) gives the existence half of `LQGMetricExistenceUniqueness` (`Proposed/LQG.lean:196`): a γ-LQG
metric with a positive Weyl exponent exists. -/
theorem lqgMetricExistence_of_cited (hF : lqgMetricFactCited.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ ξ : ℝ, 0 < ξ ∧ ∃ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 := by
  intro γ hγ0 hγ2
  obtain ⟨dγ, hd, hex, -⟩ := hF γ hγ0 hγ2
  exact ⟨γ / dγ, div_pos hγ0 (by linarith), hex⟩

end HarmonicBalls
