# Audit: normalized across-annulus scale law (z6, 2026-11-08)

Module: `HarmonicBalls/Proofs/GFF/MetricAnnulusScaleLaw.lean` (new). Credit: Leonardo Bonanno (module header; the
whole-plane GFF and its affine normalization, as in `Proofs/GFF/MetricXiSign.lean`).

## 1. Status

- Proved: for a zero-charge whole-plane GFF and `IsLQGMetric γ ξ 𝔇`, the normalized across-annulus functional
  `X_r` has the same law for every `r > 0`; the family is tight and reciprocally tight; the across distance is a.s.
  in `(0, ∞)`.
- Not proved: the around-annulus length (`pfefferAround`) and any internal diameter. Section 5 names the missing
  implications.
- Checks: `lc` CHECK OK; `lb` BUILD OK (`HarmonicBalls.Proofs.GFF.MetricAnnulusScaleLaw`). `#print axioms` of
  `normalizedAcross_identDistrib`, `normalizedAcross_tight`, `annularAcross_ae_pos_lt_top`: `[propext,
  Classical.choice, Quot.sound]`. Scan of the file: no `sorry`, `admit`, `native_decide`, `axiom`, `maxHeartbeats`.

## 2. Setting and reading

- `h^ℂ`: `IsWholePlaneGFF P hC hcirc` (`Defs/GFF.lean:93`). Zero charge means no logarithmic insertion, `f = 0`: the
  metric is `𝔇 (hC ω)` (`Defs/LQGMetric.lean`, docstring of `IsLQGMetric`: for `α₀ = 0`, `D_{h^ℂ} = 𝔇 (hC ω)`).
  "project GFF" in the task is read as this zero-charge whole-plane GFF; no projection is taken.
- `𝔇`: `IsLQGMetric γ ξ 𝔇` (`Defs/LQGMetric.lean:179`), `Q = lqgQ γ`.
- Across-annulus distance: `A_D(z₀; a, b) = inf {D x y : |x - z₀| = a, |y - z₀| = b}`, Pfeffer (arXiv:2104.04020),
  Axiom V of Definition 1.6 (the across distance is defined on p. 5). The module restates the formula as
  `annularAcross`; the staged `pfefferAcross` (`Proposed/PfefferMetricScaling.lean:51`) is not imported.
- Normalization: `r^{-ξQ} e^{-ξ h_r(0)}` with `h_r(0) = hcirc ω r 0` (`zeroChargeNormalization`). This is Axiom V's
  `c_r^{-1} e^{-ξ h_r(0)}` with `c_r = r^{ξQ}` and `f = 0`, where `pfefferCircleAverage 0 = 0`.

## 3. Argument (each step is a declaration of the module)

(a) Coordinate change and Weyl scaling (`IsLQGMetric` axioms IV and III, applied to the zero-charge field and to the
affinely normalized field). For `r > 0`, almost surely and for all `x, y`:
`ofReal D_{hC}(r x, r y) = ofReal(e^{ξ (h_r(0) + Q log r)}) · ofReal D_g(x, y)`, where
`g = affinePairing hC hcirc r 0 = h^ℂ(r ·) - h^ℂ_r(0)`. Declarations: `zeroCharge_satisfies`, `zeroCharge_scale_ae`.
Ingredients: the identity `affinePullbackPairing (·) r 0 + Q log r = affinePairing + (h_r(0) + Q log r)`
(`affinePullback_eq_affinePairing`); Weyl scaling at `f = const` by `weylScaling_add_const`
(`Steps/Sec11/WeylScalingOrder.lean:43`) and at `f = 0`. The Weyl axiom at `f = 0` gives `weylScaling 0 = ofReal D`
directly, so no arc-length reparametrization is used.

(b) Normalization cancels. `r^{-ξQ} e^{-ξ h_r(0)} · e^{ξ (h_r(0) + Q log r)} = 1` (`zeroChargeNormalization_mul`,
`exp_shift_eq`). Dilation: `sphere (r z₀) (r a) = r · sphere z₀ a` (`sphere_smul_eq_image`), so
`A_D(r z₀; r a, r b) = c · A_E(z₀; a, b)` when `D(r x, r y) = c · E(x, y)` (`annularAcross_smul`). Hence, almost surely,
`X_r = A_{D_g}(z₀; a, b)` (`normalizedAcross_ae_eq_affine`).

(c) Common law. For each `r > 0`, `g` is a whole-plane GFF (`wholePlaneGFFAffineInvariance_proved`,
`Proofs/Sec9/AffineInvarianceAssembly.lean:21`; `IsWholePlaneGFF.complex_affine` is a theorem, not a field of
the structure). The pairing observables of `h^ℂ` and `g` have the same law
(`IsWholePlaneGFF.identDistrib_observables_across_spaces`, `Proofs/Sec8/LQGUniversalApproximationLaw.lean:11`). The
across functional is an infimum over countable dense subsets `A ⊂ ∂B_a(z₀)` and `B ⊂ ∂B_b(z₀)`
(`annularAcross_eq_countableAcross`, using joint continuity of a Euclidean length metric,
`isEuclideanLengthMetric_continuous`). That infimum is distribution-measurable (`countableAcross_measurable`) and
factors through the observables (`exists_common_observable_of_distribution_measurable`,
`Proofs/Sec11/LQGBaseMetricObservable.lean:14`). Result: `annularAcross_identDistrib_affine`, and
`normalizedAcross_identDistrib`: for every `r > 0`, `X_r` has the law of `A_{𝔇(h^ℂ)}(z₀; a, b)`, which does not depend on `r`.

(d) Strict positivity and finiteness. A.s., `𝔇` is a metric inducing the Euclidean topology (`IsEuclideanLengthMetric`).
On the compact product of two disjoint circles the infimum of the continuous `D` is attained at distinct points, so
`0 < A < ∞` (`annularAcross_pos_lt_top`, `annularAcross_ae_pos_lt_top`).

(e) Tightness and reciprocal tightness. A.s. `Y = A_{D(h^ℂ)} ∈ (0, ∞)`. The bands `{(n+1)⁻¹ ≤ Y ≤ n+1}` increase to a
set of full measure, so one band has probability at least `1 - ε` (`annularBand_exists`). Each `X_r` has the same law
as `Y` (step (c)), so the same bound holds for every `r`: `normalizedAcross_tight`. The event `M⁻¹ ≤ X ≤ M` is
invariant under `X ↦ X⁻¹`, so the statement covers reciprocal tightness.

## 4. Scope boundaries

- Only zero charge (`f = 0`). For a nonzero random continuous `f`, the pulled-back field is
  `h^ℂ(r ·) + f(r ·)` minus its average, and `f(r ·)` is not affinely invariant in law, so zero-charge invariance does
  not give a common scale law. No such claim is made or assumed; `zeroCharge_satisfies` is stated only for `f = 0`.
- Quantifiers: "almost surely in `ω`, then for all points" (as in the `IsLQGMetric` axioms III and IV). No
  integrability is assumed: `integral_const_mul` holds without hypotheses in `affinePullback_eq_affinePairing`.
- Hypotheses: `IsWholePlaneGFF`, `IsLQGMetric` (as the task asks), `0 < r`, `0 < a < b`. No literature premise is added.
- `WholePlaneGFFAffineInvariance` (`Proposed/LQG.lean:51`) enters only through the proved theorem
  `wholePlaneGFFAffineInvariance_proved`, under the operator's 05:00 source check of that statement.
- Not used: `PfefferBackgroundScaling`, `IsPfefferWeakLQGMetric`, `PfefferAxiomVScale`, the Sec11 closure chain.
- Import closure of the module: 543 modules; none under `Closure`. `Proposed.LQG` and `Proposed.Birkhoff` are inherited
  through the Sec9 affine-invariance chain; the staged Pfeffer module is not in the closure.

## 5. Remaining functionals (named, not claimed)

R1. Around-annulus length, `pfefferAround` (Pfeffer Axiom V, the second functional): the infimum over closed Euclidean
loops `P` separating `∂B_a(z₀)` from `∂B_b(z₀)` of `pathLength D P`. Dilation covariance is routine (`curveLength` of a
dilated loop is `c` times the length; separation is dilation invariant) but is not written here. The blocker is the
measurability in `ω` of `A^{around}(𝔇 (h^ℂ ω))`. Missing implication: a countable family `𝓛` of loops (for example
polygonal loops with rational vertices) such that, for almost every `ω`, the infimum of the `D`-lengths over `𝓛` equals
the infimum over all separating loops. The repository has no such reduction (`Steps/Sec11/MetricArcLength.lean` gives
arc-length reparametrization and `weylScaling_zero` only), and the paper's text does not state one.

R2. Internal diameter. The paper's text uses "LQG diameter" in Proposition `mass-diam-gen`
(`paper/lqg_harmonic_ball-corrected.tex:2930`) and defines no annular internal diameter. Two readings are possible:
`diam_D(A) = sup_{x,y ∈ A} D x y`, or the internal version `sup_{x,y ∈ A} D(x, y; A)`. Locality
(`SatisfiesLQGMetricAxioms.locality`, `Defs/LQGMetric.lean`) gives measurable versions of the internal distance between
fixed points of an open set. A supremum over the annulus needs a.s. continuity of `(x, y) ↦ D(x, y; A)` on `A × A`, or a
countable dense reduction; axioms I–IV do not provide either. Missing: that continuity (or reduction), and a decision on
which reading the source uses.

No assumed tightness is used. The across law does not depend on R1 or R2.
