# Audit: CircleTestIntegralContinuity (task `sec11-circle-test-integral-continuity-on-CJ`)

Owner: z3. File: `HarmonicBalls/Proofs/Sec11/ClosureScales/CircleTestIntegralContinuity.lean` (new, 163 lines, namespace
`HarmonicBalls`, not imported by `HarmonicBalls.lean`).
Status: `lc` CHECK OK and `lb` BUILD OK (both with `-DwarningAsError=true`). Printed axioms of the nine public declarations
are exactly `[propext, Classical.choice, Quot.sound]`. Committed with this audit (see `git log`).

## 1. Written source

- `notes/sec11-proof/sec11-proof-r10.tex`, lines 1046-1062. The displayed limit (line 1052) is
  `lim_n ∫ c(2^{-n}, z) φ(z) d²z` for a countable family of tests `φ`; line 1054 reads "Each integral is a continuous
  function of `c` and the limit, where it exists, is Borel." This file formalizes the continuity of each integral and the
  Borel measurability of the literal `limsup` along `dyadicScale`. Nothing else of the written argument is formalized.

## 2. Statements, binders and carrier

| Declaration | Binders | Conclusion | Line |
|---|---|---|---|
| `exists_isCompact_circleDomain` | `0 < a`, compact `K ⊆ ℂ` | compact `S ⊆ CircleDomain` containing every `(r, z)`, `a ≤ r ≤ b`, `z ∈ K` | 42 |
| `continuous_circleTestIntegrand_q` | `z : ℂ` | `(q) ↦ q.2 ⟨(q.1.val, z), _⟩` continuous | 56 |
| `continuous_circleTestIntegrand_z` | `φ` continuous, `r`, `F` | `z ↦ F ⟨(r, z), _⟩ * φ z` continuous | 65 |
| `integrable_circleTestIntegrand` | `IsTestFunction Set.univ φ`, `hr : 0 < r`, `F` | `Integrable (fun z => F ⟨(r, z), hr⟩ * φ z)` | 73 |
| `continuous_circleTestIntegral` | `IsTestFunction Set.univ φ` | `Continuous fun q : {r // 0 < r} × C(CircleDomain, ℝ) => ∫ z, q.2 ⟨(q.1.val, z), q.1.property⟩ * φ z` | 81 |
| `continuous_circleTestIntegral_fixed` | `IsTestFunction`, `hr : 0 < r` | `Continuous fun F => ∫ z, F ⟨(r, z), hr⟩ * φ z` | 136 |
| `measurable_circleTestIntegral_fixed` | same | `Measurable` of the same map (Borel σ-algebra of `C(CircleDomain, ℝ)`) | 143 |
| `measurable_circleTestIntegral` | `IsTestFunction` | joint `Measurable` of the map of `continuous_circleTestIntegral` | 148 |
| `measurable_limsup_circleTestIntegral` | `IsTestFunction` | `Measurable fun F => Filter.limsup (fun n : ℕ => ∫ z, F ⟨(dyadicScale n, z), dyadicScale_pos n⟩ * φ z) atTop` | 156 |

- Carrier. `CircleDomain = {p : ℝ × ℂ // 0 < p.1}` (`abbrev`, `CountableCircleDecoder.lean:31`) with the subspace
  topology; `LocallyCompactSpace CircleDomain` (`CountableCircleDecoder.lean:38`). `C(CircleDomain, ℝ)` carries Mathlib's
  default compact-open topology (`ContinuousMap.compactOpen`) and its Borel σ-algebra (`ContinuousMap.measurableSpace`,
  Mathlib `BorelSpace/ContinuousMap.lean:51`); `CountableCircleDecoder.lean:44` gives `PolishSpace`. The radius space is
  `{r : ℝ // 0 < r}` with the subtype topology. Integrals are against Lebesgue measure `volume` on `ℂ`.
- Test functions. `IsTestFunction U φ := ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U` (`Defs/Laplacian.lean:47`).
  Only `ContDiff` (hence continuity) and compact support are used; `tsupport φ ⊆ univ` is not used.
- Dyadic scales: `dyadicScale k = (2⁻¹)^k` (`Defs/LQG.lean:41`), positivity `dyadicScale_pos` (`Defs/LQG.lean:84`).

## 3. Route

- Mathlib's `MeasureTheory.continuous_parametric_integral_of_continuous` (`Mathlib/MeasureTheory/Integral/Bochner/Set.lean:1129`)
  is the compactly supported continuous-parametric integration theorem. It requires `[LocallyCompactSpace X]` on the
  parameter space. `C(CircleDomain, ℝ)` is an infinite-dimensional locally convex space, so it is not locally compact
  (Riesz), and the theorem does not apply to the parameter space `{r // 0 < r} × C(CircleDomain, ℝ)`. It is therefore not
  used.
- Used instead: `MeasureTheory.continuousAt_of_dominated` (`Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:458`), with
  the domination proved from compactness. At `q₀ = (r₀, F₀)`: `S` is the compact box of `exists_isCompact_circleDomain` with
  `a = r₀/2`, `b = 2 r₀`, `K = tsupport φ`; `C` bounds `‖F₀‖` on `S` (`IsCompact.exists_bound_of_continuousOn`); `M = C + 1`;
  the open set `{q | q.1.val ∈ Ioo (r₀/2) (2 r₀) ∧ MapsTo q.2 S (Ioo (-M) M)}` is open by
  `ContinuousMap.isOpen_setOfPred_mapsTo` (`Mathlib/Topology/CompactOpen.lean:59`) and `IsOpen.inter`. On it the integrand is
  bounded by `M * ‖φ z‖`, which is integrable (continuous, compact support). Pointwise continuity in `q` at each `z` is
  `continuous_eval` (the same idiom as `continuous_circleAverage_joint` in `CircleShiftContinuity.lean`).
- Fixed radius: composition with `F ↦ (⟨r, hr⟩, F)`. Limsup: Mathlib's `Measurable.limsup`
  (`Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean:1074`) for the countable index `ℕ`.
- No hypothesis, no probability input, no bound at infinity, no domination premise is assumed. No `sorry`, `axiom`, `native_decide`.

## 4. Providers searched and reused

- Reused: `CircleDomain` and its `LocallyCompactSpace`/`PolishSpace` instances (`CountableCircleDecoder.lean`);
  `IsTestFunction` (`Defs/Laplacian.lean`); `dyadicScale`, `dyadicScale_pos` (`Defs/LQG.lean`); the Mathlib lemmas named above.
- `circleBox m` (`CountableCircleDecoder.lean:34-35`) is the compact box `[1/m, m] × closedBall 0 m` but has no compactness
  lemma in the repository (it is used only as a hypothesis at `CountableCircleDecoder.lean:74`). The compact box is therefore
  built in `exists_isCompact_circleDomain`, not taken from `circleBox`.
- Not used: `CutoffFourierSummability`, `CircleTestIntegralL2Limit`, `CanonicalProfile`, any probability or Lattice-Probability
  module, any `External` or `Proposed` input, `CircleShiftContinuity` (pattern reference only).

## 5. Import closure and credit

- Direct imports: `Defs/Laplacian`, `Defs/LQG`, `Proofs/Sec11/ClosureScales/CountableCircleDecoder`.
- Transitive closure (computed from the `import` lines): six `HarmonicBalls` modules: `Defs/Notation`, `Defs/Laplacian`,
  `Defs/GFF`, `Defs/LQG`, `CountableCircleDecoder`, and the new file. The only non-HarmonicBalls imports are `Mathlib`.
- No module of the closure mentions a Lattice-Probability (Bonanno), MarkovProcess or EllipticRegularity name, so no credit
  line is required. The five providers exist in tree `01847af`.

## 6. Checks

- `lc` (`-DwarningAsError=true`): CHECK OK, log `logs/lc/011147-3798871.log`.
- `lb HarmonicBalls.Proofs.Sec11.ClosureScales.CircleTestIntegralContinuity`: BUILD OK, log `logs/lb/011156-3815282.log`.
- Printed axioms (`lc` on a scratch file importing the module; log `logs/lc/011244-3896763.log`): all nine public declarations
  depend on `[propext, Classical.choice, Quot.sound]` only.
- Raw scan of the file for `sorry`, `admit`, `native_decide`, `axiom`, `maxHeartbeats`, `unsafe`, `implemented_by`, `extern`:
  0 hits. The file has no comments containing these words, so the comment-aware scan is identical. No `set_option`.

## 7. Remaining consumers (not discharged here)

- E56 `RawToProfileStep` and its coded-Palm consumers. `docs/campaign/GAPS-HB-1106.md:116` and `:129` name the hypothesis
  `RawToProfileStep P gamma ...`, consumed as `hB` by `palm_omega_of_stepM_stepB` and by
  `eq_r6_palm_lambda_of_stepM_stepB` (`PalmLambdaMeasurable.lean:94`). The results here are deterministic analysis on
  `C(CircleDomain, ℝ)`; they supply no GFF identification and no Palm identity, so E56 is not discharged.
- The displayed limit of `sec11-proof-r10.tex:1052` on the canonical GFF (`(g, φ*σ_{2^{-n}})`, lines 1055-1062) and the
  H^-2 reconstruction (`sec11-proof-r10.tex:1060`, `:1363-1365`) are outside this file.
- Not formalized: Borel measurability of the set of `F` where the limit exists (paper line 1054 "where it exists").
  Only the literal `limsup` (`measurable_limsup_circleTestIntegral`) is measurable here.
