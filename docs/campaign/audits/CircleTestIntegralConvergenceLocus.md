# Audit: CircleTestIntegralConvergenceLocus (task `sec11-circle-test-integral-convergence-locus`)

Owner: z3. File: `HarmonicBalls/Proofs/Sec11/ClosureScales/CircleTestIntegralConvergenceLocus.lean` (new, 103 lines,
namespace `HarmonicBalls`, not imported by `HarmonicBalls.lean`).

Status. `lc` CHECK OK (final log `015344-4053622`); `lb` BUILD OK (final log `015353-4067920`). Printed axioms of the six public
declarations are exactly `[propext, Classical.choice, Quot.sound]` (log `014858-3574724`; scratch file
`/tmp/z3-convergence-axioms.lean`, outside the repository). Raw scan of the file, comments included, for `sorry`, `axiom`,
`admit`, `native_decide`, `maxHeartbeats`, `set_option`, `extern`, `implemented_by`, `unsafe`, `Bonanno`, `Lattice`: 0 hits.
This is a Borel-measurability and convergence-identity statement; it is not a numbered closure of the paper.

## 1. Written source

- `notes/sec11-proof/sec11-proof-r10.tex`, lines 1046-1055. Lines 1051-1053 display the limit
  `lim_n ∫ c(2^{-n},z) φ(z) d²z`; lines 1054-1055 state that each integral is continuous in `c` and that "the limit, where it
  exists, is Borel".
- Lines 1074-1089: the countable validity conditions (support, equalities `χ_i T_j = χ_j T_i`, gluing, the Borel
  reconstruction `R`). Only the Borel convergence prerequisite of lines 1054-1055 is formalized here. The other conditions
  have no declaration in this file.

## 2. Declarations (binders and statements)

Namespace `HarmonicBalls`; `open MeasureTheory Set Filter Topology`. Every statement carries the literal integral
`∫ z, F ⟨(dyadicScale n, z), dyadicScale_pos n⟩ * φ z` and the literal predicate `∃ L : ℝ, Tendsto … atTop (𝓝 L)`; no
new named predicate or hypothesis is introduced (no new `def`).

| Line | Declaration | Binders | Statement |
|---|---|---|---|
| 46 | `measurableSet_circleTestIntegral_convergence` | `{φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ)` | `MeasurableSet {F : C(CircleDomain, ℝ) \| ∃ L, Tendsto (fun n : ℕ => …) atTop (𝓝 L)}` |
| 53 | `circleTestIntegral_convergence_eq_cauchy` | `{φ : ℂ → ℝ}` | locus `=` `{F \| CauchySeq (fun n => …)}` (completeness of `ℝ`) |
| 64 | `tendsto_limsup_circleTestIntegral_of_mem` | `{φ : ℂ → ℝ}` | `∀ F ∈ locus, Tendsto (fun n => …) atTop (𝓝 (Filter.limsup (fun n => …) atTop))` |
| 76 | `measurableSet_circleTestIntegral_tendsto_pairing` | `{φ} (hφ)` | `MeasurableSet {q : C(CircleDomain, ℝ) × ((ℂ → ℝ) → ℝ) \| Tendsto (fun n => ∫ z, q.1 ⟨…⟩ * φ z) atTop (𝓝 (q.2 φ))}` |
| 87 | `measurableSet_circleTestIntegral_convergence_countable` | `{𝒯 : Set (ℂ → ℝ)} (h𝒯 : 𝒯.Countable) (h𝒯t : ∀ φ ∈ 𝒯, IsTestFunction Set.univ φ)` | `MeasurableSet (⋂ φ ∈ 𝒯, locus φ)` |
| 95 | `measurableSet_circleTestIntegral_tendsto_pairing_countable` | same binders as 87 | `MeasurableSet (⋂ φ ∈ 𝒯, pairing set φ)` |

Line 42: `attribute [local instance] pairingMeasSpace` (file-local, as in `FourierFinitenessMeasurable.lean:35`). It makes the
second factor of the product σ-algebra `pairingMeasSpace` rather than the Pi σ-algebra on `(ℂ → ℝ) → ℝ`. The product
σ-algebra is `Prod.instMeasurableSpace`.

Carrier. `C(CircleDomain, ℝ)` carries `ContinuousMap.measurableSpace` (Mathlib, `borel`, `BorelSpace/ContinuousMap.lean:51`);
`CircleDomain` and the topology are from `CountableCircleDecoder.lean`. The raw pairing `T : (ℂ → ℝ) → ℝ` carries
`pairingMeasSpace` (`PalmPairingMeasurable.lean:25`, `pairingSigmaAlgebra (fun T => T) Set.univ`). The integrals are against
`volume` on `ℂ`. `dyadicScale` and `dyadicScale_pos` are in `Defs/LQG.lean:41` and `:84`. `IsTestFunction` is in
`Defs/Laplacian.lean:47`.

## 3. Providers (exact sources)

- `measurable_circleTestIntegral_fixed` (`CircleTestIntegralContinuity.lean:143`): Borel measurability of
  `F ↦ ∫ z, F ⟨(r,z), hr⟩ * φ z`, used for every `n` at `dyadicScale_pos n`.
- `measurable_pairing_eval` (`BorelCircleLimitDecoder.lean:154`): `T ↦ T φ` is measurable for `pairingMeasSpace`.
- Mathlib `MeasureTheory.measurableSet_exists_tendsto` (`MeasureTheory/Constructions/Polish/Basic.lean:998`), used at 46.
  Its countable-base Cauchy/limit argument for a complete, second countable, pseudometrizable target is inside Mathlib and is
  not re-proved here.
- Mathlib `MeasureTheory.measurableSet_tendsto_fun` (`Polish/Basic.lean:986`), used at 76 and in the countable version.
- Mathlib `Filter.Tendsto.limsup_eq` (`Topology/Order/LiminfLimsup.lean:190`), used at 64; `cauchySeq_tendsto_of_complete`
  and `Filter.Tendsto.cauchySeq`, used at 53; `MeasurableSet.biInter`, used at 87 and 95.

Existing providers checked and not duplicated. `measurable_limsup_circleTestIntegral` (`CircleTestIntegralContinuity.lean:156`)
gives the Borel limsup map; the new file adds the convergence locus and the limit identity on it. `BorelCircleLimitDecoder.lean:58`,
`:133` and `RouteACodes.lean:48` apply `measurableSet_exists_tendsto` to other carriers (an abstract space, the canonical
profile). None is on `C(CircleDomain, ℝ)` or on the product with `T`.

## 4. Import closure

- Direct imports: `CircleTestIntegralContinuity` (committed at `5c7ac82`) and `BorelCircleLimitDecoder`.
- HarmonicBalls modules reached by the import walk (script in the z3 scratch directory): `Defs.GFF`, `Defs.LQG`,
  `Defs.LQGMetric`, `Defs.Laplacian`, `Defs.Notation`, `Proofs.Sec11.ClosureScales.{BorelCircleLimitDecoder,
  CircleTestIntegralContinuity, CountableCircleDecoder, PalmPairingMeasurable}`, and `Proposed.DuplantierMillerSheffield`,
  which `PalmPairingMeasurable.lean:4` imports.
- Otherwise Mathlib only. No lattice-probability, MarkovProcess or elliptic_regularity module is reached, so no Bonanno
  credit line applies: no file here uses his code.
- Use of the staged input: a constant walk over the statements and proofs of the six declarations (`#eval` over
  `ConstantInfo` used-constants, log `015201-3887071`, scratch `/tmp/z3-convergence-deps.lean`) reaches 4861 constants
  in 400 modules. None lies in `HarmonicBalls.Proposed.*` or `HarmonicBalls.External.*`. The DMS input is imported through
  `PalmPairingMeasurable` but is not a hypothesis or a used constant of any declaration here.

## 5. Remaining, not discharged here

- Tex lines 1074-1089: the Borel support condition, the equalities `χ_i T_j = χ_j T_i`, the gluing to `T ∈ 𝓗` and the Borel
  reconstruction `R`. No Lean declaration in this file. Open.
- E56 `RawToProfileStep` (`PalmStepM.lean:42`), with consumers `PalmStepM.lean:56` and `PalmLambdaMeasurable.lean:94`
  (`hB : RawToProfileStep P γ hC hcirc c`). These convergence measurabilities do not discharge it.
- Consumers of the six new declarations: none yet (the file is new and not imported by `HarmonicBalls.lean`).

## 6. Choices

- The convergence locus is taken from Mathlib's `measurableSet_exists_tendsto` rather than a second, hand-written countable
  Cauchy argument (the equivalent exact provider). Completeness of `ℝ` appears explicitly in 53, which identifies the
  locus with the Cauchy locus.
- The countable family is a countable `Set` of test functions. Any countable indexed family is covered by its range.
- Nothing from the frozen Defs/Draft, External, Proposed, paper, dependency or `HarmonicBalls.lean` was edited.
