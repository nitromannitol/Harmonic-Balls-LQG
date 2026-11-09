# Audit: FourierFinitenessMeasurable (task `sec11-fourier-finiteness-pairing-measurability`)

Owner: z3. File: `HarmonicBalls/Proofs/Sec11/ClosureScales/FourierFinitenessMeasurable.lean` (new, 138 lines, namespace
`HarmonicBalls`, not imported by `HarmonicBalls.lean`).

Status: `lc` CHECK OK (log `012753-1367965`, no warnings); `lb` BUILD OK (log `012837-1443710`). Printed axioms of the eight
public declarations are exactly `[propext, Classical.choice, Quot.sound]` (log `012952-1573299`; scratch file
`/tmp/z3-fourier-axioms.lean`, outside the repository). Raw scan of the file for `sorry`, `axiom`, `admit`,
`native_decide`, `maxHeartbeats`, `set_option`, `Bonanno`, `Lattice` (comments included): 0 hits.

## 1. Written source

- `~/paper-fleets/hb/notes/sec11-proof/sec11-proof-r10.tex`, lines 1072-1089 (the explicit validity test). Line 1076: a valid
  code has finite weighted square sum for each `j`. Lines 1080-1082: support and the equalities `χ_i T_j = χ_j T_i` are Borel
  conditions. Lines 1085-1088: Fourier partial sums give the Borel reconstruction `R`.
- This file formalizes only the component at line 1076 (finite weighted square sums), as a Borel set on the raw pairing carrier.

## 2. Declarations, binders, conclusions

| Declaration | Line | Binders | Conclusion |
|---|---|---|---|
| `cutoffCoeff` (def) | 40 | `{ι}`, `χ : ι → ℂ → ℝ`, `L : ℝ`, `T : (ℂ → ℝ) → ℝ`, `p : ι × (ℤ × ℤ) × Bool` | `if p.2.2 then T (cutoffCosTest (χ p.1) L p.2.1) else T (cutoffSinTest (χ p.1) L p.2.1)` |
| `measurable_cutoffCoeff` | 45 | `{ι}`, `[Countable ι]`, `χ`, `hχ : ∀ i, IsTestFunction Set.univ (χ i)`, `L` | `Measurable[pairingMeasSpace] (cutoffCoeff χ L)` into `ι × (ℤ × ℤ) × Bool → ℝ` (product σ-algebra) |
| `summable_nonneg_iff_tsum_ofReal_lt_top` | 56 | `{ι}`, `{g : ι → ℝ}`, `hg : ∀ i, 0 ≤ g i` | `Summable g ↔ ∑' i, ENNReal.ofReal (g i) < ⊤` |
| `setOf_summable_eq_tsum_lt_top` | 65 | `{χ : ℂ → ℝ}`, `L` | literal set `{T \| Summable (weighted cos/sin square sums)}` = `{T \| ∑' k, ENNReal.ofReal (term k T) < ⊤}` |
| `measurableSet_fourierFiniteness` | 77 | `{χ}`, `hχ : IsTestFunction Set.univ χ`, `L` | `MeasurableSet[pairingMeasSpace]` of the literal finiteness set |
| `measurableSet_fourierFiniteness_countable` | 89 | `{ι}`, `[Countable ι]`, `χ : ι → ℂ → ℝ`, `hχ : ∀ i, …`, `L` | `MeasurableSet[pairingMeasSpace]` of `{T \| ∀ i, Summable (…χ i…)}` |
| `IsWholePlaneGFF.measurableSet_preimage_fourierFiniteness` | 107 | `{Ω} [MeasurableSpace Ω] {P} {hC} {hcirc}`, `hG : IsWholePlaneGFF P hC hcirc`, `{χ}`, `hχ`, `L` | `MeasurableSet ((fun ω => hC ω) ⁻¹' A_χ) ∧ P ((fun ω => hC ω) ⁻¹' A_χ)ᶜ = 0` |
| `IsWholePlaneGFF.measurableSet_preimage_fourierFiniteness_countable` | 123 | as above, with `{ι}`, `[Countable ι]`, `χ : ι → ℂ → ℝ`, `hχ : ∀ i, …` | the same two conclusions for the countable intersection `A = {T \| ∀ i, …}` |

The summand in every set is `(1 + (k.1 : ℝ)^2 + (k.2 : ℝ)^2)^(-2 : ℤ) * ((T (cutoffCosTest χ L k))^2 + (T (cutoffSinTest χ L k))^2)`,
written literally as in `IsWholePlaneGFF.exists_measurable_conull_cutoffFourier` (`CutoffFourierSummability.lean:206`).

## 3. Carrier and instance

- Carrier: raw pairings `T : (ℂ → ℝ) → ℝ`, with `pairingMeasSpace` (`PalmPairingMeasurable.lean:25`, the abbreviation of
  `pairingSigmaAlgebra (fun T => T) Set.univ`; `Defs/LQGMetric.lean:133`). This is the supremum of the comaps of the
  evaluations `T ↦ T φ` over test functions `φ` with `IsTestFunction Set.univ φ`.
- The file contains `attribute [local instance] pairingMeasSpace` (line 35). It is scoped to the file (`attribute ... local`)
  and makes the instance-implicit Mathlib lemmas `Measurable.of_eval` and `Measurable.tsum` resolve on the pairing σ-algebra.
  Every statement names the σ-algebra explicitly (`Measurable[pairingMeasSpace]`, `MeasurableSet[pairingMeasSpace]`).
- Pullback: the field `ω ↦ hC ω` is `pairingMeasSpace`-measurable by `measurable_pairing_field`
  (`PalmPairingMeasurable.lean:53`), which is built from the structure field `IsWholePlaneGFF.measurable_pairing`. No new hypothesis.

## 4. Providers reused (none duplicated)

- `CutoffFourierSummability.lean` (committed at `db406d0`): `cutoffCosTest` (line 43), `cutoffSinTest` (line 47),
  `isTestFunction_cutoffCosTest` (57), `isTestFunction_cutoffSinTest` (62), `frequencyWeight_nonneg` (67),
  `IsWholePlaneGFF.exists_measurable_conull_cutoffFourier_countable` (265).
- `BorelCircleLimitDecoder.lean:154` (committed at `326a1ae`): `measurable_pairing_eval`.
- `PalmPairingMeasurable.lean` (committed at `bbd65ac`): `pairingMeasSpace` (25), `measurable_pairing_field` (53).
- Mathlib: `Measurable.of_eval`, `Measurable.tsum`, `measurableSet_lt`, `MeasurableSet.iInter`, `ENNReal.ofReal_tsum_of_nonneg`,
  `ENNReal.summable_toReal`, `ENNReal.ofReal_lt_top`, `ENNReal.toReal_ofReal`, `Summable.congr`, `measure_mono_null`.
- Deprecations avoided: `measurable_pi_lambda` (use `Measurable.of_eval`), `Measurable.ennreal_tsum` (use `Measurable.tsum`),
  `Set.mem_setOf_eq` (use `Set.mem_ofPred_eq`). `lc` rejects deprecated names.

## 5. Import closure

- Direct imports: `Mathlib`, `HarmonicBalls.Defs.GFF`, `HarmonicBalls.Defs.Laplacian`,
  `HarmonicBalls.Proofs.Sec11.ClosureScales.CutoffFourierSummability`, `HarmonicBalls.Proofs.Sec11.ClosureScales.BorelCircleLimitDecoder`.
- Transitive HarmonicBalls closure: 26 files including the new file, computed by a script on the sandbox. No external package
  (`MarkovProcess`, `EllipticRegularityLean`, Lattice-Probability) appears in it. `CircleTestIntegralContinuity` is not in it.
- Credit to Leonardo Bonanno: not required. No Bonanno or Lattice-Probability declaration is used. The closure hit
  `MollifiedContinuousCircleLimit.lean` only states that no Lattice-Probability declaration is used there. The other
  "lattice" hits (`CutoffFourierSummability.lean`) are the mathematical term for the weight on `ℤ × ℤ`.

## 6. Remaining consumers and what is not discharged

- Still formalized nowhere (written argument, lines 1080-1088): the Borel support condition (`T_j` supported in `supp χ_j`),
  the equalities `χ_i T_j = χ_j T_i`, the gluing into `𝓗`, the Fourier partial-sum reconstruction `R`, and the
  intersection of all these conditions with the finiteness set. This file gives only the finite weighted square-sum component.
- Weighted finiteness alone does not validate a distribution code, and it does not discharge the open consumers:
  E56 `RawToProfileStep` (`PalmStepM.lean:42`), its consumers `palm_omega_of_stepM_stepB` (`PalmStepM.lean:56`) and
  `eq_r6_palm_lambda_of_stepM_stepB` (`PalmLambdaMeasurable.lean:88`, consumption at line 94), and the open items recorded at
  `docs/campaign/GAPS-HB-1106.md:116,129`.
- No samplewise GFF linearity or continuity hypothesis, no probability estimate, and no new standing Step is introduced.
  The pullback uses only the countable-cut-off conull theorem and the structure field `measurable_pairing`.
