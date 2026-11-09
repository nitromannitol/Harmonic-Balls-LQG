# Audit: GreenPotentialLInfinityFunctional

TASK: green-bounded-density-Linfinity-functional (worker q2, Claude Haiku 5.5)
FILE: `HarmonicBalls/Proofs/Potential/GreenPotentialLInfinityFunctional.lean` (139 lines, new)
STATUS: `lc` passes (`-DwarningAsError=true`); `lb HarmonicBalls.Proofs.Potential.GreenPotentialLInfinityFunctional` builds; all nine declarations print axioms `[propext, Classical.choice, Quot.sound]`. Raw and code-only scans for `sorry`, `axiom`, `admit`, `native_decide`, `maxHeartbeats`, `set_option`: 0 hits.

## Carrier and binders

- Carrier: `Lp ℝ ∞ (volume : Measure ℂ)` (real `L∞` classes on `ℂ` for Lebesgue measure `volume`, with the Mathlib normed space structure; `fact_one_le_top_ennreal` supplies the exponent fact globally). Representative: `⇑f : ℂ → ℝ`.
- Green row: `greenFunction U x : ℂ → ℝ` (zero-extended off `U`, `HarmonicBalls/Defs/Green.lean`). `greenFunction_nonneg hUb x y` needs only `IsBounded`.
- Common binders: `{U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)`, pole `(x : ℂ)`.

## Declarations

| Declaration | Line | Kind and conclusion |
|---|---|---|
| `abs_coeFn_le_norm_ae_top` | 42 | `(f : Lp ℝ ∞ volume)` ⊢ `∀ᵐ y, \|⇑f y\| ≤ ‖f‖` |
| `integrable_greenFunction_mul_coeFn` | 54 | `(x) (f)` ⊢ `Integrable (fun y => greenFunction U x y * ⇑f y) volume` |
| `greenPotentialLInfinityLinear` | 63 | `def`: `Lp ℝ ∞ volume →ₗ[ℝ] ℝ`, `f ↦ ∫ y, greenFunction U x y * ⇑f y`; `map_add'` and `map_smul'` by `Lp.coeFn_add`, `Lp.coeFn_smul`, `integral_congr_ae` |
| `abs_greenPotentialLInfinityLinear_le` | 83 | `(f)` ⊢ `\|∫ G f\| ≤ (∫ y, greenFunction U x y) * ‖f‖` |
| `greenPotentialLInfinityFunctional` | 101 | `def`: `Lp ℝ ∞ volume →L[ℝ] ℝ` := `LinearMap.mkContinuous` of the linear map with constant `∫ y, greenFunction U x y` |
| `greenPotentialLInfinityFunctional_apply` | 110 | `(f)` ⊢ `greenPotentialLInfinityFunctional hU hUb x f = ∫ y, greenFunction U x y * ⇑f y` (`rfl`) |
| `abs_greenPotentialLInfinityFunctional_le` | 116 | `(f)` ⊢ `\|Φ f\| ≤ (∫ y, greenFunction U x y) * ‖f‖` |
| `norm_greenPotentialLInfinityFunctional_le` | 122 | `(x)` ⊢ `‖Φ‖ ≤ ∫ y, greenFunction U x y` (`ContinuousLinearMap.opNorm_le_bound`) |
| `exists_greenPotentialLInfinityFunctional_norm_le` | 133 | `(hU) (hUb)` ⊢ `∃ C, 0 ≤ C ∧ ∀ x, ‖Φ x‖ ≤ C` |

Here `Φ x` abbreviates `greenPotentialLInfinityFunctional hU hUb x`.

## Constant

`exists_greenPotentialLInfinityFunctional_norm_le` takes its constant from `exists_greenFunction_row_integral_le` (`HarmonicBalls/Proofs/Potential/BoundedDensityGreenStability.lean:38`). That constant is `K R² (1 + |log R|)`, with `U ⊆ ball 0 R` and `K` from `exists_greenFunction_local_volume_bound`. It depends on `U` only, not on the pole. The per-pole operator norm is bounded by the pole's row mass `∫ G_U(x, ·)`, which is at most this constant.

## Providers (all committed at or before b31642b)

- `integrable_greenFunction_mul_of_ae_bounded`: `BoundedDensityGreenStability.lean:56` (integrability of `G f` for a.e. bounded `f`).
- `exists_greenFunction_row_integral_le`: `BoundedDensityGreenStability.lean:38`.
- `integrable_greenFunction_pole`: `HarmonicBalls/Proofs/Potential/GreenPoleL1Continuity.lean:62`.
- `greenFunction_nonneg`: `HarmonicBalls/Defs/Green.lean:134`.
- Mathlib: `Lp.aestronglyMeasurable` (`MeasureTheory/Function/LpSpace/Basic.lean:187`), `Lp.coeFn_add` (`:203`), `Lp.enorm_def` (`:242`), `Lp.coeFn_smul` (`:450`), `enorm_ae_le_eLpNormEssSup` (`MeasureTheory/Function/LpSeminorm/Basic.lean:938`), `eLpNorm_exponent_top` (`MeasureTheory/Function/LpSeminorm/Defs.lean:138`), `enorm_eq_ofReal_abs` (`Analysis/Normed/Group/Real.lean:110`), `ENNReal.ofReal_le_ofReal_iff` (`Basic/ENNReal/Real.lean:147`), `integral_const_mul` (`MeasureTheory/Integral/Bochner/Basic.lean:290`), `integral_mul_const` (`:294`), `LinearMap.mkContinuous` (`Analysis/Normed/Operator/ContinuousLinearMap.lean:55`), `ContinuousLinearMap.opNorm_le_bound` (`Analysis/Normed/Operator/Basic.lean:197`), and `integral_add`, `integral_congr_ae`, `integral_mono_ae`, `abs_integral_le_integral_abs`, `Integrable.abs`, `Integrable.mul_const`, `integral_nonneg`.

Search before duplicating. The nine declaration names are new. No existing declaration in `HarmonicBalls` or `docs` shares them. `ObserverGreenLInfinityAdjoint.lean` (observer densities paired with a Green row through a measure `μ`) is a different pairing, and it is not imported or reused.

## Import closure

- Direct import: `HarmonicBalls.Proofs.Potential.BoundedDensityGreenStability` (committed b31642b). The file has no other import.
- Measured in Lean with `#eval` on `env.header.moduleNames`, in a scratch file outside the repository (`/tmp/q2-linf/Closure.lean`, `lc` log `logs/lc/011451-4117135.log`): total 11,797 modules; HarmonicBalls 353 (this file adds one); Mathlib 8,537; MarkovProcess 152; LatticeProb 2 (`LatticeProb.Prob.Birkhoff`, `LatticeProb.Prob.MaximalErgodic`); Lean core and other packages 2,753.
- The earlier measurement for `BoundedDensityGreenStability` (b31642b) gave 11,796 total, HarmonicBalls 352, Mathlib 8,536, others 2,754. The total grew by exactly this module. The Mathlib-versus-other split moved by one module; I did not reconcile this shift.

## Credit

The module docstring credits Leonardo Bonanno. His code reaches this file only through the pinned Lattice-Probability (lean-v4.35) port, visible in the closure as `LatticeProb.Prob.Birkhoff` and `LatticeProb.Prob.MaximalErgodic`.

## Development record

- First `lc`: `ENNReal.ofReal_norm_eq_enorm` is not a Mathlib name. Replaced by `simpa [enorm_eq_ofReal_abs] using hy` in `abs_coeFn_le_norm_ae_top`. Also removed two no-op `dsimp only` lines.
- Second `lc`: the only error was that `simpa` left `ENNReal.ofReal |f y|` against `‖f y‖ₑ`. Fixed by the `enorm_eq_ofReal_abs` simp lemma. Then `CHECK OK`.

## Checks

- `lc` on the final source: `CHECK OK`, log `logs/lc/011250-3908577.log`.
- `lb HarmonicBalls.Proofs.Potential.GreenPotentialLInfinityFunctional`: `BUILD OK`, log `logs/lb/011339-3985585.log`.
- `#print axioms` for the nine declarations (scratch `/tmp/q2-linf/AxCheck.lean`, `lc` log `logs/lc/011451-4117137.log`): `[propext, Classical.choice, Quot.sound]` for each.
- Raw grep and code-only scan (comments stripped, nested `/- -/` handled) of the file for `sorry|axiom|admit|native_decide|maxHeartbeats|set_option`: 0 hits.
- Consumers: `grep` of `HarmonicBalls` and `docs` for `greenPotentialLInfinity`, `abs_coeFn_le_norm_ae_top`, `integrable_greenFunction_mul_coeFn`, and `GreenPotentialLInfinityFunctional`: none outside this file.

## Remaining consumers and what is not claimed

- No consumer in the repository yet. Wiring the functional into `Steps` or `Draft` statements is operator routing.
- Claimed: for each pole `x`, a continuous real-linear functional on `Lp ℝ ∞ volume` given by the literal integral, with its value, integrability, the norm estimate `|Φ f| ≤ (∫ G_U(x, ·)) ‖f‖`, and one constant `C ≥ 0` depending only on `U` bounding every `‖Φ_x‖`.
- Not claimed: a normal representative of `G_U`, boundary regularity, a singular-source representative, general-domain reciprocity, compact-pole divergence, the numbered E51 closure, any literature input (no `External` or `Proposed` module is imported), physical exponents, metric moments, Pfeffer Def 1.6 membership or Prop 4.6.
- Not touched: the reserved compact-pole divergence queue, the frozen Draft/Defs/External/Proposed files, the paper, lakefile and manifest, and `HarmonicBalls.lean`.
