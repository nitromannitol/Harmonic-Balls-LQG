# Audit: GreenPotentialFunctionalNorm (task green-functional-positive-exact-norm, worker q2)

Module: `HarmonicBalls/Proofs/Potential/GreenPotentialFunctionalNorm.lean` (new, 127 lines, namespace `HarmonicBalls`).
Carrier: `L∞` is `Lp ℝ ∞ (volume : Measure ℂ)`. `Φ x` abbreviates `greenPotentialLInfinityFunctional hU hUb x : Lp ℝ ∞ volume →L[ℝ] ℝ`, used exactly as defined at `GreenPotentialLInfinityFunctional.lean:101`; it is not redefined or replaced. Its formula is `greenPotentialLInfinityFunctional_apply` (`:110`): `Φ x f = ∫ y, greenFunction U x y * (f : ℂ → ℝ) y` for the representative `⇑f`.
Hypotheses: every declaration takes `(hU : IsOpen U) (hUb : Bornology.IsBounded U)` and the pole `x : ℂ`. Positivity adds `hf : 0 ≤ᵐ[volume] (f : ℂ → ℝ)`, and the `_of_lp` version adds `hf : 0 ≤ f` in the order of `Lp`. No assumed positive functional, no assumed norm, no External or Proposed hypothesis, no boundary, singular-source or E51 hypothesis.

## Declarations

| Line | Declaration | Statement (binders abbreviated) |
|---|---|---|
| 43 | `greenPotentialLInfinityFunctional_nonneg` | `(hU) (hUb) (x) {f} (hf : 0 ≤ᵐ[volume] ⇑f)`: `0 ≤ Φ x f` |
| 53 | `greenPotentialLInfinityFunctional_nonneg_of_lp` | `(hU) (hUb) (x) {f} (hf : 0 ≤ f)`: `0 ≤ Φ x f` |
| 61 | `greenPotentialLInfinityFunctional_eq_zero_of_notMem` | `(hU) (hUb) {x} (hx : x ∉ U)`: `Φ x = 0` |
| 70 | `greenPotentialLInfinityFunctional_empty` | `(x)`: `Φ x = 0` for `U = ∅` (`isOpen_empty`, `Bornology.isBounded_empty`) |
| 78 | `norm_toLp_const_one` | `‖MemLp.toLp (fun _ => 1) (memLp_top_const 1)‖ = 1` |
| 88 | `greenPotentialLInfinityFunctional_const_one` | `(hU) (hUb) (x)`: `Φ x (toLp 1) = ∫ y, greenFunction U x y` |
| 104 | `norm_greenPotentialLInfinityFunctional_eq` | `(hU) (hUb) (x)`: `‖Φ x‖ = ∫ y, greenFunction U x y` |
| 117 | `norm_greenPotentialLInfinityFunctional_eq_zero_of_notMem` | `(hU) (hUb) {x} (hx : x ∉ U)`: `‖Φ x‖ = 0` |
| 123 | `norm_greenPotentialLInfinityFunctional_empty` | `(x)`: `‖Φ x‖ = 0` for `U = ∅` |

The norm equality (104) is proved, not assumed. The file adds no definition, no carrier and no structure.

## Proof route and providers

- Positivity (43): `greenPotentialLInfinityFunctional_apply`; `MeasureTheory.integral_nonneg_of_ae` (Mathlib `Integral/Bochner/Basic.lean:639`); pointwise `mul_nonneg` with `greenFunction_nonneg hUb x y` (`Defs/Green.lean:134`) and `hf`.
- Order of `Lp` (53): `MeasureTheory.Lp.coeFn_nonneg` (Mathlib `Function/LpOrder.lean:48`).
- Off `U` (61): `greenFunction_of_notMem_left` (`Defs/Green.lean:97`) makes every integrand vanish, for every `f`; `ContinuousLinearMap.ext` gives the zero map.
- Empty `U` (70): the case `x ∉ ∅` of 61, using `Set.notMem_empty`.
- Constant `1` (78): `MeasureTheory.Lp.norm_toLp` (Mathlib `LpSpace/Basic.lean:246`), `eLpNorm_exponent_top` (`LpSeminorm/Defs.lean:138`), `eLpNormEssSup_const` (`LpSeminorm/Basic.lean:210`), `memLp_top_const` (`LpSeminorm/Basic.lean:269`), and `NeZero (volume : Measure ℂ)` from `IsOpenPosMeasure` (`Measure/OpenPos.lean:50`).
- Value at `1` (88): `MemLp.coeFn_toLp` (`LpSpace/Basic.lean:116`) and `integral_congr_ae`.
- Exact norm (104): `≤` is `norm_greenPotentialLInfinityFunctional_le` (`GreenPotentialLInfinityFunctional.lean:122`). `≥` evaluates the functional on the class of `1` via `ContinuousLinearMap.le_opNorm`, then uses `norm_toLp_const_one`, `greenPotentialLInfinityFunctional_const_one` and `G_U ≥ 0`. No case split: for `x ∉ U` and for `U = ∅` both sides are `0`.
- Off-`U` and empty norm (117, 123): from 61 and 70 with `norm_zero`.

Mathlib providers were searched first and reused as they are; nothing equivalent was re-proved.

## Checks (sandbox)

- `lc`: CHECK OK (`023929-652815`). The first run (`023843-542088`) failed only on the deprecated `ContinuousLinearMap.zero_apply`, replaced by `zero_apply`.
- `lb HarmonicBalls.Proofs.Potential.GreenPotentialFunctionalNorm`: BUILD OK (`024026-786018`).
- Printed axioms of all nine declarations: exactly `[propext, Classical.choice, Quot.sound]`.
- Raw scan (comments included) for sorry, admit, axiom, native_decide, unsafe, extern, implemented_by, set_option, ofReduceBool, opaque, heartbeat, maxRecDepth, decide, native, bypass, kernel: 0 hits. Comment-aware scan (comments and docstrings stripped): 0 hits.
- Import closure: 354 HarmonicBalls modules including this one; none missing. `GreenRowUniformIntegrability` in the closure: 0. `BoundedDensityGreenStability` is in the closure through the committed provider `GreenPotentialLInfinityFunctional` (`9a95b7c`); this adds no new dependency. The closure contains `HarmonicBalls.Proposed.Birkhoff` and `HarmonicBalls.Proposed.LQG` through existing imports; this module uses no declaration from them and takes no Proposed or External hypothesis.
- Tracked working tree at check time: no modified tracked file. The only untracked files were this module and another worker's `Sec11` file, which is not in this commit.
- Consumers: the new module has none. The functional is consumed by `GreenPotentialLInfinityFunctional.lean`, `GreenPotentialFunctionalContinuity.lean` and this module.
- Credit: the module docstring credits Leonardo Bonanno through the pinned Lattice-Probability (lean-v4.35) port.

## Not claimed

Nothing beyond the nine statements above. No compact-pole divergence, singular-source representative, boundary regularity, E51 content, literature input, physical exponent, metric moment or numbered closure.
