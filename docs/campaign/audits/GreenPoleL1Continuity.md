# GreenPoleL1Continuity audit

Task: q2-h2-green-pole-L1-continuity (reassigned from h2; local volume input from h2's commit 7007db1).

File: `HarmonicBalls/Proofs/Potential/GreenPoleL1Continuity.lean`.

Statement. For `U` open and bounded in `ℂ`, a pole `x ∈ U`, and a countably generated filter `l` with
`xs → x` along `l`: `∫ y, |G_U(xs i, y) - G_U(x, y)| → 0` (`tendsto_integral_abs_greenFunction_sub`).
Corollaries: along `𝓝[U] x` (`..._nhdsWithin`) and for sequences along `𝓝[U] x` (`..._atTop`).
Integrability: `integrable_greenFunction_pole` (`y ↦ G_U(z, y)` is integrable on `ℂ` for every pole `z`) and
`integrable_abs_greenFunction_sub_pole`.

Pole and domain restrictions. `IsOpen U`, `Bornology.IsBounded U`, and `x ∈ U`. The points `xs i` need not
lie in `U`, because `G_U(z, ·) = 0` for `z ∉ U`. The pole `x ∈ U` is needed for pole continuity
(`continuousAt_greenFunction_pole`). The diagonal junk value `0` of `greenFunction` is a null set and does
not affect any integral.

Route. Remove `B(x, r)`. On the disc, `integral_ball_abs_greenFunction_sub_le` bounds
`∫_B |G(p,·) - G(q,·)|` by `2 C r²(1 + |log r|)`, uniformly in the poles, from the local volume estimate.
Off the disc, `tendsto_integral_outside_ball_abs_greenFunction_sub` applies dominated convergence with the
dominator `(2π)⁻¹ log⁺(4R/r)` on `B(0, R) ⊇ U` (`greenFunction_le_posLog_div_norm`, `posLog_two_mul_div_le`)
and pointwise convergence by pole continuity. The main theorem chooses `r` small, then `ε`.

Reused, not duplicated. `exists_greenFunction_local_volume_bound` (`GreenLocalVolumeBound.lean`, 7007db1),
`tendsto_sq_mul_one_add_abs_log`, `greenFunction_ball_center_eq_posLog` (same file),
`Section6.greenFunction_le_of_subset` (`Proofs/Sec6/GreenIntegrability.lean`), `greenFunction_nonneg` and
`greenFunction_of_notMem_left/right` (`Defs/Green.lean`), `continuousAt_greenFunction_pole`
(`FiniteDiscGreenReciprocity.lean`, joint continuity of cc1b795), Mathlib `Real.posLog_le_posLog` and
`tendsto_integral_filter_of_dominated_convergence`. Search for an existing equivalent: no theorem in the
repository states L¹ continuity of the Green row in the pole. `TransposedGreenL1Operator`
(`IntegrableDensityDomainExhaustion.lean`) controls source operators and is not consumed.

Inputs. No literature input, no External or Proposed hypothesis, no frozen Draft or Defs edit. Pfeffer
Def 1.6 membership and Prop 4.6 are not used (operator08:30 / AUDIT-r9 G1).

Credit. The local volume estimate and the potential-theoretic infrastructure it uses carry the credit of
Leonardo Bonanno, as stated in the module docstring of `GreenLocalVolumeBound.lean`. No new Bonanno code is
imported here.

Checks. `lc` on the file: CHECK OK with warnings as errors. `lb HarmonicBalls.Proofs.Potential.GreenPoleL1Continuity`:
BUILD OK. Forbidden-token scan (`sorry`, `admit`, `axiom`, `native_decide`, `set_option`, `#print`) on the file:
no matches. `#print axioms` for the nine declarations in the file: each depends only on `propext`,
`Classical.choice`, `Quot.sound`.

Not covered. Boundary poles `x ∈ ∂U` (no claim); no boundary regularity; no normal-representative closure.
