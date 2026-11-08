# Audit: SingularCompactNull (singular LQG, α < Q, compact sets avoiding the origin)

Task: `singular-lqg-compact-null-away-origin` (worker z3, round 1).
Module: `HarmonicBalls/Proofs/Sec11/SingularCompactNull.lean` (new). It imports the completed zero-charge module
`HarmonicBalls/Proofs/Sec11/FixedSquareFrontierNull.lean` and reuses its APIs; that module is not edited.

## Status

- `lc`: CHECK OK (`lake env lean -DwarningAsError=true`, so no warnings either).
- `lb HarmonicBalls.Proofs.Sec11.SingularCompactNull`: BUILD OK.
- Forbidden-token scan of the module (`sorry`, `admit`, `axiom`, `native_decide`, `maxHeartbeats`): 0 hits.
  No `set_option` in the module.
- `#print axioms` (probe file outside the repository, `lake env lean`) for the two main results and three helpers
  (`lintegral_lqgMeasure_le_of_cutoff_weight`, `circleAverage_log_norm_eq_log_max`, `lqgDensity_eq_mul_radialWeight`):
  `[propext, Classical.choice, Quot.sound]` only.

## Declarations (namespace `HarmonicBalls`)

- `IsWholePlaneGFF.ae_lqgMeasure_eq_zero_of_isCompact_not_mem_zero` (main). Inputs: `hgff : IsWholePlaneGFF P hC hcirc`,
  `_hγ : 0 < γ`, `_hγ2 : γ < 2`, `_hα : α < lqgQ γ` (paper scope, kept as hypotheses, not used by the proof),
  `hμ : IsLQGMeasureOfField P γ α hcirc μ` (singular charge `α`), `hK : IsCompact K`, `h0 : (0 : ℂ) ∉ K`,
  `hKv : volume K = 0`. Conclusion: `∀ᵐ ω ∂P, μ ω K = 0`. `K` is fixed before `ω`.
- `IsWholePlaneGFF.ae_lqgMeasure_frontier_closedSquare_eq_zero_of_not_mem_zero`. Same hypotheses with
  `(a : ℂ) {L : ℝ} (hL : 0 ≤ L) (h0 : (0 : ℂ) ∉ frontier (closedSquare a L))`. Conclusion:
  `∀ᵐ ω ∂P, μ ω (frontier (closedSquare a L)) = 0`.
- Helpers: `circleAverage_log_norm_eq_log_max`, `fieldCircleAverage_eq_sub_log_max`, `radialWeight` (a def:
  `‖z‖^{-γα} = exp(-γα log ‖z‖)`), `lqgDensity_eq_mul_radialWeight`, `IsWholePlaneGFF.lintegral_lqgMeasure_le_of_cutoff_weight`.
- Reused, not re-proved: `IsWholePlaneGFF.lintegral_density_le`, `lintegral_eq_liminf_of_tendsto`,
  `exists_cutoff_of_isCompact`, `volume_setOf_re_eq_const`, `volume_setOf_im_eq_const` (zero-charge module);
  `IsWholePlaneGFF.exists_jointlyMeasurable_circleAverage`, `IsWholePlaneGFF.aemeasurable_lqgApprox`,
  `IsWholePlaneGFF.aemeasurable_lqgMeasure` (Sec5, general `α₀`); `frontier_closedSquare_subset_lines` (Sec11).
- Mathlib: `circleAverage_log_norm_sub_const_eq_log_radius_add_posLog`
  (`Mathlib/Analysis/SpecialFunctions/Integrals/PosLogEqCircleAverage.lean`), `IsCompact.exists_cthickening_subset_open`
  (`Mathlib/Topology/MetricSpace/Thickening.lean`), `IsCompact.exists_isMinOn`, `IsCompact.exists_isMaxOn`,
  `tendsto_measure_cthickening_of_isCompact`.

## Correction of the written argument (recorded, no new mathematics)

The task's written argument states `fieldCircleAverage α hcirc ε z = hcirc ε z - α log ‖z‖` for all `ε`. The Lean
definition (`HarmonicBalls/Defs/GFF.lean:118`) is `hcirc r z - α₀ · Real.circleAverage (fun x => Real.log ‖x‖) z r`,
the circle average of `log ‖·‖` over `∂B_r(z)`, which is the circle average of `h = h^ℂ - α log|·|` as in the paper.
Mathlib's identity gives this average as `log (max r ‖z‖)`, so it equals `log ‖z‖` exactly when `r ≤ ‖z‖`
(`circleAverage_log_norm_eq_log_max`). Consequently the approximating density equals the zero-charge density times
`radialWeight γ α` only on `‖z‖ ≥ ε` (`lqgDensity_eq_mul_radialWeight`). The proof uses only dyadic scales
`ε ≤ min ρ 1`, where `ρ` bounds `‖z‖` from below on the support of the cutoff, and the Fatou step runs over the tail
`k ≥ k₀`. The conclusion is unchanged.

## Route

1. Compact neighbourhood `C₀ = cthickening δ₀ K` with `C₀ ⊆ ℂ ∖ {0}` (`IsCompact.exists_cthickening_subset_open`).
   On `C₀`: a lower bound `ρ > 0` for `‖·‖` (`exists_isMinOn`), an upper bound `M` for `radialWeight` (`exists_isMaxOn`
   of a continuous function, since `0 ∉ C₀`), and `C₀ ⊆ closedBall 0 R`.
2. For a continuous `0 ≤ f ≤ 1`, `f = 1` on `K`, `f` supported in `C₀`: the first moment
   `E[ε^{γ²/2} e^{γ h_ε(z)}] ≤ (R+1)^{γ²}` (zero-charge lemma), the radial weight `≤ M` on `supp f`, Tonelli, Fatou,
   and the dyadic vague convergence on the tail give `E μ(K) ≤ (R+1)^{γ²} M ∫ f`
   (`lintegral_lqgMeasure_le_of_cutoff_weight`).
3. Urysohn cutoffs of `cthickening δ K` for `δ ≤ δ₀`, with `∫ f ≤ Leb(cthickening δ K)`. As `δ → 0`,
   `Leb(cthickening δ K) → Leb K = 0`, so `E μ(K) = 0` and `μ ω K = 0` almost surely.
4. Square: the frontier of `closedSquare a L` is a compact subset of the square and lies on four lines, hence is
   Lebesgue-null; with `0 ∉ frontier` the main statement applies.

## Scope and what is not claimed

- No samplewise absolute continuity `μ ω ≪ volume` is used. The quantifier order is `∀ᵐ ω` after the fixed `K`.
- `0 < γ < 2` and `α < Q` are kept as hypotheses (source scope). The proof uses `hgff` and `hμ` only; the existence of
  the vague limit is carried by `hμ`.
- Nothing is claimed for a frontier through `0`, for random null sets, or for all compact sets simultaneously.
- No `Proposed` or `External` Prop is a hypothesis. The import closure contains `HarmonicBalls/Proposed/Birkhoff.lean`
  and reaches `LatticeProb.Prob.Birkhoff` through `FixedSquareFrontierNull` → `Sec8/BirkhoffPort`, as recorded in
  `docs/campaign/audits/FixedSquareFrontierNull.md`. This is not a hypothesis of either main result.
- Credit: Leonardo Bonanno (LatticeProb formalization in the import closure), named in the module docstring.

## Note for the consumer (z6)

The fixed square `closedSquare fixedSquareCorner fixedSquareSide` (`Closure/FixedMassDiameter.lean:24,27`) has real
part in `[1.4975, 1.5025]`, so `0 ∉` its frontier. The `h0` argument of the square lemma is therefore discharged at the
use site by that real-part bound, not by this module.
