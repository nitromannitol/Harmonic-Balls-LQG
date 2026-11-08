# Audit: MollifiedLogCircleLimit (task sec11-mollified-log-circle-limit)

Module: `HarmonicBalls/Proofs/Sec11/ClosureScales/MollifiedLogCircleLimit.lean`
Main theorem: `HarmonicBalls.mollified_log_circle_limit` (line 368).
Source: r10 `l:r9-circle-code`, `notes/sec11-proof/sec11-proof-r10.tex` lines 1331-1350. The written argument
(Fubini plus the circle-potential formula) reads: the first term is a mollification at `z` of the continuous
function `-γ log max(r, |· - w|)`, and the second is the circle average of a mollification of `logMaxOne`.
The Lean route follows it.

## Statement as formalised

Hypotheses on `rho : ℂ → ℝ`: `_h_even` (not needed for the limit, kept), `h_nonneg`, `h_smooth : ContDiff ℝ ∞ rho`
(used only through continuity), `h_supp : tsupport rho ⊆ closedBall 0 1`, `h_one : ∫ rho = 1`. Parameters:
`γ : ℝ`, `z w : ℂ`, `hr : 0 < r`.

Conclusions:
1. for every `e > 0`, `v ↦ dmsShift γ z v * Real.circleAverage (fun u ↦ ((e:ℝ)^2)⁻¹ * rho ((e:ℝ)⁻¹ • (u - v))) w r`
   is integrable;
2. its integral tends, as `e → 0⁺` (filter `𝓝[>] 0`), to
   `-γ * Real.log (max r ‖w - z‖) + γ * Real.circleAverage logMaxOne w r`, for every `z`, including `z` on the circle.

No hypothesis beyond these: no Gaussian event, decoder, raw or profile equality, convergence premise, External or
Proposed input.

## Fidelity decisions

- Support: `tsupport rho ⊆ closedBall 0 1` (closed ball). This is weaker than the open-ball reading of "support in
  `B_1`", so the theorem covers both readings.
- Kernel: the statement writes the literal formula `((e:ℝ)^2)⁻¹ * rho ((e:ℝ)⁻¹ • x)`. The file also names it
  `mollifierAt` (line 36), used only internally, with its characterisation: total mass one (`mollifierAt_integral`,
  line 76), nonnegativity (line 59), support in `closedBall 0 e` (lines 51, 67), continuity and compact support
  (lines 63, 71), and the approximate identity (`tendsto_integral_mollifierAt_mul`, line 85).
- `dmsShift` is the Proposed definition at `HarmonicBalls/Proposed/DuplantierMillerSheffield.lean:34`, namely
  `-γ * log ‖w - z‖ + γ * log (max ‖w‖ 1)`. Only its formula is used. It is a definition, not a hypothesis, and its
  source check stays with the operator. `logMaxOne` is `Proofs/Sec11/ClosureScales/RootedShiftProfile.lean:23`.
  `Real.circleAverage` is Mathlib's `(2π)⁻¹ • ∫ θ in 0..2π, f (circleMap c R θ)`.
- The DMS unnormalised `hU` is not consumed.

## Route

1. Circle average as an integral over `Ioc 0 (2π)` (`circleAverage_eq_integral`, line 136).
2. First Fubini on `volume.prod (volume.restrict (Ioc 0 (2π)))` (`hR1` inside `integral_mul_circleAverage_mollifierAt`,
   line 255). Domination `norm_mul_mollifierAt_circle_le` (line 242): `‖g v * ρ_e(c θ - v)‖ ≤ indicator (closedBall w (r+e)) (K0 · ‖g‖) v`,
   uniform in `θ`. `K0` comes from compactness (`exists_norm_bound_of_zero_outside`, line 206). Integrability of `g` on
   compact sets comes from `LocallyIntegrable g`.
3. Substitution `v = c θ - y` (`integral_sub_left_eq_self`), then the second Fubini on the `(θ, y)` product (`hR2`).
4. Inner averages. For `g = log ‖· - z‖`, `circleAverage (fun u ↦ g (u - y)) w r = log max(r, ‖(y + z) - w‖)` by
   `HarmonicBalls.circleAverage_log_norm_sub_eq_log_max` (`circleAverage_log_sub`, line 151). For `g = logMaxOne`,
   it equals `circleAverage logMaxOne (w - y) r` (`circleAverage_comp_sub`, line 142), which is continuous in `y` by
   `continuous_circleAverage_logMaxOne` (`continuous_circleAverage_logMaxOne_sub`, line 164).
5. Limit: approximate identity at `y = 0` for continuous `h` (lines 85-134). It uses continuity of `h` at `0`,
   `∫ rho_e = 1`, `rho_e ≥ 0`, and support in `closedBall 0 e`.
6. Integrability for each `e`: `integrable_mul_of_zero_outside` (line 216) for a locally integrable factor times a
   continuous factor vanishing off `closedBall w (r+e)`. The circle average `φ_e` is continuous (line 170) and vanishes
   off that ball (line 200). Local integrability of `log ‖· - z‖` is
   `locallyIntegrable_comp_sub_of_integrableOn_ball integrableOn_ball_log_norm z` (`Proofs/Potential/Fundamental.lean:44,67`).
7. Pointwise split `dmsShift γ z v = -γ log ‖v - z‖ + γ logMaxOne v` (`max_comm`), then linearity of the integral.

## Checks

- `lc`: CHECK OK. `lc` runs with warnings as errors.
- `lb`: BUILD OK for `HarmonicBalls.Proofs.Sec11.ClosureScales.MollifiedLogCircleLimit`.
- `#print axioms` (scratch file under `/tmp`, outside the repository): `mollified_log_circle_limit`,
  `tendsto_integral_mollifierAt_mul`, `integral_mul_circleAverage_mollifierAt`, `integrable_prod_of_bound`. Each prints
  `[propext, Classical.choice, Quot.sound]`.
- Raw scan of the file for `sorry|axiom|admit|native_decide|maxHeartbeats|set_option|unsafe|implemented_by|extern`:
  no hits.
- No `Lattice-Probability` reference in the file or in its four direct imports' text. The module does not use
  Bonanno's code.

## Gaps and notes for the operator

- The approximate identity is proved in the file. I did not find a Mathlib lemma for a general continuous mollifier:
  `ContDiffBump` requires a bump structure. This is an unverified search claim: I did not search exhaustively.
- Project files read or located but not used: `Proofs/GFF/LogInsertionCircleAverages.lean` (located by name only, not
  read in detail). `Proofs/Sec11/ClosureScales/RouteACircleFubini.lean` (committed e9022ee) declares
  `integral_mul_circleAverage_symm`, a different name, and is not imported.
- Imports: `Proofs/Potential/Fundamental`, `Proofs/Sec11/ClosureScales/CirclePotential`,
  `Proofs/Sec11/ClosureScales/RootedShiftProfile`, `Proposed/DuplantierMillerSheffield`.
