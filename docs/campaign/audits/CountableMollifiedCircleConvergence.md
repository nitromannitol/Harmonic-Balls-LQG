# Audit: CountableMollifiedCircleConvergence (task sec11-countable-mollified-circle-convergence)

Module: `HarmonicBalls/Proofs/Sec11/ClosureScales/CountableMollifiedCircleConvergence.lean` (new, about 330 lines).
Source: r10 written proof, `notes/sec11-proof/sec11-proof-r10.tex` lines 1304-1312 (for each coded circle a deterministic
sequence `ε_j ↓ 0` with squared `L²` error at most `2^(-4j)`; Chebyshev and Borel-Cantelli; intersection over the
countably many circles). Audited in `AUDIT-r9.md` 931-957 and reaffirmed in `AUDIT-r10.md` 110.

Imports: `CountableCircleDecoder` (for `CircleDomain`), `MollifiedCircleGaussianL2` (for `IsWholePlaneGFF` consumers,
`isWholePlaneGFF_circleMollifier_L2`, `tendsto_wholePlaneGFFCov_pairing_pairing`, `tendsto_wholePlaneGFFCov_pairing_circle`,
`integral_sq_sub_eq_covariance`), and Mathlib. No declaration of this file uses an External or Proposed input.

Import closure: 16 repo modules and no non-Mathlib external package. `HarmonicBalls.Proposed.DuplantierMillerSheffield`
is in the closure transitively, through `MollifiedLogCircleLimit`, which `MollifiedCircleGaussianL2` already imports
(pre-existing). No declaration here refers to it.

Credit: none needed. The word "Lattice" occurs in `MollifiedContinuousCircleLimit.lean:30` only as the negative statement
"no literature input or Lattice-Probability declaration is used"; no Lattice-Probability module is in the closure.

## Hypotheses

- `IsLiteralMollifier rho` (`MollifiedCircleGaussianL2.lean:43`): the five r10 conditions on `ρ`. Nothing else on `ρ`.
- `q : I → CircleDomain` with `[Countable I]`, where `CircleDomain = {p : ℝ × ℂ // 0 < p.1}`
  (`CountableCircleDecoder.lean:31`). Coded circle `i` is `r_i = (q i).val.1`, `w_i = (q i).val.2`.
- The field: `Ω : Type u`, `[MeasurableSpace Ω]`, `P : Measure Ω` (no probability or finiteness assumption), `hC`,
  `hcirc`, and `hGFF : IsWholePlaneGFF P hC hcirc` (`Defs/GFF.lean:93`). The structure carries the measurability of
  every pairing with a test function and of every circle average of positive radius.
- No convergence, covariance-rate, decoder, representation, E56, metric, moment or density premise.

## Declarations

- `circleErr rho r w e`: the covariance expression
  `wholePlaneGFFCov (pairing φ_e) (pairing φ_e) - 2 * wholePlaneGFFCov (pairing φ_e) (circle r w) + wholePlaneGFFCov (circle r w) (circle r w)`.
  It contains no `Ω`, so it is the same number for every Gaussian field.
- `circleLevel n = (1/16)^n` and `two_zpow_neg_four_mul : (2:ℝ)^(-(4 * (n:ℤ))) = circleLevel n`. The main theorem is
  stated with the zpow `2^(-4n)` as in the task; the conversion is this lemma.
- `integral_sq_circleMollifier_sub_eq`: for `IsWholePlaneGFF` and `e > 0`,
  `∫ (hC ξ φ_e - hcirc ξ r w)^2 dP = circleErr rho r w e`. This is the identity `hid` inside
  `isWholePlaneGFF_circleMollifier_L2`, exported as a lemma with the same proof.
- `tendsto_circleErr`: `circleErr → 0` on `𝓝[>] 0`, from `tendsto_wholePlaneGFFCov_pairing_pairing` (`:450`) and
  `tendsto_wholePlaneGFFCov_pairing_circle` (`:469`).
- `exists_circleErr_lt`: for `c > 0`, a radius `δ ∈ (0,1]` with `circleErr < c` on `(0,δ)` (`tendsto_order`,
  `mem_nhdsGT_iff_exists_Ioo_subset`).
- `circleThreshold hρ q i n`: `Classical.choose` of `exists_circleErr_lt` at level `circleLevel n` for the circle `q i`.
- `circlePrefixMin f n`: the running minimum `min (f 0) ⋯ (f n)` by recursion; `circlePrefixMin_pos`, `circlePrefixMin_le`.
- `countableCircleScale hρ q i n := circlePrefixMin (circleThreshold hρ q i) n / (n + 2)`: the scales. They are fixed
  before any `Ω, P, hC, hcirc` are introduced; the only proof argument is `hρ`, a `Prop`, so the value depends on `ρ, q, i, n`.
- `countableCircleScale_pos`, `countableCircleScale_lt_threshold`, `countableCircleScale_strictAnti`,
  `countableCircleScale_tendsto`, and the bundle `countableCircleScale_spec` (positivity, `StrictAnti`, `Tendsto … (𝓝[>] 0)`).
- `measure_sq_ge_le_ofReal` (Chebyshev, lintegral form): if `∫ Y² ≤ (1/16)^n` then `P{(1/4)^n ≤ Y²} ≤ ofReal((1/4)^n)`,
  that is `P{|Y| ≥ 2^(-n)} ≤ 2^(-2n)`. It uses `mul_meas_ge_le_lintegral₀` and `ofReal_integral_eq_lintegral_ofReal`,
  so no finiteness of `P` is needed. (`ProbabilityTheory.meas_ge_le_variance_div_sq` requires `IsFiniteMeasure` and was not used.)
- `measure_limsup_sq_eq_zero`: the first Borel-Cantelli lemma (`measure_limsup_atTop_eq_zero`) with the summable bound
  `∑ (1/4)^n < ∞` (`summable_geometric_of_lt_one`, `ENNReal.ofReal_tsum_of_nonneg`).
- `measure_iUnion_limsup_sq`: the union over the countable index `I` is null (`measure_iUnion_null_iff`) and measurable
  (`MeasurableSet.measurableSet_limsup`, `MeasurableSet.iUnion`).
- `tendsto_zero_of_not_mem_limsup`: if `ξ` lies in the `limsup` of the events `{(1/4)^n ≤ g_n(·)²}` then `g_n(ξ) → 0`
  (`not_frequently`, squeeze by `(1/2)^n`, `abs_lt_of_sq_lt_sq`).
- `circleDev hC hcirc rho r w e ξ := hC ξ (circleMollifier rho w r e) - hcirc ξ r w`; `measurable_circleDev` from the
  two measurability fields of `IsWholePlaneGFF`; `integral_sq_countableCircleScale_le`: `∫ (circleDev …)² dP ≤ 2^(-4n)` at the scales.
- **Main theorem `countableCircleScale_ae_convergence`**, for every `Ω : Type u` with `P`, `hC`, `hcirc`, `hGFF`:
  (1) `∀ i n, ∫ (hC ξ (circleMollifier rho (q i).val.2 (q i).val.1 (countableCircleScale hρ q i n)) - hcirc ξ (q i).val.1 (q i).val.2)^2 ∂P ≤ (2:ℝ)^(-(4*(n:ℤ)))`;
  (2) `∃ S, MeasurableSet S ∧ P Sᶜ = 0 ∧ ∀ ξ ∈ S, ∀ i, Tendsto (fun n => hC ξ (circleMollifier … (countableCircleScale hρ q i n))) atTop (𝓝 (hcirc ξ (q i).val.1 (q i).val.2))`.
  The witness is `S = (⋃ i, limsup_n {(1/4)^n ≤ circleDev_{i,n}²})ᶜ`.

## Route notes (fidelity)

- The bad events `{(1/4)^n ≤ Y²}` are `{2^(-n) ≤ |Y|}`. Chebyshev bounds them by `2^(-2n)`, which is summable, so their
  `limsup` is null. Outside the `limsup`, `|Y_n| < 2^(-n)` eventually, so `Y_n → 0`.
- The scale choice uses only the deterministic limit of `circleErr`, never a realization. For each `n` the threshold is
  `δ_{i,n}`; `m_n = min_{k ≤ n} δ_{i,k}` is positive and non-increasing; `ε_n = m_n/(n+2) < m_n ≤ δ_n`, so
  `circleErr(ε_n) < 2^(-4n)`. Strict decrease: `ε_{n+1} ≤ m_n/(n+3) < m_n/(n+2) = ε_n`. Limit: `ε_n ≤ 1/(n+1)` since `m_n ≤ 1`.
- No rate is asserted for small `e`; the sequence is selected from the proved limit.
- No density assumption is used, and no convergence, decoder or representation premise.
- The event `S` is measurable because each event in the union is measurable, using only the measurability fields of
  `IsWholePlaneGFF`. The conull property comes from the null union.

## Checks

- `lc` OK. `lb` BUILD OK for `HarmonicBalls.Proofs.Sec11.ClosureScales.CountableMollifiedCircleConvergence` (rebuilt after
  the final edit). The `lc` log has no warnings (`-DwarningAsError=true`).
- Printed axioms, from a scratch file outside the repository (`/tmp/z3-axcheck/AxCheck.lean`), for the main theorem, the
  bundle `countableCircleScale_spec` and the other declarations: exactly `propext, Classical.choice, Quot.sound`.
- Raw and comment-stripped scans for `sorry|axiom|admit|native_decide|maxHeartbeats|opaque|unsafe|implemented_by|extern`: 0 hits.
- No name collision: `circleErr`, `circleLevel`, `circleThreshold`, `circlePrefixMin`, `countableCircleScale`, `circleDev`
  and the lemma names are not declared elsewhere in `HarmonicBalls`.
