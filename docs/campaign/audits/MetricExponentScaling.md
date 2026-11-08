# Metric exponent scaling: Pfeffer's background scaling (1.10) and the deterministic comparison

Task `pfeffer-weak-metric-exponent-scaling-bridge` (worker z6, operator05:00 metric issue). Credit: Leonardo Bonanno,
whose whole-plane GFF construction underlies the field carriers used in both Lean files below.

**Status.** The source check of Pfeffer's Definition 1.6 and Proposition 1.9 is done (section 1). The published
background scaling is staged as an explicit Prop, pending the operator's source-check (section 2). The deterministic
exponent comparison is proved at its exact asymptotic type (section 3). The weak-metric class, the tightness at exact
normalizers and the physical parameter correspondence are **not** proved; they are named targets (section 4). The
operator05:00 verdict is unchanged: eight measure/existence Props faithful, FieldAxioms citation chain incomplete,
not a false-Prop verdict. No file in `Proposed/LQG.lean`, `Defs/`, `Draft/`, `External/` or the paper was edited.

## 1. Source check: Pfeffer, arXiv:2104.04020v3

Read from the arXiv PDF (`pdftotext`, page numbers from the PDF page breaks, checked 2026-11-08).

* Section 1 definitions, p. 5. Length space: the `D`-distance is the infimum of the `D`-lengths of all paths.
  Internal metric (1.5). `D`-distance across `A`: the distance between the inner and outer boundaries of `A`.
  `D`-distance around `A`: the infimum of the `D`-distances (read: `D`-lengths, deviation 3) of closed paths separating
  the inner and outer boundaries. `h_r(0)`: the average of `h` over `∂B_r(0)`.
* (1.4), p. 4: `a_ε = ε^{1-ξQ+o_ε(1)}` as `ε → 0`, with `Q = Q(ξ) > 0` from Ding–Gwynne (DG18 Theorem 1.5,
  DG20 Proposition 1.1). `ξ ↦ Q(ξ)` is continuous and nonincreasing. (Only the value of `Q` enters the staged Prop.)
* Definition 1.6, p. 6. A weak LQG metric with parameter `ξ > 0` is a measurable map `h ↦ D_h` from `𝒟'(ℂ)` to lower
  semicontinuous metrics on `ℂ`, such that for `h` a whole-plane GFF plus a continuous function:
  I. `(ℂ, D_h)` is a length space, a.s.
  II. Locality: for each deterministic open `U`, `D_h(·,·;U)` is determined a.s. by `h|_U`.
  III. For each continuous `f`, a.s. `D_{h+f} = e^{ξf} · D_h`.
  IV. For each deterministic `z`, a.s. `D_h(· + z) = D_h(· + z, · + z)`.
  V. For each `r > 0` there is a deterministic `c_r` such that, for a fixed annulus `A`, the laws of
  `c_r^{-1} e^{-ξ h_r(0)} D(across rA)` and `c_r^{-1} e^{-ξ h_r(0)} D(around rA)` and their inverses, for `r > 0`, are
  tight. Moreover there is `Λ > 1` with `Λ^{-1} δ^Λ ≤ c_{δr}/c_r ≤ Λ δ^{-Λ}` for `δ ∈ (0,1)` and `r ∈ ℚ ∩ (0,∞)`, (1.7).
* Proposition 1.9, p. 8, equation (1.10): for `r > 0` the scaling constants `c_r` of Axiom V satisfy
  `c_{δr}/c_r = δ^{ξQ + o_δ(1)}` as `δ → 0`, at a rate uniform over all `r > 0`, with `Q = Q(ξ)` from (1.4).

Audit step 3 of `PROPOSED-LQG-SOURCE-CHECK-20261108.md` quotes (1.10) as `c_(δr)/c_r = δ^(ξQ(ξ)+o(1))`. That matches the
printed statement, with one refinement that the staged Prop records: the `o(1)` is in `δ` alone and uniform in `r`.

## 2. Staged Prop (`HarmonicBalls/Proposed/PfefferMetricScaling.lean`)

| Lean declaration | Printed source |
|---|---|
| `pfefferCircleAverage f r z` | average of `f` over `∂B_r(z)` (`h_r(0)` for `h = h^ℂ + f`), p. 5 |
| `pfefferAcross D z₀ a b`, `PfefferSeparates P z₀ a b`, `pfefferAround D z₀ a b` | across and around `A(z₀; a, b)`, p. 5 |
| `PfefferIsLscMetric D`, `PfefferIsLengthSpace D` | codomain and Axiom I, pp. 5–6 |
| `pfefferField hC f`, `pfefferNormalization ξ hcirc f c r` | `h = h^ℂ + f`; `c_r^{-1} e^{-ξ h_r(0)}` |
| `PfefferTightAcrossScales P X` | tightness of the laws of `X_r` and `X_r^{-1}` over `r > 0`, p. 6 |
| `PfefferAxiomVScale P ξ 𝔇 hC hcirc f c` | Axiom V and (1.7), p. 6 |
| `PfefferWeakAxioms P ξ 𝔇 hC hcirc f` | Axioms I–V for one field instance, p. 6 |
| `IsPfefferWeakLQGMetric ξ 𝔇` | Definition 1.6 (with `0 < ξ`), p. 6 |
| `PfefferBackgroundScaling ξ Q` | Proposition 1.9, (1.10), p. 8 |

`PfefferBackgroundScaling ξ Q` says: for every weak LQG metric `𝔇` with parameter `ξ`, every instance `(Ω, P, hC, hcirc, f)`
of a whole-plane GFF plus a continuous function, and every family `c` satisfying Axiom V for that instance, for every
`η > 0`, eventually as `δ → 0` (filter `𝓝[>] 0`), for all `r > 0`:
`|log (c (δr) / c r) / log δ - ξ Q| ≤ η`.

Null-set quantifier order follows the printed text: Axiom III is `∀ g continuous, ∀ᵐ ω` (not `∀ᵐ ω, ∀ g`), Axiom IV is
`∀ z, ∀ᵐ ω`, and Axiom II is `∀ U, ∃ G, ∀ᵐ ω`. No simultaneous-representation claim is made.

Deviations, to be decided by the operator (also in the header of the file):
1. Metrics are real-valued, as in `IsLQGMetric`. Printed internal metrics may be infinite; `ℝ≥0∞` covers the
   internal and length quantities only.
2. Measurability of `h ↦ D_h` is pointwise (`Measurable[distributionMeasurableSpace]`), not measurability into the space
   of lower semicontinuous metrics.
3. "The `D`-distances of closed paths" is read as the `D`-lengths of closed paths. "Separate the inner and outer
   boundaries" is read as: every path in `ℂ` from the inner circle to the outer circle meets the range of the closed path.
4. Axiom V is read as universal in the annulus `A(z₀; a, b)`, with the constants `c_r` chosen first, as printed.
5. The random continuous function `f` is random, as in `IsLQGMetric`.
6. The codomain (lsc metric) is imposed a.s. on the field instances only.

Direction of each deviation relative to the printed Definition 1.6 (the Prop quantifies over the class):
* Deviations 2 and 6 enlarge the class, so the staged Prop claims (1.10) for more metrics than Pfeffer does. They
  need an operator decision before admission (pointwise measurability in 2; codomain only on field instances in 6).
* Deviations 1, 4 and 5 narrow the class or the quantifier, so the staged Prop is weaker than the printed one.
* Deviation 3 changes the quantity tested in Axiom V, not the class's direction.
None of these is resolved silently; each is listed for the operator.

## 3. Proved (`HarmonicBalls/Proofs/GFF/MetricExponentScaling.lean`)

* `log_power_ratio_div_log`: if `c x = x ^ s` for `x > 0`, then `log (c (δr) / c r) / log δ = s` for `0 < δ < 1`, `r > 0`.
* `exponent_eq_of_asymptotic_power`: if `c x = x ^ s` for `x > 0` and the quotient in (1.10) is within `η` of `a` for all
  small `δ` and all `r > 0`, then `s = a`. The argument takes one `δ ∈ (0,1)` from the eventual statement and uses only
  `r = 1`. So the uniformity in `r` is not needed for the implication.
* `background_charge_eq_lqgQ_of_power_scaling`: if `ξ > 0`, `PfefferBackgroundScaling ξ Q`, `𝔇` is a weak LQG metric with
  parameter `ξ` on an instance, `c` satisfies Axiom V for that instance, and `c x = x ^ (ξ · lqgQ γ)` exactly for `x > 0`,
  then `Q = lqgQ γ`.

Axioms: `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for all three declarations (checked with a
scratch file outside the repository). Both modules pass `lc` (with `warningAsError`) and `lb`. A code scan finds no
`sorry`, `admit`, `native_decide`, `axiom`, `opaque`, `unsafe` or `maxHeartbeats`.

## 4. Remaining targets (named; none is assumed)

* **T1, weak-metric class.** For the LQG metric `𝔇` with `IsLQGMetric γ ξ 𝔇` (`Defs/LQGMetric.lean`), prove
  `IsPfefferWeakLQGMetric ξ 𝔇`. This needs a Lean proof of Axioms I–V for every whole-plane GFF plus continuous `f`,
  including the codomain condition and the tightness in Axiom V. The repository's `IsLQGMetric` Axioms I–IV are
  not sufficient on their own: they do not contain Axiom V, and the translation clause in `IsLQGMetric` is the exact
  scaling `coordChange`, not Pfeffer's Axiom IV alone.
* **T2, exact normalizers.** Prove `PfefferAxiomVScale P ξ 𝔇 hC hcirc f (fun r => r ^ (ξ * lqgQ γ))` for the LQG metric.
  Audit step 2 says this follows from exact coordinate change and GFF scale invariance, with normalized variables of
  fixed law. That argument is not yet written in the repository, so it is a target, not a claim.
* **T3, physical parameter correspondence.** Identify the Pfeffer background charge `Q(ξ)` of (1.4) for the Weyl exponent
  `ξ = γ/d_γ` with `lqgQ γ`. The deterministic step (section 3) gives `Q = lqgQ γ` once (1.10) and T1–T2 hold. The
  parameter algebra in `Proofs/GFF/BackgroundChargeParameter.lean` (`gamma_eq_of_lqgQ_eq`, `xi_eq_of_lqgQ_eq_of_mul_lqgQ_eq`)
  is the consumer of that identity, and is not re-proved here.
* **T4, source-check.** `PfefferBackgroundScaling` and the definitions it uses are new inputs. They need the operator's
  source-check before any module consumes them as a hypothesis outside this file.

Consequence for the chain in `PROPOSED-LQG-SOURCE-CHECK-20261108.md`: step 3 (1.10) is now a staged input with a Lean
type. Step 2 (weak class and exact normalizers) and step 4 (`ξ = γ/d_γ`) remain open. So the `LQGMetricFieldAxioms`
citation chain is still incomplete, and this audit does not reclassify the Prop as false.

## 5. Coordination with the h3 physical-exponent audit

`docs/campaign/audits/PhysicalGraphExponentSourceAudit.md` (commit `5faa1bb`) treats a physical graph exponent for a
fixed-pair statement, with Leonardo Bonanno credited for the formalization it uses. It introduces no declaration and no
literature input. The present audit concerns the LQG background charge `Q(ξ)` in (1.10). The two exponents are different
objects. Neither audit reconciles the other. Any identification between them belongs to T3 and is not claimed here.

## 6. Reading choices to confirm

* "Fixed annulus" in Axiom V is read as universal (deviation 4).
* "D-distances of closed paths" is read as `D`-lengths (deviation 3).
* The Prop uses `0 < ξ` inside `IsPfefferWeakLQGMetric`, from "for each `ξ > 0`" (p. 6).
* The proof uses `r = 1`, which is a valid instance of the uniform statement.
