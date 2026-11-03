# Lemma 6.13 as printed is false (ESCALATIONS E16, GRAPH F6, correction [C15])

Lean certificate: `HarmonicBalls/Proofs/Counterexamples/Lemma6_13.lean`. No sorry, axioms: propext, Classical.choice,
Quot.sound.

Paper: `paper/lqg_harmonic_ball-corrected.tex` (line numbers below). Notation: `Λ_t = Λ^z_t = Λ_{B_1;z}(t)` is the
cluster (eq:non-co-set, 592), `v = v^z_t` the odometer (eq:limit-odometer, 596), `𝔸_{r₁,r₂}(x) = B_{r₂}(x) \ B̄_{r₁}(x)`
(eq:annulus, 334).

## 1. The printed statement

Lemma 6.13 (lemma:low-mass-implies-small-odometer, 1710-1726) makes these assumptions:

* `z ∈ B_1`, and an annulus `𝔸_{ρ/2,ρ}(x₀)` "not containing `z`" (1711).
* (VG-iii) (1152) holds with `a, b ∈ (0,1)`, `N₀ ≥ 200` and `C₃`.
* `{S_j, d⁺_j}` is the shell decomposition of Lemma 6.12 (1636-1672). `Λ̃_t` is a connected component of `Λ_t ∩ B_ρ(x₀)`.
* `K_j = a M_ρ(x₀) ε_j^{β⁻}` (eq:k-j-parameter, 1715), with `ε_j = 2^{-(N₀+j)}` (eq:def-epsilon-j, 1665).

It claims eq:low-mass-small-odometer (1719-1723) for each `j ≥ 0`:

> **Hypothesis.** `μ_h(Λ̃_t ∩ 𝔸_{3r,5r}(w)) ≤ K_j` for all `r > 0` and `w ∈ B_1` with `𝔸_{r,7r}(w) ⊂ 𝔸_{ρ/2,d⁺_j}(x₀)`.
>
> **Conclusion.** `sup_{Λ̃_t ∩ 𝔸_{ρ/2,d⁺_{j+1}}(x₀)} v ≤ b^{C' C₃ (N₀+j)} · sup_{Λ̃_t ∩ 𝔸_{ρ/2,d⁺_j}(x₀)} v`.

`C' > 0` is universal.

The pole `z = x₀` is allowed, since `x₀ ∉ 𝔸_{ρ/2,ρ}(x₀)` (Lean: `center_not_mem_annulus`).

The proof needs `v · 1_{Λ̃_t}` to be subharmonic on `B_ρ(x₀)` (1776-1777; maximum principle, 1779-1808). This fails if
`z ∈ B_ρ(x₀)`, because `Δv` has the atom `-t δ_z` (Lemma 3.2, 634-636).

**Correction [C15]:** assume `B̄_ρ(x₀) ⊂ B_1 \ {z}`, as in Lemma 6.11 (1574), the only consumer. This excludes
`z = x₀` (Lean: `not_closedBall_subset_diff_center`). The corrected statement is `LowMassSmallOdometerStmt`
(Draft/Section6.lean). It is not touched by this counterexample.

**Lean form of the printed statement.** `LowMassSmallOdometerPrintedStmt` is `LowMassSmallOdometerStmt` with two changes:

* "`B̄_ρ(x₀) ⊂ B_1 \ {z}`" becomes "`z ∉ 𝔸_{ρ/2,ρ}(x₀)` and `B̄_ρ(x₀) ⊂ B_1`".
* The extra hypothesis `B̄_ρ(x₀) ⊂ B_1` is implicit in the paper. It only weakens the statement, so the refutation
  covers the literal print a fortiori.

The other readings are those of the Draft: (VG-iii) as `VeryGoodCriterionThree`, the odometer with value `+∞` at the
pole (`odometerExt`), suprema in `[0,∞]`, and one a.s. event for all parameters.

## 2. The counterexample (choice of parameters)

`z = x₀ = 0`, `ρ = 1/2`, `j = 0`, `b = 1/2`, and the universal `C₃` of Lemma 6.7. With `p = 1/2`, Lemma 6.7 gives
`a ∈ (0,1)`, `C₁^±, C₂^± > 0` and `N₁`. Set `N₀ = max(N₁, 200)`. The refutation works for every `C' > 0`; in fact the
printed conclusion fails for every factor `c < 1` in place of `b^{C' C₃ (N₀+j)}`. So it does not depend on `C'`,
`C₃`, `N₀`, or on the proof gap G23 (`b^{N-1}` versus `b^N`).

## 3. Deterministic step A: the odometer is bounded and positive off the pole (any measure `μ`)

**A1. Upper bound** (`odometer_le_of_le_dist`). For `x ∈ B_1` with `|x − z| ≥ δ > 0` and `t ≥ 0`:
`v(x) ≤ t (4π)⁻¹ δ⁻²`.

* By eq:limit-odometer (596), `v = v_{B_1;z}(t) + t G_{B_1}(z,·)`, where `v_{B_1;z}(t)` is the least supersolution.
* The least supersolution is `≤ 0`: the zero function is a supersolution (599; Defs `leastSupersolution_nonpos`).
* The explicit Green function of the ball (471-477; c1, `greenFunction_ball`, `greenBall_le` in
  Proofs/Potential/GreenBall.lean) gives
  `G_{B_1}(z,x) ≤ (4π)⁻¹ (1−|z|²)(1−|x|²)/|z−x|² ≤ (4π)⁻¹ δ⁻²`.

**A2. Positivity** (Defs `mem_cluster_iff`). For `x ∈ Λ_t` with `x ≠ z`: `v(x) > 0`.

## 4. Deterministic step B: a collar configuration violates the printed implication (any measure `μ`)

This is `exists_component_printed_fails`. Fix `z ∈ B_1`, `t ≥ 0`, `ρ > 0`, `j`, `K`, and `R ≤ min(ρ, d⁺_j, d⁺_{j+1})`.
Assume the collar configuration:

* **(C1)** `Λ_t ⊆ B_R(z)`;
* **(C2)** there is `y ∈ Λ_t` with `|y − z| > ρ/2`;
* **(C3)** `μ(Λ_t ∩ 𝔸_{ρ/2,ρ}(z)) ≤ K`.

Let `Λ̃` be the connected component of `y` in `Λ_t ∩ B_ρ(z)`. Then:

**(i) The hypothesis holds with `K`.** Take `x ∈ Λ̃ ∩ 𝔸_{3r,5r}(w)` with `𝔸_{r,7r}(w) ⊆ 𝔸_{ρ/2,d⁺_j}(z)`.
* Then `x ∈ 𝔸_{r,7r}(w)`, so `|x − z| > ρ/2`.
* By (C1), `|x − z| < R ≤ ρ`.
* So `Λ̃ ∩ 𝔸_{3r,5r}(w) ⊆ Λ_t ∩ 𝔸_{ρ/2,ρ}(z)`, and (C3) gives the bound.

**(ii) The conclusion fails for every `c < 1`.**
* Both index sets equal `S = {x ∈ Λ̃ : |x − z| > ρ/2}`. Indeed `Λ̃ ⊆ B_R(z)`, and `R ≤ d⁺_j` and `R ≤ d⁺_{j+1}`.
* Let `X = sup_S v`. Then `X ≥ v(y) > 0` by A2, since `y ∈ S` and `y ≠ z`.
* `X ≤ t (4π)⁻¹ (ρ/2)⁻² < ∞` by A1 with `δ = ρ/2`. This uses `S ⊆ B_1` and that `S` avoids the pole.
* So `X ≤ c X` with `0 < X < ∞` and `c < 1`, which is impossible.

## 5. Deterministic step C: the collar configuration occurs (`exists_collar_time`)

Fix a locally finite `μ`, `z`, `ρ > 0` with `B̄_{ρ/2}(z) ⊆ B_1`, `K > 0` and `R > ρ/2`. Write `B = B̄_{ρ/2}(z)`.
Assume the following deterministic properties of `t ↦ Λ_t`, `t > 0`:

* **(H1)** `Λ_t` is open (Lemma 3.2, 627).
* **(H2)** `Λ_s ⊆ Λ_t` for `s ≤ t` (Lemma 3.3, 644).
* **(H3)** `μ(Λ_t) ≤ t`, with equality if `closure Λ_t ⊆ B_1`. This is Lemma 3.4 (649) with Prop 5.3 (836), which gives
  `μ(∂Λ_t) = 0`.
* **(H4)** `⋂_{t>0} closure Λ_t = {z}` (eq:contains-origin, Prop 5.2, 824-828).
* **(H5)** Right-continuity (eq:continuity, Prop 5.2, 829-833): for `t > 0` and all small `ε`, there is `δ > 0` such
  that `closure Λ_{t'} ⊆ Λ_t + B_ε` for `t' ∈ [t, t+δ]`.
* **(H6)** `μ(U) > 0` for every nonempty open `U` (input I1; stated informally at 134-135).

Then some `t > 0` satisfies (C1) and (C2) with this `R`, and (C3) with this `K`. Proof:

1. **Clusters grow by at most their mass.** If `0 < s ≤ t` and `Λ_s ⊆ B`, then `μ(Λ_t \ Λ_s) ≤ t − s`.
   * `closure Λ_s ⊆ B ⊆ B_1`, so (H3) gives `μ(Λ_s) = s`.
   * Hence `μ(Λ_t \ Λ_s) = μ(Λ_t) − μ(Λ_s) ≤ t − s`, using (H2) and the measurability from (H1).
2. **Set-up.** Let `T = {t > 0 : Λ_t ⊆ B}`.
   * `T ≠ ∅`. The sets `closure Λ_t` are closed and decrease as `t ↓ 0` (H2). By (H4) their intersection is `{z}`,
     which misses the compact set `B̄_1 \ B_{ρ/2}(z)`. By compactness, some `closure Λ_{t₀}` misses it as well. Since
     `Λ_{t₀} ⊆ B_1`, this gives `Λ_{t₀} ⊆ B_{ρ/2}(z)`.
   * `T` is bounded. For `t ∈ T`, `t = μ(Λ_t) ≤ μ(B) < ∞` by (H3) and local finiteness.
   * Let `τ = sup T`. Then `τ > 0`. By (H2), `Λ_s ⊆ B` for every `s ∈ (0, τ)`.
3. **No jump at `τ`: `Λ_τ ⊆ B`.**
   * By step 1, `μ(Λ_τ \ B) ≤ μ(Λ_τ \ Λ_s) ≤ τ − s` for every `s ∈ (0, τ)`, so `μ(Λ_τ \ B) = 0`.
   * `Λ_τ \ B` is open by (H1). By (H6) it is therefore empty.
4. **Choice of `t`.** Take `ε < min(ε₀, R − ρ/2)` in (H5) at `τ`, and `κ > 0` with `κ ≤ K`. Pick `t ∈ (τ, τ+δ]` and
   `s ∈ (0, τ)` with `t − s ≤ κ`. Then:
   * **(C1)** `Λ_t ⊆ Λ_τ + B_ε ⊆ B + B_ε ⊆ B_{ρ/2+ε}(z) ⊆ B_R(z)`.
   * **(C2)** `t > τ = sup T`, so `t ∉ T`, so `Λ_t ⊄ B`.
   * **(C3)** `Λ_t ∩ 𝔸_{ρ/2,ρ}(z) ⊆ Λ_t \ Λ_s`, since `Λ_s ⊆ B`. By step 1 its mass is `≤ t − s ≤ κ ≤ K`.

## 6. Assembly (`not_lowMassSmallOdometerPrintedStmt`)

Hypotheses: the Draft statements `ClusterOpenLaplacianStmt` (3.2), `ClusterMonotoneStmt` (3.3),
`ClusterConservationOfMassStmt` (3.4), `ClusterContinuityStmt` (5.2), `ClusterBoundaryMeasureZeroStmt` (5.3),
`LQGMeasureFullSupportStmt` (I1) and `VeryGoodAnnulusProbabilityStmt` (6.7). In addition, one whole-plane GFF with
its LQG measure `μ_h` (`IsWholePlaneGFF`, `IsLQGMeasureOfField`) for some `γ ∈ (0,2)`, `α₀ < Q`, `β⁻ > (2+γ)²/2`.

1. **Lemma 6.7 applies at `x₀ = 0`.** Its hypothesis `dist(𝔸_{ρ/4,2ρ}(0), 0) = ρ/4 ≥ ρ/100` holds. So
   `P[Ē_ρ(0)ᶜ] ≤ 1/2`.
2. **Fix a typical `ω`.** Take `ω` in the intersection of the a.s. events of the printed statement, of 3.2-3.4, 5.2,
   5.3 and I1, and of local finiteness (`IsLQGLimit`). Assume also `ω ∈ Ē_ρ(0)`.
3. **`K_0 > 0`.** (VG-i) (1147) with `C₁⁻ > 0` gives `M_ρ(0) > 0`, so `K_0 = a M_ρ(0) 2^{-N₀β⁻} > 0`.
4. **The collar configuration occurs.** Step C applies with `z = 0` and `R = 3ρ/5`:
   * (H1)-(H6) are the a.s. statements at `z = 0 ∈ B_{1/2}`;
   * `B̄_{1/4} ⊆ B_1`.
5. **Step B applies.** It needs `3ρ/5 ≤ min(ρ, d⁺_0, d⁺_1)`. Here `d⁺_0 ≥ 3ρ/4` and
   `d⁺_1 ≥ 3ρ/4 − 32ρ 2^{-50} ≥ 3ρ/5` (Lean: `three_fifths_le_shellOuterRadius`; shell radii 1643-1665).
   * It yields `t > 0` and a component `Λ̃` of `Λ^0_t ∩ B_ρ(0)` satisfying the printed hypothesis for `j = 0`.
   * For this `Λ̃`, the printed conclusion fails with `c = (1/2)^{C' C₃ N₀} < 1`.
   * The printed statement, applied at `ω`, asserts that conclusion. So `ω ∉ Ē_ρ(0)`.
6. **Contradiction.** Step 5 shows `P[Ē_ρ(0)] = 0` (outer measure), hence `1 = P[Ω] ≤ 0 + P[Ē_ρ(0)ᶜ] ≤ 1/2`.

## 7. What is certified, and what remains

**Certified in Lean (no sorry, standard axioms):**

* Steps A and B hold for every measure `μ`.
* Step C holds for every locally finite `μ`.
* The implication of §6: (Draft Lemmas 3.2, 3.3, 3.4, 6.7, Props 5.2, 5.3, I1, existence of `h^ℂ` and `μ_h`)
  ⇒ ¬ (printed Lemma 6.13).

**Not certified (inputs to the implication):** the paper results used as hypotheses are not yet proved in Lean.

* **Probabilistic input.** Only Lemma 6.7 is used for a positive-probability statement: `P[Ē_ρ(0)] ≥ 1/2` for the
  parameters above. Of the event, only (VG-i) (giving `M_ρ > 0`) and (VG-iii) are used.
* **Almost-sure regularity.** Lemmas 3.2-3.4, Props 5.2 and 5.3, and I1 are used pathwise, for one realization.
* **Existence.** The existence of the whole-plane GFF and of `μ_h` (Duplantier-Sheffield) is a hypothesis.

**Reading dependencies.** None affects `z = 0`:

* Prop 5.2 is read with `Λ_t + B_ε` instead of the printed `Λ_t + B_ε(z)`. These coincide for `z = 0`.
* Prop 5.3 is read with hypothesis `closure Λ_t ⊆ B_1` (GRAPH S1).
* Lemma 6.7 is read with the complement bound (G16) and with `C₃` chosen before `b` (G28).

**A second defect of the print** (GRAPH F6). Lemma 6.9 is applied on annuli `𝔸_{3r,5r}(w) ⊆ B_1`, which the printed
hypothesis does not guarantee. [C15] (`B̄_ρ(x₀) ⊂ B_1 \ {z}`) repairs both defects.
