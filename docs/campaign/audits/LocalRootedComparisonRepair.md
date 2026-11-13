# Local rooted comparison for Lemma 8.2

Task `local-rooted-comparison-mathematical-repair`, 2026-11-06. This is a source-level repair and an exact proposed interface, not a Lean theorem or a new literature input. It does not establish the missing joint laws or close Lemma 8.2.

## Sources and scope

The [corrected paper, Lemmas 8.1–8.2, PDF pp. 41–42](https://arxiv.org/pdf/2208.11795#page=41), uses a root weighted by the ordinary whole-plane LQG measure, then compares locally to the field with a γ-log insertion. [DMS Lemma A.10, whole-plane paragraph, PDF p. 184](https://arxiv.org/pdf/1409.7055v4#page=184), states the mass-weighted sampling description modulo constants; obtaining the marked cylinder identity and matching its approximation to this repository are still source/formalization obligations. [Miller–Sheffield Proposition 2.9, PDF p. 49](https://arxiv.org/pdf/1302.4738v2#page=49), supplies finite-energy GFF shift equivalence. Localize a smooth shift by a compactly supported cutoff. Existing `WholePlaneSmoothShift.lean:112` proves the local mean-zero pairing-law implication; `RootedLogarithmicShift.lean:59` gives the root-dependent logarithmic version. These are field laws, not joint laws of the raw LQG measures.

Fix `0 < γ < 2`, `α₀ < Q`, and an admissible `β`, `ζ > 0`, `b ∈ (0,1)`. Let `H` be the circle-average-one normalized whole-plane GFF, `h = H − α₀ log|·|`, `μ = μ_h`, and `λ = μ_H`. Weyl scaling gives `λ(dz) = |z|^(α₀γ) μ(dz)` away from 0. Let `B = B_1(0)`, `M = λ(B)`; `0 < M < ∞` almost surely. The conditional root law is `λ|B / M`, not the mass-biased field law. For any nonnegative marked observable `F`, its expectation is `E[∫_B F(h,z) λ(dz)/M]`. The unnormalized bind is `E[∫_B F(h,z) λ(dz)]`, with total mass `π` under the DMS normalization. Since `M` is positive finite, normalized and unnormalized marked laws are mutually absolutely continuous; division by π instead produces the mass-biased probability, not the conditional-root probability. For the desired a.e. conclusion one direction of domination suffices.

On the marked field carrier the DMS insertion is `G_z(x) = H(x) − γ log|x−z| + γ log max(|x|,1)`. For `z ∈ B`, its unit-circle average is zero: the circle mean of `log|e^{it}−z|` and the correction both vanish. The inserted representative of **h** is `G_z − α₀ log|x|`; omitting the latter changes the local measure. On a smaller ball it is a smooth perturbation, not a global one.

## Actual local observation and an exact replacement obligation

For each integer `j ≥ 1`, set `r_j = 1/(16j)` and `D_j = {z : 3r_j < |z| and |z| < 1 − 3r_j}`. These sets cover `B \ {0}`. On `D_j`, `B_{2r_j}(z)` avoids both 0 and the unit circle, so `−α₀ log|z+u|` is smooth in `B_{2r_j}(0)` and the DMS correction vanishes there. Let `T_z(x)=x−z`. The **actual raw recentered restricted measure** is

`L_j(ω,z) = (T_z)_*( μ(ω)|B_{r_j}(z) )`.

It is a measure supported in `B_{r_j}(0)`, not the global translated μ. Use the measurable carrier `C × Measure C`; on the full-support locally finite locus define `N_j(η) = η / η(B_{r_j/2}(0))`, with any fixed measurable default off that locus. This removes precisely the random positive additive-constant factor. Define

`O_j(ω,z) = (z, N_j(L_j(ω,z)))`,
`V_j(z,ω) = (z, N_j(ν(ω)|B_{r_j}(0)))`,

where `ν = μ_{H−γ log|·|}` uses a whole-plane GFF normalized at 0. No measure is reconstructed by definition of `O_j`. Both maps must be proved measurable (or replaced by measurable versions with a.e. equality for the relevant laws). Let `κ` be the kernel `λ|B/M` and let `ρ_j = volume.restrict D_j`. The concrete Lean-shaped local comparison is, for every `j`,

```lean
(P ⊗ₘ κ).restrict (Prod.snd ⁻¹' D j) |>.map (O j) ≪
  (ρ j).prod P |>.map (V j)
```

Here `O j : Ω × ℂ → ℂ × Measure ℂ` and `V j : ℂ × Ω → ℂ × Measure ℂ` are the actual maps above, and all the kernel, restriction, normalization and measurability hypotheses are explicit. This is a proposed conditional theorem statement, not an available declaration or a staged input. For Lean syntax without pipeline ambiguity, write `(Measure.map (O j) ((P ⊗ₘ κ).restrict (Prod.snd ⁻¹' D j))) ≪ (Measure.map (V j) ((ρ j).prod P))`. The right side has finite total mass `volume(D_j)`, while the left has at most mass one. A projective carrier is essential to this particular route: local pairing observations are modulo constants, and raw unnormalized masses are not determined by them. No arbitrary shift into the original Ω, global measure comparison, or assumed common decoder appears in this type.

The source-level route to this obligation has three separate steps:

1. The marked DMS identity, plus Weyl scaling, gives domination of the actual observed left law by the observation of `μ_{G_z−α₀ log|·|}` under `dz P(dH)` on `D_j`. This step must include **joint field–measure** identification, not merely equality of the field marginal, and the normalization by `M` is handled before pushing forward. In particular, the DMS theorem as currently staged does not itself provide this map equality.
2. For each fixed z, translate by `T_z`. The modulo-constants law of `H(z+·)` is that of `H`, and the extra shift is `−α₀ log|z+·|` on the buffered ball. A smooth cutoff and Cameron–Martin yield local field domination by `H−γ log|·|`. Joint measurability and Fubini give domination with z retained. The translation changes the pinned additive constant randomly; `N_j` removes its effect.
3. To push the field law through to the **actual** `N_j(L_j)`, prove a measurable local GMC observation that simultaneously identifies these normalized restrictions under both laws, or prove the joint field/measure domination directly. Locality and Weyl scaling motivate this bridge but the existing field-only theorem does not provide it. This is a genuine unresolved Lean/source-matching leaf; do not simply postulate a common decoder as already constructed. `GFFSamplewiseRepresentation.md` records the separate raw random-test/version issue. An alternative joint circle-average law may bypass it.

## Countable tail event and exact transfer

Fix the parameters chosen by the singular frequency theorem, including its actual adjusted `a` and `C₃`; do not assume the constants are unchanged under a phase repair. For each `n`, evaluate `G_n(z) ∩ Ē_{2⁻ⁿ}(z)` from `T_{−z*}η` where `η` is the second component. This is local when `2·2⁻ⁿ < r_j`: the mass and Green tests lie within `B_{2ρ}(z)`; in (VG-iii), `k ≥ 1` gives `r ≤ ρ/7` and the good-annulus region is within `(1+5/7)ρ < 2ρ` of z. Multiplying by a finite positive constant preserves all these predicates. Their precise countable indexing uses n, the dyadic ε index, the integer lattice indices, and the finite set of admissible powers of 7; the good-annulus predicate still quantifies over Borel sets. Its measurable/countable-witness reduction is a separate issue: `GoodEventWitnesses.lean:75` assumes such a witness family, and `GoodEventMeasurable.lean:28` assumes measurability of the unit good event. Thus countable scale indexing alone does not prove the event measurable.

Let `F_j` be the set of `(z,η)` for which, for all sufficiently large N, at least `(1−ζ)N` indices in `[N+1,2N]` satisfy these predicates. This is a countable union/intersection of finite count conditions **once** the individual predicates are measurable. For each fixed `j`, the finitely many n with `2·2⁻ⁿ ≥ r_j` never enter blocks `[N+1,2N]` for large N. Consequently `F_j` is determined by the local observation, and it has exactly the same eventual-frequency truth value for the original μ at z. With `V_j`-a.e. membership and the displayed domination, `O_j`-a.e. membership follows. Integrating the normalized kernel gives the conclusion for `λ`-a.e. z; since `λ` and μ are equivalent on `B \ {0}` and μ is atomless, it holds for μ-a.e. z in B. The countable cover over j handles every nonzero root.

Fixed-radius local absolute continuity is sufficient for this *single tail event*; no uniform Radon–Nikodym bound as radius shrinks is needed. It does not imply that individual high-probability events at changing scales retain quantitative bounds, nor does pointwise AC alone identify the frequency event as measurable from a fixed restriction. For example, on ℕ, `Q({n})=2^{-n}` and `P({n})` proportional to `1/n²` are equivalent, yet `Q({n≥k})/P({n≥k}) → 0`; there is no uniform probability ratio. The transfer uses reference probability one for the whole countable tail event, not scale-by-scale bounds.

There is an additional phase obligation. The printed lattice in (VG-iii) is anchored at the original origin, as preserved by `Defs/Annuli.lean:85` (G21); after recentering at z it is shifted by `−z`. The singular theorem for the origin lattice alone does not imply the frequency assertion for this varying phase. `RootedUniformPhaseCertificate.lean:23` supplies a conditional uniform-phase certificate with an explicitly reduced `a`, but its reference-measure interpretation and rooted-measure identification remain separate. One must prove the actual `(volume|D_j) × P`-a.e. `V_j ∈ F_j` with the same constants used on the left, via that uniform-phase result and its hypotheses, or give another phase-sensitive argument. This is not a claim that the paper's result is false.

## Unresolved leaves and handoff

* Establish the marked DMS formula and its simultaneous joint LQG measure/Weyl interpretation for the repository's `IsWholePlaneGFF` and `IsLQGMeasureOfField` representations; cite DMS A.10 above. The existing `RootedObservedBindLaw.lean:19,71` only handles bind and normalized-law measure theory.
* Prove the displayed local observed-measure domination, including measurable actual restrictions, projective normalization, local GMC identification and translation modulo constants; field-only local domination is already available.
* Prove measurability of the actual good-annulus predicate (or an adequate measurable completion/witness theorem) and the phase-sensitive reference tail event with matching constants. `RootedJointObservedFrequency.lean:19` shows one conditional joint-observation route, but assumes its joint domination and unit good-event measurability.
* Assemble the deterministic locality, positivity, atomlessness and Fubini steps above in Lean. The mathematical transfer conditional on these leaves is explicit; no numbered result is claimed closed.
