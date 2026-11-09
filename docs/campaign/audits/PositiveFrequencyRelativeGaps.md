# Audit: positive-frequency good scales have relative gaps tending to one

TASK: z3-z4q-positive-frequency-good-scale-relative-gaps (operator, 2026-11-09)
FILE: HarmonicBalls/Proofs/MeasureTheory/PositiveFrequencyRelativeGaps.lean (new, 162 lines)
NAMESPACE: HarmonicBalls.PositiveFrequencyRelativeGaps

## Scope

Only the deterministic implication of r10 `l:r10-paths` (`notes/sec11-proof/sec11-proof-r10.tex`,
lines 491–510; sha256 3365b58f…, fleet copy, not in the repository). It is not the singular metric,
not the ergodic input (Walters, Theorem 1.14), and not a consumer wiring. Pfeffer Def 1.6 and
Prop 4.6 are neither used nor imported.

## Declarations and statements (exact)

- `IsGoodPos S n := 0 < n ∧ n ∈ S` (line 37).
- `goodCount S N := (S ∩ Icc 1 N).ncard`, that is `#{1 ≤ n ≤ N : n ∈ S}` (line 41).
- `goodEnum S k := Nat.nth (IsGoodPos S) k`, the zero-indexed increasing enumeration of the good
  positive indices (line 45). The paper's `nᵢ` (i ≥ 1) equals `goodEnum S (i - 1)`.
- `goodCount_eq_count` (line 49): `goodCount S N = Nat.count (IsGoodPos S) (N + 1)`.
- `goodSet_infinite` (line 68): `0 < p`, `(goodCount S N : ℝ) / N → p` ⊢ `(Set.ofPred (IsGoodPos S)).Infinite`.
- `goodCount_goodEnum` (line 89): enumeration identity `goodCount S (goodEnum S k) = k + 1`, proved from
  `Nat.count` and `Nat.count_nth_of_infinite`, not assumed.
- `positive_frequency_relative_gaps` (line 100). Hypotheses: `S : Set ℕ`, `hp : 0 < p`,
  `hfreq : Tendsto (fun N => (goodCount S N : ℝ) / N) atTop (𝓝 p)`. Conclusions, conjoined:
  1. `StrictMono (goodEnum S)`;
  2. `Set.range (goodEnum S) = {n | IsGoodPos S n}`;
  3. `∀ k, goodCount S (goodEnum S k) = k + 1`;
  4. `(k + 1) / goodEnum S k → p`;
  5. `k / goodEnum S k → p` (the paper's `i/nᵢ → p`, after the index shift);
  6. `goodEnum S k / k → p⁻¹` (the paper's `nᵢ/i → 1/p`);
  7. `goodEnum S (k + 1) / goodEnum S k → 1`.

No bound on absolute gaps is assumed. The only hypotheses are `p > 0` and the counting frequency,
which is the premise of the implication itself, not its conclusion.

## Route

1. `goodCount` is `Set.ncard` of `S ∩ Icc 1 N`; it equals `Nat.count` over `[0, N]` of the
   predicate `IsGoodPos S`, since `0` is excluded by positivity.
2. Positive frequency forces an infinite good set: a finite set gives a bounded count, so the
   quotient tends to `0`, and `p ≤ 0` contradicts `hp`.
3. `Nat.nth_strictMono`, `Nat.nth_mem_of_infinite`, `Nat.range_nth_of_infinite` give the enumeration.
4. `(hfreq.comp hgrow)` along `goodEnum` with the count identity gives `(k+1)/nₖ → p`.
5. `1/nₖ → 0` (since `k ≤ nₖ → ∞`) gives `k/nₖ → p` by subtraction.
6. `Tendsto.inv₀` (with `p ≠ 0`) gives `nₖ/k → p⁻¹`, using `inv_div`.
7. Consecutive ratio: `nₖ₊₁/nₖ = (nₖ₊₁/(k+2)) · ((k+1)/nₖ) · ((k+2)/(k+1))`. The factors tend to
   `p⁻¹`, `p` and `1` (the last via `1 + 1/(k+1)`), so the product tends to `1`.

Zero indices: `0` is never enumerated, every `nₖ > 0`, and all denominators in the ratios are
positive. Shifting the index by one leaves all limits unchanged.

## Mathlib and reuse search

- Used: `Nat.nth`, `Nat.nth_strictMono`, `Nat.nth_mem_of_infinite`, `Nat.range_nth_of_infinite`,
  `Nat.count_succ`, `Nat.count_nth_of_infinite`, `Nat.count_eq_card_filter_range`,
  `Set.ncard_le_ncard`, `Set.ncard_coe_finset`, `tendsto_natCast_atTop_atTop`,
  `tendsto_one_div_add_atTop_nhds_zero_nat`, `tendsto_add_atTop_nat`, `Filter.Tendsto.inv₀`,
  `inv_div`, `le_of_tendsto_of_tendsto'`.
- Mathlib has no natural-density API (no `density`/`natDensity` definition found), so the frequency
  is stated directly on `Set.ncard`.
- Repository grep: no existing enumeration or relative-gap declaration. The Sec8 `PositiveThreshold*`
  and `LQGFrequencyFromRatios` files are ergodic/probabilistic consumers, not overlapping.
- Lattice-Probability: no declaration consumed. No credit line to Leonardo Bonanno is required by this
  file; the credit rule applies only to code that consumes that package.

## Checks

- `lc` OK 070419-2838464 (after the final edits); `lb` OK 070430-2855597 (module built).
- Axioms (`scratch/z3probe/PFRGAxioms.lean`, untracked, not committed): all four declarations print
  exactly `propext`, `Classical.choice`, `Quot.sound`.
- Scan of the new file for `sorry`, `admit`, `axiom`, `native_decide`, `maxHeartbeats`, `set_option`,
  `Proposed`, `External`, `Bonanno`, `Lattice`: no matches.

## Notes for the operator

- The statement uses the zero-indexed `Nat.nth`; the paper's 1-indexed `nᵢ` is `goodEnum S (i - 1)`.
  Both (k+1)/nₖ and k/nₖ are stated, so either reading of "i/nᵢ → p" is covered.
- The frequency hypothesis `p > 0` is what the ergodic step must supply in the consumer; that
  supply (Walters 1.14 applied to `1_{Y ≤ M}`) is not formalized here and is not used.
- No consumer is wired (r10 `l:r10-paths` and task h1 consume the relative gaps separately).
