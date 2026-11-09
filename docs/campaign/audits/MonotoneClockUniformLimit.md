# Monotone clock uniform limit (audit)

Task: `ncs1-lbm-monotone-clock-uniform-limit` (worker z3, EFFORT max). Owned: `HarmonicBalls/Proofs/LBM/MonotoneClockUniformLimit.lean` (145 lines, new) and this audit.

## Source

- `notes/wpn-steps4/steps4-final.tex`, Section 6, lines 1997-2026; the estimate is displayed at lines 2003-2022. The file is not in the repository. Fleet copy: `/home/nitro/paper-fleets/hb/notes/wpn-steps4/steps4-final.tex`, sha256 `f9da848c8ad8179d8fd94795b7bfbdf198d7e8aefd38c72c89788a56acdba932` (checked).
- Displayed estimate (source 2003-2022): for a rational partition `0 = q_0 < ... < q_N = T` of mesh at most `δ` and `q_i ≤ t ≤ q_{i+1}`,
  `|C(t) - a(t)| ≤ max_ℓ |C(q_ℓ) - a(q_ℓ)| + sup{|a(u) - a(v)| : u, v ∈ [0,T], |u - v| ≤ δ}`.
  The source then lets k → ∞, refines the partition, and uses uniform continuity of `a` to kill the last term.
- The source states this for integer `T > 0`. The Lean statement covers every real `T ≥ 0` (grid window `[0, T + 1]`).

## Lean declarations (exact statements)

1. `HarmonicBalls.MonotoneClockUniformLimit.abs_sub_le_max_add_oscillation` (line 36):
   `{cx ct cy ax am ay : ℝ} (h₁ : cx ≤ ct) (h₂ : ct ≤ cy) (h₃ : ax ≤ am) (h₄ : am ≤ ay) : |ct - am| ≤ max |cx - ax| |cy - ay| + (ay - ax)`.
   This is the source's finite-partition bound, with the maximum over the grid reduced to the two endpoints of the cell that contains `t`.

2. `HarmonicBalls.MonotoneClockUniformLimit.monotone_clock_uniform_limit` (line 50), with hypotheses
   - `C : ℕ → ℝ → ℝ`, `a : ℝ → ℝ`;
   - `hC : ∀ n, MonotoneOn (C n) (Ici 0)`;
   - `ha : ContinuousOn a (Ici 0)`, `ha_mono : MonotoneOn a (Ici 0)`;
   - `hlim : ∀ q : ℚ, 0 ≤ q → Tendsto (fun n => C n (q : ℝ)) atTop (𝓝 (a (q : ℝ)))`;

   and conclusion
   `∀ T : ℝ, 0 ≤ T → ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) T, |C n t - a t| < ε`.

## Quantifier audit

- Task text: each `C n` monotone on `Ici 0`; `a` continuous and monotone on `Ici 0`; if `C n q → a q` for every nonnegative rational `q`, then for every `T ≥ 0` and `ε > 0`, eventually in `n`, `|C n t - a t| < ε` for all `t ∈ Icc 0 T`. The Lean statement matches this term by term.
- Index `n ∈ ℕ` along `atTop`; time `t ∈ ℝ`; rationals `q : ℚ` with `0 ≤ q`, cast to `ℝ`.
- Added hypotheses: none. No uniform-convergence, clock-continuity, inverse-continuity or stochastic hypothesis is used.
- `0 ≤ T` is not used by the proof (for `T < 0` the conclusion is vacuous). The binder is named `_hT` and kept because the task states the quantifier.
- `T = 0`: the window is `[0, 1]`; the cell of `t = 0` is `[0, 1/s]` with left endpoint `0`. The same argument applies, with no special case.
- Endpoints: each `t ∈ [0, T]` lies in a cell `x ≤ t < y` with `x = ⌊t s⌋₊ / s` and `y = (⌊t s⌋₊ + 1) / s`. Both `t = 0` and `t = T` are covered, since the argument is for all `t` in the closed interval. Both grid endpoints lie in the finite index range `Finset.range (M0 + 2)`.
- The conclusion is the strict bound `< ε` for every `t ∈ Icc 0 T`. The proof gives `< 2ε/3 < ε`.

## Route

1. Heine-Cantor: `a` is uniformly continuous on `[0, T + 1]` (`IsCompact.uniformContinuousOn_of_continuous`, `Mathlib/Topology/UniformSpace/HeineCantor.lean:49`; `Metric.uniformContinuousOn_iff`, `Mathlib/Topology/MetricSpace/Pseudo/Defs.lean:762`), at tolerance `ε/3`, with modulus `δ`.
2. Mesh `1/s < δ` with `s = m + 1` (`exists_nat_one_div_lt`, `Mathlib/Algebra/Order/Archimedean/Basic.lean:214`). Grid points `q_j = j/(m+1)` are nonnegative rationals.
3. Finitely many indices `j < M0 + 2`, where `(T + 1) s ≤ M0`. For each `j`, `Metric.tendsto_nhds` (`Pseudo/Defs.lean:891`) gives `∀ᶠ n, |C n q_j - a q_j| < ε/3`. `Filter.eventually_all_finset` (`Mathlib/Order/Filter/Finite.lean:258`) combines the finitely many.
4. For `t ∈ [0, T]`, put `i = ⌊t s⌋₊`, so `x = i/s ≤ t < y = (i+1)/s` (`Nat.floor_le`, `Nat.lt_floor_add_one`, `Mathlib/Algebra/Order/Floor/Semiring.lean:47, 63`). Here `x, y ∈ [0, T + 1]` and `i, i + 1 < M0 + 2`.
5. Cell estimate (item 1) with monotone `C n` and monotone `a`: `|C n t - a t| ≤ max(|C n x - a x|, |C n y - a y|) + (a y - a x)`.
6. Cell oscillation: `|a y - a x| < ε/3` by uniform continuity, since `|y - x| = 1/s < δ`. With both grid errors `< ε/3`, the bound is `< 2ε/3 < ε`.

## Mathlib and package search (search first)

- Dini's theorem (`Mathlib/Topology/UniformSpace/Dini.lean`, lemmas at lines 54-135) assumes continuous approximants and pointwise convergence at every point of the domain. The clocks here are only monotone and converge only on the nonnegative rationals, so Dini does not apply directly. The rational-partition argument (the source's step) is used instead.
- Mathlib's `Monotone.*tendsto_atTop` lemmas concern limits along filters, not uniform convergence.
- `.lake/packages/MarkovProcess` and `.lake/packages/elliptic_regularity`: a grep for `Monotone` matched only killed-process and gluing files. Those were identified by file name only; none was read.

## Checks

- `lc`: CHECK OK, log `052506-1348290` (`-DwarningAsError=true`).
- `lb HarmonicBalls.Proofs.LBM.MonotoneClockUniformLimit`: BUILD OK, log `052533-1397206`.
- Axioms (untracked probe `scratch/z3probe/MCAxioms.lean`, log `052540-1412123`): both declarations depend only on `[propext, Classical.choice, Quot.sound]`.
- Source scan (grep): no `sorry`, `admit`, `native_decide`, `maxHeartbeats`, `unsafe`, `extern`, `axiom` or `set_option`.
- Imports: Mathlib only. No Bonanno or lattice-probability code, and no Draft, Defs, External or Proposed inputs. No credit line is needed.
- Only owned paths are committed. The root `HarmonicBalls.lean` and the consumers are not edited.

## Consumer (not wired in this task)

- Consumer: the first conjunct of the frozen `GreenPotentialLiouvilleHolderStmt` (`Draft/Section2.lean:161-169`), via `IsLQGClock` (`Defs/LBM.lean:89-93`).
- This lemma supplies only the deterministic uniform convergence of the released construction. Still separate and not done here: stochastic martingale clock construction, joint measurability, supplied-clock identification, factor2 expected-exit identity, and the final Hölder assembly. Proposition 2.5 remains Lean-pending.
