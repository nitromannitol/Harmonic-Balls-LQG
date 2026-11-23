# Locally uniform convergence of the clock without insertion, every 0 < γ < 2

The dyadic Liouville clocks of the whole-plane field without insertion,
`I_n(t) = ∫₀ᵗ ε_n^{γ²/2} e^{γ h_{ε_n}(B_s)} ds` with `ε_n = 2^{-(n+1)}` and `h` normalized by `h_1(0) = 0`,
converge locally uniformly on `[0, ∞)` to a continuous, nonnegative and nondecreasing limit, almost surely
under the field-path product law, from every start and for every `0 < γ < 2`.
`ae_exists_locally_uniform_limit_clock_nonpositive` (`LQGClockExteriorClockConvergence.lean:213`) proves this
for nonpositive insertions and `γ² < 2` only; at `α = 0` the range `2 ≤ γ² < 4` is new.

## What is proved

All files are in `HarmonicBalls/Proofs/Potential/`; the new file is `LQGClockZeroInsertionConvergence.lean`.

| Result | Declaration | Line |
|---|---|---|
| half-disc clocks at countably many path-dependent horizons in `[0, 1]`, `0 < γ < 2` | `ae_brownian_field_tendsto_countable_halfDisc_clocks_zero` | `:58` |
| dyadic half-disc cell moments under the product law, `γ² < 4` | `exists_halfDisc_dyadic_cell_moment_zero` | `:120` |
| uniform convergence of the half-disc clocks on `[0, 1]` | `ae_tendstoUniformlyOn_halfDisc_clock_zero` | `:176` |
| the same after every integer time shift | `ae_exists_uniform_limit_integer_shift_halfDisc_clock_zero` | `:295` |
| locally uniform convergence of the half-disc clocks on `[0, ∞)` | `ae_exists_locally_uniform_limit_halfDisc_clock_zero` | `:363` |
| locally uniform convergence of the full clocks, `0 < γ < 2` | `ae_exists_locally_uniform_limit_clock_zero` | `:430` |
| the same for `0 < γ`, `2 ≤ γ²`, `γ < 2` and fields on `Type`, as one proposition | `forall_ae_exists_locally_uniform_limit_clock_zero_of_two_le_sq` | `:449` |

## Route

1. Fixed horizons. For almost every path and almost every field, the occupation integrals of the half-disc
   indicator against `ε^{γ²/2} e^{γ(h_ε - h_1(0))}` converge along the dyadic scales at countably many
   path-dependent horizons (`ae_brownian_field_tendsto_countable_occupation_tests`,
   `LQGClockCountableOccupationTests.lean:15`, any bounded test function supported in a disc, `0 < γ < 2`).
   Without insertion the half-disc density is the plain density, so the test function is the indicator.
2. Cell moments. For `γ² < 4`, `E[(I^in(t+h) - I^in(t))^p] ≤ C h^a` with `p ∈ (1, 2]`,
   `a = p - γ² p (p - 1)/4 > 1`, for all smoothing radii in `(0, 1/2]`, starts, `t ≥ 0` and `h ∈ (0, 1]`
   (`exists_halfDisc_cell_rpow_le`, `LQGClockAnnularScaleRecursion.lean:1704`), turned into the product-law
   form by Tonelli's inequality `lintegral_prod_le`.
3. The dyadic cell moment criterion (`ae_exists_continuousOn_monotoneOn_limit_of_dyadic_cell_moment`,
   `LQGClockDyadicCellMomentUniform.lean:186`) gives uniform convergence on `[0, 1]` with a continuous limit.
4. The Markov property at integer times (`ae_prod_planarBrownianMotion_shift_of_forall_ae`,
   `LQGClockAnnularStoppedUniformLimit.lean:190`) gives every unit block, hence `[0, ∞)`.
5. The exterior clocks and the gluing are those of the existing theorem:
   `ae_exists_locally_uniform_limit_clock_of_halfDisc_of_cell_moment` (`LQGClockExteriorClockHorizon.lean:351`)
   with `exists_exterior_dyadic_cell_moment` (`LQGClockAnnularScaleRecursion.lean:2367`, `γ² < 4`, any insertion).

## Departures from the source

Berestycki (arXiv:1301.3356, Section 2) proves the convergence of the clock for the Dirichlet field of a domain,
for a fixed time, quenched in the path, by a second moment for small `γ` and a thick-point truncation for every
`γ < 2`, and continuity of the limit from the absence of atoms. Here the field is the whole-plane field with
`h_1(0) = 0`. The localization is the one already in the repository: the fixed-horizon step is quenched in the
path, for the field recentred at the circle average `h_R(0)` on a disc of radius `R` containing the support of
the test function, by a field-expectation bound of the thick-point truncation along the occupation measure of
the path (`ae_brownian_submeasure_field_increment_le_of_radius`, `LQGClockBrownianRadiusIncrement.lean:18`),
summable along the dyadic scales, and then returns to the normalization `h_1(0) = 0`. Continuity of the limit
and uniformity in time come from the annealed dyadic cell moments (a Kolmogorov criterion) rather than from
the absence of atoms, and the passage from `[0, 1]` to `[0, ∞)` from the Markov property at integer times.

No existing statement is changed.
