# Proposition 2.6: the clock of reflected Liouville Brownian motion in a square

Proposition 2.6 (`ReflectedLBMHeatKernelStmt`, `HarmonicBalls/Draft/Section2.lean:225`) asks for a finite, jointly
continuous, strictly positive heat kernel of reflected Liouville Brownian motion in a square `K = closedSquare a L`
with respect to `μ_h`. The printed proof (corrected source, lines 563-567) cites Kigami 2019, Theorem 13.1, with input
Lemma 2.4, and a scaling argument. Kigami's theorem concerns the time change of reflected Brownian motion in the unit
square by the additive functional whose Revuz measure is a given measure. This note records the proof that the LQG
clock of reflected Brownian motion in `K`, read in the unit square, is such an additive functional for the normalized
LQG measure, so that the cited theorem applies, and the proof of the strict positivity of the kernel from the cited
theorem of Keller–Lenz–Vogt–Wojciechowski. Proposition 2.6 follows from the two cited statements
(`reflectedLBMHeatKernelStmt_of_kigami_of_klvw`, `ReflectedLBMHeatKernelProposition.lean`), and the two instances of
them that its proof uses are proved, so that Proposition 2.6 holds with no cited input
(`reflectedLBMHeatKernelStmt_holds`, `ReflectedLBMHeatKernelProved.lean`; section "Proposition 2.6 with no cited
input" below).

## What is proved

All files are in `HarmonicBalls/Proofs/Potential/`. `K₀ = closedSquare 0 1`, `Q_x` is reflected Brownian motion in
`K₀` from `x` (`reflectedPlanarBrownianMotion 0 1`), `ν = μ_h(K)⁻¹ ((z - a)/L)_* (μ_h|_K)`
(`unitSquareNormalizedMeasure`).

| Result | Declaration | File |
|---|---|---|
| Lebesgue measure on `K₀` is invariant: `∫_{K₀} E_x ψ(b_s) dx = ∫_{K₀} ψ` | `lintegral_lintegral_reflectedPlanarBrownianMotion_eval` | `ReflectedLebesgueInvariance.lean` |
| Markov property at fixed times; `E_x[I²] ≤ 2 U E_x[I]` for `I = ∫_{(0,1]} g(b_s) ds` | `lintegral_reflected_eval_mul_shift`, `lintegral_windowOccupation_sq_le` | `ReflectedBrownianMarkov.lean` |
| Folded Gaussian kernel `≤ (2√2 S)² p_{2r}`; uniform Green bound from ball bounds | `lintegral_planarGaussian_squareFold_le`, `lintegral_windowOccupation_reflected_le` | `ReflectedGreenPotentialBound.lean` |
| Revuz formula `∫ g d(Rev A) = ∫_{K₀} dx E_x ∫_{(0,1]} g(b_s) dA_s` | `lintegral_unitSquareRevuzMeasure_of_isUnitSquarePCAF` | `ReflectedRevuzFormula.lean` |
| Revuz measure of a limit of clocks with densities | `unitSquareRevuzMeasure_eq_of_density_clocks` | `ReflectedRevuzIdentification.lean` |
| `μ_h(frontier K) = 0` almost surely for a fixed square, every insertion | `IsWholePlaneGFF.ae_lqgMeasure_frontier_closedSquare_eq_zero_of_pos` | `ReflectedLQGRevuzMeasure.lean` |
| Clock identification: `Rev A = ν` almost surely | `ae_exists_isUnitSquarePCAF_revuz_eq` | `ReflectedLQGRevuzMeasure.lean` |
| Proposition 2.6 from the cited theorem and positivity | `reflectedLBMHeatKernel_of_kigami_of_positivity` | `ReflectedLQGRevuzMeasure.lean` |
| Symmetry of every jointly continuous heat kernel of the time change | `isLBMHeatKernel_symm` | `ReflectedHeatKernelSymmetry.lean` |
| Proposition 2.6 from the cited theorems of Kigami and KLVW alone | `reflectedLBMHeatKernelStmt_of_kigami_of_klvw` | `ReflectedLBMHeatKernelProposition.lean` |
| The instances of Kigami Thm 13.1 and KLVW Thm A.2 that the proof uses | `kigamiLQGInstanceStmt`, `klvwHeatKernelInstanceStmt` | `ReflectedLBMHeatKernelProved.lean` |
| Proposition 2.6 with no cited input | `reflectedLBMHeatKernelStmt_holds` | `ReflectedLBMHeatKernelProved.lean` |

All print [propext, Classical.choice, Quot.sound] (`checks/AxiomGate.lean`, log 1125-060247-2846846; rows 9 and 10, log 1125-143543-2746961; the last two rows, log 1125-221630-17367).

## Route

The literature route identifies the clock through the strict Revuz correspondence
(Fukushima–Oshima–Takeda 2011, Theorems 5.1.7 and 6.2.1) and the uniqueness of the clock of killed Brownian motion
on discs inside the square. The Lean proof computes the Revuz measure of the clock directly, as the IDLA-Mated-CRT
formalization does for planar Brownian motion (MatedCRT/FirstPass/Derived/OccupationBallLawAssembly.lean and the
files it imports, ported with credit):

1. The circle-average approximations of the clock, read in `K₀`, are clocks with the continuous densities
   `ρ_k(z) = L² μ_h(K)⁻¹ ε_k^{γ²/2} e^{γ h_{ε_k}(a + L z)}` (`transportedClockApprox_eq_integral`), and converge to the
   clock uniformly on `[0, 1]` in probability from every start (definition of the LQG clock).
2. Under `P = ∫_{K₀} Q_x dx` their occupation integrals `X_k = ∫_{(0,1]} f ρ_k(b_s) ds` converge in measure to the
   occupation integral of the clock, and have second moments bounded uniformly in `k`: the folded Gaussian kernel is
   dominated by the sum over the reflections (the Neumann kernel of the square is a sum of reflected Gaussian
   kernels), and the approximations have uniform power ball bounds (Lemma 2.4 for the approximations,
   `IsWholePlaneGFF.ae_singular_approximant_ball_power_all_disks`). Vitali's theorem gives `E X_k → E X`.
3. `E X_k = ∫_{K₀} f ρ_k` by the invariance of Lebesgue measure, and `E X = ∫ f d(Rev A)` by the Revuz formula.
4. `∫_{K₀} f ρ_k → ∫ f dν` by the vague convergence of the approximations, the change of variables `z = (y - a)/L`
   and `μ_h(frontier K) = 0`. The last is the first-moment argument of
   `HarmonicBalls/Proofs/Sec11/SingularCompactNull.lean` away from the insertion, and the clipped-ball volume bound at
   the insertion when it lies on the frontier.

## Departures from the cited sources

* The clock is identified by computing its Revuz measure, not through the Revuz correspondence and the uniqueness of
  the clock of killed Brownian motion. No Dirichlet form is constructed.
* The Revuz measure is taken with respect to Lebesgue measure on `K₀` over the time window `(0, 1]`, with the raw
  additive functional of `IsUnitSquarePCAF` (per-start null sets), as in the cited statement
  `kigamiHeatKernelContinuityCited`.

## The Chapman–Kolmogorov identity

`IsLBMHeatKernel.chapmanKolmogorov` (`HarmonicBalls/Proofs/Potential/ReflectedHeatKernelChapmanKolmogorov.lean`):
for every additive functional `A` of reflected Brownian motion in `K₀`, every finite `ν` charging every relative ball
of `K₀` with no atoms in `K₀`, and every heat kernel `p` of the time change by `A` with respect to `ν` that is jointly
continuous on `(0, ∞) × K₀ × K₀`, `p(s + t, x, y) = ∫_{K₀} p(s, x, z) p(t, z, y) dν(z)` for `s, t > 0`, `x, y ∈ K₀`.

1. Strong Markov property of planar Brownian motion at optional times (Revuz–Yor 1999, Theorem III.3.7), ported
   with credit from IDLA-Mated-CRT; it passes to reflected Brownian motion through the fold, which maps `F⁰_t` into
   `F⁰_t`, commutes with the shifts, and leaves the law of reflected Brownian motion unchanged when applied to the
   start.
2. Additivity of the clock at optional times and of its right inverse, `τ_{r+v} = τ_r + τ̄_v ∘ θ_{τ_r}`
   (Revuz–Yor 1999, Chapter X, Section 1 and Proposition V.1.1; Fukushima–Oshima–Takeda 2011, Section A.3), ported
   with credit from IDLA-Mated-CRT; the clock is required to be unbounded only from the start considered.
3. Semigroup property of the time change: `Q_x[b_{τ_{s+t}} ∈ S] = E_x[Q_{b_{τ_s}}[b_{τ_t} ∈ S]]`
   (Fukushima–Oshima–Takeda 2011, Section 6.2).
4. The clock is unbounded from every `x ∈ K₀`: on `{A_∞ ≤ t}` the right inverse `τ_t` is `0`, so the time-changed
   point at time `t` is `x`, which has probability `∫_{{x}} p(t, x, ·) dν = 0`.
5. Tonelli's theorem gives the identity `ν`-almost everywhere in `y`; continuity and full support give it
   everywhere (`eqOn_of_forall_setLIntegral_eq`, the argument of `IsLBMHeatKernel.eq_of_continuousOn`).

Departure: `A_∞ = ∞` is usually obtained from the Paley–Zygmund inequality and the Markov property at integer
times; here it follows from the existence of the heat kernel and the absence of atoms of `ν` (step 4).

## The transition semigroup and positivity

`reflectedLBMHeatKernel_of_kigami_of_klvw` (`HarmonicBalls/Proofs/Potential/ReflectedLQGHeatKernelPositivity.lean`)
derives Proposition 2.6 from `kigamiHeatKernelContinuityCited`, `klvwPositivityImprovingCited` and two hypotheses
on the unit-square kernel `p'` of the clock of the square: `hsymm` (`p'(t, x, y) = p'(t, y, x)`) and `hirr` (the
transition semigroup `heatKernelL2Semigroup ν p'` is irreducible, [KLVW] Definition A.1).

1. The clock is positive at positive times from every interior start: while the planar path stays in the square,
   the folded path is the planar path, so the approximating clocks agree and so do their limits, and the planar clock
   of Proposition 2.5 is strictly increasing from `0` (`ReflectedClockStartPositivity.lean`). The frontier of the
   square is `μ_h`-null, so this holds from `ν`-almost every start.
2. Integral operators with kernels continuous on `K₀ × K₀` act on `L²(ν)`; Schur's test bounds them, a symmetric
   kernel gives a symmetric operator, and a kernel given by the Chapman–Kolmogorov integral gives the composed
   operator (`HeatKernelL2Operator.lean`).
3. For a symmetric kernel, `T_t` (`T_0 = id`) is a semigroup of symmetric sub-Markov contractions; it is strongly
   continuous because the right inverse of the clock tends to `0` from `ν`-almost every start, so `T_t g → g`
   for bounded continuous `g`, and these are dense in `L²(ν)` (`ReflectedHeatKernelL2Semigroup.lean`).
4. By the cited KLVW Theorem A.2 an irreducible such semigroup is positivity improving, and
   `p'(t, x, y) = ∫ p'(t/3, x, z) (T_{t/3} p'(t/3, ·, y))(z) dν(z) > 0`.

## Symmetry and irreducibility

`reflectedLBMHeatKernelStmt_of_kigami_of_klvw` (`ReflectedLBMHeatKernelProposition.lean`) discharges `hsymm` and
`hirr`; Proposition 2.6 (`ReflectedLBMHeatKernelStmt`) then follows from `kigamiHeatKernelContinuityCited` and
`klvwPositivityImprovingCited` alone. Kigami 2019, Theorem 10.10 (strict positivity) is not used: its hypotheses
(an admissible measure, i.e. (8.1) and the measure-theoretic properties of the time change, and a heat kernel
controlled by rate functions) use the quasi-support and the time-changed Dirichlet form, which the repository does not
have. The direct route below uses the volume bounds (13.1) of `ν` only through its mass, full support, absence of
atoms and the upper ball bounds.

1. **The Neumann kernel.** The law of `b_s` under `Q_x` is `k_s(x, y) dy` on `K₀` with
   `k_s(x, y) = q_s(x₁, y₁) q_s(x₂, y₂)`, `q_s(u, v) = ∑_n (φ_s(v + 2n - u) + φ_s(2n - v - u))`; `k_s` is symmetric,
   jointly continuous on `(0, ∞) × K₀ × K₀` and, for `s ≤ 1`, dominated by a Gaussian of twice the variance
   (`ReflectedNeumannKernel.lean`, `squareNeumannKernel_le_heat`).
2. **The occupation identity from every start.** Under the Lebesgue start the mean occupation measure of
   `(s, b_s)` under `dA_s` is `ds ⊗ ν` (additivity, stationarity and the Revuz formula,
   `lebesgueOccupationMeasure_eq_prod`, `ReflectedClockOccupation.lean`); partitioning `(a, T]`, the Markov property at
   the partition times and dominated convergence give, for every `x ∈ K₀`,
   `E_x ∫ F(s, b_s) dA_s = ∫∫ F(s, y) k_s(x, y) ds ν(dy)` (`bind_pathOccupationMeasure_eq`,
   `ReflectedClockOccupationEveryStart.lean`). All occupation integrals are written in the time `u` of the time change.
3. **The resolvent identity.** With `G f(x) = E_x ∫_0^∞ e^{-β s} f(b_s) dA_s` and
   `U f(x) = E_x ∫_0^∞ e^{-c u - β τ_u} f(Y_u) du`, `U f + c U G f = G f` on `K₀`, by additivity of the clock at
   `τ_r` and the strong Markov property there (`clockResolvent_add_clockResolvent_clockGreen`,
   `ReflectedClockResolvent.lean`; Fukushima–Oshima–Takeda 2011, proof of Theorem 6.2.1).
4. **Symmetry of the resolvent.** By step 2, `G` has the symmetric kernel `∫_0^∞ e^{-β s} k_s ds` with respect to `ν`.
   `U(x, ·) ≤ G(x, ·)`, so for bounded `h ≥ 0` the measure `∫ h(x) U(x, ·) ν(dx)` has a density `U* h`; from step 3,
   `(I + c G) U* h = G h`, `U G h = G U* h`, and `U h = U* h` `ν`-almost everywhere once `G 1` is bounded on `K₀`
   (`lintegral_mul_clockResolvent_comm`, `ReflectedClockResolventSymmetry.lean`). `G 1` is bounded for `β > 0`:
   `E_y ∫_{(0,1]} dA ≤ L` uniformly by the Gaussian bound and the ball bounds (a Riesz potential estimate), and the
   Markov property at integer times gives `G 1 ≤ L ∑ e^{-β n}` (`exists_clockGreen_one_le`,
   `ReflectedClockGreenBound.lean`). Monotone convergence as `β ↓ 0` gives the symmetry of the resolvent
   `R_c f(x) = E_x ∫_0^∞ e^{-c u} f(Y_u) du` (`lintegral_mul_clockResolvent_zero_comm`).
5. **Symmetry of the kernel.** `⟨1_E, R_c 1_F⟩_ν = ∫_0^∞ e^{-c u} φ_{E,F}(u) du` with
   `φ_{E,F}(u) = ∫_{E ∩ K₀} ∫_{F ∩ K₀} p'(u, x, y) ν(dy) ν(dx)`, continuous and bounded on `(0, ∞)`. Uniqueness of the
   Laplace transform (`eqOn_Ioi_of_laplace_eq`, `LaplaceTransformUniqueness.lean`: under `x = e^{-u}` the moments of two
   finite measures on `[0, 1]` agree, and the Weierstrass approximation theorem identifies them) gives
   `φ_{E,F} = φ_{F,E}`, and continuity with full support of `ν` gives `p'(t, x, y) = p'(t, y, x)` on
   `(0, ∞) × K₀ × K₀` (`isLBMHeatKernel_symm`, `ReflectedHeatKernelSymmetry.lean`).
6. **Irreducibility.** For a symmetric kernel an invariant set `D` of intermediate mass would make
   `p'(t, z, z) = 0` at a point `z` common to the closed supports of `ν` on `D` and on `D^c`, which meet in the
   connected square; this contradicts Chapman–Kolmogorov, symmetry and unit row mass
   (`isIrreducibleSemigroup_heatKernelL2Semigroup`, `ReflectedHeatKernelIrreducible.lean`).

All print [propext, Classical.choice, Quot.sound] (`checks/AxiomGate.lean`, log 1125-143543-2746961).

## Proposition 2.6 with no cited input

The proof of Proposition 2.6 uses the cited theorems only through two instances, stated in the repository as
`KigamiLQGInstanceStmt` (`SquareClippedBallVolume.lean`) and `KLVWHeatKernelInstanceStmt`
(`ReflectedHeatKernelL2Semigroup.lean`); `reflectedLBMHeatKernelStmt_of_instances`
(`ReflectedLBMHeatKernelProposition.lean`) derives Proposition 2.6 from them. Both are proved
(`ReflectedLBMHeatKernelProved.lean`) by the following route: the centered Neumann
Green kernel of the square gives a continuous density of the time change from every start and for every version of
the clock, and its eigenfunction expansion gives strict positivity at every point. Here `A` is an additive
functional of reflected Brownian motion in `K₀` (`IsUnitSquarePCAF`) whose Revuz measure `ν` is a probability measure
carried by `K₀`, charging every relative ball, with `ν(B̄(y, r)) ≤ C r^β` (`IsUpperRegularSpeed`).

1. **Mixing of the Neumann kernel.** `k_s` satisfies Chapman–Kolmogorov at every point, `k_1 ≥ δ > 0` on `K₀ × K₀`,
   and `|k_s − 1| ≤ C e^{−cs}` for `s ≥ 1` (`exists_abs_neumannKernel_sub_one_le`, `ReflectedNeumannMixing.lean`).
2. **Unbounded clocks.** A clock with nonzero Revuz measure tends to infinity almost surely from every start
   (`ae_tendsto_atTop_of_isUnitSquarePCAF`, `ReflectedClockUnbounded.lean`).
3. **The centered Green kernel** `g̃(x, y) = ∫_0^∞ (k_s(x, y) − 1) ds`, bounded by `C(1 + |x − y|^{−θ})`, with rows
   continuous from `K₀` into `L²(ν)` (`exists_abs_centeredGreenKernel_le`, `continuousOn_greenRow`,
   `ReflectedCenteredGreenKernel.lean`).
4. **The centered Green operator** `G = QVQ` on `L²(ν)`, with `Q` the projection on mean zero and `V` the integral
   operator of `g̃`, is compact and symmetric (`ReflectedGreenOperator.lean`), and `⟨f, Gf⟩ ≥ 0` with equality
   only for `f = 0` on mean zero (`ReflectedGreenPositivity.lean`). The spectral
   theorem for compact self-adjoint operators gives a Hilbert basis `1, ϕ_i` with `Gϕ_i = μ_i ϕ_i`, `μ_i > 0`
   (`IsUpperRegularSpeed.exists_greenEigenbasis`, `ReflectedGreenSpectral.lean`).
5. **The resolvent identity.** For `f` bounded of mean zero, `R_c f + c R_c(Vf) = Vf` on `K₀` for the resolvent
   `R_c` of the time change `Y_u = b(A⁻¹(u))` from every start (`resolventReal_add_resolventReal_greenPotential`,
   `ReflectedCenteredResolvent.lean`; from the discounted Green kernels `g_β = g̃ + 1/β + o(1)`,
   `ReflectedDiscountedGreen.lean`). So `R_c ϕ_i = ϕ_i/(c + 1/μ_i)`, and uniqueness of the Laplace transform almost
   everywhere (`ae_eq_of_laplace_eq`, `LaplaceTransformUniquenessAe.lean`) with right continuity in time gives
   `E_x ϕ_i(Y_u) = e^{−u/μ_i} ϕ_i(x)` for every `u > 0` and every start `x ∈ K₀` (`timeChangeTransition_eigenfun`,
   `ReflectedEigenTransition.lean`).
6. **The kernel.** `p(t, x, y) = 1 + ∑ e^{−t/μ_i} ϕ_i(x) ϕ_i(y)` converges uniformly on `[t₀, ∞) × K₀ × K₀`
   (`|ϕ_i| ≤ B/μ_i`, `∑ μ_i² ≤ B²`) and is jointly continuous (`GreenEigenData.continuousOn_eigenKernel`,
   `ReflectedEigenKernel.lean`). For bounded continuous `ψ`, `E_x ψ(Y_v) = ∫ p(v, x, y) ψ(y) ν(dy)` from every start,
   by finite eigenfunction combinations, the `L²` error bound `R_c|h| ≤ (2B + 1/c) ‖h‖₂` and the fundamental theorem
   of calculus in time (`timeChangeTransition_eq_integral_eigenKernel`, `ReflectedEigenKernelTests.lean`). A bump
   function gives `p ≥ 0`, the law of `Y_v` under `Q_x` is `p(v, x, y) ν(dy)`, and `p` is a heat kernel of the time
   change from every start (`isLBMHeatKernel_eigenKernel`, `ReflectedEigenHeatKernel.lean`).
7. **Strict positivity.** `p(s, y, y) ≥ 1`; by Chapman–Kolmogorov a positive value at `(u, x, y)` stays positive at all
   later times; so a zero at `t₀` would make `p(·, x, y)` vanish on `(0, t₀)`, but `t ↦ p(t, x, y)` extends to a
   holomorphic function on `Re t > 0` that tends to `1`, and the identity theorem excludes it (`eigenKernel_pos`).
8. **The instances.** For Kigami's theorem the kernel is `p` (the volume bounds (13.1) give `IsUpperRegularSpeed`
   through `closedBall_le_of_ball_le`). For KLVW, every jointly continuous heat kernel of the time change equals `p`
   on `(0, ∞) × K₀ × K₀` (`IsLBMHeatKernel.eq_of_continuousOn`), so its transition operator at `t > 0` sends every
   `f ≥ 0` with `⟨f, f⟩ > 0` to a function positive `ν`-almost everywhere (`klvwHeatKernelInstanceStmt`).
   `KLVWHeatKernelInstanceStmt` carries, besides the hypotheses of the cited theorem, that `ν` is the Revuz measure
   of `A`, a probability measure with the upper ball bounds; `pos_of_isIrreducibleSemigroup` passes them on.

**Fidelity of the two cited statements** (`kigamiHeatKernelContinuityCited` and `klvwPositivityImprovingCited`,
checked against Kigami 2019 and KLVW 2015; no change to either statement). Kigami 2019, Theorem 13.1: the ball hypothesis is
exact on `[0, 1]²`; the Lean statement selects existence and joint continuity of the kernel and omits weak exponential
decay, (13.2) and (13.5); Kigami's process has generator `Δ` while folded Brownian motion here has generator `Δ/2`, so
the kernel in the time units used here is `p_μ(t/2, x, y)`; and the Lean statement adds a quantifier, the transition
formula for every additive functional with Revuz measure `μ` and from every start, which the expansion above proves
directly for the instance used. KLVW Theorem A.2: `klvwPositivityImprovingCited` is a valid specialization of
(iii) ⟺ (i) to finite measures, real `L²` and symmetric sub-Markov semigroups.

All print [propext, Classical.choice, Quot.sound] (`checks/AxiomGate.lean`, log 1125-221630-17367).

## What remains

Nothing for Proposition 2.6: `reflectedLBMHeatKernelStmt_holds` has no hypothesis. The cited statements
`kigamiHeatKernelContinuityCited` and `klvwPositivityImprovingCited` stay in `HarmonicBalls/FirstPass/Cited/` as
transcriptions of the sources; no step of this proof takes them as hypotheses (`reflectedLBMHeatKernelStmt_of_kigami_of_klvw`
records the earlier route from them).
