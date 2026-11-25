# Proposition 2.6: the clock of reflected Liouville Brownian motion in a square

Proposition 2.6 (`ReflectedLBMHeatKernelStmt`, `HarmonicBalls/Draft/Section2.lean:225`) asks for a finite, jointly
continuous, strictly positive heat kernel of reflected Liouville Brownian motion in a square `K = closedSquare a L`
with respect to `μ_h`. The printed proof (corrected source, lines 563-567) cites Kigami 2019, Theorem 13.1, with input
Lemma 2.4, and a scaling argument. Kigami's theorem concerns the time change of reflected Brownian motion in the unit
square by the additive functional whose Revuz measure is a given measure. This note records the proof that the LQG
clock of reflected Brownian motion in `K`, read in the unit square, is such an additive functional for the normalized
LQG measure, so that the cited theorem applies. What remains of Proposition 2.6 is the strict positivity of the kernel.

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

All print [propext, Classical.choice, Quot.sound] (`checks/AxiomGate.lean`, log 1125-060247-2846846).

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

## What remains

Strict positivity of the unit-square kernel (`hpos` of `reflectedLBMHeatKernel_of_kigami_of_positivity`). The
literature route uses the symmetry of the time-changed semigroup with respect to `ν` and the irreducibility of the
time-changed Neumann form (Kigami 2019, Theorem 6.8; Keller–Lenz–Vogt–Wojciechowski, Theorem A.2), which are not in
the repository. The Chapman–Kolmogorov identity above is the semigroup law of the `L²(ν)` operators of the kernel.
