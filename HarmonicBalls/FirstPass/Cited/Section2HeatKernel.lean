import HarmonicBalls.Draft.Section2

/-!
# Proposition 2.6: the cited heat kernel continuity theorem of Kigami

Proposition 2.6 (prop:lbm-continuity, paper/lqg_harmonic_ball-corrected.tex:560-:562) states that for a square `K`,
almost surely, the heat kernel `p^K_t(x,y)` of γ-LBM with Neumann boundary conditions on `K` (defined by
eq:defining-property-of-kernel, :552-:553, with correction [C5]: density with respect to `μ_h`) exists, is finite,
jointly continuous and strictly positive for all `(t,x,y) ∈ (0,∞) × K × K`. Its proof (:563-:567) reads, as printed:

> This is [Kig19, Theorem 13.1] with input given by Lemma 2.4. Strictly speaking, [Kig19, Theorem 13.1] concerns the
> transition density of reflecting γ-LBM in the unit square. A scaling argument shows that [Kig19, Theorem 13.1]
> applies to the transition density of reflecting γ-LBM in any fixed square.

[Kig19] = Jun Kigami, *Time changes of the Brownian motion: Poincaré inequality, heat kernel estimate and
protodistance*, Mem. Amer. Math. Soc. 259(1250):v+118, 2019 (bibitem `kigami2019`).

This module states that literature input, Theorem 13.1 of [Kig19] in the case the paper uses (the unit square
`K₀ = [0,1]² = closedSquare 0 1`), as the Prop `kigamiHeatKernelContinuityCited`: a statement about the time change of
reflected Brownian motion by a deterministic measure, not about the Gaussian free field.

## Theorem 13.1 of [Kig19]

As recorded in docs/campaign/E19-route-b.md:160-:166 (checked there against the 98-page preprint, p. 59; it restates
Theorem 1.1, preprint p. 5): "Assume that α = 0. Let µ be a Borel regular probability measure on K. Suppose that there
exist positive constants c1, c2, α1, α2 such that α1 ≥ α2 and c1 r^{α1} ≤ µ(B∗(x, r)) ≤ c2 r^{α2} (13.1) for any
x ∈ K and any r ∈ (0, 1]. Then µ has weak exponential decay, there exists a jointly continuous heat kernel
pµ(t, x, y) on (0, ∞) × K × K associated with the time change of the Brownian motion with respect to µ and
[on-diagonal bounds (13.2)]". Here `K` is a generalized Sierpinski carpet with resistance exponent `α = 0`, which
includes the unit square of Theorem 1.1, and the Brownian motion is reflected Brownian motion on `K`.

## Reading of the cited statement

* **Measure.** `μ` is a Borel probability measure on `ℂ` carried by `K₀` (`μ K₀ᶜ = 0`); a finite Borel measure on a
  metric space is regular, so "Borel regular" adds nothing. `B∗(x, r)` is read as the relative Euclidean ball
  `B(x, r) ∩ K₀` (open), and `μ (B(x, r) ∩ K₀) = μ (B(x, r))` since `μ` is carried by `K₀`. A closed-ball or
  cell-neighbourhood reading of `B∗` gives the same class of measures, with other constants.
* **Time change.** The time change of the Brownian motion with respect to `μ` is the time change by the positive
  continuous additive functional (PCAF) whose Revuz measure is `μ` (Fukushima-Oshima-Takeda, *Dirichlet forms and
  symmetric Markov processes*, 2nd ed. 2011, Theorem 6.2.1; [Kig19], Section 6). The PCAF objects
  (`IsUnitSquarePCAF`, `unitSquareRevuzMeasure`) are those of MatedCRT/External/RevuzTimeChange.lean (`IsPCAF`,
  `revuz`) of the IDLA formalization, written here for reflected Brownian motion in `K₀` and starting points in `K₀`.
  The PCAF is quantified universally, so the statement applies to every version of it.
* **Normalization of time.** [Kig19]'s Brownian motion on `[0,1]²` is the diffusion of the Neumann energy
  `∫ ∇f · ∇g` (generator `Δ`), while `reflectedPlanarBrownianMotion 0 1` (HarmonicBalls/Defs/LBM.lean:179) is the
  folded planar Brownian motion (generator `Δ/2`), the same process at half speed. If `A` is the PCAF of the latter
  with Revuz measure `μ` (with respect to Lebesgue measure on `K₀`), its time change at time `t` is the time change of
  [Kig19] at time `t/2`, so [Kig19]'s kernel `k` and the kernel `p` here satisfy `p t x y = k (t/2) x y`. Joint
  continuity on `(0,∞) × K₀ × K₀` is the same statement for both.
* **Heat kernel.** `IsLBMHeatKernel` (Defs/LBM.lean:194): `p ≥ 0` and `Q_x[b_{A⁻¹(t)} ∈ S] = ∫_{S ∩ K₀} p t x y dμ(y)`
  for every `t > 0`, every start `x ∈ K₀` and Borel `S`: the density is with respect to `μ`, as in [C5]. "Associated
  with the time change" is read as this transition formula from every starting point; [Kig19] gives it in equation
  (10.11) of Theorem 10.10, of which Theorem 13.1 is the specialization to ball bounds.
* **Omitted conclusions.** Weak exponential decay of `μ` and the on-diagonal bounds (13.2) are not used by the paper
  and are not stated. Strict positivity of the kernel is not part of Theorem 13.1 as recorded (Theorem 10.10 states
  it under its admissibility hypotheses) and is not stated.
* **Scaling.** The passage from the unit square to an arbitrary square (:565-:566) is a separate step of the paper,
  not part of the cited theorem; it is not included.

## Status of Proposition 2.6 in the repository

| Declaration | Location | Content |
|---|---|---|
| `ReflectedLBMHeatKernelStmt` | Draft/Section2.lean:225 | the printed Proposition 2.6; no producer and no consumer (COUNTED-MANIFEST row 2.6: Draft only) |
| `liouvilleVolumeGrowthStmt_of_ballMass_derivedInputs43` | FirstPass/Phase2/DerivedInputs43.lean:156 | Lemma 2.4, `LiouvilleVolumeGrowthStmt`, without premises (COUNTED-MANIFEST row 2.4) |
| `liouvilleVolumeGrowthStmt_of_ballMass` | Steps/Sec2/VolumeGrowth.lean:80 | Lemma 2.4 from `LiouvilleBallMassBoundStep` |
| `lqgVolumeGrowthAllScalesStmt_of_rows123` | FirstPass/Phase2/DerivedInputs29.lean:66 | I2, `LQGVolumeGrowthAllScalesStmt`: almost surely, two-sided power bounds `r^{β⁻} ≤ μ_h(B_r(z)) ≤ r^{β⁺}` for all `r < r₀` and `z ∈ B_R` |

What only the cited statement supplies: the existence and joint continuity of the heat kernel of the time change of
reflected Brownian motion in the unit square by a deterministic measure with two-sided power bounds on balls.

## Why `kigamiHeatKernelContinuityCited → LiouvilleVolumeGrowthStmt → ReflectedLBMHeatKernelStmt` is not direct

1. (missing, the principal step; [NCS1]) identification of the clock: almost surely, for every `x ∈ K`, the LQG clock
   `F ω x` of reflected Brownian motion (`IsLQGClock (reflectedPlanarBrownianMotion a L) γ (fieldCircleAverage α₀
   (hcirc ω)) x (F ω x)`, a limit in probability of circle-average regularizations) agrees `Q_x`-almost surely with
   one PCAF of reflected Brownian motion in `K` whose Revuz measure is `μ_h` restricted to `K`. [Kig19] does not prove
   it (its Example 11.3 only verifies weak exponential decay of a Liouville measure on `[0,1]²`), and no declaration
   of the repository states it.
2. (missing) strict positivity, the third conjunct of `ReflectedLBMHeatKernelStmt`: it is not part of Theorem 13.1.
3. (not direct from Lemma 2.4) hypothesis (13.1) for the normalized measure `μ_h(K)⁻¹ T_*(μ_h|_K)`, `T` the affine map
   of `K` onto `[0,1]²`: it needs, almost surely, bounds at every scale `r ≤ 1` and every centre in `K`, and
   `0 < μ_h(K) < ∞`. `LiouvilleVolumeGrowthStmt` is a bound at one scale, with polynomially high probability, for
   centres in `B_1`; the almost sure bound at all small scales is I2 (table above), and the remaining scales up to
   `1` follow by monotonicity.
4. (a separate step of the paper, :565-:566) the scaling from `[0,1]²` to `closedSquare a L`: the affine change of
   reflected Brownian motion (folding commutes with `z ↦ a + L z`), of the PCAF and its Revuz measure, and of time.
   The repository does not state it.

Because of steps 1 and 2 no implication is proved here.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory MarkovProcess Set
open scoped ENNReal NNReal

/-- The time shift `θ_s b = b (s + ·)` of a continuous path (`LatticeProb.pathShift` of the Lattice-Probability
package, for paths in `ℂ`). -/
noncomputable def pathTimeShift (b : ContinuousPath ℂ) (s : ℝ≥0) : ContinuousPath ℂ :=
  ContinuousMap.comp b ⟨fun u => s + u, continuous_const.add continuous_id⟩

/-- The natural `σ`-field `F⁰_t = σ(b_s : s ≤ t)` of the canonical path up to time `t` (`pathFiltration` of
MatedCRT/External/RevuzTimeChange.lean). -/
noncomputable abbrev pathNaturalFiltration (t : ℝ≥0) : MeasurableSpace (ContinuousPath ℂ) :=
  ⨆ s ≤ t, MeasurableSpace.comap (fun b : ContinuousPath ℂ => b s) inferInstance

/-- `IsUnitSquarePCAF A`: `A t b` is a *positive continuous additive functional* of reflected Brownian motion in the
unit square `K₀ = closedSquare 0 1` (`reflectedPlanarBrownianMotion 0 1`), for starting points in `K₀` (Revuz-Yor,
*Continuous martingales and Brownian motion*, 3rd ed. 1999, Chapter X, Definition 1.1, raw form; the definition
`IsPCAF` of MatedCRT/External/RevuzTimeChange.lean for this process): measurable, adapted to the natural filtration up
to null sets, almost surely continuous and nondecreasing from `0`, and additive `A_{t+s} = A_t + A_s ∘ θ_t` almost
surely for every start `x ∈ K₀` and all `s, t`. -/
structure IsUnitSquarePCAF (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) : Prop where
  /-- Each `A t` is a measurable functional of the path. -/
  measurable : ∀ t, Measurable (A t)
  /-- `A t` is `F⁰_t`-measurable up to a null set, for every start in `K₀`. -/
  adapted : ∀ x ∈ closedSquare 0 1, ∀ t, ∃ g : ContinuousPath ℂ → ℝ≥0,
    Measurable[pathNaturalFiltration t] g ∧ A t =ᵐ[reflectedPlanarBrownianMotion 0 1 x] g
  /-- Almost surely `A` vanishes at `0` and is continuous and nondecreasing in time. -/
  path : ∀ x ∈ closedSquare 0 1, ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 x,
    A 0 b = 0 ∧ Continuous (fun t => A t b) ∧ Monotone (fun t => A t b)
  /-- Additivity `A_{t+s} = A_t + A_s ∘ θ_t`, almost surely for all `s, t`. -/
  additive : ∀ x ∈ closedSquare 0 1, ∀ s t, ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 x,
    A (t + s) b = A t b + A s (pathTimeShift b t)

open scoped Classical in
/-- The right-continuous rational-time regularization of a functional `A`: for a path along which `A` is
nondecreasing on the nonnegative rationals, `t ↦ inf {A q b : q ∈ ℚ≥0, q > t}`; for every other path, `0` (the
function `regularize` of MatedCRT/External/RevuzTimeChange.lean). It equals `A · b` when `A · b` is continuous and
nondecreasing. -/
noncomputable def clockRationalRegularization (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (t : ℝ≥0)
    (b : ContinuousPath ℂ) : ℝ≥0 :=
  if ∀ p q : ℚ≥0, p ≤ q → A p b ≤ A q b then ⨅ q : {q : ℚ≥0 // t < (q : ℝ≥0)}, A (q.1 : ℝ≥0) b else 0

open scoped Classical in
/-- The Lebesgue-Stieltjes function of a nondecreasing clock `a : ℝ≥0 → ℝ≥0` (extended by `a 0` to the negative
half-line), and a default for a clock that is not nondecreasing. -/
noncomputable def clockStieltjesFunction (a : ℝ≥0 → ℝ≥0) : StieltjesFunction ℝ :=
  if h : Monotone a then
    (show Monotone (fun x : ℝ => ((a x.toNNReal : ℝ≥0) : ℝ)) from
      fun x y hxy => by exact_mod_cast h (Real.toNNReal_mono hxy)).stieltjesFunction
  else default

/-- The occupation measure of the path `b` against the Stieltjes measure of the clock `a` on `(0, 1]`:
`S ↦ ∫_{(0,1]} 1_S(b_s) da_s`. -/
noncomputable def clockOccupationMeasure (a : ℝ≥0 → ℝ≥0) (b : ContinuousPath ℂ) : Measure ℂ :=
  (((clockStieltjesFunction a).measure).restrict (Ioc (0 : ℝ) 1)).map (fun s : ℝ => b s.toNNReal)

/-- The *Revuz measure* of `A` for reflected Brownian motion in `K₀ = closedSquare 0 1` with respect to Lebesgue
measure on `K₀`: `S ↦ ∫_{K₀} dx E_x ∫_{(0,1]} 1_S(b_s) dA_s` (Revuz-Yor 1999, Chapter X, Section 2;
Fukushima-Oshima-Takeda 2011, (5.1.13) with `h ≡ 1`; Lebesgue measure on `K₀` is invariant for reflected Brownian
motion, so the time interval `(0, 1]` gives the Revuz measure itself). Computed on the rational-time regularization
of `A`, as `revuz` of MatedCRT/External/RevuzTimeChange.lean. -/
noncomputable def unitSquareRevuzMeasure (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) : Measure ℂ :=
  ((volume : Measure ℂ).restrict (closedSquare 0 1)).bind fun x =>
    (reflectedPlanarBrownianMotion 0 1 x).bind fun b =>
      clockOccupationMeasure (fun t => clockRationalRegularization A t b) b

/-- Kigami's heat kernel continuity theorem, the literature input of the proof of Proposition 2.6
(prop:lbm-continuity, paper/lqg_harmonic_ball-corrected.tex:563-:567), cited as printed: "This is [Kig19, Theorem
13.1] with input given by Lemma 2.4" (J. Kigami, *Time changes of the Brownian motion: Poincaré inequality, heat
kernel estimate and protodistance*, Mem. Amer. Math. Soc. 259(1250), 2019, Theorem 13.1). PENDING TRUTH CHECK.

Statement, in the case the paper uses (the unit square `K₀ = closedSquare 0 1`, resistance exponent `α = 0`). Let
`μ` be a Borel probability measure carried by `K₀` with two-sided power bounds (13.1):
`c₁ r^{α₁} ≤ μ(B(x, r)) ≤ c₂ r^{α₂}` for all `x ∈ K₀` and `r ∈ (0, 1]`, with positive constants and `α₁ ≥ α₂`. Let
`A` be a PCAF of reflected Brownian motion in `K₀` (`IsUnitSquarePCAF`) with Revuz measure `μ`
(`unitSquareRevuzMeasure A = μ`). Then the time change of reflected Brownian motion by `A` has a heat kernel `p`
with respect to `μ` (`IsLBMHeatKernel`, transition formula from every start in `K₀`) that is jointly continuous on
`(0,∞) × K₀ × K₀`.

See the module docstring for the reading of `B∗(x, r)`, the normalization of time (`p t x y = k (t/2) x y` for
[Kig19]'s kernel `k`) and the conclusions of Theorem 13.1 that are not stated (weak exponential decay, the
on-diagonal bounds (13.2)). The scaling from the unit square to an arbitrary square (:565-:566) is a separate step
of the paper and is not part of this statement. -/
def kigamiHeatKernelContinuityCited : Prop :=
  ∀ μ : Measure ℂ, IsProbabilityMeasure μ → μ (closedSquare 0 1)ᶜ = 0 →
  ∀ c₁ c₂ α₁ α₂ : ℝ, 0 < c₁ → 0 < c₂ → 0 < α₁ → 0 < α₂ → α₂ ≤ α₁ →
  (∀ x ∈ closedSquare 0 1, ∀ r : ℝ, 0 < r → r ≤ 1 →
    ENNReal.ofReal (c₁ * r ^ α₁) ≤ μ (Metric.ball x r) ∧
      μ (Metric.ball x r) ≤ ENNReal.ofReal (c₂ * r ^ α₂)) →
  ∀ A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0, IsUnitSquarePCAF A → unitSquareRevuzMeasure A = μ →
  ∃ p : ℝ → ℂ → ℂ → ℝ,
    IsLBMHeatKernel (reflectedPlanarBrownianMotion 0 1) (fun _ b t => (A t b : ℝ)) (closedSquare 0 1) μ p ∧
    ContinuousOn (fun s : ℝ × ℂ × ℂ => p s.1 s.2.1 s.2.2)
      (Ioi 0 ×ˢ closedSquare 0 1 ×ˢ closedSquare 0 1)

end HarmonicBalls
