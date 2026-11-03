import HarmonicBalls.Draft.Section5

/-!
# Section 9: statements of Lemma 9.1, Proposition 9.2 and Lemmas 9.3-9.4 (uniqueness of harmonic balls)

Statements of the numbered results of Section 9 (sec:uniqueness, lines 2270-2475) of the corrected draft: the
comparison of Green potentials of subharmonic and harmonic balls with a point mass (Lemma 9.1, the quadrature
inequality of Sakai and Shahgholian-Sjödin), the uniqueness of subharmonic balls up to `μ_h`-null sets
(Proposition 9.2), the inclusion of the boundary of a harmonic ball in the closure of the regularized cluster of the
same mass (Lemma 9.3) and the equality of regular open sets which agree `μ_h`-almost everywhere (Lemma 9.4). The
proof of Proposition 5.6 (prop:uniqueness, lines 2411-2475) is printed in this section; its statement is
`UniquenessHarmonicBallsStmt` of `HarmonicBalls/Draft/Section5.lean`.

## Random setting

Each statement quantifies over `0 < γ < 2`, `α₀ < Q = lqgQ γ`, a probability space `(Ω, P)`, a whole-plane GFF
`h^ℂ` (`IsWholePlaneGFF P hC hcirc`) and a random measure `μ` with `μ ω = μ_h` for `h = h^ℂ - α₀ log |·|`
(`IsLQGMeasureOfField P γ α₀ hcirc μ`). "Almost surely" / "on an event of probability 1" is `∀ᵐ ω ∂P` placed before
all the other quantifiers, as printed. Lemma 9.1 has no probability-one qualifier: it is stated for every
realisation `μ ω` (its proof, lines 2291-2313, is deterministic).

## Conventions and readings

* *Harmonic ball* is `IsHarmonicBallGen` (`Defs/HarmonicBall.lean`): a harmonic ball for the enlarged class of test
  functions of lines 136-146, with correction [C7]. Line 2332 says "in the sense of eq:harmonic-ball" (test functions
  harmonic in a neighbourhood of `closure A`, `IsHarmonicBall`), but the proofs of Lemma 9.1(2) and Lemma 9.3 use the
  test function `G_{B_R}(·,x)` for `x ∈ ∂A`, which is in the enlarged class (`greenFunction_mem_greenPotentialClass`)
  and is not harmonic near `closure A`. With `IsHarmonicBall` the proofs break down and the analogous statements
  for Lebesgue measure (whose proofs are identical) are false, with `R = 2`, `z = 0`: for Lemma 9.1(2), the slit
  disc `A = B_1 \ [1/2, 3/4]` is a domain and a harmonic ball centred at `0`, and on the slit
  `f(x) = (1/2) log(1/|x|) - (1 - |x|²)/4 > 0`; for Lemma 9.3, `A = {x ∈ B_1 : |x| ∉ C}` with `C ⊆ [1/2, 1)`
  closed, of positive length and with empty interior (concentric annuli; a harmonic ball centred at `0`, by the mean
  value property on circles, with `closure A = closure B_1`) has `∂B_1 ⊆ ∂A`, while `Λ_t(0)` is the disc of area
  `t = |A| < π`. For `μ_h` the slit example is `Λ_t(z)` minus a segment of `μ_h`-measure `0`.
* *Subharmonic ball* is `IsSubharmonicBall` (eq:subharmonic-ball, line 742; `Draft/Section4.lean`).
* `A ⋐ B_R` (lines 2317, 2337) is `closure A ⊆ B_R`. In Lemma 9.1 the printed "a domain strictly contained which
  contains `z`" (line 2280) lacks "in `B_R`" (docs/campaign/GRAPH.md G13); it is read `closure A ⊆ B_R`, the reading
  needed for `O = B_R` to be an admissible open set in eq:sub-harmonic-potential (`O ⊇ closure A`) and the
  hypothesis under which the lemma is used (lines 2321, 2342). A *domain* is a connected open set (`IsConnected`).
* `μ_h(A) = t` is `μ A = ENNReal.ofReal t`; in the function `f` of eq:obstacle-comp, `μ_h(A)` is the real number
  `μ.real A` (finite for subharmonic and harmonic balls).
* Green function: `greenFunction (ball 0 R)` (`Defs/Green.lean`), with junk value `0` on the diagonal where the
  paper's value is `+∞`. The function `f` of eq:obstacle-comp is `+∞` at `x = z` in the paper and the junk value
  `-∫_A G_{B_R}(z,y) μ_h(dy)` here, so the inequality `f ≥ 0` of Lemma 9.1(1) is stated off the pole.
* `Λ^{B_R;z}_t` (italic, `\cluster`, eq:non-co-set, line 592) is `cluster μ R z t`; the regularized cluster
  `Λ^{B_R;z}_t = int(closure Λ^{B_R;z}_t)` (upright, `\regcluster`, eq:regular-cluster, line 846) is
  `regularizedCluster μ R z t`. The whole-plane regularized clusters `Λ_t(z)` of Theorem 5.5
  (theorem:full-theorem-minus-uniqueness, line 863) enter Lemma 9.3 as in `UniquenessHarmonicBallsStmt`: a random
  family `Λhat ω z t` which almost surely, for every `z`, has the properties of Theorem 5.5
  (`IsRegularizedClusterFamily`). Such a family is unique: each `Λhat ω z t` is bounded, hence equal to
  `regularizedCluster (μ ω) r z t` for all large `r`.
* Regular open (`int(closure X) = X`, line 2395) is `IsRegularOpen` (`Defs/HarmonicBall.lean`).

## Corrections applied

[C7] (enlarged test class, line 146) through `IsHarmonicBallGen`; [C10] (Proposition 9.2, line 2317: conclude
`Λ^{B_R;z}_t ⊆ A` for the cluster, not for its regularization; ESCALATIONS E11, docs/campaign/GRAPH.md F5). See
`~/paper-fleets/hb/CORRECTIONS-PROPOSED.md`.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

/-- Lemma 9.1 (lemma:obstacle-comp, line 2279; Theorem 2.1 of Shahgholian-Sjödin 2013 and Sakai 1984, with a
complete proof printed at lines 2291-2313). Let `R > 0`, `z ∈ B_R`, and let `A` be a domain with `closure A ⊆ B_R`
containing `z`. Let `f(x) = μ_h(A) G_{B_R}(x,z) - ∫_A G_{B_R}(x,y) μ_h(dy)` (eq:obstacle-comp, line 2281).
1. If `A` is a subharmonic ball centred at `z`, then `f ≥ 0` on `B_R` (off the pole `z`, where the paper's `f` is
   `+∞`).
2. If `A` is a harmonic ball centred at `z`, then `f = 0` on `B_R \ A`.

* No probability-one qualifier is printed: the statement is for every realisation `μ ω` of `μ_h`. The proof uses
  only the definitions and the symmetry of `G_{B_R}`, so it holds for every measure.
* "A domain strictly contained" (line 2280) is read `closure A ⊆ B_R` (docs/campaign/GRAPH.md G13; see the module
  docstring). The domain hypotheses (open, connected) are kept as printed; openness is also part of both ball
  notions.
* "Harmonic ball" in (2) is `IsHarmonicBallGen` ([C7]): the proof (line 2307) applies the mean value property to
  `G_{B_R}(·,x)` with `x ∈ B_R \ A`, possibly `x ∈ ∂A`; with the narrow class `IsHarmonicBall` (2) fails for a
  slit disc (module docstring).
* The test function of (1) is `-G_{B_R}(·,x)`, i.e. eq:sub-harmonic-potential with `O = B_R`, `ν = -δ_x`, `q = 0`;
  the printed class asks for real values (line 746), and `-G_{B_R}(·,x)` is `-∞` at `x` (GRAPH G13). In
  `subharmonicBallTestClass` the value at `x` is the junk value `0` and the class is the paper's one off `x`. -/
def ObstacleComparisonStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ ω : Ω, ∀ R : ℝ, 0 < R → ∀ z ∈ ball (0 : ℂ) R, ∀ A : Set ℂ, IsOpen A → IsConnected A →
    closure A ⊆ ball (0 : ℂ) R → z ∈ A →
    (IsSubharmonicBall (μ ω) A z → ∀ x ∈ ball (0 : ℂ) R, x ≠ z →
      0 ≤ (μ ω).real A * greenFunction (ball 0 R) x z - ∫ y in A, greenFunction (ball 0 R) x y ∂(μ ω)) ∧
    (IsHarmonicBallGen (μ ω) A z → ∀ x ∈ ball (0 : ℂ) R \ A,
      (μ ω).real A * greenFunction (ball 0 R) x z - ∫ y in A, greenFunction (ball 0 R) x y ∂(μ ω) = 0)

/-- Proposition 9.2 (prop:sub-harmonic-ball-uniqueness, line 2315), with correction [C10]. On an event of
probability 1: if `A ⋐ B_R` is a subharmonic ball centred at `z ∈ B_R` with `μ_h(A) = t` for some `t, R > 0`, then
the cluster `Λ^{B_R;z}_t` (eq:non-co-set) is contained in `A`, and `μ_h(A \ Λ^{B_R;z}_t) = 0` for the regularized
cluster `Λ^{B_R;z}_t = int(closure Λ^{B_R;z}_t)` (eq:regular-cluster).

* [C10] (ESCALATIONS E11, docs/campaign/GRAPH.md F5): the printed first conclusion is
  `int(closure Λ^{B_R;z}_t) ⊆ A` (line 2317, `\regcluster`). The proof (lines 2320-2323) shows only
  `Λ^{B_R;z}_t ⊆ A` (`\cluster`, line 2322); with `A = Λ^{B_R;z}_t` the printed claim would force
  `Λ^{B_R;z}_t = int(closure Λ^{B_R;z}_t)`, which the paper never proves. The second conclusion is as printed.
* The proposition is not used in the paper (line 2327). Its proof also needs `μ_h(Λ^{B_R;z}_t) = t`
  (Lemma 3.4 and Proposition 8.1 scaled to `B_R`, not cited; GRAPH G15).
* `A ⋐ B_R` is `closure A ⊆ B_R`. -/
def SubharmonicBallUniquenessStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ (A : Set ℂ) (z : ℂ) (t R : ℝ), 0 < t → 0 < R → z ∈ ball (0 : ℂ) R →
    closure A ⊆ ball (0 : ℂ) R → IsSubharmonicBall (μ ω) A z → μ ω A = ENNReal.ofReal t →
    cluster (μ ω) R z t ⊆ A ∧ μ ω (A \ regularizedCluster (μ ω) R z t) = 0

/-- Lemma 9.3 (lemma:contains-boundary, line 2336). Let `{Λ_t(z)}_{t > 0, z ∈ ℂ}` be given by Theorem 5.5. Almost
surely, every harmonic ball `A ⋐ B_R` centred at `z ∈ B_R` with `t = μ_h(A) > 0` satisfies
`∂A ⊆ closure Λ_t(z)`.

* `Λ_t(z)` is `Λhat ω z t` for a random family which almost surely, for every `z`, has the properties of
  Theorem 5.5 (`IsRegularizedClusterFamily`), as in `UniquenessHarmonicBallsStmt` (module docstring).
* "Harmonic ball" is `IsHarmonicBallGen` ([C7]). Line 2332 says "in the sense of eq:harmonic-ball"; with that
  narrow class the Lebesgue analogue fails (concentric annuli, module docstring), and the proof (Lemma 9.1(2) at
  line 2351) needs the enlarged class.
* `R > 0` is implicit (`z ∈ B_R`). `A ⋐ B_R` is `closure A ⊆ B_R`; the radius `R` may be enlarged in the proof
  (line 2342). -/
def HarmonicBallBoundarySubsetStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ Λhat : Ω → ℂ → ℝ → Set ℂ, (∀ᵐ ω ∂P, ∀ z : ℂ, IsRegularizedClusterFamily (μ ω) (Λhat ω z) z) →
  ∀ᵐ ω ∂P, ∀ (A : Set ℂ) (z : ℂ) (R t : ℝ), z ∈ ball (0 : ℂ) R → closure A ⊆ ball (0 : ℂ) R →
    IsHarmonicBallGen (μ ω) A z → 0 < t → μ ω A = ENNReal.ofReal t →
    frontier A ⊆ closure (Λhat ω z t)

/-- Lemma 9.4 (lemma:regular-open-ae, line 2394). Almost surely, the following is true. Let `X` and `Y` be open
subsets of `ℂ` with `int(closure X) = X` and `int(closure Y) = Y`. If `μ_h(X \ Y) = μ_h(Y \ X) = 0`, then `X = Y`.

The openness hypotheses are kept as printed (they follow from regularity, `IsRegularOpen.isOpen`). The proof
(lines 2399-2409) uses only that `μ_h` charges every nonempty open set (input I1). -/
def RegularOpenEqOfAEEqStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ X Y : Set ℂ, IsOpen X → IsOpen Y → IsRegularOpen X → IsRegularOpen Y →
    μ ω (X \ Y) = 0 → μ ω (Y \ X) = 0 → X = Y

end HarmonicBalls
