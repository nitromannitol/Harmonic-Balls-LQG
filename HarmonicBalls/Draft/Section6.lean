import HarmonicBalls.Defs.GFF
import HarmonicBalls.Defs.LQG
import HarmonicBalls.Defs.Obstacle
import HarmonicBalls.Defs.Brownian
import HarmonicBalls.Draft.Section11

/-!
# Section 6: statements of Propositions 6.1, 6.2 and Lemmas 6.3-6.13

Statements of the numbered results of Section 6 (sec:harnack-type-estimate, lines 1048-1955 of the corrected draft):
the Harnack-type estimate for clusters at very good annuli (Propositions 6.1, 6.2), the prevalence of good and very
good annuli (Lemmas 6.3-6.7, with the cited annulus iteration Lemma 6.5 of Gwynne-Miller), the harmonic comparison
between the odometer and the Liouville mass of the cluster (Lemmas 6.8-6.10), and the induction over shells
(Lemmas 6.11-6.13).

## Random setting

As in `Draft/Section3.lean`: each statement quantifies over `0 < γ < 2`, `α₀ < Q = lqgQ γ`, a probability space
`(Ω, P)`, a whole-plane GFF `h^ℂ` (`IsWholePlaneGFF P hC hcirc`) and a random measure `μ` with `μ ω = μ_h`
(`IsLQGMeasureOfField P γ α₀ hcirc μ`), `h = h^ℂ - α₀ log |·|`. The cluster is `Λ^z_t = cluster (μ ω) 1 z t` and the
odometer `v^z_t = odometer (μ ω) 1 z t` (the macro `\odometer` of the paper is `u` of eq:limit-odometer, line 596).
Deterministic constants are chosen before the probability space. The results stated "given `h`" (Lemmas 6.8-6.13)
hold on one event of probability one for all `z`, `t` and all annuli, the event of Lemmas 3.1-3.2 on which their
proofs run (GRAPH.md, entries 6.8-6.13).

## Objects used from `Defs/Annuli.lean` (namespace `HarmonicBalls`)

* `IsGoodAnnulus μ r z a b`: the good annulus event `E_r(z; a, b)` (eq:good-annulus-harmonic, lines 1115-1123);
* `annulusBallMassSize μ β⁻ ρ x₀`: the size `M_ρ(x₀)` (eq:alternate-size, line 1129); `SG_ρ(x₀; s₁, s₂)`
  (eq:alternate-size-2(-full), lines 1134, 1140) is `annulusGreenPotentialSup μ x₀ (s₁ρ) (s₂ρ)`;
* `IsVeryGoodAnnulus`: the very good annulus event `Ē_ρ(x₀; N₀, a, b, C₁^±, C₂^±, C₃)` (lines 1144-1157).

These are shared with Sections 7, 8 and 11. Earlier versions of this file carried copies in namespace
`HarmonicBalls.Section6`; the copies of `IsGoodAnnulus` and `annulusBallMassSize` were definitionally equal (`rfl`) to
the shared ones and the copy of `IsVeryGoodAnnulus` differed only in the packaging of (VG-iii), see
`Section6.isVeryGoodAnnulus_iff`.

## Objects defined here (namespace `HarmonicBalls.Section6`)

* `scaledLattice`, `VeryGoodCriterionThree`: the lattice `δ ℤ²` and criterion (VG-iii) of the very good annulus event;
  `isVeryGoodAnnulus_iff` splits `IsVeryGoodAnnulus` into (VG-i), (VG-ii) and `VeryGoodCriterionThree`;
* `fieldSigmaAlgebraModConst`, `IsFieldMeasurableModConst`: `σ(h|_U)` modulo additive constant (lines 1123, 1263;
  GRAPH D9);
* `shellWidth`, `shellRadius`, `shellOuterRadius`, `shellScale`, `shell`: the shell decomposition of Lemma 6.12;
* `odometerExt`: the odometer with its paper value `+∞` at the pole, valued in `[0, ∞]`.

## Corrections and readings

* [C15] (Lemma 6.13, lines 1710-1712; ESCALATIONS E16): "an annulus `𝔸_{ρ/2,ρ}(x₀)` not containing `z`" is replaced by
  `closure B_ρ(x₀) ⊂ B_1 \ {z}`, as in Lemma 6.11. As printed the lemma is false for `z = x₀`.
* eq:good-annulus-harmonic (line 1120, GRAPH slip list): "`𝓑^u` exits `𝔸_{3r,5r}(z)` before exiting `Y`" is
  impossible for `Y ⊆ 𝔸` (so the printed event always holds); the intended event (lines 1090-1091) is
  `τ_𝔸 ≤ τ_Y`: `𝓑^u` stays in `Y` until it exits the annulus.
* Constants and `α₀`, `β⁻` (GRAPH G19(iii), D10; operator E31, 2026-11-03 04:20 and fix (4) of 04:45). The statements
  follow the PRINTED quantifier order. In Propositions 6.1, 6.2 and Lemmas 6.3, 6.6 the constants printed as depending
  only on `γ` (and the listed parameters: `α(γ)`, `a(b, γ)`, `C^±(a, γ)`, `N₁(b, γ)`) are chosen before `α₀` and before
  the probability space; in Lemma 6.6 the exponent `β⁻ > (2+γ)²/2` of `M_ρ` is quantified with `γ` before them (the
  paper treats it as a function of `γ`, line 1911: "`b` depends only on `γ` (through `β⁻`)"). These `α₀`-uniform forms
  are true by localization (operator verdict on E22, 2026-11-03 04:35; docs/campaign/cex/AlphaUniformity.md §3). In the other statements of this section `α₀` and `β⁻` are quantified with `γ` before the constants, which may
  depend on them; for Lemma 6.4 ([C25]) and Lemma 6.7 ([C26]) this is required. A constant uniform in `α₀` is false
  already for Lemma 6.4: at `z = 0` (admissible, `dist(𝔸_{3r,5r}(0), 0) = 3r`) and `α₀ → -∞`, the density
  `|x|^{-γα₀}` puts all but a vanishing fraction of `μ_h(𝔸_{3r,5r}(0))` in `𝔸_{4.9r,5r}(0)`, while `Y = 𝔸_{3r,4.9r}(0)`
  is crossed (inner circle first) with probability `log(4.9/4)/log(4.9/3) > 0.4`.
* "Universal" constants (`c` in Lemmas 6.3, 6.6 and Proposition 6.1, `C₃` in Lemmas 6.6, 6.7, `C'` in Lemma 6.13)
  are chosen before `γ`; constants "depending only on `s₁, …, s₄`" (Lemmas 6.8, 6.10) are chosen before `γ`.
* Quantifier on `C₃` (GRAPH G18, G28). Lemma 6.11 prints "there exists a universal `C₃` and `b = b(γ)`"; its proof
  takes `C₃` as given (line 1830) and sets `b` from it (eq:choice-of-b, line 1916), and the assembly with Lemma 6.6
  (line 1594) needs the `C₃` of Lemma 6.6. Lemmas 6.11 and 6.13 are stated for every `C₃ > 0` (stronger than printed),
  with `b = b(γ, α₀, β⁻, C₃)`. The printed dependences "`N₁` depending only on `a, γ, C₁⁻, C₂⁺`" and "`α` depending
  on `a, N₀, γ, C₁⁻`" are encoded by functions `N₁ a C₁⁻ C₂⁺` and `α a N₀ C₁⁻`.
* Probabilities of events not shown measurable (GRAPH G16) are outer measures. "`P[E] ≥ p`" (Lemmas 6.4, 6.7) is
  stated as `P[Eᶜ] ≤ 1 - p` (outer measure of the complement), the stronger form, as in `PolyHighProb`.
* Propositions 6.1, 6.2 (lines 1067, 1079): `t` is unbound; read "for all `t > 0`" (line 1053). The events `Ē_ρ(x₀)`
  are existential; Proposition 6.2 carries its own `α`, events and the prevalence clause of Proposition 6.1
  (GRAPH 6.2), so that it does not refer to Proposition 6.1.
* Lemma 6.9 (line 1459), new slip: for `A = B_1 \ {z}` (open, in `B_1`, not containing `z`) and `t` small
  (`closure Λ^z_t ⊂ B_1`), the probability is `0` (the path meets `B_1 \ Λ^z_t` before `∂B_1`) while the supremum is
  `+∞` (`z ∈ ∂A ∩ closure Λ^x_t`), and `v^z_t(x) > 0`: with `∞ · 0 = 0` the printed inequality is false. The
  statement assumes the supremum finite (automatic when `z ∉ closure A`, as in its only use, Lemma 6.13); when it is
  infinite and the probability positive the printed bound is trivial. The event "exits `A` before hitting
  `A \ Λ^x_t`" is `τ_A ≤ τ^{A \ Λ^x_t}` (non-strict, the path does not visit `A \ Λ^x_t` on `[0, τ_A]`).
* Lemma 6.5 (line 1262) is cited from GM20b `gwynne2020local`, Lemma 3.1 (line 1259); its statement here is the input to
  be admitted. Lemma 6.13: the sup over "`z ∈ B_1`" (line 1713) has dummy `w` (clash with the centre `z`).
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology MarkovProcess
open scoped ENNReal Pointwise

namespace Section6

/-! ## Good and very good annuli (Section 6.1, lines 1105-1161)

The good annulus event `IsGoodAnnulus`, the size `annulusBallMassSize` and the very good annulus event
`IsVeryGoodAnnulus` are those of `Defs/Annuli.lean`. -/

/-- The scaled lattice `δ ℤ² = {δ (j + k i) : j, k ∈ ℤ}` (lines 1157, 1172). -/
def scaledLattice (δ : ℝ) : Set ℂ :=
  {w | ∃ j k : ℤ, w = (δ : ℂ) * ((j : ℂ) + (k : ℂ) * Complex.I)}

theorem mem_scaledLattice {δ : ℝ} {w : ℂ} :
    w ∈ scaledLattice δ ↔ ∃ j k : ℤ, w = (δ : ℂ) * ((j : ℂ) + (k : ℂ) * Complex.I) :=
  Iff.rfl

/-- Criterion (VG-iii) (line 1157): for each `ε ∈ {2^{-n}}_{n ≥ N₀}` and each `w ∈ (ερ/100) ℤ² ∩ 𝔸_{ρ/2,ρ}(x₀)`
there are at least `C₃ log₇ ε^{-1/2}` radii `r ∈ [ερ, ε^{1/2} ρ] ∩ {ρ 7^{-k}}_{k ≥ 1}` for which `E_r(w; a, b)`
occurs. The lattice is not centred at `x₀`, as printed (GRAPH G21). -/
def VeryGoodCriterionThree (μ : Measure ℂ) (ρ : ℝ) (x₀ : ℂ) (N₀ : ℕ) (a b C₃ : ℝ) : Prop :=
  ∀ n : ℕ, N₀ ≤ n → ∀ w ∈ scaledLattice (dyadicScale n * ρ / 100) ∩ annulus x₀ (ρ / 2) ρ,
    C₃ * Real.logb 7 (dyadicScale n ^ (-(1 / 2 : ℝ))) ≤
      ({r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
        (∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus μ r w a b}.ncard : ℝ)

/-- The very good annulus event `Ē_ρ(x₀) = Ē_ρ(x₀; N₀, a, b, C₁^±, C₂^±, C₃)` of `Defs/Annuli.lean` (lines 1144-1157),
split into its three criteria, for `μ = μ_h`:
* (VG-i) `C₁⁻ ≤ M_ρ(x₀) / μ(𝔸_{ρ/4,2ρ}(x₀)) ≤ C₁⁺`;
* (VG-ii) `C₂⁻ ≤ SG_ρ(x₀) / μ(𝔸_{ρ/4,2ρ}(x₀)) ≤ C₂⁺`, `SG_ρ(x₀) = annulusGreenPotentialSup μ x₀ (ρ/4) (2ρ)`
  (eq:alternate-size-2, line 1134);
* (VG-iii) `VeryGoodCriterionThree`.
Ratios are in `[0, ∞]`; (VG-i) forces `0 < μ(𝔸_{ρ/4,2ρ}(x₀)) < ∞` and `0 < M_ρ(x₀) < ∞`. -/
theorem isVeryGoodAnnulus_iff (μ : Measure ℂ) (βminus ρ : ℝ) (x₀ : ℂ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ : ℝ) :
    IsVeryGoodAnnulus μ βminus ρ x₀ N₀ a b C₁m C₁p C₂m C₂p C₃ ↔
      annulusBallMassSize μ βminus ρ x₀ / μ (annulus x₀ (ρ / 4) (2 * ρ)) ∈
          Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p) ∧
        annulusGreenPotentialSup μ x₀ (ρ / 4) (2 * ρ) / μ (annulus x₀ (ρ / 4) (2 * ρ)) ∈
          Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p) ∧
        VeryGoodCriterionThree μ ρ x₀ N₀ a b C₃ := by
  unfold IsVeryGoodAnnulus VeryGoodCriterionThree
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun n hn w hw => h3 n hn w hw.2 hw.1⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun n hn z hz hl => h3 n hn z ⟨hl, hz⟩⟩

/-- The grid `(B_{1+ε} \ B_{10 √ε}) ∩ (ε/100) ℤ²` of Lemmas 6.3, 6.6 and Proposition 6.1 (lines 1068, 1172, 1298). -/
def prevalenceGrid (ε : ℝ) : Set ℂ :=
  (ball (0 : ℂ) (1 + ε) \ ball 0 (10 * Real.sqrt ε)) ∩ scaledLattice (ε / 100)

/-! ## The field modulo additive constant (GRAPH D9) -/

/-- `σ(h|_U)` *viewed modulo additive constant* (lines 1123, 1263, 1279): the σ-algebra generated by the pairings
`(h, φ)` with test functions `φ` supported in `U` and `∫ φ = 0`. It does not depend on `α₀` (the `α₀`-term of
`fieldPairing` is a deterministic shift), so it is the same for `h` and `h^ℂ`. -/
@[instance_reducible]
noncomputable def fieldSigmaAlgebraModConst {Ω : Type*} (α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (U : Set ℂ) :
    MeasurableSpace Ω :=
  ⨆ (φ : ℂ → ℝ) (_ : IsTestFunction U φ ∧ ∫ x, φ x = 0),
    MeasurableSpace.comap (fun ω => fieldPairing α₀ (hC ω) φ) inferInstance

/-- An event is *measurable with respect to `h|_U` viewed modulo additive constant* (line 1263): it is `P`-a.s.
equal to an event of `fieldSigmaAlgebraModConst α₀ hC U` (the locality convention of CONVENTIONS.md). -/
def IsFieldMeasurableModConst {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (U : Set ℂ) (E : Set Ω) : Prop :=
  ∃ E' : Set Ω, MeasurableSet[fieldSigmaAlgebraModConst α₀ hC U] E' ∧ E =ᵐ[P] E'

/-! ## The odometer with its value at the pole -/

/-- The odometer `v^z_t = v_{B_1;z}(t)` (eq:limit-odometer, line 596) in `[0, ∞]`, with the paper's value `+∞` at the
pole `z` (the junk value of `odometer` is not used). The odometer is nonnegative, so `ENNReal.ofReal` loses nothing
off the pole. -/
noncomputable def odometerExt (μ : Measure ℂ) (z : ℂ) (t : ℝ) (x : ℂ) : ℝ≥0∞ :=
  if x = z then ⊤ else ENNReal.ofReal (odometer μ 1 z t x)

/-! ## The shell decomposition (Lemma 6.12, lines 1636-1672) -/

/-- `l_j = ρ 2^{-j/4} 2^{-50}` (line 1643). -/
noncomputable def shellWidth (ρ : ℝ) (j : ℕ) : ℝ :=
  ρ * (2 : ℝ) ^ (-(j : ℝ) / 4) * (2 : ℝ)⁻¹ ^ 50

/-- `d_0 = 3ρ/4`, `d_j = d_{j-1} - 32 l_{j-1}` (lines 1647-1650). -/
noncomputable def shellRadius (ρ : ℝ) : ℕ → ℝ
  | 0 => 3 / 4 * ρ
  | j + 1 => shellRadius ρ j - 32 * shellWidth ρ j

/-- `d^+_j = d_j + 8 l_j` (eq:def-epsilon-j, line 1665). -/
noncomputable def shellOuterRadius (ρ : ℝ) (j : ℕ) : ℝ :=
  shellRadius ρ j + 8 * shellWidth ρ j

/-- `ε_j = 2^{-(N₀ + j)}` (eq:def-epsilon-j, line 1665). -/
noncomputable def shellScale (N₀ j : ℕ) : ℝ :=
  dyadicScale (N₀ + j)

/-- The shell `S_j = ∂B_{d_j}(x₀) + B_{l_j}` (line 1639), a Minkowski sum. -/
def shell (x₀ : ℂ) (ρ : ℝ) (j : ℕ) : Set ℂ :=
  sphere x₀ (shellRadius ρ j) + ball (0 : ℂ) (shellWidth ρ j)

end Section6

open Section6

/-! ## Proposition 6.1 and Proposition 6.2 -/

/-- Proposition 6.1 (prop:harnack-type-property, line 1065). There is `α = α(γ) > 0` and events `Ē_ρ(x₀)`
(`ρ ∈ (0,1)`, `x₀ ∈ ℂ`) such that for each `z ∈ B_1` and `t > 0`: if `Ē_ρ(x₀)` occurs, `closure B_ρ(x₀) ⊂ B_1 \ {z}` and
`μ_h(Λ^z_t ∩ 𝔸_{ρ/2,ρ}(x₀)) ≤ α μ_h(𝔸_{ρ/2,ρ}(x₀))`, then `Λ^z_t ∩ B_{ρ/2}(x₀) = ∅`. Moreover there is a universal
`c > 0` such that with polynomially high probability as `ε → 0`, each `x₀ ∈ (B_{1+ε} \ B_{10√ε}) ∩ (ε/100) ℤ²` has
at least `c log ε^{-1/2}` radii `ρ ∈ [ε, ε^{1/2}] ∩ {8^{-n}}_{n ∈ ℕ}` for which `Ē_ρ(x₀)` occurs.

Readings: `t` unbound at line 1067, read "for all `t > 0`" (line 1053); `α = α(γ)` is chosen before `α₀`, as printed
(E31, module docstring);
the events are arbitrary subsets of `Ω` (outer probability in `PolyHighProb`); the implication is required for every
sample point of the event (equivalent to almost every, the events being existential). -/
def HarnackTypeEstimateStmt : Prop :=
  ∃ c : ℝ, 0 < c ∧
  ∀ γ : ℝ, 0 < γ → γ < 2 →
  ∃ α : ℝ, 0 < α ∧ ∀ α₀ : ℝ, α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∃ E : ℝ → ℂ → Set Ω,
    (∀ ω, ∀ ρ ∈ Ioo (0 : ℝ) 1, ∀ x₀ : ℂ, ω ∈ E ρ x₀ → ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
      closedBall x₀ ρ ⊆ ball 0 1 \ {z} →
      μ ω (cluster (μ ω) 1 z t ∩ annulus x₀ (ρ / 2) ρ) ≤
        ENNReal.ofReal α * μ ω (annulus x₀ (ρ / 2) ρ) →
      cluster (μ ω) 1 z t ∩ ball x₀ (ρ / 2) = ∅) ∧
    PolyHighProb P fun ε => {ω | ∀ x₀ ∈ prevalenceGrid ε,
      c * Real.log (ε ^ (-(1 / 2 : ℝ))) ≤
        ({ρ : ℝ | ρ ∈ Icc ε (Real.sqrt ε) ∧ (∃ n : ℕ, ρ = (8 : ℝ)⁻¹ ^ n) ∧ ω ∈ E ρ x₀}.ncard : ℝ)}

/-- Proposition 6.2 (prop:harnack-type-stronger-property, line 1078). In the setting of Proposition 6.1: if
`Ē_ρ(x₀)` occurs (`ρ ∈ (0,1)`, `x₀ ∈ ℂ`), `closure B_ρ(x₀) ⊂ B_1 \ {z}` and `Λ̃_t` is a connected component of
`Λ^z_t ∩ B_ρ(x₀)` with `μ_h(Λ̃_t ∩ 𝔸_{ρ/2,ρ}(x₀)) ≤ α μ_h(𝔸_{ρ/2,ρ}(x₀))`, then
`Λ̃_t ∩ closure B_{ρ/2}(x₀) = ∅`.

"The setting of Proposition 6.1" is made explicit: `α`, the events and their prevalence are those of Proposition
6.1, restated here (GRAPH 6.2), so this statement implies `HarnackTypeEstimateStmt` (line 1083). `t` and `z` are
read as in Proposition 6.1; `α = α(γ)` is chosen before `α₀`, as printed (E31), as in Lemma 10.1. -/
def HarnackTypeComponentStmt : Prop :=
  ∃ c : ℝ, 0 < c ∧
  ∀ γ : ℝ, 0 < γ → γ < 2 →
  ∃ α : ℝ, 0 < α ∧ ∀ α₀ : ℝ, α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∃ E : ℝ → ℂ → Set Ω,
    (∀ ω, ∀ ρ ∈ Ioo (0 : ℝ) 1, ∀ x₀ : ℂ, ω ∈ E ρ x₀ → ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
      closedBall x₀ ρ ⊆ ball 0 1 \ {z} →
      ∀ Λ ∈ connectedComponentsIn (cluster (μ ω) 1 z t ∩ ball x₀ ρ),
        μ ω (Λ ∩ annulus x₀ (ρ / 2) ρ) ≤ ENNReal.ofReal α * μ ω (annulus x₀ (ρ / 2) ρ) →
        Λ ∩ closedBall x₀ (ρ / 2) = ∅) ∧
    PolyHighProb P fun ε => {ω | ∀ x₀ ∈ prevalenceGrid ε,
      c * Real.log (ε ^ (-(1 / 2 : ℝ))) ≤
        ({ρ : ℝ | ρ ∈ Icc ε (Real.sqrt ε) ∧ (∃ n : ℕ, ρ = (8 : ℝ)⁻¹ ^ n) ∧ ω ∈ E ρ x₀}.ncard : ℝ)}

/-! ## Lemmas 6.3-6.5: good annuli are prevalent -/

/-- Lemma 6.3 (lemma:good-annuli, line 1169). Fix `b ∈ (0,1)`. There are `a = a(b, γ) > 0` and a universal `c > 0`
such that with polynomially high probability as `ε → 0`, each `z ∈ (B_{1+ε} \ B_{10√ε}) ∩ (ε/100) ℤ²` has at least
`c log₇ ε^{-1/2}` radii `r ∈ [ε, ε^{1/2}] ∩ {7^{-n}}_{n ∈ ℕ}` for which `E_r(z; a, b)` occurs.

`a ∈ (0,1)` (the parameter range of eq:good-annulus-harmonic, line 1116; stronger than the printed `a > 0`, and
equivalent since `E_r(z; a, b)` is monotone in `a`). `a = a(b, γ)` is chosen before `α₀`, as printed (E31, module
docstring). Stated for every `α₀ < Q`, including `α₀ = 0` (used in Lemma 6.7, line 1361). -/
def ManyGoodAnnuliStmt : Prop :=
  ∃ c : ℝ, 0 < c ∧
  ∀ γ : ℝ, 0 < γ → γ < 2 →
  ∀ b ∈ Ioo (0 : ℝ) 1, ∃ a ∈ Ioo (0 : ℝ) 1, ∀ α₀ : ℝ, α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  PolyHighProb P fun ε => {ω | ∀ z ∈ prevalenceGrid ε,
    c * Real.logb 7 (ε ^ (-(1 / 2 : ℝ))) ≤
      ({r : ℝ | r ∈ Icc ε (Real.sqrt ε) ∧ (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧ IsGoodAnnulus (μ ω) r z a b}.ncard : ℝ)}

/-- Lemma 6.4 (lemma:annulus-hit, line 1185). Let `b, p ∈ (0,1)`. There is `a = a(b, p, γ) ∈ (0,1)` such that
`P[E_r(z; a, b)] ≥ p` for all `r > 0` and all `z` with `dist(𝔸_{3r,5r}(z), {0}) ≥ r/100`.

`a` may depend on `α₀` (GRAPH G19(iii); a uniform choice is false, module docstring); the probability bound is stated
for the complement (G16). -/
def GoodAnnulusProbabilityStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ b ∈ Ioo (0 : ℝ) 1, ∀ p ∈ Ioo (0 : ℝ) 1, ∃ a ∈ Ioo (0 : ℝ) 1,
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ r : ℝ, 0 < r → ∀ z : ℂ, r / 100 ≤ infDist (0 : ℂ) (annulus z (3 * r) (5 * r)) →
    P {ω | ¬ IsGoodAnnulus (μ ω) r z a b} ≤ ENNReal.ofReal (1 - p)

open Classical in
/-- Lemma 6.5 (lemma:annulus-iterate, line 1262; cited: Gwynne-Miller, *Local metrics of the Gaussian free field*,
Ann. Inst. Fourier 70 (2020), Lemma 3.1, printed at line 1259). Fix `0 < s₁ < s₂ < 1`. For each `α > 0` and
`β ∈ (0,1)` there are `p = p(α, β, s₁, s₂) ∈ (0,1)` and `C = C(α, β, s₁, s₂) > 0` such that: for every decreasing
sequence of radii with `r_{k+1}/r_k ≤ s₁` and events `E_{r_k}` measurable with respect to `h|_{𝔸_{s₁r_k, s₂r_k}(0)}`
viewed modulo additive constant, if `P[E_{r_k}] ≥ p` for every `k`, then the number `N(K)` of `k ∈ [1, K]` for which
`E_{r_k}` occurs satisfies `P[N(K) < βK] ≤ C e^{-αK}` for every `K ∈ ℕ`.

The sequence is indexed from `0` (`N(K)` counts `k ∈ {0, …, K-1}`, the paper's `k ∈ [1, K]` after a shift). The
field is `h = h^ℂ - α₀ log |·|` for any `α₀`; the σ-algebra modulo additive constant does not depend on `α₀`
(`fieldSigmaAlgebraModConst`), so this is the statement of GM20b for `h^ℂ`. This is a literature input. -/
def AnnulusIterationStmt : Prop :=
  ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ → s₂ < 1 →
  ∀ α : ℝ, 0 < α → ∀ β ∈ Ioo (0 : ℝ) 1,
  ∃ p ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, 0 < C ∧
  ∀ α₀ : ℝ, ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
  ∀ r : ℕ → ℝ, (∀ k, 0 < r k) → (∀ k, r (k + 1) ≤ s₁ * r k) →
  ∀ E : ℕ → Set Ω, (∀ k, IsFieldMeasurableModConst P α₀ hC (annulus 0 (s₁ * r k) (s₂ * r k)) (E k)) →
    (∀ k, ENNReal.ofReal p ≤ P (E k)) →
    ∀ K : ℕ, P {ω | (((Finset.range K).filter fun k => ω ∈ E k).card : ℝ) < β * K} ≤
      ENNReal.ofReal (C * Real.exp (-α * K))

/-! ## Lemmas 6.6-6.7: very good annuli are prevalent -/

/-- Lemma 6.6 (lemma:very-good-annuli, line 1296). Fix `b ∈ (0,1)`. There are `a = a(b, γ)`, universal `c, C₃ > 0`,
`C₁^±, C₂^± > 0` depending on `a, γ`, and `N₁ = N₁(b, γ) ≥ 1` such that for all `N₀ ≥ N₁`, with polynomially high
probability as `ε → 0`, each `x₀ ∈ (B_{1+ε} \ B_{10√ε}) ∩ (ε/100) ℤ²` has at least `c log₈ ε^{-1/2}` radii
`ρ ∈ [ε, ε^{1/2}] ∩ {8^{-n}}_{n ∈ ℕ}` for which `Ē_ρ(x₀; N₀, a, b, C₁^±, C₂^±, C₃)` occurs.

`a ∈ (0,1)` (parameter range of the very good event, line 1145). The constants `a, C₁^±, C₂^±, N₁` are chosen
before `α₀`, as printed (E31, module docstring); they may depend on `β⁻`, which is quantified with `γ` before them
(line 1911: the paper's constants depend on `γ` "through `β⁻`"). -/
def ManyVeryGoodAnnuliStmt : Prop :=
  ∃ c C₃ : ℝ, 0 < c ∧ 0 < C₃ ∧
  ∀ γ : ℝ, 0 < γ → γ < 2 →
  ∀ βminus : ℝ, (2 + γ) ^ 2 / 2 < βminus →
  ∀ b ∈ Ioo (0 : ℝ) 1, ∃ a ∈ Ioo (0 : ℝ) 1,
  ∃ C₁m C₁p C₂m C₂p : ℝ, 0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
  ∃ N₁ : ℕ, 1 ≤ N₁ ∧ ∀ N₀ : ℕ, N₁ ≤ N₀ → ∀ α₀ : ℝ, α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  PolyHighProb P fun ε => {ω | ∀ x₀ ∈ prevalenceGrid ε,
    c * Real.logb 8 (ε ^ (-(1 / 2 : ℝ))) ≤
      ({ρ : ℝ | ρ ∈ Icc ε (Real.sqrt ε) ∧ (∃ n : ℕ, ρ = (8 : ℝ)⁻¹ ^ n) ∧
        IsVeryGoodAnnulus (μ ω) βminus ρ x₀ N₀ a b C₁m C₁p C₂m C₂p C₃}.ncard : ℝ)}

/-- Lemma 6.7 (lemma:very-good-annuli-hit, line 1307). Let `b, p ∈ (0,1)`. There are `a = a(b, p, γ) ∈ (0,1)`,
`C₁^±, C₂^±` depending on `a, γ, p`, a universal `C₃ > 0` and `N₁ = N₁(b, p, γ) ≥ 1` such that for all `N₀ ≥ N₁`,
`P[Ē_ρ(x₀)] ≥ p` for all `ρ > 0` and all `x₀` with `dist(𝔸_{ρ/4,2ρ}(x₀), {0}) ≥ ρ/100`.

The universal `C₃` is chosen first (GRAPH G28: `C₃` before `b`); the probability bound is stated for the complement
(G16). The constants may depend on `α₀` and `β⁻` (module docstring). -/
def VeryGoodAnnulusProbabilityStmt : Prop :=
  ∃ C₃ : ℝ, 0 < C₃ ∧
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ βminus : ℝ, (2 + γ) ^ 2 / 2 < βminus →
  ∀ b ∈ Ioo (0 : ℝ) 1, ∀ p ∈ Ioo (0 : ℝ) 1, ∃ a ∈ Ioo (0 : ℝ) 1,
  ∃ C₁m C₁p C₂m C₂p : ℝ, 0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
  ∃ N₁ : ℕ, 1 ≤ N₁ ∧ ∀ N₀ : ℕ, N₁ ≤ N₀ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ ρ : ℝ, 0 < ρ → ∀ x₀ : ℂ, ρ / 100 ≤ infDist (0 : ℂ) (annulus x₀ (ρ / 4) (2 * ρ)) →
    P {ω | ¬ IsVeryGoodAnnulus (μ ω) βminus ρ x₀ N₀ a b C₁m C₁p C₂m C₂p C₃} ≤ ENNReal.ofReal (1 - p)

/-! ## Lemmas 6.8-6.10: harmonic comparison -/

/-- Lemma 6.8 (lemma:odometer-annuli, line 1389). Fix `0 < s₁ < s₂ < s₃ < s₄`. There is `C`, depending only on
`s₁, …, s₄`, such that for `z ∈ B_1`, every annulus `𝔸_{s₁r,s₄r}(w) ⊂ B_1` not containing `z` and every union
`Λ̂_t` of connected components of `𝔸_{s₁r,s₄r}(w) ∩ Λ^z_t`:
`μ_h(𝔸_{s₂r,s₃r}(w) ∩ Λ̂_t) ≤ C sup_{x ∈ Λ̂_t} v^z_t(x)`.

`t` is unbound in the print: every `t > 0`. "Union of connected components": `Λ̂ ⊆ 𝔸 ∩ Λ` and `Λ̂` contains the
component of each of its points. -/
def AnnulusMassBoundByOdometerStmt : Prop :=
  ∀ s₁ s₂ s₃ s₄ : ℝ, 0 < s₁ → s₁ < s₂ → s₂ < s₃ → s₃ < s₄ →
  ∃ C : ℝ, 0 < C ∧
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t → ∀ r : ℝ, 0 < r → ∀ w : ℂ,
    annulus w (s₁ * r) (s₄ * r) ⊆ ball 0 1 → z ∉ annulus w (s₁ * r) (s₄ * r) →
    ∀ Λ : Set ℂ, Λ ⊆ annulus w (s₁ * r) (s₄ * r) ∩ cluster (μ ω) 1 z t →
      (∀ x ∈ Λ, connectedComponentIn (annulus w (s₁ * r) (s₄ * r) ∩ cluster (μ ω) 1 z t) x ⊆ Λ) →
      μ ω (annulus w (s₂ * r) (s₃ * r) ∩ Λ) ≤ ENNReal.ofReal C * ⨆ x ∈ Λ, odometerExt (μ ω) z t x

/-- Lemma 6.9 (lemma:harmonic-odometer-comparison, line 1459). Let `z ∈ B_1` and `A ⊆ B_1` open with `z ∉ A`. For all
`x ∈ A ∩ Λ^z_t`, `v^z_t(x) ≤ (sup_{∂A ∩ closure Λ^x_t} v^z_t) P[𝓑^x exits A before hitting A \ Λ^x_t | h]`, where
`Λ^x_t` is the connected component of `A ∩ Λ^z_t` containing `x` and `𝓑^x` is a Brownian motion independent of `h`.

Readings (module docstring): the supremum is assumed finite (the printed inequality is false for `A = B_1 \ {z}`,
where the supremum is `+∞` and the probability `0`); "exits `A` before hitting `A \ Λ^x_t`" is
`τ_A ≤ τ^{A \ Λ^x_t}`. -/
def OdometerHarmonicMeasureBoundStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t → ∀ A : Set ℂ, IsOpen A → A ⊆ ball 0 1 → z ∉ A →
    ∀ x ∈ A ∩ cluster (μ ω) 1 z t, ∀ Λx : Set ℂ, Λx = connectedComponentIn (A ∩ cluster (μ ω) 1 z t) x →
      (⨆ y ∈ frontier A ∩ closure Λx, odometerExt (μ ω) z t y) ≠ ⊤ →
      odometerExt (μ ω) z t x ≤ (⨆ y ∈ frontier A ∩ closure Λx, odometerExt (μ ω) z t y) *
        planarBrownianMotion x {p | ContinuousPath.exitTime A p ≤ hittingTime (A \ Λx) p}

/-- Lemma 6.10 (lemma:odometer-bound-lqg-mass, line 1512). Fix `0 < s₁ < s₂ < s₃ < s₄`. There is `c > 0`, depending
only on `s₁, …, s₄`, such that for all `z ∈ B_1`:
`sup_{x ∈ 𝔸_{s₂ρ,s₃ρ}(x₀)} v^z_t(x) ≤ c SG_ρ(x₀; s₁, s₄)` for all `𝔸_{s₁ρ,s₄ρ}(x₀) ⊂ B_1 \ {z}` such that
`(Λ^z_t)ᶜ ∩ 𝔸_{s₂ρ,s₃ρ}(x₀) ≠ ∅`.

`SG_ρ(x₀; s₁, s₄) = annulusGreenPotentialSup μ x₀ (s₁ρ) (s₄ρ)` (eq:alternate-size-2-full, line 1140); `t > 0`
arbitrary. -/
def OdometerBoundByAnnulusMassStmt : Prop :=
  ∀ s₁ s₂ s₃ s₄ : ℝ, 0 < s₁ → s₁ < s₂ → s₂ < s₃ → s₃ < s₄ →
  ∃ c : ℝ, 0 < c ∧
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t → ∀ ρ : ℝ, 0 < ρ → ∀ x₀ : ℂ,
    annulus x₀ (s₁ * ρ) (s₄ * ρ) ⊆ ball 0 1 \ {z} →
    ((cluster (μ ω) 1 z t)ᶜ ∩ annulus x₀ (s₂ * ρ) (s₃ * ρ)).Nonempty →
    ⨆ x ∈ annulus x₀ (s₂ * ρ) (s₃ * ρ), odometerExt (μ ω) z t x ≤
      ENNReal.ofReal c * annulusGreenPotentialSup (μ ω) x₀ (s₁ * ρ) (s₄ * ρ)

/-! ## Lemmas 6.11-6.13: very good annuli satisfy the Harnack-type estimate -/

/-- Lemma 6.11 (lemma:very-good-annuli-satisfy-harnack-type-estimate, line 1567). There are a universal `C₃ > 0` and
`b = b(γ) ∈ (0,1)` such that for every `z ∈ B_1` and every choice of `C₁^±, C₂^± > 0` and `a ∈ (0,1)` there are
`N₁ ≥ 200` depending only on `a, γ, C₁⁻, C₂⁺` and, for each `N₀ ≥ N₁`, `α ∈ (0,1)` depending on `a, N₀, γ, C₁⁻`,
with the property: if `ρ ∈ (0,1)`, `x₀ ∈ B_1`, `closure B_ρ(x₀) ⊂ B_1 \ {z}`, `Ē_ρ(x₀)` occurs and `Λ̃_t` is a connected
component of `Λ^z_t ∩ B_ρ(x₀)` with `μ_h(Λ̃_t ∩ 𝔸_{ρ/2,ρ}(x₀)) ≤ α μ_h(𝔸_{ρ/2,ρ}(x₀))`, then
`Λ̃_t ∩ closure B_{ρ/2}(x₀) = ∅`.

Stated for every `C₃ > 0` with `b = b(γ, α₀, β⁻, C₃)` (GRAPH G18, G28; stronger than the printed existential `C₃`);
`N₁ a C₁⁻ C₂⁺` and `α a N₀ C₁⁻` are functions, encoding the printed dependences; they may also depend on the
quantities fixed before them (`γ, α₀, β⁻, C₃`; G23 needs `N₁` to depend on `C₃`). One event of probability one
serves all parameters, `z`, `t` and annuli (the proof is deterministic on the event of Lemmas 3.1-3.2). -/
def VeryGoodAnnulusHarnackTypeStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ βminus : ℝ, (2 + γ) ^ 2 / 2 < βminus →
  ∀ C₃ : ℝ, 0 < C₃ → ∃ b ∈ Ioo (0 : ℝ) 1,
  ∃ N₁ : ℝ → ℝ → ℝ → ℕ, ∃ α : ℝ → ℕ → ℝ → ℝ,
    (∀ a ∈ Ioo (0 : ℝ) 1, ∀ C₁m C₂p : ℝ, 0 < C₁m → 0 < C₂p →
      200 ≤ N₁ a C₁m C₂p ∧ ∀ N₀ : ℕ, N₁ a C₁m C₂p ≤ N₀ → α a N₀ C₁m ∈ Ioo (0 : ℝ) 1) ∧
    ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ a ∈ Ioo (0 : ℝ) 1, ∀ C₁m C₁p C₂m C₂p : ℝ, 0 < C₁m → 0 < C₁p → 0 < C₂m → 0 < C₂p →
      ∀ N₀ : ℕ, N₁ a C₁m C₂p ≤ N₀ →
      ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t → ∀ ρ ∈ Ioo (0 : ℝ) 1, ∀ x₀ ∈ ball (0 : ℂ) 1,
      closedBall x₀ ρ ⊆ ball 0 1 \ {z} →
      IsVeryGoodAnnulus (μ ω) βminus ρ x₀ N₀ a b C₁m C₁p C₂m C₂p C₃ →
      ∀ Λ ∈ connectedComponentsIn (cluster (μ ω) 1 z t ∩ ball x₀ ρ),
        μ ω (Λ ∩ annulus x₀ (ρ / 2) ρ) ≤ ENNReal.ofReal (α a N₀ C₁m) * μ ω (annulus x₀ (ρ / 2) ρ) →
        Λ ∩ closedBall x₀ (ρ / 2) = ∅

/-- Lemma 6.12 (lemma:shell-decomposition, line 1636). Fix `ρ ∈ (0,1)` and `x₀ ∈ B_1`, and let `S_j = ∂B_{d_j}(x₀) +
B_{l_j}` with `l_j = ρ 2^{-j/4} 2^{-50}`, `d_0 = 3ρ/4`, `d_j = d_{j-1} - 32 l_{j-1}`. For each `N₀ ≥ 200`:
* (eq:contained-in-annulus) `⋃_j (S_j + B_{8l_j}) ⋐ 𝔸_{ρ/2,ρ}(x₀)`;
* (eq:sparse-shells) `(S_j + B_{8l_j}) ∩ ⋃_{j' ≠ j} S_{j'} = ∅` for `j ≥ 0`;
* (eq:annulus-contained-in-ball) with `ε_j = 2^{-(N₀+j)}` and `d^+_j = d_j + 8l_j`, for each `j ≥ 0` and `w ∈ S_j`:
  `B_{8 ε_j^{1/2} ρ}(w) ⊂ 𝔸_{ρ/2,d^+_j}(x₀) ⊂ 𝔸_{ρ/2,ρ}(x₀)`.

`⋐` is "the closure is compact and contained in" (`B_l` = `ball 0 l`, Minkowski sums). -/
def ShellDecompositionStmt : Prop :=
  ∀ ρ ∈ Ioo (0 : ℝ) 1, ∀ x₀ ∈ ball (0 : ℂ) 1, ∀ N₀ : ℕ, 200 ≤ N₀ →
    (IsCompact (closure (⋃ j, shell x₀ ρ j + ball (0 : ℂ) (8 * shellWidth ρ j))) ∧
      closure (⋃ j, shell x₀ ρ j + ball (0 : ℂ) (8 * shellWidth ρ j)) ⊆ annulus x₀ (ρ / 2) ρ) ∧
    (∀ j : ℕ, (shell x₀ ρ j + ball (0 : ℂ) (8 * shellWidth ρ j)) ∩ (⋃ j' ∈ {j' | j' ≠ j}, shell x₀ ρ j') = ∅) ∧
    ∀ j : ℕ, ∀ w ∈ shell x₀ ρ j,
      ball w (8 * Real.sqrt (shellScale N₀ j) * ρ) ⊆ annulus x₀ (ρ / 2) (shellOuterRadius ρ j) ∧
      annulus x₀ (ρ / 2) (shellOuterRadius ρ j) ⊆ annulus x₀ (ρ / 2) ρ

/-- Lemma 6.13 (lemma:low-mass-implies-small-odometer, line 1710), corrected by [C15]. Let `z ∈ B_1` and
`closure B_ρ(x₀) ⊂ B_1 \ {z}` (printed: "`𝔸_{ρ/2,ρ}(x₀)` not containing `z`", false for `z = x₀`, E16), such that
(VG-iii) occurs with parameters `a, b ∈ (0,1)`, `N₀ ≥ 200` and `C₃ > 0`. Let `{S_j, d^+_j}` be the shell decomposition of
Lemma 6.12, `Λ̃_t` a connected component of `Λ^z_t ∩ B_ρ(x₀)` and `K_j = a M_ρ(x₀) ε_j^{β⁻}`. Then for each `j ≥ 0`:
if `μ_h(Λ̃_t ∩ 𝔸_{3r,5r}(w)) ≤ K_j` for all `r > 0`, `w ∈ B_1` with `𝔸_{r,7r}(w) ⊂ 𝔸_{ρ/2,d^+_j}(x₀)`, then
`sup_{Λ̃_t ∩ 𝔸_{ρ/2,d^+_{j+1}}(x₀)} v^z_t ≤ b^{C' C₃ (N₀+j)} sup_{Λ̃_t ∩ 𝔸_{ρ/2,d^+_j}(x₀)} v^z_t`, where `C' > 0` is
universal.

Stated for every `C₃ > 0` (GRAPH G18; the printed `C₃` is the universal constant of Lemma 6.6). The printed proof
gives the factor `b^{N-1}` with `N` good radii, which needs `N₀` large depending on `C₃` (G23, proof gap); counting all
`N ≥ C₃ log₇ ε_j^{-1/2}` radii gives `b^N`, which suffices for every `C₃ > 0`. -/
def LowMassSmallOdometerStmt : Prop :=
  ∃ C' : ℝ, 0 < C' ∧
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ βminus : ℝ, (2 + γ) ^ 2 / 2 < βminus →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
  ∀ a ∈ Ioo (0 : ℝ) 1, ∀ b ∈ Ioo (0 : ℝ) 1, ∀ N₀ : ℕ, 200 ≤ N₀ → ∀ C₃ : ℝ, 0 < C₃ →
  ∀ ρ : ℝ, 0 < ρ → ∀ x₀ : ℂ, closedBall x₀ ρ ⊆ ball 0 1 \ {z} →
  VeryGoodCriterionThree (μ ω) ρ x₀ N₀ a b C₃ →
  ∀ Λ ∈ connectedComponentsIn (cluster (μ ω) 1 z t ∩ ball x₀ ρ), ∀ j : ℕ,
    (∀ r : ℝ, 0 < r → ∀ w ∈ ball (0 : ℂ) 1,
      annulus w r (7 * r) ⊆ annulus x₀ (ρ / 2) (shellOuterRadius ρ j) →
      μ ω (Λ ∩ annulus w (3 * r) (5 * r)) ≤
        ENNReal.ofReal a * annulusBallMassSize (μ ω) βminus ρ x₀ *
          ENNReal.ofReal (shellScale N₀ j ^ βminus)) →
    ⨆ x ∈ Λ ∩ annulus x₀ (ρ / 2) (shellOuterRadius ρ (j + 1)), odometerExt (μ ω) z t x ≤
      ENNReal.ofReal (b ^ (C' * C₃ * ((N₀ : ℝ) + j))) *
        ⨆ x ∈ Λ ∩ annulus x₀ (ρ / 2) (shellOuterRadius ρ j), odometerExt (μ ω) z t x

/-! ## Sanity lemmas -/

namespace Section6

/-- (VG-iii) holds vacuously for `C₃ ≤ 0`: `log₇ ε^{-1/2} ≥ 0` for `ε = 2^{-n} ≤ 1`. -/
theorem veryGoodCriterionThree_of_nonpos (μ : Measure ℂ) (ρ : ℝ) (x₀ : ℂ) (N₀ : ℕ) (a b : ℝ) {C₃ : ℝ}
    (hC₃ : C₃ ≤ 0) : VeryGoodCriterionThree μ ρ x₀ N₀ a b C₃ := by
  intro n _ w _
  have hε : 0 < dyadicScale n := by unfold dyadicScale; positivity
  have hε1 : dyadicScale n ≤ 1 := by
    unfold dyadicScale; exact pow_le_one₀ (by norm_num) (by norm_num)
  have hlog : 0 ≤ Real.logb 7 (dyadicScale n ^ (-(1 / 2 : ℝ))) := by
    apply Real.logb_nonneg (by norm_num)
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε1 (by norm_num)
  exact (mul_nonpos_of_nonpos_of_nonneg hC₃ hlog).trans (Nat.cast_nonneg _)

/-- The odometer takes the value `+∞` at the pole. -/
@[simp] theorem odometerExt_self (μ : Measure ℂ) (z : ℂ) (t : ℝ) : odometerExt μ z t z = ⊤ := by
  simp [odometerExt]

/-- `σ(h|_U)` modulo additive constant is coarser than `σ(h|_U)`. -/
theorem fieldSigmaAlgebraModConst_le {Ω : Type*} (α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (U : Set ℂ) :
    fieldSigmaAlgebraModConst α₀ hC U ≤ fieldSigmaAlgebra α₀ hC U :=
  iSup₂_le fun φ hφ => le_iSup₂_of_le (f := fun (φ : ℂ → ℝ) (_ : IsTestFunction U φ) =>
    MeasurableSpace.comap (fun ω => fieldPairing α₀ (hC ω) φ) inferInstance) φ hφ.1 le_rfl

/-- The first shell radius is `3ρ/4` (line 1648). -/
@[simp] theorem shellRadius_zero (ρ : ℝ) : shellRadius ρ 0 = 3 / 4 * ρ := rfl

end Section6

end HarmonicBalls
