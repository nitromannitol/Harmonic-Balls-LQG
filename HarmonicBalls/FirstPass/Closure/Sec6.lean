import HarmonicBalls.FirstPass.S6

/-!
# Phase-1 closure of Section 6

For each paper-owned numbered result 6.n of Section 6 (`docs/campaign/INVENTORY.tsv`), `closure_6_n` has the conclusion
of the counted theorem `HarmonicBalls.FirstPass.S6.firstPass_6_n` (`FirstPass/S6.lean`). Its only hypotheses
are the three literature inputs of Section 6, shared by all twelve closures:
* `hDG`: `WholePlaneLQGBallMassBounds` (`Proposed/LQG.lean:154`; Ding-Gwynne arXiv:1807.01072, Lemma 3.8, whole-plane case),
  Proposed, pending source-check;
* `hCC`: `LQGMeasureCoordChange` at insertion `0` (`Proposed/LQG.lean:116`; paper eq:measure-coord, Fact 2.1 IV;
  Duplantier-Sheffield 2011, Prop 2.1), Proposed, pending source-check;
* `hE`: `LQGMeasureExistence` (`Proposed/LQG.lean:68`; paper eq:measure-lim, Section 2.2; Duplantier-Sheffield arXiv:0808.1560,
  Prop 1.1), Proposed, pending source-check.

No numbered result is used as a hypothesis. Lemma 6.5 (annulus iteration, cited from Gwynne-Miller, Ann. Inst. Fourier 70
(2020), Lemma 3.1) is not a closure: it is a cited result, not a paper-owned one, and the chain proves what it
needs. Proof bodies are applications of the `firstPass_6_n` theorems only.
-/

namespace HarmonicBalls.Closure

open HarmonicBalls HarmonicBalls.Section6Full

universe u

variable (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
  (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
  (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)

include hDG hCC hE

/-- Closure of Proposition 6.1 (`prop:harnack-type-property`): the Harnack-type estimate with events `Ē_ρ(x₀)`. -/
theorem closure_6_1 : HarnackTypeEstimateStmt.{u} :=
  HarmonicBalls.FirstPass.S6.firstPass_6_1 hDG hCC hE

/-- Closure of Proposition 6.2 (`prop:harnack-type-stronger-property`): the component form of the Harnack-type estimate. -/
theorem closure_6_2 : HarnackTypeComponentStmt.{u} :=
  HarmonicBalls.FirstPass.S6.firstPass_6_2 hDG hCC hE

/-- Closure of Lemma 6.3 (`lemma:good-annuli`): many good annuli at every lattice point, with the seven-adic radii. -/
theorem closure_6_3 : ManyGoodAnnuliStmt.{u} :=
  HarmonicBalls.FirstPass.S6.firstPass_6_3 hDG hCC hE

/-- Closure of Lemma 6.4 (`lemma:annulus-hit`): a good annulus occurs with probability at least `p`. -/
theorem closure_6_4 : GoodAnnulusProbabilityStmt.{u} :=
  HarmonicBalls.FirstPass.S6.firstPass_6_4 hDG hCC hE

/-- Closure of Lemma 6.6 (`lemma:very-good-annuli`): many very good annuli at every lattice point. -/
theorem closure_6_6 : ManyVeryGoodAnnuliStmt.{u} :=
  HarmonicBalls.FirstPass.S6.firstPass_6_6 hDG hCC hE

/-- Closure of Lemma 6.7 (`lemma:very-good-annuli-hit`): `P[Ē_ρ(x₀)] ≥ p` for all admissible `ρ`, `x₀`. -/
theorem closure_6_7 : VeryGoodAnnulusProbabilityStmt.{u} :=
  HarmonicBalls.FirstPass.S6.firstPass_6_7 hDG hCC hE

/-- Closure of Lemma 6.8 (`lemma:odometer-annuli`): the odometer bound on a union of components of
`𝔸_{s₁r,s₄r}(w) ∩ Λ^z_t`, with a constant depending on `s₁, …, s₄`. -/
theorem closure_6_8 : AnnulusMassBoundByOdometerStmt.{u} :=
  HarmonicBalls.FirstPass.S6.firstPass_6_8 hDG hCC hE

/-- Closure of Lemma 6.9 (`lemma:harmonic-odometer-comparison`): the odometer at `x ∈ A ∩ Λ^z_t` is bounded by the
supremum on `∂A ∩ closure Λ^x_t` times the Brownian exit probability from `A` before `A \ Λ^x_t`. -/
theorem closure_6_9 : OdometerHarmonicMeasureBoundStmt.{u} :=
  HarmonicBalls.FirstPass.S6.firstPass_6_9 hDG hCC hE

/-- Closure of Lemma 6.10 (`lemma:odometer-bound-lqg-mass`): the odometer on the outer annulus is bounded by the
annular LQG mass `SG_ρ(x₀; s₁, s₄)`. -/
theorem closure_6_10 : OdometerBoundByAnnulusMassStmt.{u} :=
  HarmonicBalls.FirstPass.S6.firstPass_6_10 hDG hCC hE

/-- Closure of Lemma 6.11 (`lemma:very-good-annuli-satisfy-harnack-type-estimate`): very good annuli satisfy the
Harnack-type estimate with the constants `N₁`, `α`, `C₃`, `b` of the printed lemma. -/
theorem closure_6_11 : VeryGoodAnnulusHarnackTypeStmt.{u} :=
  HarmonicBalls.FirstPass.S6.firstPass_6_11 hDG hCC hE

/-- Closure of Lemma 6.12 (`lemma:shell-decomposition`): the shells `S_j + B_{8 l_j}` have union compactly contained in
`𝔸_{ρ/2,ρ}(x₀)`. -/
theorem closure_6_12 : ShellDecompositionStmt :=
  HarmonicBalls.FirstPass.S6.firstPass_6_12 hDG hCC hE

/-- Closure of Lemma 6.13 (`lemma:low-mass-implies-small-odometer`, corrected by [C15]): small LQG mass of the shells
forces a small odometer. -/
theorem closure_6_13 : LowMassSmallOdometerStmt.{u} :=
  HarmonicBalls.FirstPass.S6.firstPass_6_13 hDG hCC hE

end HarmonicBalls.Closure
