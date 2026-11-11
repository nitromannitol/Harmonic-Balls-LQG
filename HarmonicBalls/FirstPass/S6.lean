import HarmonicBalls.Proofs.Sec6.FullThreeInputAssembly

/-! # Section 6: the numbered harmonic-measure and annulus estimates

Each `firstPass_6_<n>` has the Draft statement of the printed result 6.<n> as its conclusion
(`HarmonicBalls/Draft/Section6.lean`). Its only hypotheses are the three EXTERNAL LQG background inputs of
`HarmonicBalls.Section6Full.section6Full_of_three_inputs`, which are existing Proposed Props and are reused, not frozen anew:
* `hDG`: `WholePlaneLQGBallMassBounds` (`HarmonicBalls/Proposed/LQG.lean`), whole-plane LQG ball-mass estimates;
* `hCC`: `LQGMeasureCoordChange` (`HarmonicBalls/Proposed/LQG.lean`), the LQG measure under complex affine maps, insertion `0`;
* `hE`: `LQGMeasureExistence` (`HarmonicBalls/Proposed/LQG.lean`), existence of the γ-LQG measure at every insertion `α₀ < Q`.

No numbered result of this paper is used as a hypothesis. The annulus iteration (Lemma 6.5, cited from Gwynne-Miller,
Ann. Inst. Fourier 70 (2020), Lemma 3.1) is not a hypothesis anywhere: it is proved in the chain from the
Lattice-Probability port of Leonardo Bonanno's proof (`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`), and the
Section 2 all-scales volume growth input is derived from `hDG` inside the chain. Lemma 6.5 therefore has no theorem here.
-/

namespace HarmonicBalls.FirstPass.S6

open HarmonicBalls HarmonicBalls.Section6Full

universe u

variable (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
  (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
  (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)

include hDG hCC hE

/-- Proposition 6.1 (`prop:harnack-type-property`): the Harnack-type estimate with events `Ē_ρ(x₀)`. -/
theorem firstPass_6_1 : HarnackTypeEstimateStmt.{u} :=
  harnackTypeEstimateStmt_of_three_inputs hDG hCC hE

/-- Proposition 6.2 (`prop:harnack-type-stronger-property`): the component form of the Harnack-type estimate. -/
theorem firstPass_6_2 : HarnackTypeComponentStmt.{u} :=
  harnackTypeComponentStmt_of_three_inputs hDG hCC hE

/-- Lemma 6.3 (`lemma:good-annuli`): many good annuli at every lattice point, with the seven-adic radii. -/
theorem firstPass_6_3 : ManyGoodAnnuliStmt.{u} :=
  manyGoodAnnuliStmt_of_three_inputs hDG hCC hE

/-- Lemma 6.4 (`lemma:annulus-hit`): a good annulus occurs with probability at least `p`. -/
theorem firstPass_6_4 : GoodAnnulusProbabilityStmt.{u} :=
  goodAnnulusProbabilityStmt_of_three_inputs hDG hCC hE

/-- Lemma 6.6 (`lemma:very-good-annuli`): with polynomially high probability each lattice point `x₀` has at least
`c log₈ ε^{-1/2}` radii `ρ` for which the very good annulus event `Ē_ρ(x₀)` occurs. -/
theorem firstPass_6_6 : ManyVeryGoodAnnuliStmt.{u} :=
  manyVeryGoodAnnuliStmt_of_three_inputs hDG hCC hE

/-- Lemma 6.7 (`lemma:very-good-annuli-hit`): `P[Ē_ρ(x₀)] ≥ p` for all `ρ > 0` and all `x₀` with
`dist(𝔸_{ρ/4,2ρ}(x₀), {0}) ≥ ρ/100`. -/
theorem firstPass_6_7 : VeryGoodAnnulusProbabilityStmt.{u} :=
  veryGoodAnnulusProbabilityStmt_of_three_inputs hDG hCC hE

/-- Lemma 6.8 (`lemma:odometer-annuli`): a bound, with constant `C = C(s₁, …, s₄)`, on the odometer of a union of
connected components of `𝔸_{s₁r,s₄r}(w) ∩ Λ^z_t`. -/
theorem firstPass_6_8 : AnnulusMassBoundByOdometerStmt.{u} :=
  annulusMassBoundByOdometerStmt_of_three_inputs hDG hCC hE

/-- Lemma 6.9 (`lemma:harmonic-odometer-comparison`): the odometer `v^z_t(x)` at `x ∈ A ∩ Λ^z_t` is bounded by the
supremum of `v^z_t` on `∂A ∩ closure Λ^x_t` times the Brownian exit probability from `A` before `A \ Λ^x_t`. -/
theorem firstPass_6_9 : OdometerHarmonicMeasureBoundStmt.{u} :=
  odometerHarmonicMeasureBoundStmt_of_three_inputs hDG hCC hE

/-- Lemma 6.10 (`lemma:odometer-bound-lqg-mass`): `sup_{x ∈ 𝔸_{s₂ρ,s₃ρ}(x₀)} v^z_t(x) ≤ c SG_ρ(x₀; s₁, s₄)`. -/
theorem firstPass_6_10 : OdometerBoundByAnnulusMassStmt.{u} :=
  odometerBoundByAnnulusMassStmt_of_three_inputs hDG hCC hE

/-- Lemma 6.11 (`lemma:very-good-annuli-satisfy-harnack-type-estimate`): very good annuli satisfy the Harnack-type
estimate with the constants `N₁`, `α`, `C₃` and `b` of the printed lemma. -/
theorem firstPass_6_11 : VeryGoodAnnulusHarnackTypeStmt.{u} :=
  veryGoodAnnulusHarnackTypeStmt_of_three_inputs hDG hCC hE

/-- Lemma 6.12 (`lemma:shell-decomposition`): the shells `S_j + B_{8 l_j}` have union compactly contained in
`𝔸_{ρ/2,ρ}(x₀)` (eq:contained-in-annulus), with the radii `d_j` and widths `l_j` of the printed shell decomposition. -/
theorem firstPass_6_12 : ShellDecompositionStmt :=
  shellDecompositionStmt_of_three_inputs hDG hCC hE

/-- Lemma 6.13 (`lemma:low-mass-implies-small-odometer`, corrected by [C15]): under (VG-iii) with parameters `a, b`,
`N₀ ≥ 200` and `C₃`, small LQG mass of the shells forces a small odometer. -/
theorem firstPass_6_13 : LowMassSmallOdometerStmt.{u} :=
  lowMassSmallOdometerStmt_of_three_inputs hDG hCC hE


end HarmonicBalls.FirstPass.S6
