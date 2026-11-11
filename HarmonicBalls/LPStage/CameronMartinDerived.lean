import Mathlib
import HarmonicBalls.LPStage.GFF

/-!
# Cameron-Martin facts for the whole-plane GFF (LP stage)

LP forms of the two derived Cameron-Martin facts of the Harmonic-balls draft, stated on the LP-stage whole-plane GFF
(`LatticeProb.Gauss.IsWholePlaneGFF`, `HarmonicBalls/LPStage/GFF.lean`):

* `LatticeProb.Gauss.CameronMartinGFFReweighting`: the Cameron-Martin theorem for the whole-plane GFF
  (Miller-Sheffield, Imaginary Geometry IV, arXiv:1302.4738v2, Proposition 2.9). LP form of
  `HarmonicBalls.S11aj.CameronMartinGFFReweighting` (`HarmonicBalls/FirstPass/Frozen/S11aj.lean:33`).
* `LatticeProb.Gauss.CameronMartinGFFMutualAbsCont`: mutual absolute continuity of the shifted whole-plane GFF on
  distribution-level events (Miller-Sheffield, Imaginary Geometry IV, Proposition 2.9). LP form of
  `HarmonicBalls.CameronMartinGFFMutualAbsCont` (`HarmonicBalls/FirstPass/Frozen/S11d.lean:74`).

This file holds the statements, and the copied LP versions of the Gaussian-law helpers that the derivation of the second
statement from the first uses (`gaussian_process_map_eq_of_mean_covariance`, `wholePlaneGFF_localFieldPairings_map_eq`,
copied from `HarmonicBalls/Steps/Sec11/GaussianProcessLaw.lean:17` and `:68`). The derivation of
`CameronMartinGFFReweighting` (`HarmonicBalls/FirstPass/Phase2/CameronMartinReweightingDerived2.lean:267`) is not yet
copied: its closure exceeds the copy budget (see `notes/z7.md`). Neither statement is proved in this file yet.
-/

namespace LatticeProb.Gauss

open MeasureTheory ProbabilityTheory

universe u

/-- Test functions supported in `U`, as a subtype (LP copy of `HarmonicBalls.LocalFieldTest`,
`HarmonicBalls/Steps/Sec11/LocalPairingLaw.lean:17`). -/
def LocalFieldTest (U : Set ℂ) := {φ : ℂ → ℝ // IsTestFunction U φ}

/-- The process of local pairings of the log-singular field (LP copy of `HarmonicBalls.localFieldPairings`,
`HarmonicBalls/Steps/Sec11/LocalPairingLaw.lean:20`). -/
noncomputable def localFieldPairings {Ω : Type*} (α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (U : Set ℂ) (ω : Ω) : LocalFieldTest U → ℝ :=
  fun φ => fieldPairing α₀ (hC ω) φ.1

/-- Real Gaussian processes with the same means and covariances have the same joint law. No countability assumption
on the index set is needed (LP copy of `HarmonicBalls.gaussian_process_map_eq_of_mean_covariance`,
`HarmonicBalls/Steps/Sec11/GaussianProcessLaw.lean:17`). -/
theorem gaussian_process_map_eq_of_mean_covariance
    {Ω Ω' T : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (Q : Measure Ω') (X : T → Ω → ℝ) (Y : T → Ω' → ℝ)
    (hX : IsGaussianProcess X P) (hY : IsGaussianProcess Y Q)
    (hXm : ∀ t, Measurable (X t)) (hYm : ∀ t, Measurable (Y t))
    (hmean : ∀ t, (∫ ω, X t ω ∂P) = ∫ ω, Y t ω ∂Q)
    (hcov : ∀ s t, cov[X s, X t; P] = cov[Y s, Y t; Q]) :
    P.map (fun ω t => X t ω) = Q.map (fun ω t => Y t ω) := by
  let := hX.isProbabilityMeasure
  let := hY.isProbabilityMeasure
  have hXall : AEMeasurable (fun ω t => X t ω) P := (measurable_pi_iff.mpr hXm).aemeasurable
  have hYall : AEMeasurable (fun ω t => Y t ω) Q := (measurable_pi_iff.mpr hYm).aemeasurable
  apply (isProjectiveLimit_map hXall).unique
  intro I
  have hfinite : P.map (fun ω => I.restrict (X · ω)) =
      Q.map (fun ω => I.restrict (Y · ω)) := by
    apply (MeasurableEquiv.toLp 2 (_ → ℝ)).map_measurableEquiv_injective
    rw [MeasurableEquiv.coe_toLp, ← PiLp.coe_symm_continuousLinearEquiv 2 ℝ]
    have := (hX.hasGaussianLaw I).isGaussian_map
    have := (hY.hasGaussianLaw I).isGaussian_map
    apply IsGaussian.ext
    · rw [integral_map, integral_map, integral_map, integral_map]
      · simp only [id_eq]
        rw [ContinuousLinearEquiv.integral_comp_comm, ContinuousLinearEquiv.integral_comp_comm]
        congr 1
        funext i
        rw [eval_integral, eval_integral]
        · exact hmean i
        · exact fun i => (hY.hasGaussianLaw_eval _).integrable
        · exact fun i => (hX.hasGaussianLaw_eval _).integrable
      all_goals first
        | fun_prop
        | exact (measurable_pi_iff.mpr fun i : I => hXm i).aemeasurable
        | exact (measurable_pi_iff.mpr fun i : I => hYm i).aemeasurable
    · rw [← ContinuousLinearMap.toBilinForm_inj]
      refine LinearMap.BilinForm.ext_of_isSymm isPosSemidef_covarianceBilin.isSymm
        isPosSemidef_covarianceBilin.isSymm fun x => ?_
      simp only [ContinuousLinearMap.toBilinForm_apply]
      rw [PiLp.coe_symm_continuousLinearEquiv, covarianceBilin_apply_pi, covarianceBilin_apply_pi]
      · congrm ∑ i, ∑ j, _ * ?_
        rw [covariance_map, covariance_map]
        · exact hcov i j
        all_goals first | exact Measurable.aestronglyMeasurable (by fun_prop) | exact .of_eval (fun _ => hX.aemeasurable _) | exact .of_eval (fun _ => hY.aemeasurable _)
      · exact fun i => (IsGaussian.hasGaussianLaw_id.eval i).memLp_two
      · exact fun i => (IsGaussian.hasGaussianLaw_id.eval i).memLp_two
  rw [isProjectiveLimit_map hYall I]
  exact hfinite.symm

/-- Two whole-plane GFF realizations have identical joint laws for every collection of local test-function pairings
(LP copy of `HarmonicBalls.wholePlaneGFF_localFieldPairings_map_eq`, `HarmonicBalls/Steps/Sec11/GaussianProcessLaw.lean:68`). -/
theorem wholePlaneGFF_localFieldPairings_map_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ}
    (hP : IsWholePlaneGFF P hC hcirc) (hQ : IsWholePlaneGFF Q hC' hcirc')
    (α₀ : ℝ) (U : Set ℂ) :
    P.map (localFieldPairings α₀ hC U) = Q.map (localFieldPairings α₀ hC' U) := by
  let o (φ : LocalFieldTest U) : GFFObservable.Admissible :=
    ⟨.pairing φ.1, ⟨φ.2.1, φ.2.2.1, Set.subset_univ _⟩⟩
  let X (φ : LocalFieldTest U) (ω : Ω) := hC ω φ.1
  let Y (φ : LocalFieldTest U) (ω : Ω') := hC' ω φ.1
  have hX : IsGaussianProcess X P := hP.isGaussianProcess.comp_right o
  have hY : IsGaussianProcess Y Q := hQ.isGaussianProcess.comp_right o
  have hXm : ∀ φ, Measurable (X φ) := fun φ => hP.measurable_pairing _ (o φ).2
  have hYm : ∀ φ, Measurable (Y φ) := fun φ => hQ.measurable_pairing _ (o φ).2
  have hmean : ∀ φ, (∫ ω, X φ ω ∂P) = ∫ ω, Y φ ω ∂Q := by
    intro φ
    exact (hP.integral_eq_zero _ (o φ).2).trans (hQ.integral_eq_zero _ (o φ).2).symm
  have hcov : ∀ φ ψ, cov[X φ, X ψ; P] = cov[Y φ, Y ψ; Q] := by
    intro φ ψ
    exact (hP.covariance_eq _ _ (o φ).2 (o ψ).2).trans
      (hQ.covariance_eq _ _ (o φ).2 (o ψ).2).symm
  have heq := gaussian_process_map_eq_of_mean_covariance P Q X Y hX hY hXm hYm hmean hcov
  let F (v : LocalFieldTest U → ℝ) (φ : LocalFieldTest U) :=
    v φ - α₀ * ∫ x, φ.1 x * Real.log ‖x‖
  have hF : Measurable F := by
    apply measurable_pi_iff.mpr
    intro φ
    exact (measurable_pi_apply φ).sub measurable_const
  have hPX : Measurable (fun ω φ => X φ ω) := measurable_pi_iff.mpr hXm
  have hQY : Measurable (fun ω φ => Y φ ω) := measurable_pi_iff.mpr hYm
  have hmap := congrArg (fun ν : Measure (LocalFieldTest U → ℝ) => ν.map F) heq
  rw [Measure.map_map hF hPX, Measure.map_map hF hQY] at hmap
  exact hmap

/-- **LP form of the Cameron-Martin theorem for the whole-plane GFF.** For every whole-plane GFF `(P, hC, hcirc)` and
every smooth compactly supported `f` with zero unit-circle average, there is a measure `P'` equivalent to `P` under
which the shifted pairings `addFunPairing (hC ω) f` and the shifted circle averages `hcirc ω r z + Av_{∂B_r(z)} f`
form a whole-plane GFF (Miller-Sheffield, Imaginary Geometry IV, Proposition 2.9). Statement only; no proof yet. -/
def CameronMartinGFFReweighting : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc → ∀ f : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f →
    HasCompactSupport f → Real.circleAverage f 0 1 = 0 →
    ∃ P' : Measure Ω, P' ≪ P ∧ P ≪ P' ∧
      IsWholePlaneGFF P' (fun ω => addFunPairing (hC ω) f)
        (fun ω r z => hcirc ω r z + Real.circleAverage f z r)

/-- **LP form of the mutual absolute continuity of the shifted whole-plane GFF.** For every whole-plane GFF `(P, hC,
hcirc)` and smooth compactly supported `g` with zero unit-circle average, `hC` under `P` and `hC + g` have the same null
sets among the events of `distributionMeasurableSpace` (the σ-algebra generated by the test pairings). LP form of
`HarmonicBalls.CameronMartinGFFMutualAbsCont` (`HarmonicBalls/FirstPass/Frozen/S11d.lean:74`). Statement only; no proof
yet. -/
def CameronMartinGFFMutualAbsCont : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (g : ℂ → ℝ), IsWholePlaneGFF P hC hcirc → ContDiff ℝ (⊤ : ℕ∞) g →
    HasCompactSupport g → Real.circleAverage g 0 1 = 0 →
    ∀ B : Set ((ℂ → ℝ) → ℝ), MeasurableSet[distributionMeasurableSpace] B →
      (P ((fun ω => hC ω) ⁻¹' B) = 0 ↔ P ((fun ω => addFunPairing (hC ω) g) ⁻¹' B) = 0)

end LatticeProb.Gauss
