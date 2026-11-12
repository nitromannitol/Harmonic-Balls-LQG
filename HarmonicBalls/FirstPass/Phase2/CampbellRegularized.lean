import HarmonicBalls.FirstPass.Phase2.CampbellCovariance
import HarmonicBalls.FirstPass.Phase2.CampbellJointMeasurable
import LatticeProb.Gauss.GaussianTilt

/-!
# Regularized Campbell identity for the circle-average approximation of the LQG measure

For a whole-plane GFF `h^ℂ` with pairings `(h^ℂ, φ)` and circle averages `h_ε(z)`, a fixed scale `ε > 0` and a point `z`
with `‖z‖ + ε ≤ 1`, weighting the law of the pairings by `ε^{γ²/2} e^{γ h_ε(z)}` shifts every pairing `(h^ℂ, φ)` by
`γ Cov((h^ℂ, φ), h_ε(z))` (the Cameron-Martin tilt of a Gaussian process, with `Var h_ε(z) = -log ε`). Integrating
over a set `U` of such points and exchanging the integrals gives the regularized form of the Campbell identity for the
rooted measure (Duplantier-Sheffield, §3.3; Duplantier-Miller-Sheffield, Lemma A.10, proof):
`E ∫_U Φ((h^ℂ, ·), z) ε^{γ²/2} e^{γ h_ε(z)} dz = ∫_U E Φ((h^ℂ, ·) + γ Cov((h^ℂ, ·), h_ε(z)), z) dz`.

## Main results

* `IsWholePlaneGFF.lintegral_circleWeight_mul_eq`: the identity at a fixed point `z`.
* `IsWholePlaneGFF.lintegral_lintegral_circleWeight_mul_eq`: the identity integrated over `U`.
-/

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

namespace HarmonicBalls

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Gaussian tilt by a circle average.** For `ε > 0`, `‖z‖ + ε ≤ 1` and a measurable `Φ` of the pairings with
test functions, `E[ε^{γ²/2} e^{γ h_ε(z)} Φ((h^ℂ, ·))] = E[Φ((h^ℂ, ·) + γ Cov((h^ℂ, ·), h_ε(z)))]`. -/
theorem IsWholePlaneGFF.lintegral_circleWeight_mul_eq (hh : IsWholePlaneGFF P hC hcirc) {ε : ℝ} (hε : 0 < ε)
    {z : ℂ} (hz : ‖z‖ + ε ≤ 1) (γ : ℝ) {Φ : ({φ : ℂ → ℝ // IsTestFunction univ φ} → ℝ) → ℝ≥0∞}
    (hΦ : Measurable Φ) :
    ∫⁻ ω, ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω ε z)) * Φ (fun φ => hC ω φ.1) ∂P
      = ∫⁻ ω, Φ (fun φ => hC ω φ.1 + γ * cov[fun ω => hC ω φ.1, fun ω => hcirc ω ε z; P]) ∂P := by
  have : IsProbabilityMeasure P := hh.isGaussianProcess.isProbabilityMeasure
  let o : Option {φ : ℂ → ℝ // IsTestFunction univ φ} → GFFObservable.Admissible := fun t =>
    Option.elim t ⟨.circle ε z, hε⟩ fun φ => ⟨.pairing φ.1, φ.2⟩
  have hY := hh.isGaussianProcess.comp_right o
  have hYm : ∀ t, Measurable fun ω => (o t).1.eval (hC ω) (hcirc ω) := by
    rintro (_ | φ)
    · exact hh.measurable_circle ε z hε
    · exact hh.measurable_pairing φ.1 φ.2
  have hcen : ∀ t, P[fun ω => (o t).1.eval (hC ω) (hcirc ω)] = 0 := fun t =>
    hh.integral_eq_zero (o t).1 (o t).2
  have hΦ' : Measurable fun x : Option {φ : ℂ → ℝ // IsTestFunction univ φ} → ℝ => Φ fun φ => x (some φ) :=
    hΦ.comp (measurable_pi_iff.mpr fun φ => measurable_pi_apply (some φ))
  have key := LatticeProb.Gauss.lintegral_exp_mul_tilt hY hYm hcen none γ hΦ'
  have hvar : Var[fun ω => hcirc ω ε z; P] = -Real.log ε := hh.variance_circle_eq_neg_log hε hz
  have hw : ∀ ω, ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω ε z) =
      Real.exp (γ * hcirc ω ε z - γ ^ 2 * Var[fun ω => hcirc ω ε z; P] / 2) := fun ω => by
    rw [hvar, Real.rpow_def_of_pos hε, ← Real.exp_add]
    congr 1
    ring
  simp only [hw]
  exact key

/-- **Regularized Campbell identity.** For `ε > 0`, a measurable set `U` with `‖z‖ + ε ≤ 1` on `U` and a measurable
`Φ` of the pairings with test functions and of the point,
`E ∫_U ε^{γ²/2} e^{γ h_ε(z)} Φ((h^ℂ, ·), z) dz = ∫_U E Φ((h^ℂ, ·) + γ Cov((h^ℂ, ·), h_ε(z)), z) dz`. -/
theorem IsWholePlaneGFF.lintegral_lintegral_circleWeight_mul_eq (hh : IsWholePlaneGFF P hC hcirc) {ε : ℝ}
    (hε : 0 < ε) (γ : ℝ) {U : Set ℂ} (hU : MeasurableSet U) (hU1 : ∀ z ∈ U, ‖z‖ + ε ≤ 1)
    {Φ : ({φ : ℂ → ℝ // IsTestFunction univ φ} → ℝ) × ℂ → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ ω, ∫⁻ z in U, ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω ε z)) *
        Φ (fun φ => hC ω φ.1, z) ∂volume ∂P
      = ∫⁻ z in U, ∫⁻ ω, Φ (fun φ => hC ω φ.1 + γ * cov[fun ω => hC ω φ.1, fun ω => hcirc ω ε z; P], z) ∂P
          ∂volume := by
  have : IsProbabilityMeasure P := hh.isGaussianProcess.isProbabilityMeasure
  have hpr : Measurable fun p : Ω × ℂ => (fun φ : {φ : ℂ → ℝ // IsTestFunction univ φ} => hC p.1 φ.1) :=
    measurable_pi_iff.mpr fun φ => (hh.measurable_pairing φ.1 φ.2).comp measurable_fst
  have hmeas : AEMeasurable (Function.uncurry fun ω z => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) *
      Real.exp (γ * hcirc ω ε z)) * Φ (fun φ => hC ω φ.1, z)) (P.prod (volume.restrict U)) := by
    refine (ENNReal.measurable_ofReal.comp_aemeasurable (aemeasurable_const.mul
      (Real.measurable_exp.comp_aemeasurable (aemeasurable_const.mul
        (hh.aemeasurable_circle_uncurry hε (volume.restrict U)))))).mul ?_
    exact (hΦ.comp (hpr.prodMk measurable_snd)).aemeasurable
  rw [lintegral_lintegral_swap hmeas]
  refine setLIntegral_congr_fun hU fun z hz => ?_
  exact hh.lintegral_circleWeight_mul_eq hε (hU1 z hz) γ (hΦ.comp (measurable_id.prodMk measurable_const))

end HarmonicBalls
