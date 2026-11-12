import HarmonicBalls.Proofs.GFF.FullObservableDilationMixing
import HarmonicBalls.Proofs.Sec6.ContinuousWeylCircleAverage
import HarmonicBalls.Proofs.Sec8.CircleLogPotential
import HarmonicBalls.Proposed.DuplantierMillerSheffield

/-!
# Covariance facts for the Campbell identity of the whole-plane LQG measure

The proof of the rooted-measure description of the LQG measure (Duplantier-Miller-Sheffield, Lemma A.10) weights the
field by `ε^{γ²/2} e^{γ h_ε(z)}` and tilts it by the Cameron-Martin shift `γ Cov(·, h_ε(z))`. This file collects the
covariance facts used there.

* `wholePlaneGFFCov_circle_self_eq_neg_log`, `IsWholePlaneGFF.variance_circle_eq_neg_log`: inside the unit disk,
  `Var(h_ε(z)) = -log ε`, so the weight `ε^{γ²/2} e^{γ h_ε(z)}` has mean one.
* `tendsto_wholePlaneGFFCov_circle`, `IsWholePlaneGFF.tendsto_covariance_pairing_circle`: as `ε → 0`, the covariance
  of an admissible observable with `h_ε(z)` converges to its covariance potential at `z`.
* `mul_wholePlaneCov_eq_dmsShift`, `mul_observableCovariancePotential_pairing_eq`: for `‖z‖ ≤ 1`, `γ` times the
  covariance kernel at `z` is the shift `f_z(w) = -γ log |w - z| + γ log max(|w|, 1)` of Lemma A.10.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Metric Set
open scoped Topology

namespace HarmonicBalls

/-- Inside the closed unit disk the variance of a circle average is `-log ε`. -/
theorem wholePlaneGFFCov_circle_self_eq_neg_log {ε : ℝ} (hε : 0 < ε) {z : ℂ} (hz : ‖z‖ + ε ≤ 1) :
    wholePlaneGFFCov (.circle ε z) (.circle ε z) = -Real.log ε := by
  have hdisk : ∀ x ∈ Metric.sphere z ε, ‖x‖ ≤ 1 := fun x hx => by
    rw [mem_sphere_iff_norm] at hx
    calc ‖x‖ = ‖(x - z) + z‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - z‖ + ‖z‖ := norm_add_le _ _
      _ ≤ 1 := by linarith
  have hN0 : Real.circleAverage wholePlaneNormalization z ε = 0 := by
    have hEq : Set.EqOn wholePlaneNormalization (fun _ => (0 : ℝ)) (Metric.sphere z |ε|) := by
      intro y hy
      rw [abs_of_pos hε] at hy
      simp [wholePlaneNormalization, max_eq_right (hdisk y hy)]
    rw [Real.circleAverage_congr_sphere hEq, Real.circleAverage_const]
  have hinner : ∀ x ∈ Metric.sphere z ε,
      Real.circleAverage (fun y => wholePlaneCov x y) z ε = -Real.log ε := by
    intro x hx
    have hx0 : wholePlaneNormalization x = 0 := by
      simp [wholePlaneNormalization, max_eq_right (hdisk x hx)]
    have hzx : ‖z - x‖ = ε := by
      rw [← dist_eq_norm, dist_comm]
      exact mem_sphere.1 hx
    rw [circleAverage_wholePlaneCov_eq hε z x, hx0, hN0, hzx, max_self]
    ring
  have hEq : Set.EqOn (fun x => Real.circleAverage (fun y => wholePlaneCov x y) z ε)
      (fun _ => -Real.log ε) (Metric.sphere z |ε|) := by
    rw [abs_of_pos hε]
    exact hinner
  show Real.circleAverage (fun x => Real.circleAverage (fun y => wholePlaneCov x y) z ε) z ε
    = -Real.log ε
  rw [Real.circleAverage_congr_sphere hEq, Real.circleAverage_const]

/-- Inside the closed unit disk, `Var(h_ε(z)) = -log ε`. -/
theorem IsWholePlaneGFF.variance_circle_eq_neg_log {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc) {ε : ℝ} (hε : 0 < ε)
    {z : ℂ} (hz : ‖z‖ + ε ≤ 1) :
    Var[fun ω => hcirc ω ε z; P] = -Real.log ε := by
  have hm : AEMeasurable (fun ω => hcirc ω ε z) P := (hh.measurable_circle ε z hε).aemeasurable
  have hc : cov[fun ω => hcirc ω ε z, fun ω => hcirc ω ε z; P] =
      wholePlaneGFFCov (.circle ε z) (.circle ε z) :=
    hh.covariance_eq (.circle ε z) (.circle ε z) hε hε
  rw [← covariance_self hm, hc, wholePlaneGFFCov_circle_self_eq_neg_log hε hz]

/-- The covariance of a circle average `h_ε(z)` with an admissible observable converges, as `ε → 0`, to the covariance
potential of the observable at `z`. -/
theorem tendsto_wholePlaneGFFCov_circle (o : GFFObservable.Admissible) (z : ℂ) :
    Tendsto (fun ε : ℝ => wholePlaneGFFCov (.circle ε z) o.1) (𝓝 0)
      (𝓝 (observableCovariancePotential o.1 z)) := by
  have ht := (Section6.continuous_circleAverage_radius_center
    (continuous_observableCovariancePotential o)).tendsto (0, z)
  have hlim := ht.comp (tendsto_id.prodMk_nhds (tendsto_const_nhds (x := z)))
  simp only [Function.comp_def, id, Real.circleAverage_zero] at hlim
  exact hlim

/-- The covariance of the pairing `(h, φ)` with the circle average `h_ε(z)` converges, as `ε ↓ 0`, to the logarithmic
covariance potential `∫ φ(w) K(z, w) dw` of `φ` at `z`. -/
theorem IsWholePlaneGFF.tendsto_covariance_pairing_circle {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc) {φ : ℂ → ℝ}
    (hφ : IsTestFunction univ φ) (z : ℂ) :
    Tendsto (fun ε => cov[fun ω => hC ω φ, fun ω => hcirc ω ε z; P]) (𝓝[>] 0)
      (𝓝 (observableCovariancePotential (.pairing φ) z)) := by
  have hlim := (tendsto_wholePlaneGFFCov_circle ⟨.pairing φ, hφ⟩ z).mono_left
    (nhdsWithin_le_nhds (s := Ioi 0))
  refine hlim.congr' (eventually_nhdsWithin_of_forall fun ε hε => ?_)
  exact (hh.covariance_observable_circle_eq_potential ⟨.pairing φ, hφ⟩ hε z).symm

/-- For `‖z‖ ≤ 1`, `γ K(z, w) = f_z(w) = -γ log |w - z| + γ log max(|w|, 1)`, at every `w` (both sides vanish at
`w = z` with the convention `log 0 = 0`). -/
theorem mul_wholePlaneCov_eq_dmsShift {z : ℂ} (hz : ‖z‖ ≤ 1) (γ : ℝ) (w : ℂ) :
    γ * wholePlaneCov z w = dmsShift γ z w := by
  unfold wholePlaneCov dmsShift
  rcases eq_or_ne w z with rfl | hwz
  · simp [max_eq_right hz]
  · have h1 : 0 < ‖z - w‖ := norm_pos_iff.2 (sub_ne_zero.2 hwz.symm)
    have h2 : 0 < max ‖w‖ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    rw [max_eq_right hz, one_mul, Real.log_div h2.ne' h1.ne', norm_sub_rev]
    ring

/-- For `‖z‖ ≤ 1`, `γ` times the covariance potential of the pairing with `φ` at `z` is the pairing of the shift
`f_z` of Lemma A.10 with `φ`. -/
theorem mul_observableCovariancePotential_pairing_eq {z : ℂ} (hz : ‖z‖ ≤ 1) (γ : ℝ) (φ : ℂ → ℝ) :
    γ * observableCovariancePotential (.pairing φ) z = ∫ w, dmsShift γ z w * φ w := by
  change γ * ∫ w, φ w * wholePlaneCov z w = _
  rw [← integral_const_mul]
  congr 1
  funext w
  rw [← mul_wholePlaneCov_eq_dmsShift hz γ w]
  ring

end HarmonicBalls
