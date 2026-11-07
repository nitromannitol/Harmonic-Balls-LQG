import HarmonicBalls.Proofs.Sec8.CenteredCircleLocal
import HarmonicBalls.Proofs.Sec8.CirclePairingCovariance

/-! # Circle averages as limits of annular field pairings

The imported Section 8 development uses Leonardo Bonanno's
`LatticeProb.Bonanno.LQGMetric.Field.CameronMartin` formalization.+-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ProbabilityTheory

namespace HarmonicBalls

/-- Normalized annular pairings converge in probability to the corresponding
whole-plane GFF circle average. -/
theorem IsWholePlaneGFF.tendstoInMeasure_circleDensity_pairing
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) {r η : ℝ}
    (hr : 0 < r) (hη : 0 < η) (z : ℂ) :
    TendstoInMeasure P (fun n ω => hC ω (fun x =>
      (∫ y, circleDensity r (circleDensityWidth r η n)
        (circleDensityWidth_pos hr hη n) 0 y)⁻¹ *
      circleDensity r (circleDensityWidth r η n) (circleDensityWidth_pos hr hη n) z x))
      atTop (fun ω => hcirc ω r z) := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  let φ : ℕ → ℂ → ℝ := fun n x =>
    (∫ y, circleDensity r (circleDensityWidth r η n)
      (circleDensityWidth_pos hr hη n) 0 y)⁻¹ *
      circleDensity r (circleDensityWidth r η n) (circleDensityWidth_pos hr hη n) z x
  have hφ (n : ℕ) : IsTestFunction univ (φ n) := by
    refine ⟨contDiff_const.mul (circleDensity_contDiff _ _ _ _), ?_, subset_univ _⟩
    exact (circleDensity_hasCompactSupport hr.le (circleDensityWidth_pos hr hη n) z).mul_left
  have hp (n : ℕ) : MemLp (fun ω => hC ω (φ n)) 2 P :=
    (hGFF.isGaussianProcess.hasGaussianLaw_eval
      (⟨.pairing (φ n), hφ n⟩ : GFFObservable.Admissible)).memLp (by simp)
  have hc : MemLp (fun ω => hcirc ω r z) 2 P :=
    (hGFF.hasGaussianLaw_circle hr z).memLp (by simp)
  have hm (n : ℕ) : ∫ ω, (hC ω (φ n) - hcirc ω r z) ∂P = 0 := by
    have hp0 := hGFF.integral_eq_zero (.pairing (φ n)) (hφ n)
    have hc0 := hGFF.integral_eq_zero (.circle r z) hr
    simp only [GFFObservable.eval] at hp0 hc0
    rw [integral_sub ((hp n).integrable (by simp)) (hc.integrable (by simp)), hp0, hc0, sub_zero]
  have hv (n : ℕ) : variance (fun ω => hC ω (φ n) - hcirc ω r z) P =
      wholePlaneGFFCov (.pairing (φ n)) (.pairing (φ n)) +
      wholePlaneGFFCov (.circle r z) (.circle r z) -
      2 * wholePlaneGFFCov (.pairing (φ n)) (.circle r z) := by
    change variance ((fun ω => hC ω (φ n)) - (fun ω => hcirc ω r z)) P = _
    rw [variance_sub (hp n) hc, ← covariance_self (hp n).aemeasurable,
      ← covariance_self hc.aemeasurable]
    have hpp := hGFF.covariance_eq (.pairing (φ n)) (.pairing (φ n)) (hφ n) (hφ n)
    have hcc := hGFF.covariance_eq (.circle r z) (.circle r z) hr hr
    have hpc := hGFF.covariance_eq (.pairing (φ n)) (.circle r z) (hφ n) hr
    simp only [GFFObservable.eval] at hpp hcc hpc
    rw [hpp, hcc, hpc]
    ring
  have hvar : Tendsto (fun n => variance (fun ω => hC ω (φ n) - hcirc ω r z) P)
      atTop (𝓝 0) := by
    have hself := circleDensity_pairing_covariance_tendsto hr hη z z
    have hcross := circleDensity_circle_covariance_tendsto hr hη hr z z
    have h := (hself.add_const (wholePlaneGFFCov (.circle r z) (.circle r z))).sub
      (hcross.const_mul (2 : ℝ))
    have h' : Tendsto (fun n => wholePlaneGFFCov (.pairing (φ n)) (.pairing (φ n)) +
      wholePlaneGFFCov (.circle r z) (.circle r z) -
      2 * wholePlaneGFFCov (.pairing (φ n)) (.circle r z)) atTop (𝓝 0) := by
      convert h using 1
      simp
      ring
    simpa only [hv] using h'
  exact tendstoInMeasure_of_centered_variance_tendsto_zero P _ _
    (fun n => (hp n).sub hc) hm hvar

#print axioms IsWholePlaneGFF.tendstoInMeasure_circleDensity_pairing
end HarmonicBalls
