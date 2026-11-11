import HarmonicBalls.Proofs.Sec8.CenteredCircleLocal
import HarmonicBalls.Proofs.Sec8.CommonApproximationLaw
import HarmonicBalls.Proofs.Sec6.AnnulusLawTransfer

/-! # Local test approximations of centered circles

The imported Section 8 development uses Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization.
-/

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ProbabilityTheory

namespace HarmonicBalls

/-- A centered circle average is the limit in probability of pairings with
local mean-zero tests. The tests are the signed annular approximations used
in the construction of the local circle decoder. -/
theorem IsWholePlaneGFF.exists_localPairing_centeredCircle_approximation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ε r : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hr : 0 < r) (z : ℂ)
    (hz : closedBall z r ⊆ ball 0 ε) :
    ∃ φ : ℕ → Section6.LocalTest (ball 0 ε),
      TendstoInMeasure P (fun n ω => Section6.localPairingProc (ball 0 ε) hC ω (φ n))
        atTop (fun ω => hcirc ω r z - hcirc ω r 0) := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  obtain ⟨η, hη, _, htests, _, _⟩ := exists_local_circleDensity_tests hr z hz
  let ψ := circleDensityDifference r η hr hη z
  have htest (n : ℕ) : IsTestFunction (ball 0 ε) (ψ n) ∧ ∫ x, ψ n x = 0 := htests n
  have htestU (n : ℕ) : IsTestFunction univ (ψ n) :=
    ⟨(htest n).1.1, (htest n).1.2.1, subset_univ _⟩
  let φ : ℕ → Section6.LocalTest (ball 0 ε) := fun n =>
    ⟨⟨⟨ψ n, (htest n).1.1, (htest n).1.2.1, subset_univ _⟩, (htest n).2⟩,
      (htest n).1.2.2⟩
  refine ⟨φ, ?_⟩
  have hp (n : ℕ) : MemLp (fun ω => hC ω (ψ n)) 2 P :=
    (hGFF.isGaussianProcess.hasGaussianLaw_eval
      (⟨.pairing (ψ n), htestU n⟩ : GFFObservable.Admissible)).memLp (by simp)
  have hzLp : MemLp (fun ω => hcirc ω r z) 2 P :=
    (hGFF.hasGaussianLaw_circle hr z).memLp (by simp)
  have h0Lp : MemLp (fun ω => hcirc ω r 0) 2 P :=
    (hGFF.hasGaussianLaw_circle hr 0).memLp (by simp)
  have hm : ∀ n, ∫ ω, (hC ω (ψ n) - (hcirc ω r z - hcirc ω r 0)) ∂P = 0 := by
    intro n
    have hp0 := hGFF.integral_eq_zero (.pairing (ψ n)) (htestU n)
    have hz0 := hGFF.integral_eq_zero (.circle r z) hr
    have h00 := hGFF.integral_eq_zero (.circle r 0) hr
    simp only [GFFObservable.eval] at hp0 hz0 h00
    have hxy : Integrable (fun ω => hcirc ω r z - hcirc ω r 0) P :=
      (hzLp.sub h0Lp).integrable (by simp)
    rw [integral_sub ((hp n).integrable (by simp)) hxy,
      integral_sub (hzLp.integrable (by simp)) (h0Lp.integrable (by simp)), hp0, hz0, h00]
    ring
  have hkernel := hGFF.circleDensityDifference_error_tendsto_of_self hr hη z
    (hGFF.circleDensityDifference_self_covariance_tendsto hr hη z)
  have hvar : Tendsto (fun n => variance
      (fun ω => hC ω (ψ n) - (hcirc ω r z - hcirc ω r 0)) P) atTop (𝓝 0) := by
    convert hkernel using 1
    funext n
    exact hGFF.variance_pairing_sub_circle_difference hr z (ψ n) (htestU n)
  exact tendstoInMeasure_of_centered_variance_tendsto_zero P _ _
    (fun n => (hp n).sub (hzLp.sub h0Lp)) hm hvar

/-- The same local test sequence gives a joint field and circle law comparison
when it converges to the corresponding centered circle under the second law.
The deterministic correction accounts for the logarithmic singularity. -/
theorem IsWholePlaneGFF.exists_localPairing_tests_for_joint_circle_law
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {α₀ ε r : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hr : 0 < r) (z : ℂ)
    (hz : closedBall z r ⊆ ball 0 ε) :
    ∃ φ : ℕ → Section6.LocalTest (ball 0 ε),
      ∀ {Ξ : Type*} [MeasurableSpace Ξ] (Q : Measure Ξ)
        (Y : Ξ → (Section6.LocalTest (ball 0 ε) → ℝ)) (_hY : Measurable Y)
        (_hdom : Q.map Y ≪ P.map (Section6.localPairingProc (ball 0 ε) hC))
        (g : Ξ → ℝ),
        TendstoInMeasure Q (fun n ξ => Y ξ (φ n)) atTop
          (fun ξ => g ξ + α₀ * (Real.circleAverage (fun x => Real.log ‖x‖) z r -
            Real.circleAverage (fun x => Real.log ‖x‖) 0 r)) →
        Q.map (fun ξ => (Y ξ, g ξ)) ≪
          P.map (fun ω => (Section6.localPairingProc (ball 0 ε) hC ω,
            fieldCircleAverage α₀ (hcirc ω) r z -
              fieldCircleAverage α₀ (hcirc ω) r 0)) := by
  obtain ⟨φ, hφ⟩ := hGFF.exists_localPairing_centeredCircle_approximation hr z hz
  refine ⟨φ, ?_⟩
  intro Ξ _ Q Y hY hdom g hlim
  let X := Section6.localPairingProc (ball 0 ε) hC
  have hX : Measurable X := measurable_pi_iff.mpr fun v =>
    hGFF.measurable_pairing v.1.1 (Section6.isTestFunction_of_testC v.1.1)
  obtain ⟨F, hF, hFP, hFQ⟩ := exists_common_limit_of_tendstoInMeasure P Q X Y
    (fun n x => x (φ n)) (fun n => measurable_pi_apply (φ n))
    (fun ω => hcirc ω r z - hcirc ω r 0)
    (fun ξ => g ξ + α₀ * (Real.circleAverage (fun x => Real.log ‖x‖) z r -
      Real.circleAverage (fun x => Real.log ‖x‖) 0 r)) hφ hlim
  let c := α₀ * (Real.circleAverage (fun x => Real.log ‖x‖) z r -
    Real.circleAverage (fun x => Real.log ‖x‖) 0 r)
  let G := fun x => (x, F x - c)
  have hG : Measurable G := measurable_id.prodMk (hF.sub_const c)
  have hrootmap : Q.map (fun ξ => (Y ξ, g ξ)) = Q.map (G ∘ Y) := by
    apply Measure.map_congr
    filter_upwards [hFQ] with ξ hξ
    change (Y ξ, g ξ) = (Y ξ, F (Y ξ) - c)
    rw [hξ]
    simp only [c, add_sub_cancel_right]
  have hrefmap : P.map (fun ω => (X ω,
      fieldCircleAverage α₀ (hcirc ω) r z - fieldCircleAverage α₀ (hcirc ω) r 0)) =
      P.map (G ∘ X) := by
    apply Measure.map_congr
    filter_upwards [hFP] with ω hω
    change (X ω, _) = (X ω, F (X ω) - c)
    rw [hω]
    simp only [fieldCircleAverage, c]
    congr 1
    ring
  rw [hrootmap, hrefmap, ← Measure.map_map hG hY, ← Measure.map_map hG hX]
  exact hdom.map hG

end HarmonicBalls
