import HarmonicBalls.Proofs.Sec8.LocalCirclePairingApproximation
import HarmonicBalls.Proofs.Sec11.CanonicalPairingShift

/-! # Smooth shifts of centered circle approximations

A continuous shift acts on the signed annular test approximations by the
corresponding difference of circle averages in the limit.
The imported Section 8 development uses Leonardo Bonanno's LatticeProb
formalization.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology

namespace HarmonicBalls

/-- Pairing a continuous function with the signed annular approximations
converges to its centered circle average. -/
theorem circleDensityDifference_integral_tendsto_circleAverage
    {r η : ℝ} (hr : 0 < r) (hη : 0 < η) (z : ℂ)
    {g : ℂ → ℝ} (hg : Continuous g) :
    Tendsto (fun n => ∫ x, g x * circleDensityDifference r η hr hη z n x)
      atTop (𝓝 (Real.circleAverage g z r - Real.circleAverage g 0 r)) := by
  have ht := (circleDensity_integral_tendsto_circleAverage hr hη z hg).sub
    (circleDensity_integral_tendsto_circleAverage hr hη 0 hg)
  apply ht.congr'
  filter_upwards with n
  let δ := circleDensityWidth r η n
  let hδ := circleDensityWidth_pos hr hη n
  let m : ℝ := (∫ y, circleDensity r δ hδ 0 y)⁻¹
  have hi (v : ℂ) : Integrable (fun x => m * circleDensity r δ hδ v x * g x) := by
    apply ((continuous_const.mul (circleDensity_contDiff r δ hδ v).continuous).mul hg).integrable_of_hasCompactSupport
    exact (circleDensity_hasCompactSupport hr.le hδ v).mul_left.mul_right
  symm
  change (∫ x, g x * (m * circleDensity r δ hδ z x - m * circleDensity r δ hδ 0 x)) =
    (∫ x, m * circleDensity r δ hδ z x * g x) -
      ∫ x, m * circleDensity r δ hδ 0 x * g x
  simp_rw [mul_sub, mul_comm (g _)]
  exact integral_sub (hi z) (hi 0)

/-- One sequence of local tests approximates the centered GFF circle average
in probability and simultaneously gives the correct circle-average shift for
every continuous deterministic function. -/
theorem IsWholePlaneGFF.exists_local_circleDensity_smooth_shift_approximation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ε r : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hr : 0 < r) (z : ℂ)
    (hz : closedBall z r ⊆ ball 0 ε) :
    ∃ (η : ℝ) (hη : 0 < η),
      (∀ n, IsTestFunction (ball 0 ε) (circleDensityDifference r η hr hη z n) ∧
        ∫ x, circleDensityDifference r η hr hη z n x = 0) ∧
      TendstoInMeasure P (fun n ω => hC ω (circleDensityDifference r η hr hη z n))
        atTop (fun ω => hcirc ω r z - hcirc ω r 0) ∧
      ∀ g : ℂ → ℝ, Continuous g →
        Tendsto (fun n => ∫ x, g x * circleDensityDifference r η hr hη z n x)
          atTop (𝓝 (Real.circleAverage g z r - Real.circleAverage g 0 r)) := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  obtain ⟨η, hη, _, htests, _, _⟩ := exists_local_circleDensity_tests hr z hz
  let ψ := circleDensityDifference r η hr hη z
  have htest (n : ℕ) : IsTestFunction (ball 0 ε) (ψ n) ∧ ∫ x, ψ n x = 0 := htests n
  have htestU (n : ℕ) : IsTestFunction univ (ψ n) :=
    ⟨(htest n).1.1, (htest n).1.2.1, subset_univ _⟩
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
  refine ⟨η, hη, htest, ?_, ?_⟩
  · exact tendstoInMeasure_of_centered_variance_tendsto_zero P _ _
      (fun n => (hp n).sub (hzLp.sub h0Lp)) hm hvar
  · intro g hg
    exact circleDensityDifference_integral_tendsto_circleAverage hr hη z hg

/-- A centered circle average of a log-singular field has one measurable
local decoder that transforms correctly under every continuous deterministic
shift. The exceptional set is common to all shifts. -/
theorem IsWholePlaneGFF.exists_local_singular_circle_smooth_shift_decoder
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ε r α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hr : 0 < r) (z : ℂ)
    (hz : closedBall z r ⊆ ball 0 ε) :
    ∃ F : (LocalZeroMeanTest (ball 0 ε) → ℝ) → ℝ, Measurable F ∧
      ∀ᵐ ω ∂P, ∀ g : ℂ → ℝ, Continuous g →
        F (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω) =
          (fieldCircleAverage α (hcirc ω) r z - fieldCircleAverage α (hcirc ω) r 0) +
            (Real.circleAverage g z r - Real.circleAverage g 0 r) := by
  obtain ⟨η, hη, htest, hprob, hdet⟩ :=
    hGFF.exists_local_circleDensity_smooth_shift_approximation hr z hz
  let ψ := circleDensityDifference r η hr hη z
  let φ : ℕ → LocalZeroMeanTest (ball 0 ε) := fun n => ⟨ψ n, htest n⟩
  obtain ⟨s, hs, hae⟩ := hprob.exists_seq_tendsto_ae
  let c : ℝ := α * (Real.circleAverage (fun x : ℂ => Real.log ‖x‖) z r -
    Real.circleAverage (fun x : ℂ => Real.log ‖x‖) 0 r)
  let f : ℕ → (LocalZeroMeanTest (ball 0 ε) → ℝ) → ℝ := fun n v =>
    v (φ (s n)) + α * (∫ x, ψ (s n) x * Real.log ‖x‖) - c
  let F := fun v => limUnder atTop (fun n => f n v)
  have hF : Measurable F := by
    apply (StronglyMeasurable.limUnder ?_).measurable
    intro n
    exact (((measurable_pi_apply (φ (s n))).add_const _).sub_const _).stronglyMeasurable
  refine ⟨F, hF, ?_⟩
  filter_upwards [hae] with ω hω g hg
  have hlim := hω.add ((hdet g hg).comp hs.tendsto_atTop)
  have ht : Tendsto (fun n => f n (localModConstPairings α
      (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω)) atTop
      (𝓝 ((fieldCircleAverage α (hcirc ω) r z - fieldCircleAverage α (hcirc ω) r 0) +
        (Real.circleAverage g z r - Real.circleAverage g 0 r))) := by
    have ht' := hlim.sub_const c
    convert ht' using 1
    · funext n
      simp only [f, localModConstPairings, fieldPairing, addFunPairing, φ, ψ, Function.comp_apply]
      ring
    · simp only [fieldCircleAverage, c]
      ring
  exact ht.limUnder_eq

/-- A countable family of centered circle averages admits compatible local
decoders with one exceptional set for all continuous shifts. -/
theorem IsWholePlaneGFF.exists_countable_local_singular_circle_shift_decoders
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] {P : Measure Ω} {ε α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (r : ι → ℝ) (z : ι → ℂ)
    (hr : ∀ i, 0 < r i) (hz : ∀ i, closedBall (z i) (r i) ⊆ ball 0 ε) :
    ∃ F : ι → (LocalZeroMeanTest (ball 0 ε) → ℝ) → ℝ,
      (∀ i, Measurable (F i)) ∧ ∀ᵐ ω ∂P, ∀ i g, Continuous g →
        F i (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω) =
          (fieldCircleAverage α (hcirc ω) (r i) (z i) -
            fieldCircleAverage α (hcirc ω) (r i) 0) +
          (Real.circleAverage g (z i) (r i) - Real.circleAverage g 0 (r i)) := by
  choose F hFm hFeq using fun i =>
    hGFF.exists_local_singular_circle_smooth_shift_decoder (α := α) (hr i) (z i) (hz i)
  exact ⟨F, hFm, ae_all_iff.mpr hFeq⟩

#print axioms IsWholePlaneGFF.exists_countable_local_singular_circle_shift_decoders
#print axioms circleDensityDifference_integral_tendsto_circleAverage
#print axioms IsWholePlaneGFF.exists_local_singular_circle_smooth_shift_decoder
#print axioms IsWholePlaneGFF.exists_local_circleDensity_smooth_shift_approximation

end HarmonicBalls
