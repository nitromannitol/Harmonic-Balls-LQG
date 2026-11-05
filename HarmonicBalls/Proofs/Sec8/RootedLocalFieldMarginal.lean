import HarmonicBalls.Proofs.Sec8.BufferedRootedLocalEvents

/-! # Marginal comparison of the recentered rooted field

The canonical reconstruction uses Leonardo Bonanno's distribution-valued
whole-plane GFF work. The rooted-field change of measure is an explicit
hypothesis, not established here.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Metric Set
open scoped ENNReal

namespace HarmonicBalls

/-- On a buffered root region, the normalized recentered field law is
absolutely continuous with respect to the origin-inserted local field law,
provided the unnormalized whole-plane rooted comparison holds. -/
theorem IsWholePlaneGFF.normalized_recentered_field_ac_origin_insertion
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (μ : Ω → Measure ℂ)
    (hμ : AEMeasurable μ P) (B : Set ℂ) (hB : MeasurableSet B)
    (hfin : ∀ᵐ ω ∂P, μ ω B ≠ ∞) (ρ : Measure ℂ) (γ : ℝ)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hside : ∀ᵐ z ∂ρ, ‖z‖ + R ≤ 1 ∨ 1 + R ≤ ‖z‖)
    (hrooted : (P.bind fun ω => ((μ ω).restrict B).map
      (fun z => (Section6.pairingProc hC ω, z))) ≪
      shiftedRootReferenceLaw ρ P (fun p => fun φ : LQGMetric.TestC0 =>
        hC p.2 φ.1 + ∫ x, φ.1 x *
          (-γ * Real.log ‖x - p.1‖ + γ * Real.log (max ‖x‖ 1)))) :
    (P ⊗ₘ weightedRestrictionKernel P μ hμ B hB (fun _ => 1) measurable_const).map
      (fun p => recenteredDistributionObservation (ball 0 r)
        (Section6.pairingProc hC p.1, p.2)) ≪
    P.map (fun ω => fun φ : Section6.LocalTest (ball 0 r) =>
      hC ω φ.1.1 + ∫ x, φ.1.1 x * (-γ * Real.log ‖x‖)) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let X : Ω → (Section6.LocalTest (ball 0 r) → ℝ) := fun ω φ =>
    hC ω φ.1.1 + ∫ x, φ.1.1 x * (-γ * Real.log ‖x‖)
  let Y : Ω × ℂ → (Section6.LocalTest (ball 0 r) → ℝ) := fun p =>
    recenteredDistributionObservation (ball 0 r) (Section6.pairingProc hC p.1, p.2)
  have hX : Measurable X := by
    apply measurable_pi_iff.mpr
    intro φ
    exact (hh.measurable_pairing φ.1.1 (Section6.isTestFunction_of_testC φ.1.1)).add_const _
  have hY : Measurable Y := (measurable_recenteredDistributionObservation (ball 0 r)).comp
    (((Section6.measurable_pairingProc hh).comp measurable_fst).prodMk measurable_snd)
  have hdom := hh.normalized_recentered_observation_ac_origin_insertion μ hμ B hB hfin
    ρ γ hr hrR hside hrooted
  apply Measure.AbsolutelyContinuous.mk
  intro A hA hzero
  have hp : ∀ᵐ ω ∂P, X ω ∈ Aᶜ := by
    apply (ae_map_iff hX.aemeasurable hA.compl).1
    exact measure_eq_zero_iff_ae_notMem.mp hzero
  have href := ae_shiftedRootReferenceLaw_of_field_event ρ P X hX Aᶜ hA.compl hp
  have hpair : Measurable (fun p : Ω × ℂ => (Y p, p.2)) := hY.prodMk measurable_snd
  have hroot := (ae_map_iff hpair.aemeasurable (measurable_fst hA.compl)).1 (hdom.ae_le href)
  apply measure_eq_zero_iff_ae_notMem.mpr
  exact (ae_map_iff hY.aemeasurable hA.compl).2 hroot

#print axioms IsWholePlaneGFF.normalized_recentered_field_ac_origin_insertion

end HarmonicBalls
