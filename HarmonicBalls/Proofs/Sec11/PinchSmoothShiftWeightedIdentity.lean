import HarmonicBalls.Proofs.Sec11.PinchActualJointShiftConsumer
import HarmonicBalls.Proofs.GFF.WholePlaneSmoothShiftDensity

/-! # Weighted smooth shifts of local pinch events -/

noncomputable section

open HarmonicBalls MeasureTheory Filter Set Metric Laplacian
open scoped ENNReal Real

namespace HarmonicBalls

private def globalTest (φ : LocalZeroMeanTest univ) : LQGMetric.TestC0 :=
  ⟨⟨φ.1, φ.2.1.1, φ.2.1.2.1, subset_univ _⟩, φ.2.2⟩

private def insertedPairingMap (α : ℝ) (F : LQGMetric.TestC0 → ℝ) :
    LocalZeroMeanTest univ → ℝ :=
  fun φ => F (globalTest φ) - α * ∫ z, φ.1 z * Real.log ‖z‖

private theorem measurable_insertedPairingMap (α : ℝ) : Measurable (insertedPairingMap α) := by
  apply measurable_pi_iff.mpr
  intro φ
  exact (measurable_pi_apply (globalTest φ)).sub_const _

private theorem insertedPairingMap_base {Ω : Type} (α : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (ω : Ω) :
    insertedPairingMap α (Section6.pairingProc hC ω) = localModConstPairings α hC univ ω := by
  rfl

private theorem insertedPairingMap_shift {Ω : Type} (α : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (ω : Ω) (g : ℂ → ℝ) :
    insertedPairingMap α (fun φ : LQGMetric.TestC0 => hC ω φ.1 + ∫ z, φ.1 z * g z) =
      localModConstPairings α (fun ω => addFunPairing (hC ω) g) univ ω := by
  funext φ
  simp only [insertedPairingMap, localModConstPairings, fieldPairing, addFunPairing, globalTest]
  congr 2
  congr 1
  funext z
  exact mul_comm _ _

/-- The local field and pinch event have the energy-normalized smooth-shift density. -/
theorem IsWholePlaneGFF.pinchLocalRule_joint_smooth_shift_density
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hDfield : IsLQGMetricOfField P γ ξ α hC D)
    (haxioms : LQGMetricFieldAxioms P γ ξ α hC hcirc) (hξ : 0 ≤ ξ)
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    (g : ℂ → ℝ) (hg : IsTestFunction univ g)
    (E : Set (LocalZeroMeanTest (ball (0 : ℂ) 7) → ℝ)) (hE : MeasurableSet E)
    (M : ℝ) :
    P {ω | localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 7) ω ∈ E ∧
      S11m.LocalRule.pinchLocalRule
        ((μ ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * g z))))
        (fun x y => (weylScaling (D ω) ξ g x y).toReal) W T Q' Q U V δ M} =
    ∫⁻ ω in {ω | localModConstPairings α hC (ball 0 7) ω ∈ E ∧
      S11m.LocalRule.pinchLocalRule (μ ω) (D ω) W T Q' Q U V δ M},
      ENNReal.ofReal (Real.exp (hC ω fun z => -(2 * π)⁻¹ * Δ g z) /
        Real.exp ((2 * π)⁻¹ * (∫ z, ‖fderiv ℝ g z‖ ^ 2) / 2)) ∂P := by
  let I := S11az.pinchCountSets V W T Q' Q δ
  obtain ⟨ψ, hψ, hψint⟩ := IsTestFunction.exists_integral_eq_one
    (isOpen_univ : IsOpen (univ : Set ℂ)) ⟨0, mem_univ _⟩
  obtain ⟨domain, pair, hv, _, hd⟩ := exists_pinch_countable_metric_coordinates hgeo I
  obtain ⟨R, hR, F, hF, hbase, hshift⟩ :=
    h.exists_joint_smooth_shift_decoder_law_on_domains_between_of_field hμ hγ hγ2 hα
      (a := 6) (ε := 7) (by norm_num) (by norm_num) hDfield haxioms domain
      (fun n => (hv n).1) (fun n => (hv n).2.1) ψ hψ hψint pair
      (fun n => (hv n).2.2) hξ
  let B := E ×ˢ pinchCoordinateEvent (U := U) I domain pair M
  have hB : MeasurableSet B := hE.prod
    (measurableSet_pinchCoordinateEvent hgeo.isOpen_U.measurableSet I domain pair M)
  let A := (F ∘ insertedPairingMap α) ⁻¹' B
  have hA : MeasurableSet A := (hF.comp (measurable_insertedPairingMap α)) hB
  have hx := h.ae_pinchCoordinateEvent_iff_localRule hμ hγ hγ2 hα hDfield haxioms
    hgeo hR.1 I domain pair hd (fun ω => Real.exp (ξ * (-hC ω ψ)))
      (fun _ => Real.exp_pos _) M
  have hy := h.ae_shifted_pinchCoordinateEvent_iff_localRule hμ hγ hγ2 hα hDfield haxioms hξ
    hgeo hR.1 I domain pair hd g hg
      (fun ω => Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z))))
      (fun _ => Real.exp_pos _) M
  have hxset : Section6.pairingProc hC ⁻¹' A =ᵐ[P]
      {ω | localModConstPairings α hC (ball 0 7) ω ∈ E ∧
        S11m.LocalRule.pinchLocalRule (μ ω) (D ω) W T Q' Q U V δ M} := by
    apply Filter.eventuallyEqSet_iff.mpr
    filter_upwards [hbase, hx] with ω hbaseω hxω
    change F (insertedPairingMap α (Section6.pairingProc hC ω)) ∈ B ↔ _
    rw [insertedPairingMap_base, hbaseω]
    exact and_congr_right (fun _ => hxω)
  have hyset : (fun ω (φ : LQGMetric.TestC0) =>
      hC ω φ.1 + ∫ z, φ.1 z * g z) ⁻¹' A =ᵐ[P]
      {ω | localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 7) ω ∈ E ∧
        S11m.LocalRule.pinchLocalRule
          ((μ ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * g z))))
          (fun x y => (weylScaling (D ω) ξ g x y).toReal) W T Q' Q U V δ M} := by
    apply Filter.eventuallyEqSet_iff.mpr
    filter_upwards [(hshift g hg).1, hy] with ω hshiftω hyω
    change F (insertedPairingMap α (fun φ : LQGMetric.TestC0 =>
      hC ω φ.1 + ∫ z, φ.1 z * g z)) ∈ B ↔ _
    rw [insertedPairingMap_shift, hshiftω]
    exact and_congr_right (fun _ => hyω)
  obtain ⟨Z, _, hZ, _, hdensity⟩ := h.smooth_shift_density_of_isTestFunction hg
  have hid := (hdensity A hA).1
  rw [hZ, measure_congr hyset, Measure.restrict_congr_set hxset] at hid
  exact hid

/-- The actual field and the three local pinch events obey the weighted shift identity. -/
theorem IsWholePlaneGFF.pinchLocal_events_joint_smooth_shift_density_actual
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hDfield : IsLQGMetricOfField P γ ξ α hC D)
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    (g : ℂ → ℝ) (hg : IsTestFunction univ g)
    (E : Set (LocalZeroMeanTest (ball (0 : ℂ) 7) → ℝ)) (hE : MeasurableSet E)
    (M : ℝ) :
    P {ω | localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 7) ω ∈ E ∧
      pinchFirstEventLocal (fun x y => (weylScaling (D ω) ξ g x y).toReal) W T Q' Q δ ∧
      pinchSecondEventLocal ((μ ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * g z))))
        (fun x y => (weylScaling (D ω) ξ g x y).toReal) U V δ M ∧
      pinchThirdEventLocal (fun x y => (weylScaling (D ω) ξ g x y).toReal) V W δ} =
    ∫⁻ ω in {ω | localModConstPairings α hC (ball 0 7) ω ∈ E ∧
      pinchFirstEventLocal (D ω) W T Q' Q δ ∧
      pinchSecondEventLocal (μ ω) (D ω) U V δ M ∧ pinchThirdEventLocal (D ω) V W δ},
      ENNReal.ofReal (Real.exp (hC ω fun z => -(2 * π)⁻¹ * Δ g z) /
        Real.exp ((2 * π)⁻¹ * (∫ z, ‖fderiv ℝ g z‖ ^ 2) / 2)) ∂P := by
  have hcopy := hDfield
  obtain ⟨𝔇, h𝔇, _⟩ := hcopy
  have hd := h.pinchLocalRule_joint_smooth_shift_density hμ hγ hγ2 hα hDfield
    (lqgMetricFieldAxiomsUnivFrozen_derived Ω P γ ξ α hC hcirc)
    (isLQGMetric_xi_pos γ ξ 𝔇 hγ hγ2 h𝔇).le hgeo g hg E hE M
  simpa only [S11m.LocalRule.pinchLocalRule] using hd

/-- The three local pinch events have the energy-normalized smooth-shift probability. -/
theorem IsWholePlaneGFF.pinchLocal_events_smooth_shift_density_actual
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hDfield : IsLQGMetricOfField P γ ξ α hC D)
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    (g : ℂ → ℝ) (hg : IsTestFunction univ g) (M : ℝ) :
    P {ω | pinchFirstEventLocal (fun x y => (weylScaling (D ω) ξ g x y).toReal) W T Q' Q δ ∧
      pinchSecondEventLocal ((μ ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * g z))))
        (fun x y => (weylScaling (D ω) ξ g x y).toReal) U V δ M ∧
      pinchThirdEventLocal (fun x y => (weylScaling (D ω) ξ g x y).toReal) V W δ} =
    ∫⁻ ω in {ω | pinchFirstEventLocal (D ω) W T Q' Q δ ∧
      pinchSecondEventLocal (μ ω) (D ω) U V δ M ∧ pinchThirdEventLocal (D ω) V W δ},
      ENNReal.ofReal (Real.exp (hC ω fun z => -(2 * π)⁻¹ * Δ g z) /
        Real.exp ((2 * π)⁻¹ * (∫ z, ‖fderiv ℝ g z‖ ^ 2) / 2)) ∂P := by
  have hd := h.pinchLocal_events_joint_smooth_shift_density_actual hμ hγ hγ2 hα hDfield
    hgeo g hg (univ : Set (LocalZeroMeanTest (ball (0 : ℂ) 7) → ℝ)) MeasurableSet.univ M
  simpa only [mem_univ, true_and] using hd

end HarmonicBalls
