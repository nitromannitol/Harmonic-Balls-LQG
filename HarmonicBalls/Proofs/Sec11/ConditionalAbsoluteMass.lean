import HarmonicBalls.Proofs.Sec11.AbsoluteLQGMassShiftDecoder
import HarmonicBalls.Proofs.Sec11.ConditionalObservableShift
import HarmonicBalls.Proofs.Sec11.MassDiameterShiftPreservingEvent

/-! # Conditional positivity of absolute LQG mass

The Cameron–Martin input is Leonardo Bonanno's
`LatticeProb.Bonanno.LQGMetric.Field.CameronMartin` formalization.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped ENNReal
namespace HarmonicBalls

/-- Full support gives conditional positive probability of arbitrarily large
mass on a compact continuity set when the amplification region is disjoint
from the outside observation and the pinned unit circle. -/
theorem IsWholePlaneGFF.condExp_absolute_mass_pos_of_full_support
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ε α γ M : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hγ : 0 < γ) (hM : 0 ≤ M) (S V O U : Set ℂ)
    (hScompact : IsCompact S) (hS : MeasurableSet S)
    (hV : IsOpen V) (hVne : V.Nonempty) (hVS : V ⊆ S)
    (hO : IsOpen O) (hSO : S ⊆ O) (hOU : Disjoint O U)
    (hpin : sphere (0 : ℂ) 1 ⊆ U)
    (hbuffer : ∀ n z, z ∈ S → closedBall z (dyadicScale n) ⊆ ball 0 ε)
    (hfront : ∀ᵐ ω ∂P, μ ω (frontier S) = 0)
    (hfull : ∀ᵐ ω ∂P, ∀ V : Set ℂ, IsOpen V → V.Nonempty → 0 < μ ω V) :
    ∀ᵐ ω ∂P, 0 < (P[({ω | ENNReal.ofReal M < μ ω S}).indicator (fun _ => (1 : ℝ)) |
      MeasurableSpace.comap (localModConstPairings α hC U) inferInstance]) ω := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  obtain ⟨D, hDm, hDe⟩ := hGFF.exists_global_shifted_lqgMass_decoder hμ S hS
    hScompact.isBounded hbuffer hfront
  let B : Set (LocalZeroMeanTest univ → ℝ) := {v | ENNReal.ofReal M < D v}
  have hB : MeasurableSet B := measurableSet_lt measurable_const hDm
  let X := localModConstPairings α hC univ
  have hX : Measurable (localModConstPairings α hC U) := measurable_pi_iff.mpr fun φ =>
    (hGFF.measurable_pairing φ.1 (φ.2.1.mono_set (subset_univ _))).sub_const _
  have hm : MeasurableSpace.comap (localModConstPairings α hC U) inferInstance ≤
      ‹MeasurableSpace Ω› := measurable_iff_comap_le.mp hX
  have hp := hGFF.condExp_modConst_pos_of_interior_shifts α U B hB (by
    intro F hF hFp
    obtain ⟨f, hf, _, hfO, hfpos⟩ := exists_mass_increasing_shift_preserving_event P μ F
      (hm F hF) hFp hScompact hS hV hVne hVS hO hSO hfull hγ hM
    have hfU : ∀ z ∈ U, f z = 0 := fun z hz => hfO z (fun hzO => Set.disjoint_left.mp hOU hzO hz)
    have hfpin : Real.circleAverage f 0 1 = 0 := by
      calc
        Real.circleAverage f 0 1 = Real.circleAverage (fun _ : ℂ => (0 : ℝ)) 0 1 := by
          apply Real.circleAverage_congr_sphere
          intro z hz
          exact hfU z (hpin (by simpa using hz))
        _ = 0 := by rw [Real.circleAverage_const]
    refine ⟨f, hf, hfU, ?_⟩
    have heq : {ω | ω ∈ F ∧ ENNReal.ofReal M <
        (μ ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * f z))) S} =ᵐ[P]
        {ω | ω ∈ F ∧ localModConstPairings α
          (fun ω => addFunPairing (hC ω) f) univ ω ∈ B} := by
      filter_upwards [hDe] with ω hω
      have he := hω f hf.1.continuous hfpin
      simp only [B, mem_ofPred_eq, he]
    rwa [← measure_congr heq])
  have heq : {ω | ENNReal.ofReal M < μ ω S} =ᵐ[P] X ⁻¹' B := by
    filter_upwards [hDe] with ω hω
    have he := hω (fun _ => 0) continuous_const (by rw [Real.circleAverage_const])
    have hshift : (fun ω => addFunPairing (hC ω) (fun _ => 0)) = hC := by
      funext ω φ
      simp [addFunPairing]
    rw [hshift] at he
    have hw : (μ ω).withDensity (fun _ => ENNReal.ofReal (Real.exp (γ * 0))) = μ ω := by
      simp
    rw [hw] at he
    simp only [B, X, mem_ofPred_eq, mem_preimage, he]
  have hi : ({ω | ENNReal.ofReal M < μ ω S}).indicator (fun _ => (1 : ℝ)) =ᵐ[P]
      (X ⁻¹' B).indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [heq] with ω hω
    have hiff : ω ∈ {ω | ENNReal.ofReal M < μ ω S} ↔ ω ∈ X ⁻¹' B := iff_of_eq hω
    by_cases h : ω ∈ {ω | ENNReal.ofReal M < μ ω S}
    · have h' := hiff.mp h
      simp [h, h']
    · have h' : ω ∉ X ⁻¹' B := fun ht => h (hiff.mpr ht)
      simp [h, h']
  filter_upwards [hp, condExp_congr_ae (m := MeasurableSpace.comap
    (localModConstPairings α hC U) inferInstance) hi] with ω hpω he
  rw [he]
  exact hpω

#print axioms IsWholePlaneGFF.condExp_absolute_mass_pos_of_full_support
end HarmonicBalls
