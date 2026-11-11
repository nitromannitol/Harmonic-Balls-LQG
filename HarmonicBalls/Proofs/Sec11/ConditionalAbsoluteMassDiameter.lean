import HarmonicBalls.Proofs.Sec11.JointAbsoluteMassMetricDecoder
import HarmonicBalls.Proofs.Sec11.ConditionalObservableVersions
import HarmonicBalls.Steps.Sec11.InternalDiameterDecoder

/-! # Conditional positivity of absolute mass and diameter

The Cameron–Martin input is Leonardo Bonanno's
`LatticeProb.Bonanno.LQGMetric.Field.CameronMartin` formalization.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
namespace HarmonicBalls

/-- If every positive outside event admits an interior shift on which the
mass and diameter bounds hold with positive probability, their unshifted
event has positive conditional probability. The metric and mass are decoded
jointly from the pinned field. -/
theorem IsWholePlaneGFF.condExp_absolute_mass_diameter_pos_of_shifts
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ε α γ ξ δ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (S K U : Set ℂ) (hS : MeasurableSet S) (hbounded : Bornology.IsBounded S)
    (hbuffer : ∀ n z, z ∈ S → closedBall z (dyadicScale n) ⊆ ball 0 ε)
    (hfront : ∀ᵐ ω ∂P, μ ω (frontier S) = 0)
    (hδ : 0 < δ) (hpin : sphere (0 : ℂ) 1 ⊆ U)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction univ ψ) (hψint : ∫ x, ψ x = 1)
    (c d : ℝ≥0∞)
    (hpos : ∀ F : Set Ω,
      MeasurableSet[MeasurableSpace.comap (localModConstPairings 0 hC U) inferInstance] F →
      0 < P F → ∃ g : ℂ → ℝ, IsTestFunction univ g ∧ (∀ z ∈ U, g z = 0) ∧
        0 < P {ω | ω ∈ F ∧ c < ((μ ω).withDensity
          (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) S ∧
          internalDiam (𝔇 (addFunPairing (hC ω) g)) δ K < d}) :
    ∀ᵐ ω ∂P, 0 < (P[({ω | c < μ ω S ∧ internalDiam (𝔇 (hC ω)) δ K < d}).indicator
      (fun _ => (1 : ℝ)) | MeasurableSpace.comap (localModConstPairings 0 hC U) inferInstance]) ω := by
  obtain ⟨D, hD, hDe⟩ := h.exists_joint_absolute_mass_continuous_metric_shift_decoder
    hμ S hS hbounded hbuffer hfront 𝔇 h𝔇 ψ hψ hψint
  obtain ⟨T, hT, hTe⟩ := exists_measurable_internalDiameter_decoder
    (isOpen_thickening) (self_subset_thickening hδ K)
  let B : Set (LocalZeroMeanTest univ → ℝ) := {v | c < (D v).1 ∧ T (D v).2 < d}
  have hB : MeasurableSet B := (measurableSet_lt measurable_const (measurable_fst.comp hD)).inter
    (measurableSet_lt (hT.comp (measurable_snd.comp hD)) measurable_const)
  have hG (g : ℂ → ℝ) (hg : IsTestFunction univ g) (hgU : ∀ z ∈ U, g z = 0) :
      {ω | c < ((μ ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) S ∧
          internalDiam (𝔇 (addFunPairing (hC ω) g)) δ K < d} =ᵐ[P]
        (localModConstPairings 0 (fun ω => addFunPairing (hC ω) g) univ) ⁻¹' B := by
    have hgpin : Real.circleAverage g 0 1 = 0 := by
      calc
        Real.circleAverage g 0 1 = Real.circleAverage (fun _ : ℂ => (0 : ℝ)) 0 1 := by
          apply Real.circleAverage_congr_sphere
          intro z hz
          exact hgU z (hpin (by simpa using hz))
        _ = 0 := by rw [Real.circleAverage_const]
    have hw := ae_wholePlane_weylScaling_shift P γ ξ hC hcirc 𝔇 h𝔇 h
      (fun _ => g) (fun _ => hg.1.continuous) (fun _ => measurable_const)
    filter_upwards [hDe g hg.1.continuous hgpin, hw] with ω hd hw
    have hmetric : IsEuclideanLengthMetric (fun x y => (D (localModConstPairings 0
        (fun ω => addFunPairing (hC ω) g) univ ω)).2 (x,y)) := by
      convert hw.2.1 using 1
      funext x y
      exact hd.2 x y
    have hdiam := hTe (D (localModConstPairings 0
      (fun ω => addFunPairing (hC ω) g) univ ω)).2 hmetric
    have hfun : (fun x y => (D (localModConstPairings 0
        (fun ω => addFunPairing (hC ω) g) univ ω)).2 (x,y)) =
        𝔇 (addFunPairing (hC ω) g) := by
      funext x y
      exact hd.2 x y
    rw [hfun] at hdiam
    change (_ ∧ _) = (_ ∧ _)
    rw [hd.1, hdiam]
    rfl
  let Z : ℂ → ℝ := fun _ => 0
  have hZ : IsTestFunction univ Z := ⟨contDiff_const, HasCompactSupport.zero, by simp [Z]⟩
  have hz := hG Z hZ (by simp [Z])
  have hzero : (fun ω => addFunPairing (hC ω) Z) = hC := by
    funext ω φ
    simp [addFunPairing, Z]
  have hz' : {ω | c < μ ω S ∧ internalDiam (𝔇 (hC ω)) δ K < d} =ᵐ[P]
      (localModConstPairings 0 hC univ) ⁻¹' B := by
    filter_upwards [hz] with ω hω
    have h0 : addFunPairing (hC ω) Z = hC ω := congrFun hzero ω
    have hw : (μ ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * Z z))) = μ ω := by
      simp [Z]
    rw [hzero] at hω
    simpa only [h0, hw] using hω
  have hp := h.condExp_modConst_pos_of_interior_shifts 0 U B hB (by
    intro F hF hFp
    obtain ⟨g, hg, hgU, hp⟩ := hpos F hF hFp
    refine ⟨g, hg, hgU, ?_⟩
    have heq : {ω | ω ∈ F ∧ c < ((μ ω).withDensity
        (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) S ∧
        internalDiam (𝔇 (addFunPairing (hC ω) g)) δ K < d} =ᵐ[P]
        {ω | ω ∈ F ∧ localModConstPairings 0
          (fun ω => addFunPairing (hC ω) g) univ ω ∈ B} := by
      filter_upwards [hG g hg hgU] with ω he
      have he' := iff_of_eq he
      exact propext (and_congr_right fun _ => he')
    rwa [← measure_congr heq])
  have hi : ({ω | c < μ ω S ∧ internalDiam (𝔇 (hC ω)) δ K < d}).indicator
      (fun _ => (1 : ℝ)) =ᵐ[P] ((localModConstPairings 0 hC univ) ⁻¹' B).indicator
        (fun _ => (1 : ℝ)) := by
    filter_upwards [hz'] with ω hω
    have hiff := iff_of_eq hω
    by_cases ha : c < μ ω S ∧ internalDiam (𝔇 (hC ω)) δ K < d
    · simp [ha, hiff.mp ha]
    · have hb : ω ∉ (localModConstPairings 0 hC univ) ⁻¹' B := fun hh => ha (hiff.mpr hh)
      simp [ha, hb]
  filter_upwards [hp, condExp_congr_ae (m := MeasurableSpace.comap
    (localModConstPairings 0 hC U) inferInstance) hi] with ω hpω he
  rw [he]
  exact hpω

end HarmonicBalls
