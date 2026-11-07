import HarmonicBalls.Proofs.Sec11.ConditionalAbsoluteMassDiameter
import HarmonicBalls.Proofs.Sec11.MassDiameterShiftedPositive

/-! # Positive joint mass and diameter from a smooth shift

The Cameron–Martin input is Leonardo Bonanno's
`LatticeProb.Bonanno.LQGMetric.Field.CameronMartin` formalization. -/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
namespace HarmonicBalls

/-- Positive probability of the joint mass and diameter event after a smooth
shift preserving the circle normalization implies positive probability before
the shift. Both observables use the same field decoder. -/
theorem IsWholePlaneGFF.absolute_mass_diameter_pos_of_shift
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ε α γ ξ δ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (S K : Set ℂ) (hS : MeasurableSet S) (hbounded : Bornology.IsBounded S)
    (hbuffer : ∀ n z, z ∈ S → closedBall z (dyadicScale n) ⊆ ball 0 ε)
    (hfront : ∀ᵐ ω ∂P, μ ω (frontier S) = 0) (hδ : 0 < δ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction univ ψ) (hψint : ∫ x, ψ x = 1)
    (c d : ℝ≥0∞) (g : ℂ → ℝ) (hg : IsTestFunction univ g)
    (hpin : Real.circleAverage g 0 1 = 0)
    (hp : 0 < P {ω | c < ((μ ω).withDensity
      (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) S ∧
      internalDiam (𝔇 (addFunPairing (hC ω) g)) δ K < d}) :
    0 < P {ω | c < μ ω S ∧ internalDiam (𝔇 (hC ω)) δ K < d} := by
  obtain ⟨D, hD, hDe⟩ := h.exists_joint_absolute_mass_continuous_metric_shift_decoder
    hμ S hS hbounded hbuffer hfront 𝔇 h𝔇 ψ hψ hψint
  obtain ⟨T, hT, hTe⟩ := exists_measurable_internalDiameter_decoder
    (isOpen_thickening) (self_subset_thickening hδ K)
  let B : Set (LocalZeroMeanTest univ → ℝ) := {v | c < (D v).1 ∧ T (D v).2 < d}
  have hB : MeasurableSet B := (measurableSet_lt measurable_const (measurable_fst.comp hD)).inter
    (measurableSet_lt (hT.comp (measurable_snd.comp hD)) measurable_const)
  have hG (f : ℂ → ℝ) (hf : Continuous f) (hfp : Real.circleAverage f 0 1 = 0) :
      {ω | c < ((μ ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * f z)))) S ∧
          internalDiam (𝔇 (addFunPairing (hC ω) f)) δ K < d} =ᵐ[P]
        (localModConstPairings 0 (fun ω => addFunPairing (hC ω) f) univ) ⁻¹' B := by
    have hw := ae_wholePlane_weylScaling_shift P γ ξ hC hcirc 𝔇 h𝔇 h
      (fun _ => f) (fun _ => hf) (fun _ => measurable_const)
    filter_upwards [hDe f hf hfp, hw] with ω hd hw
    have hmetric : IsEuclideanLengthMetric (fun x y => (D (localModConstPairings 0
        (fun ω => addFunPairing (hC ω) f) univ ω)).2 (x,y)) := by
      convert hw.2.1 using 1
      funext x y
      exact hd.2 x y
    have hdiam := hTe (D (localModConstPairings 0
      (fun ω => addFunPairing (hC ω) f) univ ω)).2 hmetric
    have hfun : (fun x y => (D (localModConstPairings 0
        (fun ω => addFunPairing (hC ω) f) univ ω)).2 (x,y)) =
        𝔇 (addFunPairing (hC ω) f) := by
      funext x y
      exact hd.2 x y
    rw [hfun] at hdiam
    change (_ ∧ _) = (_ ∧ _)
    rw [hd.1, hdiam]
    rfl
  let X := localModConstPairings 0 hC univ
  let Y := localModConstPairings 0 (fun ω => addFunPairing (hC ω) g) univ
  have hX : Measurable X := measurable_pi_iff.mpr fun φ =>
    (h.measurable_pairing φ.1 φ.2.1).sub_const _
  have hY : Measurable Y := measurable_pi_iff.mpr fun φ =>
    ((h.measurable_pairing φ.1 φ.2.1).add_const _).sub_const _
  have hYpos : 0 < P.map Y B := by
    rw [Measure.map_apply hY hB, ← measure_congr (hG g hg.1.continuous hpin)]
    exact hp
  have hXpos : 0 < P.map X B := by
    by_contra hn
    have hz : P.map X B = 0 := nonpos_iff_eq_zero.mp (not_lt.mp hn)
    exact (ne_of_gt hYpos) ((h.singular_smooth_shift_modConst_pairing_laws hg 0 univ).1 hz)
  rw [Measure.map_apply hX hB] at hXpos
  have hz := hG (fun _ => 0) continuous_const (by rw [Real.circleAverage_const])
  have hzero : (fun ω => addFunPairing (hC ω) (fun _ => 0)) = hC := by
    funext ω φ
    simp [addFunPairing]
  have hz' : {ω | c < μ ω S ∧ internalDiam (𝔇 (hC ω)) δ K < d} =ᵐ[P] X ⁻¹' B := by
    filter_upwards [hz] with ω hω
    have h0 : addFunPairing (hC ω) (fun _ => 0) = hC ω := congrFun hzero ω
    have hw : (μ ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * (0 : ℝ)))) = μ ω := by
      simp
    rw [hzero] at hω
    simpa only [h0, hw] using hω
  rwa [measure_congr hz']

#print axioms IsWholePlaneGFF.absolute_mass_diameter_pos_of_shift

/-- A positive seed with protected mass and small tile distances gives
unconditional joint mass and diameter positivity by core contraction. -/
theorem IsWholePlaneGFF.absolute_mass_diameter_pos_of_core_seed
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ε α γ ξ δ a σ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ) (hξ : 0 < ξ)
    {ι : Type*} (S K O O₀ O₁ C : Set ℂ) (H J : ι → Set ℂ)
    (hS : MeasurableSet S) (hbounded : Bornology.IsBounded S)
    (hbufferS : ∀ n z, z ∈ S → closedBall z (dyadicScale n) ⊆ ball 0 ε)
    (hfront : ∀ᵐ ω ∂P, μ ω (frontier S) = 0) (hδ : 0 < δ)
    (hpin : Disjoint O₁ (sphere (0 : ℂ) 1))
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction univ ψ) (hψint : ∫ x, ψ x = 1)
    (c : ℝ≥0∞) (ha : 0 ≤ a) (hmargin : a + a < σ)
    (hO : IsOpen O) (hO₀ : IsOpen O₀) (hO₀conn : IsConnected O₀)
    (hO₀O : O₀ ⊆ O) (hO₁ : IsOpen O₁)
    (hO₀compact : IsCompact (closure O₀)) (hO₀O₁ : closure O₀ ⊆ O₁)
    (hdisjoint : Disjoint O₁ S)
    (hJopen : ∀ i, IsOpen (J i)) (hJO : ∀ i, J i ⊆ O)
    (hCcompact : IsCompact C) (hCO₀ : C ⊆ O₀)
    (hbuffer : O ⊆ thickening δ K)
    (hcover : ∀ x ∈ K, x ∈ C ∨ ∃ i, x ∈ H i)
    (hattach : ∀ i, (H i ∩ C).Nonempty)
    (A : Set Ω) (hAp : 0 < P A)
    (hA : ∀ ω ∈ A, c < μ ω S ∧ ∀ i, ∀ x ∈ H i, ∀ y ∈ H i,
      internalMetric (𝔇 (hC ω)) (J i) x y ≤ ENNReal.ofReal a) :
    0 < P {ω | c < μ ω S ∧ internalDiam (𝔇 (hC ω)) δ K < ENNReal.ofReal σ} := by
  obtain ⟨g, hg, _, hgO, hp⟩ := exists_positive_mass_small_diameter_wholePlane_shift
    P γ ξ hξ hC hcirc 𝔇 μ h𝔇 h ha hmargin hO hO₀ hO₀conn hO₀O hO₁
    hO₀compact hO₀O₁ hdisjoint hS hJopen hJO hCcompact hCO₀ hbuffer hcover
    hattach A hAp hA
  have hgpin : Real.circleAverage g 0 1 = 0 := by
    calc
      Real.circleAverage g 0 1 = Real.circleAverage (fun _ : ℂ => (0 : ℝ)) 0 1 := by
        apply Real.circleAverage_congr_sphere
        intro z hz
        exact hgO z (fun hzO => Set.disjoint_left.mp hpin hzO (by simpa using hz))
      _ = 0 := by rw [Real.circleAverage_const]
  exact h.absolute_mass_diameter_pos_of_shift hμ S K hS hbounded hbufferS hfront hδ
    𝔇 h𝔇 ψ hψ hψint c _ g hg hgpin hp

#print axioms IsWholePlaneGFF.absolute_mass_diameter_pos_of_core_seed
end HarmonicBalls
