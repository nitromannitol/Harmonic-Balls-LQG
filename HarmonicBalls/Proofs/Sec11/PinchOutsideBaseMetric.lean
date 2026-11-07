import HarmonicBalls.Proofs.Sec11.PinchOutsideAbsolutePairing
import HarmonicBalls.Proofs.Sec11.PinchOutsideSphereDistance
import HarmonicBalls.Proofs.Sec11.MeasurableCenteredBaseLocality

/-! # Absolute base-metric locality outside the core

The centered metric decoder uses Leonardo Bonanno's
`LatticeProb.Bonanno.LQGMetric.Field.CameronMartin` formalization. -/

namespace HarmonicBalls
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

/-- The absolute internal metric of the whole-plane field on the inner ball
has a version measurable in the outside field modulo additive constants. -/
theorem IsCorrectedPinchConfiguration.exists_outside_internal_baseMetric
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇) :
    ∃ G : Ω → ℂ → ℂ → ℝ≥0∞,
      (∀ x y, @Measurable Ω ℝ≥0∞
        (MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ) inferInstance) _
        (fun ω => G ω x y)) ∧
      ∀ᵐ ω ∂P, ∀ x ∈ ball 0 (3 * δ), ∀ y ∈ ball 0 (3 * δ),
        internalMetric (𝔇 (hC ω)) (ball 0 (3 * δ)) x y = G ω x y := by
  let B : Set ℂ := ball 0 (3 * δ)
  have hB : IsOpen B := isOpen_ball
  have hBne : B.Nonempty := ⟨0, mem_ball_self (by have := h.δ₀_mem.1; positivity)⟩
  have hBout : B ⊆ (closure W)ᶜ := h.inner_sphere_ball_subset_outside
  obtain ⟨ψ, hψ, hψint⟩ := IsTestFunction.exists_integral_eq_one hB hBne
  obtain ⟨X, hX, hXe⟩ := h.exists_outside_absolute_pairing hgff ψ (hψ.mono_set hBout) hψint
  have hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (𝔇 (hC ω)) := by
    have hh := ae_wholePlane_weylScaling_shift P γ ξ hC hcirc 𝔇 h𝔇 hgff
      (fun _ _ => 0) (fun _ => continuous_const) (fun _ => measurable_const)
    exact hh.mono fun _ hh => hh.1
  have hmetric' : ∀ᵐ ω ∂P, IsEuclideanLengthMetric
      (fun x y => Real.exp (ξ * (-hC ω ψ)) * 𝔇 (hC ω) x y) := by
    filter_upwards [hmetric] with ω hw
    exact hw.const_mul (Real.exp_pos _)
  have hcount := fun (p : ℕ → ℂ × ℂ) hp =>
    hgff.exists_modConst_countable_internal_baseMetric (α := 0) 𝔇 h𝔇 hB ψ hψ hψint p hp
  obtain ⟨G, hG, hGe⟩ := exists_internalMetric_version_of_countable
    (Section6.fieldSigmaAlgebraModConst 0 hC B) hB hBne hmetric' hcount
  let H : Ω → ℂ → ℂ → ℝ≥0∞ := fun ω x y => ENNReal.ofReal (Real.exp (ξ * X ω)) * G ω x y
  refine ⟨H, ?_, ?_⟩
  · intro x y
    have hG' : @Measurable Ω ℝ≥0∞
        (MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ) inferInstance) _
        (fun ω => G ω x y) := by
      rw [← fieldSigmaAlgebraModConst_eq_comap_localModConstPairings]
      exact (hG x y).mono (fieldSigmaAlgebraModConst_mono 0 hC hBout) le_rfl
    exact ((measurable_const.mul hX).exp.ennreal_ofReal).mul hG'
  · filter_upwards [hGe, hXe] with ω hg hx x hxB y hyB
    dsimp [H]
    rw [hx, ← hg x hxB y hyB, internalMetric_const_mul _ (Real.exp_pos _)]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    have hz : ξ * hC ω ψ + ξ * (-hC ω ψ) = 0 := by ring
    rw [hz]
    simp [B]

/-- The absolute distance between the two pinch spheres is determined by the
outside field for a whole-plane GFF base metric. -/
theorem IsCorrectedPinchConfiguration.exists_outside_baseMetric_sphere_distance
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇) :
    ∃ a : Ω → ℝ≥0∞, @Measurable Ω ℝ≥0∞
      (MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ) inferInstance) _ a ∧
      a =ᵐ[P] fun ω => ENNReal.ofReal
        (setDist (𝔇 (hC ω)) (sphere 0 δ) (sphere 0 (2 * δ))) := by
  have hm : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (𝔇 (hC ω)) := by
    have hh := ae_wholePlane_weylScaling_shift P γ ξ hC hcirc 𝔇 h𝔇 hgff
      (fun _ _ => 0) (fun _ => continuous_const) (fun _ => measurable_const)
    exact hh.mono fun _ hh => hh.1
  obtain ⟨G, hG, hGe⟩ := h.exists_outside_internal_baseMetric hgff 𝔇 h𝔇
  apply exists_local_pinch_sphere_distance_representative h.δ₀_mem.1 hm
  · intro x hx y hy
    exact hG x y
  · filter_upwards [hGe] with ω hw x hx y hy
    apply hw x _ y _
    · rw [mem_sphere] at hx
      rw [mem_ball]
      linarith [h.δ₀_mem.1]
    · rw [mem_sphere] at hy
      rw [mem_ball]
      linarith [h.δ₀_mem.1]

#print axioms IsCorrectedPinchConfiguration.exists_outside_baseMetric_sphere_distance
#print axioms IsCorrectedPinchConfiguration.exists_outside_internal_baseMetric
end HarmonicBalls
