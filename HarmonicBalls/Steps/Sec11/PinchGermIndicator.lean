import HarmonicBalls.Steps.Sec11.PinchLocalEvent

/-! # Germ-measurable pinch indicators -/

namespace HarmonicBalls

open Set Metric Filter MeasureTheory Topology

open Classical in
/-- The staged metric and measure locality inputs give bounded dyadic pinch
indicators which represent the event almost surely and are eventually
measurable with respect to every field neighborhood of the marked point. -/
theorem exists_germ_measurable_pinchIndicators
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {γ ξ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {U T Q' Q : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q' Q)
    (M : ℝ) (z : ℂ) (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α₀ < lqgQ γ)
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hD : IsLQGMetricOfField P γ ξ α₀ hC D)
    (hmloc : LQGMeasureLocality P γ α₀ hC hcirc)
    (haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc) :
    ∃ X : ℕ → Ω → ℝ,
      (∀ n, Measurable (X n)) ∧ (∀ n ω, X n ω ∈ Icc (0 : ℝ) 1) ∧
      (∀ᵐ ω ∂P, ∀ n, X n ω = if pinchPointEventWithInternalBounds (μ ω) (D ω)
        U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z then 1 else 0) ∧
      (∀ ε, 0 < ε → ∃ K, ∀ n, K ≤ n →
        Measurable[fieldSigmaAlgebra α₀ hC (ball z ε)] (X n)) := by
  have hex (n : ℕ) := @exists_local_lqg_pinchEvent_representative Ω mΩ P γ ξ α₀ hC hcirc D μ
    U T Q' Q hconfig M z ((2 : ℝ)⁻¹ ^ n) (by positivity) hγ hγ₂ hα hgff hμ hD hmloc haxioms
  choose E hE hEeq using hex
  let X : ℕ → Ω → ℝ := fun n ω => if ω ∈ E n then 1 else 0
  have hm (n : ℕ) : Measurable (X n) := by
    exact Measurable.ite ((hgff.fieldSigmaAlgebra_le α₀ _ ) _ (hE n)) measurable_const measurable_const
  have hb (n : ℕ) (ω : Ω) : X n ω ∈ Icc (0 : ℝ) 1 := by
    dsimp only [X]
    split_ifs <;> norm_num
  have heq : ∀ᵐ ω ∂P, ∀ n, X n ω = if pinchPointEventWithInternalBounds (μ ω) (D ω)
      U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z then 1 else 0 := by
    filter_upwards [ae_all_iff.mpr hEeq] with ω hω
    intro n
    simp only [X, ← hω n]
  have hlim : Tendsto (fun n : ℕ => 6 * ((2 : ℝ)⁻¹ ^ n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
        (by norm_num : (2 : ℝ)⁻¹ < 1)).const_mul 6
  have hgerm : ∀ ε, 0 < ε → ∃ K, ∀ n, K ≤ n →
      Measurable[fieldSigmaAlgebra α₀ hC (ball z ε)] (X n) := by
    intro ε hε
    obtain ⟨K, hK⟩ := eventually_atTop.mp (hlim.eventually (Iio_mem_nhds hε))
    refine ⟨K, fun n hn => ?_⟩
    have hsub : ball z (6 * ((2 : ℝ)⁻¹ ^ n)) ⊆ ball z ε :=
      ball_subset_ball (le_of_lt (hK n hn))
    let : MeasurableSpace Ω := fieldSigmaAlgebra α₀ hC (ball z ε)
    exact Measurable.ite ((fieldSigmaAlgebra_mono α₀ hC hsub) _ (hE n))
      measurable_const measurable_const
  exact ⟨X, hm, hb, heq, hgerm⟩

end HarmonicBalls
