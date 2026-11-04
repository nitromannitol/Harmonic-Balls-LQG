import HarmonicBalls.Proofs.Sec11.PinchNormalizedLQGMass

/-! # Modulo-constant local tail versions of pinch events

The imported Section 8 construction uses Leonardo Bonanno's LatticeProb
formalization. The normalized metric locality hypothesis remains explicit.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric Topology
open scoped ENNReal

open Classical in
/-- Normalized metric locality gives local versions of all sufficiently small
pinch events. The LQG measure normalization is constructed from centered circle
averages, full support and the LQG limit. -/
theorem IsWholePlaneGFF.exists_modConst_local_pinch_tail_versions
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    {γ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hfull : ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ ω U)
    (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    {U T Q V : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q V) (M : ℝ)
    (hmetric : ∀ ε, 0 < ε → ∃ K, ∀ n, K ≤ n →
      ∃ (c : Ω → ℝ) (G : Ω → ℂ → ℂ → ℝ≥0∞),
        (∀ᵐ ω ∂P, 0 < c ω) ∧
        (∀ x y, Measurable[Section6.fieldSigmaAlgebraModConst α₀ hC (ball 0 ε)]
          (fun ω => G ω x y)) ∧
        (∀ᵐ ω ∂P, ∀ x ∈ ball 0 (6 * ((2 : ℝ)⁻¹ ^ n)),
          ∀ y ∈ ball 0 (6 * ((2 : ℝ)⁻¹ ^ n)),
          internalMetric (fun x y => c ω * D ω x y)
            (ball 0 (6 * ((2 : ℝ)⁻¹ ^ n))) x y = G ω x y)) :
    ∀ ε, 0 < ε → ∃ K, ∃ Y : ℕ → Ω → ℝ,
      (∀ n, K ≤ n → Measurable[Section6.fieldSigmaAlgebraModConst α₀ hC (ball 0 ε)] (Y n)) ∧
      (∀ n, K ≤ n → (fun ω => if pinchPointEventWithInternalBounds (μ ω) (D ω)
        U T Q V M ((2 : ℝ)⁻¹ ^ n) 0 then (1 : ℝ) else 0) =ᵐ[P] Y n) := by
  intro ε hε
  let m := Section6.fieldSigmaAlgebraModConst α₀ hC (ball 0 ε)
  let : MeasurableSpace Ω := mΩ
  obtain ⟨R, hR, ν, hν, hνeq⟩ := hGFF.exists_modConst_normalized_lqg_masses P hμ hfull hε
  obtain ⟨K₁, hK₁⟩ := hmetric ε hε
  have hlim : Tendsto (fun n : ℕ => 6 * ((2 : ℝ)⁻¹ ^ n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
        (by norm_num : (2 : ℝ)⁻¹ < 1)).const_mul 6
  obtain ⟨K₂, hK₂⟩ := eventually_atTop.mp (hlim.eventually (Iio_mem_nhds hR.1))
  let K := max K₁ K₂
  have hlocal (n : ℕ) (hn : K ≤ n) : ∃ A : Set Ω, MeasurableSet[m] A ∧
      ∀ᵐ ω ∂P, (pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q V M
        ((2 : ℝ)⁻¹ ^ n) 0 ↔ ω ∈ A) := by
    obtain ⟨c, G, hc, hG, hGeq⟩ := hK₁ n ((le_max_left K₁ K₂).trans hn)
    have hball : ball (0 : ℂ) (6 * ((2 : ℝ)⁻¹ ^ n)) ⊆ ball 0 R :=
      ball_subset_ball (le_of_lt (hK₂ n ((le_max_right K₁ K₂).trans hn)))
    have hscale : ∀ᵐ ω ∂P, 0 < c ω ∧ (μ ω (ball 0 R))⁻¹ ≠ 0 ∧
        (μ ω (ball 0 R))⁻¹ ≠ ∞ := by
      filter_upwards [hc, hνeq] with ω hcω hνω
      exact ⟨hcω, hνω.1, hνω.2.1⟩
    have hmass : ∀ B : Set ℂ, MeasurableSet B → B ⊆ ball 0 (6 * ((2 : ℝ)⁻¹ ^ n)) →
        ∃ Z : Ω → ℝ≥0∞, Measurable[m] Z ∧
          ∀ᵐ ω ∂P, ((μ ω (ball 0 R))⁻¹ • μ ω) B = Z ω := by
      intro B hB hBsub
      refine ⟨fun ω => ν ω B, (Measure.measurable_coe hB).comp hν, ?_⟩
      filter_upwards [hνeq] with ω hω
      exact hω.2.2 B hB (hBsub.trans hball)
    exact @exists_local_pinchEvent_representative_of_normalized_borel_mass Ω mΩ P m D μ G
      U T Q V hconfig M 0 _ (by positivity) c (fun ω => (μ ω (ball 0 R))⁻¹)
      hscale hD hG hGeq hmass
  have hex (n : ℕ) : ∃ A : Set Ω, MeasurableSet[m] A ∧
      (K ≤ n → ∀ᵐ ω ∂P, (pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q V M
        ((2 : ℝ)⁻¹ ^ n) 0 ↔ ω ∈ A)) := by
    by_cases hn : K ≤ n
    · obtain ⟨A, hA, hAeq⟩ := hlocal n hn
      exact ⟨A, hA, fun _ => hAeq⟩
    · exact ⟨∅, @MeasurableSet.empty Ω m, fun h => (hn h).elim⟩
  choose A hA hAeq using hex
  let Y : ℕ → Ω → ℝ := fun n ω => if ω ∈ A n then 1 else 0
  refine ⟨K, Y, ?_, ?_⟩
  · intro n hn
    exact Measurable.ite (hA n) measurable_const measurable_const
  · intro n hn
    filter_upwards [hAeq n hn] with ω hω
    simp only [Y, hω]

#print axioms IsWholePlaneGFF.exists_modConst_local_pinch_tail_versions

end HarmonicBalls
