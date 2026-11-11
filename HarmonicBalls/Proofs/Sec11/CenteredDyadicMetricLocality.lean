import HarmonicBalls.Proofs.Sec11.CenteredSingularMetricLocality

/-! # Dyadic normalized metric locality

A single local version for each centered internal metric supplies the dyadic
locality hypothesis used in the pinch-frequency argument. Centered metric
locality itself remains an explicit hypothesis.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric Topology
open scoped ENNReal

/-- Locality of centered singular internal metrics on open subsets of a ball
implies the normalized modulo-constant dyadic metric locality used for pinch
scales. -/
theorem IsWholePlaneGFF.exists_modConst_dyadic_internalMetrics_of_centered_locality
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) =
        weylScaling (𝔇 (hC ω)) ξ (fun x => -α * Real.log ‖x‖) u v)
    (hlocal : ∀ ε, 0 < ε → ∀ ψ : ℂ → ℝ,
      IsTestFunction (ball 0 ε) ψ → (∫ x, ψ x) = 1 →
      ∀ V : Set ℂ, IsOpen V → V ⊆ ball 0 ε →
      ∃ G : Ω → ℂ → ℂ → ℝ≥0∞,
        (∀ x y, Measurable[fieldSigmaAlgebra α
          (fun ω => centeredTestPairing (hC ω) ψ) (ball 0 ε)] (fun ω => G ω x y)) ∧
        ∀ᵐ ω ∂P, ∀ x ∈ V, ∀ y ∈ V,
          internalMetric (fun u v =>
            (weylScaling (𝔇 (addFunPairing (hC ω) (fun _ => -hC ω ψ))) ξ
              (fun z => -α * Real.log ‖z‖) u v).toReal) V x y = G ω x y) :
    ∀ ε, 0 < ε → ∃ K, ∀ n, K ≤ n →
      ∃ (c : Ω → ℝ) (G : Ω → ℂ → ℂ → ℝ≥0∞),
        (∀ᵐ ω ∂P, 0 < c ω) ∧
        (∀ x y, Measurable[Section6.fieldSigmaAlgebraModConst α hC (ball 0 ε)]
          (fun ω => G ω x y)) ∧
        (∀ᵐ ω ∂P, ∀ x ∈ ball 0 (6 * ((2 : ℝ)⁻¹ ^ n)),
          ∀ y ∈ ball 0 (6 * ((2 : ℝ)⁻¹ ^ n)),
          internalMetric (fun x y => c ω * D ω x y)
            (ball 0 (6 * ((2 : ℝ)⁻¹ ^ n))) x y = G ω x y) := by
  intro ε hε
  obtain ⟨ψ, hψ, hψint⟩ := IsTestFunction.exists_integral_eq_one
    (isOpen_ball : IsOpen (ball (0 : ℂ) ε)) ⟨0, mem_ball_self hε⟩
  have hlim : Tendsto (fun n : ℕ => 6 * ((2 : ℝ)⁻¹ ^ n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
        (by norm_num : (2 : ℝ)⁻¹ < 1)).const_mul 6
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hlim.eventually (Iio_mem_nhds hε))
  refine ⟨K, ?_⟩
  intro n hn
  have hsub : ball (0 : ℂ) (6 * ((2 : ℝ)⁻¹ ^ n)) ⊆ ball 0 ε :=
    ball_subset_ball (le_of_lt (hK n hn))
  exact h.exists_modConst_internalMetric_of_centered_locality 𝔇 h𝔇 hD ψ hψ hψint
    (hlocal ε hε ψ hψ hψint _ isOpen_ball hsub)


end HarmonicBalls
