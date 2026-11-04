import HarmonicBalls.Proofs.Sec11.SingularMetricConstantShift
import HarmonicBalls.Steps.Sec11.CenteredFieldSigma

/-! # Normalized locality of the base LQG metric

For a pointwise linear pairing, locality of the base metric after a random
constant shift yields locality modulo constants. The corresponding result for
the logarithmically singular Weyl metric requires an additional argument.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric Topology
open scoped ENNReal

/-- The base LQG metric normalized by a reference pairing has internal
metric representatives measurable in the field modulo constants. The
pointwise linearity of the pairing on local tests is explicit. -/
theorem IsWholePlaneGFF.exists_modConst_internal_baseMetric_of_linearOnTests
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    {U : Set ℂ} (hU : IsOpen U) (hlin : ∀ ω, IsLinearOnTests U (hC ω))
    (ψ : ℂ → ℝ) (hψ : IsTestFunction U ψ) (hψint : ∫ x, ψ x = 1) :
    ∃ (c : Ω → ℝ) (G : Ω → ℂ → ℂ → ℝ≥0∞),
      (∀ᵐ ω ∂P, 0 < c ω) ∧
      (∀ x y, Measurable[Section6.fieldSigmaAlgebraModConst α hC U] (fun ω => G ω x y)) ∧
      (∀ᵐ ω ∂P, ∀ x ∈ U, ∀ y ∈ U,
        internalMetric (fun x y => c ω * 𝔇 (hC ω) x y) U x y = G ω x y) := by
  let c : Ω → ℝ := fun ω => -hC ω ψ
  have hc : Measurable c := (h.measurable_pairing ψ (hψ.mono_set (subset_univ _))).neg
  have ha := h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc (fun ω _ => c ω) h
    (fun _ => continuous_const) (fun _ => hc)
  obtain ⟨G, hG, hGeq⟩ := ha.locality U hU
  have hsigma : pairingSigmaAlgebra (fun ω => addFunPairing (hC ω) (fun _ => c ω)) U =
      Section6.fieldSigmaAlgebraModConst α hC U := by
    have hpair : (fun ω => addFunPairing (hC ω) (fun _ => c ω)) =
        (fun ω φ => hC ω φ - (∫ x, φ x) * hC ω ψ) := by
      funext ω φ
      simp only [addFunPairing, integral_const_mul, c]
      ring
    rw [hpair]
    have heq := fieldSigmaAlgebra_sub_reference_eq_modConst α hC U hlin ψ hψ hψint
    rw [fieldSigmaAlgebra_eq, fieldSigmaAlgebra_eq_pairingSigmaAlgebra] at heq
    have hp : (fun ω => fieldPairing 0 (fun φ => hC ω φ - (∫ x, φ x) * hC ω ψ)) =
        (fun ω φ => hC ω φ - (∫ x, φ x) * hC ω ψ) := by
      funext ω φ
      simp [fieldPairing]
    rw [hp] at heq
    exact heq
  have hs := h.ae_baseMetric_add_random_constant 𝔇 h𝔇 c hc
  refine ⟨fun ω => Real.exp (ξ * c ω), G,
    Filter.Eventually.of_forall (fun _ => Real.exp_pos _), ?_, ?_⟩
  · intro x y
    rw [← hsigma]
    exact hG x y
  · filter_upwards [hs, hGeq] with ω hs hg x hx y hy
    have heq : 𝔇 (addFunPairing (hC ω) (fun _ => c ω)) =
        fun u v => Real.exp (ξ * c ω) * 𝔇 (hC ω) u v := by
      funext u v
      exact hs u v
    rw [← heq]
    exact hg x hx y hy

/-- Normalized base-metric internal distances are measurable in any larger
field restriction modulo constants. -/
theorem IsWholePlaneGFF.exists_modConst_internal_baseMetric_of_linearOnTests_subset
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    {U V : Set ℂ} (hU : IsOpen U) (hUV : U ⊆ V)
    (hlin : ∀ ω, IsLinearOnTests U (hC ω))
    (ψ : ℂ → ℝ) (hψ : IsTestFunction U ψ) (hψint : ∫ x, ψ x = 1) :
    ∃ (c : Ω → ℝ) (G : Ω → ℂ → ℂ → ℝ≥0∞),
      (∀ᵐ ω ∂P, 0 < c ω) ∧
      (∀ x y, Measurable[Section6.fieldSigmaAlgebraModConst α hC V] (fun ω => G ω x y)) ∧
      (∀ᵐ ω ∂P, ∀ x ∈ U, ∀ y ∈ U,
        internalMetric (fun x y => c ω * 𝔇 (hC ω) x y) U x y = G ω x y) := by
  obtain ⟨c, G, hc, hG, hEq⟩ :=
    h.exists_modConst_internal_baseMetric_of_linearOnTests 𝔇 h𝔇 hU hlin ψ hψ hψint
  refine ⟨c, G, hc, ?_, hEq⟩
  intro x y
  exact (hG x y).mono (fieldSigmaAlgebraModConst_mono α hC hUV) le_rfl

/-- At sufficiently small dyadic scales, the base-metric internal distances
have normalized local versions modulo additive constants. -/
theorem IsWholePlaneGFF.exists_modConst_dyadic_internal_baseMetrics_of_linearOnTests
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hlin : ∀ ω, IsLinearOnTests univ (hC ω)) :
    ∀ ε, 0 < ε → ∃ K, ∀ n, K ≤ n →
      ∃ (c : Ω → ℝ) (G : Ω → ℂ → ℂ → ℝ≥0∞),
        (∀ᵐ ω ∂P, 0 < c ω) ∧
        (∀ x y, Measurable[Section6.fieldSigmaAlgebraModConst α hC (ball 0 ε)]
          (fun ω => G ω x y)) ∧
        (∀ᵐ ω ∂P, ∀ x ∈ ball 0 (6 * ((2 : ℝ)⁻¹ ^ n)),
          ∀ y ∈ ball 0 (6 * ((2 : ℝ)⁻¹ ^ n)),
          internalMetric (fun x y => c ω * 𝔇 (hC ω) x y)
            (ball 0 (6 * ((2 : ℝ)⁻¹ ^ n))) x y = G ω x y) := by
  intro ε hε
  have hlim : Tendsto (fun n : ℕ => 6 * ((2 : ℝ)⁻¹ ^ n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
        (by norm_num : (2 : ℝ)⁻¹ < 1)).const_mul 6
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hlim.eventually (Iio_mem_nhds hε))
  refine ⟨K, ?_⟩
  intro n hn
  have hr : 0 < 6 * ((2 : ℝ)⁻¹ ^ n) := by positivity
  obtain ⟨ψ, hψ, hψint⟩ := IsTestFunction.exists_integral_eq_one
    (isOpen_ball : IsOpen (ball (0 : ℂ) (6 * ((2 : ℝ)⁻¹ ^ n)))) ⟨0, mem_ball_self hr⟩
  have hlin' (ω : Ω) : IsLinearOnTests (ball 0 (6 * ((2 : ℝ)⁻¹ ^ n))) (hC ω) := by
    intro φ ψ hφ hψ a b
    exact hlin ω φ ψ (hφ.mono_set (subset_univ _)) (hψ.mono_set (subset_univ _)) a b
  exact h.exists_modConst_internal_baseMetric_of_linearOnTests_subset 𝔇 h𝔇 isOpen_ball
    (ball_subset_ball (le_of_lt (hK n hn))) hlin' ψ hψ hψint

#print axioms IsWholePlaneGFF.exists_modConst_internal_baseMetric_of_linearOnTests_subset
#print axioms IsWholePlaneGFF.exists_modConst_dyadic_internal_baseMetrics_of_linearOnTests

#print axioms IsWholePlaneGFF.exists_modConst_internal_baseMetric_of_linearOnTests

end HarmonicBalls
