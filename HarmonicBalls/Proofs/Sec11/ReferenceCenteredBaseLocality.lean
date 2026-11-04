import HarmonicBalls.Proofs.Sec11.CenteredBaseMetricLocality

/-! # Base metric locality from reference centering

Only the reference-centering identity is needed for normalized base-metric
locality. This identity remains an explicit hypothesis; the GFF interface
alone does not assert simultaneous linearity of its sample pairings.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set
open scoped ENNReal

/-- A reference-centering identity on local tests identifies the sigma algebra
of the shifted field with the original field modulo constants. -/
theorem fieldSigmaAlgebra_sub_reference_eq_modConst_of_centering
    {Ω : Type*} (α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (U : Set ℂ)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction U ψ) (hψint : ∫ x, ψ x = 1)
    (hcenter : ∀ ω φ, IsTestFunction U φ →
      centeredTestPairing (hC ω) ψ φ = hC ω φ - (∫ x, φ x) * hC ω ψ) :
    fieldSigmaAlgebra α (fun ω φ => hC ω φ - (∫ x, φ x) * hC ω ψ) U =
      Section6.fieldSigmaAlgebraModConst α hC U := by
  rw [← fieldSigmaAlgebra_centeredTestPairing_eq_modConst α hC U ψ hψ hψint]
  unfold fieldSigmaAlgebra
  congr 1
  ext1 φ
  congr 1
  ext1 hφ
  congr 1
  funext ω
  simp only [fieldPairing, hcenter ω φ hφ]

/-- A reference-centering identity, weaker than full linearity of the pairing,
gives normalized local internal distances for the base LQG metric. -/
theorem IsWholePlaneGFF.exists_modConst_internal_baseMetric_of_centering
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    {U : Set ℂ} (hU : IsOpen U) (ψ : ℂ → ℝ)
    (hψ : IsTestFunction U ψ) (hψint : ∫ x, ψ x = 1)
    (hcenter : ∀ ω φ, IsTestFunction U φ →
      centeredTestPairing (hC ω) ψ φ = hC ω φ - (∫ x, φ x) * hC ω ψ) :
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
    have heq := fieldSigmaAlgebra_sub_reference_eq_modConst_of_centering α hC U ψ hψ
      hψint hcenter
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

#print axioms fieldSigmaAlgebra_sub_reference_eq_modConst_of_centering
#print axioms IsWholePlaneGFF.exists_modConst_internal_baseMetric_of_centering

end HarmonicBalls
