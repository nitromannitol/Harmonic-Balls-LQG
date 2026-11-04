import HarmonicBalls.Proofs.Sec8.CenteredCircleLocal
import HarmonicBalls.Proofs.Sec8.ContinuityExhaustion
import HarmonicBalls.Steps.Sec11.PinchNormalizedMeasure

/-! # Modulo-constant local normalized LQG masses

The Section 8 construction used here imports Leonardo Bonanno's LatticeProb
formalization. The reference ball is strictly inside the field neighborhood.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric
open scoped ENNReal

/-- In every origin neighborhood, the restriction of the LQG measure to a
smaller deterministic ball has a normalized version measurable from the field
modulo constants. The statement includes equality of all local Borel masses
on one common almost-sure event. -/
theorem IsWholePlaneGFF.exists_modConst_normalized_lqg_masses
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    {γ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hfull : ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ ω U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R ∈ Ioo (0 : ℝ) ε, ∃ ν : Ω → Measure ℂ,
      @Measurable Ω (Measure ℂ) (Section6.fieldSigmaAlgebraModConst α₀ hC (ball 0 ε)) _ ν ∧
      ∀ᵐ ω ∂P,
        (μ ω (ball 0 R))⁻¹ ≠ 0 ∧ (μ ω (ball 0 R))⁻¹ ≠ ∞ ∧
        ∀ B : Set ℂ, MeasurableSet B → B ⊆ ball 0 R →
          ((μ ω (ball 0 R))⁻¹ • μ ω) B = ν ω B := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  let m := Section6.fieldSigmaAlgebraModConst α₀ hC (ball 0 ε)
  let : MeasurableSpace Ω := mΩ
  have hm : m ≤ mΩ := (Section6.fieldSigmaAlgebraModConst_le α₀ hC _).trans
    (hGFF.fieldSigmaAlgebra_le α₀ _)
  have hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) := by
    filter_upwards [hμ] with ω hω
    exact hω.isLocallyFiniteMeasure
  have hpositive := ae_referenceBall_pos_finite P μ hfull hloc
  obtain ⟨R, E, hR, _, hbuffer, hversion⟩ :=
    hGFF.exists_normalizedRestriction_of_centered_versions P m hm hμ hpositive hε
  have hex : ∀ n : ℕ, ∃ d : Ω → ℂ → ℝ,
      @Measurable (Ω × ℂ) ℝ (m.prod inferInstance) _ (Function.uncurry d) ∧
      ∀ᵐ ω ∂P, ∀ z, closedBall z (dyadicScale n) ⊆ ball 0 ε →
        d ω z = fieldCircleAverage α₀ (hcirc ω) (dyadicScale n) z -
          fieldCircleAverage α₀ (hcirc ω) (dyadicScale n) 0 := by
    intro n
    exact hGFF.exists_joint_centered_circle_version (α₀ := α₀) (ε := ε) (dyadicScale_pos n)
  choose d hdm hdeq using hex
  obtain ⟨ν, hν, hνeq⟩ := hversion d hdm (fun n => (hdeq n).mono fun ω hω z hz => hω z (hbuffer n z hz))
  refine ⟨R, hR, ν, hν, ?_⟩
  filter_upwards [hpositive, hνeq] with ω hpos heq
  obtain ⟨hne, htop⟩ := hpos R hR.1
  refine ⟨ENNReal.inv_ne_zero.mpr htop, ENNReal.inv_ne_top.mpr hne, ?_⟩
  intro B hB hBR
  rw [heq, normalizedRestriction, Measure.smul_apply, Measure.smul_apply,
    Measure.restrict_apply hB, inter_eq_self_of_subset_left hBR]

#print axioms IsWholePlaneGFF.exists_modConst_normalized_lqg_masses

end HarmonicBalls
