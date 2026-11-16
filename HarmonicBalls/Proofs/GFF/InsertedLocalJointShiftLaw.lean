import HarmonicBalls.Proofs.Sec11.ShiftedNormalizedMeasureDecoder
import HarmonicBalls.FirstPass.Phase2.SquarePositiveHolds

/-! # Local field and normalized measure under smooth shifts

A local centered field and its normalized LQG measure have equivalent joint
laws after a deterministic smooth compactly supported perturbation.
-/

open MeasureTheory Filter Set Metric
open scoped ENNReal

namespace HarmonicBalls

/-- The local centered field and normalized measure are jointly equivalent in
law under each fixed smooth compactly supported shift. -/
theorem IsWholePlaneGFF.exists_local_field_normalizedMeasure_shift_law
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ε α γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hfull : ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ ω U)
    (hε : 0 < ε) :
    ∃ R ∈ Ioo (0 : ℝ) ε, ∀ g : ℂ → ℝ, IsTestFunction univ g →
      P.map (fun ω =>
        (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω,
          normalizedRestriction ((μ ω).withDensity
            (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R))) ≪
        P.map (fun ω =>
          (localModConstPairings α hC (ball 0 ε) ω,
            normalizedRestriction (μ ω) (ball 0 R))) ∧
      P.map (fun ω =>
        (localModConstPairings α hC (ball 0 ε) ω,
          normalizedRestriction (μ ω) (ball 0 R))) ≪
        P.map (fun ω =>
          (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω,
            normalizedRestriction ((μ ω).withDensity
              (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R))) := by
  obtain ⟨R, hR, D, hDm, _, hD⟩ := hGFF.exists_shifted_normalized_measure_decoder hμ hfull hε
  refine ⟨R, hR, ?_⟩
  intro g hg
  let X := localModConstPairings α hC (ball 0 ε)
  let Y := localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε)
  have hX : Measurable X := by
    apply measurable_pi_iff.mpr
    intro φ
    change Measurable (fun ω => hC ω φ.1 - α * ∫ x, φ.1 x * Real.log ‖x‖)
    exact (hGFF.measurable_pairing φ.1 (φ.2.1.mono_set (subset_univ _))).sub_const _
  have hY : Measurable Y := by
    apply measurable_pi_iff.mpr
    intro φ
    change Measurable (fun ω => (hC ω φ.1 + ∫ x, g x * φ.1 x) -
      α * ∫ x, φ.1 x * Real.log ‖x‖)
    exact ((hGFF.measurable_pairing φ.1 (φ.2.1.mono_set (subset_univ _))).add_const _).sub_const _
  have hzero : (fun ω => addFunPairing (hC ω) (fun _ => 0)) = hC := by
    funext ω φ
    simp [addFunPairing]
  have hzeroTest : IsTestFunction univ (fun _ : ℂ => (0 : ℝ)) :=
    ⟨contDiff_const, HasCompactSupport.zero, by simp⟩
  have hbase := hD (fun _ => 0) hzeroTest
  simp only [hzero, mul_zero, Real.exp_zero, ENNReal.ofReal_one] at hbase
  have hwone (ω : Ω) : (μ ω).withDensity (fun _ => 1) = μ ω := withDensity_one
  simp only [hwone] at hbase
  have hshift := hD g hg
  let F := fun v => (v, D v)
  have hF : Measurable F := measurable_id.prodMk hDm
  have hforward := (hGFF.singular_smooth_shift_modConst_pairing_laws hg α (ball 0 ε)).1.map hF
  have hback := (hGFF.singular_smooth_shift_modConst_pairing_laws hg α (ball 0 ε)).2.map hF
  change (P.map Y).map F ≪ (P.map X).map F at hforward
  change (P.map X).map F ≪ (P.map Y).map F at hback
  rw [Measure.map_map hF hY, Measure.map_map hF hX] at hforward
  rw [Measure.map_map hF hX, Measure.map_map hF hY] at hback
  have hb : P.map (F ∘ X) = P.map (fun ω => (X ω, normalizedRestriction (μ ω) (ball 0 R))) := by
    apply Measure.map_congr
    filter_upwards [hbase] with ω hω
    exact Prod.ext rfl hω
  have hs : P.map (F ∘ Y) = P.map (fun ω => (Y ω, normalizedRestriction ((μ ω).withDensity
      (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R))) := by
    apply Measure.map_congr
    filter_upwards [hshift] with ω hω
    exact Prod.ext rfl hω
  rw [hb, hs] at hforward hback
  exact ⟨hforward, hback⟩

/-- For subcritical LQG, the local centered field and normalized measure have
equivalent joint laws under each fixed smooth compactly supported shift. -/
theorem IsWholePlaneGFF.exists_local_field_normalizedMeasure_shift_law_of_subcritical
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ε α γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ) (hε : 0 < ε) :
    ∃ R ∈ Ioo (0 : ℝ) ε, ∀ g : ℂ → ℝ, IsTestFunction univ g →
      P.map (fun ω =>
        (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω,
          normalizedRestriction ((μ ω).withDensity
            (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R))) ≪
        P.map (fun ω =>
          (localModConstPairings α hC (ball 0 ε) ω,
            normalizedRestriction (μ ω) (ball 0 R))) ∧
      P.map (fun ω =>
        (localModConstPairings α hC (ball 0 ε) ω,
          normalizedRestriction (μ ω) (ball 0 R))) ≪
        P.map (fun ω =>
          (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω,
            normalizedRestriction ((μ ω).withDensity
              (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R))) := by
  exact hGFF.exists_local_field_normalizedMeasure_shift_law hμ
    (lqgMeasureFullSupportStmt_holds γ α hγ hγ2 hα Ω P hC hcirc μ hGFF hμ) hε


end HarmonicBalls
