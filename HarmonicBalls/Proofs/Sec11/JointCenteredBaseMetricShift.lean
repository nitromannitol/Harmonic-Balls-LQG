import HarmonicBalls.Proofs.Sec11.CenteredShiftDecoder
import HarmonicBalls.Proofs.Sec11.ShiftedNormalizedMeasureDecoder

/-! # Joint measure and centered base metric under smooth shifts

The metric here is the whole-plane base metric. Extending this decoder to
internal distances of the logarithmically singular metric remains separate.
The Cameron–Martin arguments use Leonardo Bonanno's LatticeProb formalization.
-/

noncomputable section

namespace HarmonicBalls

open MeasureTheory Filter Set Metric
open scoped ENNReal

/-- The normalized log-singular LQG measure and countably many reference-
normalized base metric distances have a common full-field decoder. Each fixed
smooth shift has equivalent joint law and its geometric Weyl description. -/
theorem IsWholePlaneGFF.exists_joint_measure_centered_baseMetric_shift_decoder
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α ε : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hfull : ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ ω U)
    (hε : 0 < ε) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (ψ : ℂ → ℝ)
    (hψ : IsTestFunction univ ψ) (hψint : ∫ x, ψ x = 1)
    (p : ℕ → ℂ × ℂ) :
    ∃ R ∈ Ioo (0 : ℝ) ε,
      ∃ F : (LocalZeroMeanTest univ → ℝ) → Measure ℂ × (ℕ → ℝ), Measurable F ∧
      ∀ g : ℂ → ℝ, IsTestFunction univ g →
        (∀ᵐ ω ∂P, F (localModConstPairings 0
          (fun ω => addFunPairing (hC ω) g) univ ω) =
          (normalizedRestriction ((μ ω).withDensity
              (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R),
            fun n => Real.exp (ξ * (-(hC ω ψ + ∫ x, g x * ψ x))) *
              (weylScaling (𝔇 (hC ω)) ξ g (p n).1 (p n).2).toReal)) ∧
        P.map (F ∘ localModConstPairings 0
          (fun ω => addFunPairing (hC ω) g) univ) ≪
          P.map (F ∘ localModConstPairings 0 hC univ) ∧
        P.map (F ∘ localModConstPairings 0 hC univ) ≪
          P.map (F ∘ localModConstPairings 0
            (fun ω => addFunPairing (hC ω) g) univ) := by
  obtain ⟨R, hR, M, hM, _, hMeq⟩ := h.exists_shifted_normalized_measure_decoder hμ hfull hε
  obtain ⟨G, hG, hGeq⟩ := h.exists_centered_baseMetric_shift_decoder 𝔇 h𝔇 ψ hψ hψint p
  let Q : (LocalZeroMeanTest univ → ℝ) → LocalZeroMeanTest (ball 0 ε) → ℝ :=
    fun v φ => v ⟨φ.1, φ.2.1.mono_set (subset_univ _), φ.2.2⟩ -
      α * ∫ x, φ.1 x * Real.log ‖x‖
  have hQ : Measurable Q := by
    apply measurable_pi_iff.mpr
    intro φ
    exact (measurable_pi_apply
      (⟨φ.1, φ.2.1.mono_set (subset_univ _), φ.2.2⟩ : LocalZeroMeanTest univ)).sub_const _
  let F := fun v => (M (Q v), G v)
  have hF : Measurable F := (hM.comp hQ).prodMk hG
  have hQeq (T : (ℂ → ℝ) → ℝ) :
      Q (localModConstPairings 0 id univ T) = localModConstPairings α id (ball 0 ε) T := by
    funext φ
    simp [Q, localModConstPairings, fieldPairing]
  refine ⟨R, hR, F, hF, ?_⟩
  intro g hg
  let X := localModConstPairings 0 hC univ
  let Y := localModConstPairings 0 (fun ω => addFunPairing (hC ω) g) univ
  have hX : Measurable X := by
    apply measurable_pi_iff.mpr
    intro φ
    change Measurable (fun ω => hC ω φ.1 - 0 * ∫ x, φ.1 x * Real.log ‖x‖)
    exact (h.measurable_pairing φ.1 φ.2.1).sub_const _
  have hY : Measurable Y := by
    apply measurable_pi_iff.mpr
    intro φ
    change Measurable (fun ω => (hC ω φ.1 + ∫ x, g x * φ.1 x) -
      0 * ∫ x, φ.1 x * Real.log ‖x‖)
    exact ((h.measurable_pairing φ.1 φ.2.1).add_const _).sub_const _
  have hac := h.singular_smooth_shift_modConst_pairing_laws hg 0 univ
  change P.map Y ≪ P.map X ∧ P.map X ≪ P.map Y at hac
  have hf := hac.1.map hF
  have hb := hac.2.map hF
  rw [Measure.map_map hF hY, Measure.map_map hF hX] at hf
  rw [Measure.map_map hF hX, Measure.map_map hF hY] at hb
  refine ⟨?_, hf, hb⟩
  filter_upwards [hMeq g hg, hGeq g hg.1.continuous] with ω hm hg'
  apply Prod.ext
  · change M (Q (localModConstPairings 0 id univ (addFunPairing (hC ω) g))) = _
    rw [hQeq]
    exact hm
  · funext n
    exact hg' n

#print axioms IsWholePlaneGFF.exists_joint_measure_centered_baseMetric_shift_decoder

end HarmonicBalls
