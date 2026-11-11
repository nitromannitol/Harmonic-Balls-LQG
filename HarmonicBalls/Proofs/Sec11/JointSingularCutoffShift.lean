import HarmonicBalls.Proofs.Sec11.ContinuousBaseMetricShiftDecoder
import HarmonicBalls.Proofs.Sec11.ShiftedNormalizedMeasureDecoder

/-! # Joint singular-measure and cutoff-metric shifts

The cutoff metric represents the singular internal metric on domains away
from the origin. The shifted cutoff has not been identified here with the
Weyl shift of the singular metric. The Cameron–Martin argument uses
Leonardo Bonanno's LatticeProb formalization.
-/

noncomputable section

namespace HarmonicBalls

open MeasureTheory Filter Set Metric
open scoped ENNReal

/-- Jointly decode the normalized singular measure and the normalized
singular internal distances on domains at positive distance from zero.
Smoothly shifted observations have equivalent laws and an explicit
cutoff-background metric interpretation. -/
theorem IsWholePlaneGFF.exists_joint_singular_cutoff_shift_decoder
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α ε : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hfull : ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ ω U)
    (hε : 0 < ε) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) =
        weylScaling (𝔇 (hC ω)) ξ (fun x => -α * Real.log ‖x‖) u v)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (ψ : ℂ → ℝ) (hψ : IsTestFunction univ ψ) (hψint : ∫ x, ψ x = 1)
    {r : ℝ} (hr : 0 < r) (U : ℕ → Set ℂ) (hU : ∀ n, IsOpen (U n))
    (haway : ∀ n z, z ∈ U n → r ≤ ‖z‖)
    (p : ℕ → ℂ × ℂ) (hp : ∀ n, (p n).1 ∈ U n) :
    let f : ℂ → ℝ := fun z => -α * Real.log (max ‖z‖ r)
    ∃ R ∈ Ioo (0 : ℝ) ε,
      ∃ F : (LocalZeroMeanTest univ → ℝ) → Measure ℂ × (ℕ → ℝ≥0∞), Measurable F ∧
        (∀ᵐ ω ∂P, F (localModConstPairings 0 hC univ ω) =
          (normalizedRestriction (μ ω) (ball 0 R), fun n =>
            ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, f z * ψ z)))) *
              internalMetric (D ω) (U n) (p n).1 (p n).2)) ∧
        ∀ g : ℂ → ℝ, IsTestFunction univ g →
          (∀ᵐ ω ∂P, F (localModConstPairings 0
            (fun ω => addFunPairing (hC ω) g) univ ω) =
            (normalizedRestriction ((μ ω).withDensity
              (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R), fun n =>
                ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, (g z + f z) * ψ z)))) *
                  internalMetric (fun x y =>
                    (weylScaling (𝔇 (hC ω)) ξ (fun z => g z + f z) x y).toReal)
                    (U n) (p n).1 (p n).2)) ∧
          P.map (F ∘ localModConstPairings 0
            (fun ω => addFunPairing (hC ω) g) univ) ≪
            P.map (F ∘ localModConstPairings 0 hC univ) ∧
          P.map (F ∘ localModConstPairings 0 hC univ) ≪
            P.map (F ∘ localModConstPairings 0
              (fun ω => addFunPairing (hC ω) g) univ) := by
  obtain ⟨G, hG, hGbase, hGshift⟩ :=
    h.exists_internal_singularMetric_cutoff_shift_decoder 𝔇 h𝔇 hD hmetric ψ hψ hψint
      hr U hU haway p hp
  obtain ⟨R, hR, M, hM, _, hMeq⟩ := h.exists_shifted_normalized_measure_decoder hμ hfull hε
  let Q : (LocalZeroMeanTest univ → ℝ) → LocalZeroMeanTest (ball 0 ε) → ℝ :=
    fun v φ => v ⟨φ.1, φ.2.1.mono_set (subset_univ _), φ.2.2⟩ -
      α * ∫ x, φ.1 x * Real.log ‖x‖
  have hQ : Measurable Q := by
    apply measurable_pi_iff.mpr
    intro φ
    exact (measurable_pi_apply
      (⟨φ.1, φ.2.1.mono_set (subset_univ _), φ.2.2⟩ : LocalZeroMeanTest univ)).sub_const _
  have hQeq (T : (ℂ → ℝ) → ℝ) :
      Q (localModConstPairings 0 id univ T) = localModConstPairings α id (ball 0 ε) T := by
    funext φ
    simp [Q, localModConstPairings, fieldPairing]
  let F := fun v => (M (Q v), G v)
  have hF : Measurable F := (hM.comp hQ).prodMk hG
  have hzero : (fun ω => addFunPairing (hC ω) (fun _ => 0)) = hC := by
    funext ω φ
    simp [addFunPairing]
  have hzeroTest : IsTestFunction univ (fun _ : ℂ => (0 : ℝ)) :=
    ⟨contDiff_const, HasCompactSupport.zero, by simp⟩
  have hbase := hMeq (fun _ => 0) hzeroTest
  simp only [hzero, mul_zero, Real.exp_zero, ENNReal.ofReal_one] at hbase
  have hwone (ω : Ω) : (μ ω).withDensity (fun _ => 1) = μ ω := withDensity_one
  simp only [hwone] at hbase
  refine ⟨R, hR, F, hF, ?_, ?_⟩
  · filter_upwards [hbase, hGbase] with ω hm hg
    apply Prod.ext
    · change M (Q (localModConstPairings 0 id univ (hC ω))) = _
      rw [hQeq]
      exact hm
    · funext n
      exact hg n
  · intro g hg
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
    filter_upwards [hMeq g hg, hGshift g hg.1.continuous] with ω hm hg'
    apply Prod.ext
    · change M (Q (localModConstPairings 0 id univ (addFunPairing (hC ω) g))) = _
      rw [hQeq]
      exact hm
    · funext n
      exact hg' n


end HarmonicBalls
