import HarmonicBalls.Proofs.Sec11.ShiftedNormalizedMeasureDecoder
import HarmonicBalls.Proofs.Sec11.JointNormalizedSmoothShift

/-! # Joint normalized measure and local metric under smooth shifts

The measure component of the common decoder is identified with the
Weyl-weighted LQG measure. The shifted metric component is left as a decoder;
its identification with the Weyl-scaled metric requires a further argument.
The Cameron–Martin theorem uses Leonardo Bonanno's LatticeProb formalization.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped ENNReal

namespace HarmonicBalls

/-- A countable local metric observable and the normalized LQG measure have
one field decoder, whose smooth-shifted law is equivalent to the original
joint law. The shifted measure component is the Weyl-weighted restriction. -/
theorem IsWholePlaneGFF.exists_joint_shifted_measure_metric_decoder
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ε α γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hfull : ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ ω U)
    (hε : 0 < ε) {V : Set ℂ}
    (c : Ω → ℝ) (G : Ω → ℂ → ℂ → ℝ≥0∞)
    (hG : ∀ x y, Measurable[Section6.fieldSigmaAlgebraModConst α hC (ball 0 ε)]
      (fun ω => G ω x y))
    (hGeq : ∀ᵐ ω ∂P, ∀ x ∈ V, ∀ y ∈ V,
      internalMetric (fun x y => c ω * D ω x y) V x y = G ω x y)
    (p : ℕ → ℂ × ℂ) (hp : ∀ n, (p n).1 ∈ V ∧ (p n).2 ∈ V) :
    ∃ R ∈ Ioo (0 : ℝ) ε,
      ∃ F : (LocalZeroMeanTest (ball 0 ε) → ℝ) → Measure ℂ × (ℕ → ℝ≥0∞),
        Measurable F ∧
        (∀ᵐ ω ∂P, F (localModConstPairings α hC (ball 0 ε) ω) =
          (normalizedRestriction (μ ω) (ball 0 R), fun n =>
            internalMetric (fun x y => c ω * D ω x y) V (p n).1 (p n).2)) ∧
        ∀ g : ℂ → ℝ, IsTestFunction univ g →
          (∀ᵐ ω ∂P, (F (localModConstPairings α
            (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω)).1 =
            normalizedRestriction ((μ ω).withDensity
              (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R)) ∧
          P.map (F ∘ localModConstPairings α
            (fun ω => addFunPairing (hC ω) g) (ball 0 ε)) ≪
            P.map (F ∘ localModConstPairings α hC (ball 0 ε)) ∧
          P.map (F ∘ localModConstPairings α hC (ball 0 ε)) ≪
            P.map (F ∘ localModConstPairings α
              (fun ω => addFunPairing (hC ω) g) (ball 0 ε)) := by
  obtain ⟨R, hR, M, hM, _, hMeq⟩ := h.exists_shifted_normalized_measure_decoder hμ hfull hε
  let X := localModConstPairings α hC (ball 0 ε)
  let Q : Ω → ℕ → ℝ≥0∞ := fun ω n => G ω (p n).1 (p n).2
  have hQ : Measurable[Section6.fieldSigmaAlgebraModConst α hC (ball 0 ε)] Q := by
    let : MeasurableSpace Ω := Section6.fieldSigmaAlgebraModConst α hC (ball 0 ε)
    exact measurable_pi_iff.mpr fun n => hG _ _
  have hQ' : Measurable[MeasurableSpace.comap X inferInstance] Q := by
    rw [← fieldSigmaAlgebraModConst_eq_comap_localModConstPairings]
    exact hQ
  obtain ⟨N, hN, hNeq⟩ := hQ'.exists_eq_measurable_comp
  let F := fun v => (M v, N v)
  have hF : Measurable F := hM.prodMk hN
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
  · filter_upwards [hbase, hGeq] with ω hm hg
    apply Prod.ext
    · exact hm
    · funext n
      change N (X ω) n = internalMetric (fun x y => c ω * D ω x y) V (p n).1 (p n).2
      change (N ∘ X) ω n = _
      rw [← congrFun hNeq ω]
      exact (hg _ (hp n).1 _ (hp n).2).symm
  · intro g hg
    let Y := localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε)
    have hX : Measurable X := by
      apply measurable_pi_iff.mpr
      intro φ
      change Measurable (fun ω => hC ω φ.1 - α * ∫ x, φ.1 x * Real.log ‖x‖)
      exact (h.measurable_pairing φ.1 (φ.2.1.mono_set (subset_univ _))).sub_const _
    have hY : Measurable Y := by
      apply measurable_pi_iff.mpr
      intro φ
      change Measurable (fun ω => (hC ω φ.1 + ∫ x, g x * φ.1 x) -
        α * ∫ x, φ.1 x * Real.log ‖x‖)
      exact ((h.measurable_pairing φ.1 (φ.2.1.mono_set (subset_univ _))).add_const _).sub_const _
    have hdom := h.singular_smooth_shift_modConst_pairing_laws hg α (ball 0 ε)
    change P.map Y ≪ P.map X ∧ P.map X ≪ P.map Y at hdom
    have hf := hdom.1.map hF
    have hb := hdom.2.map hF
    rw [Measure.map_map hF hY, Measure.map_map hF hX] at hf
    rw [Measure.map_map hF hX, Measure.map_map hF hY] at hb
    exact ⟨hMeq g hg, hf, hb⟩

/-- Under fixed-scale positive diameter moments, the dyadic singular metric
and the normalized LQG measure have a common local smooth-shift decoder.
The affine-invariance input is staged and the diameter moments are explicit. -/
theorem IsWholePlaneGFF.exists_dyadic_joint_measure_metric_decoder_of_diameter_moments
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hfull : ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ ω U)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) =
        weylScaling (𝔇 (hC ω)) ξ (fun x => -α * Real.log ‖x‖) u v)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hξ : 0 < ξ) (hα : 0 ≤ α) (hαQ : α < lqgQ γ) (β : ℝ) (hβ : 0 < β) :
    ∃ (ρ : ℝ) (N : ℕ) (z : ℕ → ℂ), 0 < ρ ∧
      ((∀ i, i ≤ N → (∫⁻ ω, (⨆ x ∈ closedBall (z i) ρ,
        ⨆ y ∈ closedBall (z i) ρ,
          internalMetric (𝔇 (hC ω)) (ball (z i) (2 * ρ)) x y) ^ β ∂P) ≠ ∞) →
        ∀ ε, 0 < ε → ∃ K, ∀ n, K ≤ n →
          ∀ p : ℕ → ℂ × ℂ,
          (∀ k, (p k).1 ∈ ball 0 (6 * ((2 : ℝ)⁻¹ ^ n)) ∧
            (p k).2 ∈ ball 0 (6 * ((2 : ℝ)⁻¹ ^ n))) →
          ∃ (c : Ω → ℝ) (R : ℝ), 0 < R ∧ R < ε ∧ (∀ᵐ ω ∂P, 0 < c ω) ∧
            ∃ F : (LocalZeroMeanTest (ball 0 ε) → ℝ) → Measure ℂ × (ℕ → ℝ≥0∞),
              Measurable F ∧
              (∀ᵐ ω ∂P, F (localModConstPairings α hC (ball 0 ε) ω) =
                (normalizedRestriction (μ ω) (ball 0 R), fun k =>
                  internalMetric (fun x y => c ω * D ω x y)
                    (ball 0 (6 * ((2 : ℝ)⁻¹ ^ n))) (p k).1 (p k).2)) ∧
              ∀ g : ℂ → ℝ, IsTestFunction univ g →
                (∀ᵐ ω ∂P, (F (localModConstPairings α
                  (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω)).1 =
                  normalizedRestriction ((μ ω).withDensity
                    (fun x => ENNReal.ofReal (Real.exp (γ * g x)))) (ball 0 R)) ∧
                P.map (F ∘ localModConstPairings α
                  (fun ω => addFunPairing (hC ω) g) (ball 0 ε)) ≪
                  P.map (F ∘ localModConstPairings α hC (ball 0 ε)) ∧
                P.map (F ∘ localModConstPairings α hC (ball 0 ε)) ≪
                  P.map (F ∘ localModConstPairings α
                    (fun ω => addFunPairing (hC ω) g) (ball 0 ε))) := by
  obtain ⟨ρ, N, z, hρ, hcriterion⟩ :=
    h.exists_dyadic_locality_criterion_of_positive_diameter_moments hAff 𝔇 h𝔇 hD
      hmetric hξ hα hαQ β hβ
  refine ⟨ρ, N, z, hρ, ?_⟩
  intro hmom ε hε
  obtain ⟨K, hK⟩ := hcriterion hmom ε hε
  refine ⟨K, ?_⟩
  intro n hn p hp
  obtain ⟨c, G, hc, hG, hGeq⟩ := hK n hn
  obtain ⟨R, hR, F, hFm, hFbase, hFshift⟩ :=
    h.exists_joint_shifted_measure_metric_decoder hμ hfull hε c G hG hGeq p hp
  exact ⟨c, R, hR.1, hR.2, hc, F, hFm, hFbase, hFshift⟩



end HarmonicBalls
