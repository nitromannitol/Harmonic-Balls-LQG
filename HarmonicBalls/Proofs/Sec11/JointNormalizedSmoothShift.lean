import HarmonicBalls.Proofs.Sec11.PinchNormalizedLQGMass
import HarmonicBalls.Proofs.Sec11.SmoothShiftModConstObservable
import HarmonicBalls.Proofs.Sec11.DyadicLocalityPositiveMoments

/-! # Joint normalized metric and mass observables under smooth shifts

The normalized local LQG masses and the local metric version are decoded
jointly from the same field modulo constants. The imported Cameron–Martin
argument uses Leonardo Bonanno's LatticeProb formalization. The geometric
identification of the shifted decoder is a separate question.
-/

noncomputable section

namespace HarmonicBalls

open MeasureTheory Filter Set Metric
open scoped ENNReal

/-- A countable collection of normalized local metric distances and LQG
masses has a common field decoder. Its law is equivalent to the law obtained
by translating the field pairings by a smooth function. The local metric
version is an explicit hypothesis; for singular metrics it can be supplied
by the puncture-removal and diameter-moment results. -/
theorem IsWholePlaneGFF.exists_joint_normalized_smooth_shift_decoder
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hfull : ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ ω U)
    {ε : ℝ} (hε : 0 < ε) {V : Set ℂ}
    (c : Ω → ℝ) (G : Ω → ℂ → ℂ → ℝ≥0∞)
    (hG : ∀ x y, Measurable[Section6.fieldSigmaAlgebraModConst α hC (ball 0 ε)]
      (fun ω => G ω x y))
    (hGeq : ∀ᵐ ω ∂P, ∀ x ∈ V, ∀ y ∈ V,
      internalMetric (fun x y => c ω * D ω x y) V x y = G ω x y)
    (p : ℕ → ℂ × ℂ) (hp : ∀ n, (p n).1 ∈ V ∧ (p n).2 ∈ V)
    (B : ℕ → Set ℂ) (hB : ∀ n, MeasurableSet (B n))
    {g : ℂ → ℝ} (hg : IsTestFunction univ g) :
    ∃ R ∈ Ioo (0 : ℝ) ε, ∃ ν : Ω → Measure ℂ,
      ∃ F : (LocalZeroMeanTest (ball 0 ε) → ℝ) → ℕ → (ℝ≥0∞ × ℝ≥0∞),
        Measurable F ∧
        (∀ ω n, F (localModConstPairings α hC (ball 0 ε) ω) n =
          (G ω (p n).1 (p n).2, ν ω (B n))) ∧
        (∀ᵐ ω ∂P, ∀ n, B n ⊆ ball 0 R →
          F (localModConstPairings α hC (ball 0 ε) ω) n =
            (internalMetric (fun x y => c ω * D ω x y) V (p n).1 (p n).2,
              ((μ ω (ball 0 R))⁻¹ • μ ω) (B n))) ∧
        P.map (F ∘ localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε)) ≪
          P.map (F ∘ localModConstPairings α hC (ball 0 ε)) ∧
        P.map (F ∘ localModConstPairings α hC (ball 0 ε)) ≪
          P.map (F ∘ localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε)) := by
  obtain ⟨R, hR, ν, hν, hνeq⟩ := h.exists_modConst_normalized_lqg_masses P hμ hfull hε
  let X : Ω → ℕ → (ℝ≥0∞ × ℝ≥0∞) :=
    fun ω n => (G ω (p n).1 (p n).2, ν ω (B n))
  have hX : Measurable[Section6.fieldSigmaAlgebraModConst α hC (ball 0 ε)] X := by
    let : MeasurableSpace Ω := Section6.fieldSigmaAlgebraModConst α hC (ball 0 ε)
    apply measurable_pi_iff.mpr
    intro n
    exact (hG _ _).prodMk ((Measure.measurable_coe (hB n)).comp hν)
  obtain ⟨F, hF, hFeq, _, hforward, hbackward⟩ :=
    h.exists_smooth_shift_modConst_observable hg α (ball 0 ε) X hX
  have hfun : F ∘ localModConstPairings α hC (ball 0 ε) = X := funext hFeq
  refine ⟨R, hR, ν, F, hF, ?_, ?_, ?_, ?_⟩
  · intro ω n
    exact congrFun (hFeq ω) n
  · filter_upwards [hνeq, hGeq] with ω hmass hmetric n hsub
    rw [hFeq]
    dsimp [X]
    have hm := hmass.2.2 _ (hB n) hsub
    simp only [Measure.smul_apply, smul_eq_mul] at hm
    rw [hmetric _ (hp n).1 _ (hp n).2, hm]
  · simpa only [hfun] using hforward
  · simpa only [hfun] using hbackward

/-- Fixed-scale diameter moments supply the singular-metric locality needed
for the joint normalized metric-mass decoder. The affine-invariance input is
staged, and the displayed diameter moments remain explicit. -/
theorem IsWholePlaneGFF.exists_joint_singular_decoder_of_diameter_moments
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hfull : ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ ω U)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) =
        weylScaling (𝔇 (hC ω)) ξ (fun x => -α * Real.log ‖x‖) u v)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (s : ℝ) (hs : 0 ≤ s) (hξ : 0 < ξ) (hα : 0 ≤ α) (hαQ : α < lqgQ γ)
    (β : ℝ) (hβ : 0 < β)
    {ε : ℝ} (hε : 0 < ε) {V : Set ℂ} (hV : IsOpen V)
    (hne : (V \ {0}).Nonempty) (hVU : V ⊆ ball 0 ε)
    (hball : ball (0 : ℂ) (Real.exp (1 - s)) ⊆ V)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction (ball 0 ε) ψ) (hψint : ∫ x, ψ x = 1)
    (p : ℕ → ℂ × ℂ) (hp : ∀ n, (p n).1 ∈ V ∧ (p n).2 ∈ V)
    (B : ℕ → Set ℂ) (hB : ∀ n, MeasurableSet (B n))
    {g : ℂ → ℝ} (hg : IsTestFunction univ g) :
    ∃ (δ : ℝ) (N : ℕ) (z : ℕ → ℂ), 0 < δ ∧
      ((∀ i, i ≤ N → (∫⁻ ω, (⨆ x ∈ closedBall (z i) δ,
        ⨆ y ∈ closedBall (z i) δ,
          internalMetric (𝔇 (hC ω)) (ball (z i) (2 * δ)) x y) ^ β ∂P) ≠ ∞) →
        ∃ (c : Ω → ℝ) (R : ℝ), 0 < R ∧ R < ε ∧ (∀ᵐ ω ∂P, 0 < c ω) ∧
        ∃ F : (LocalZeroMeanTest (ball 0 ε) → ℝ) → ℕ → (ℝ≥0∞ × ℝ≥0∞),
          Measurable F ∧
          (∀ᵐ ω ∂P, ∀ n, B n ⊆ ball 0 R →
            F (localModConstPairings α hC (ball 0 ε) ω) n =
              (internalMetric (fun x y => c ω * D ω x y) V (p n).1 (p n).2,
                ((μ ω (ball 0 R))⁻¹ • μ ω) (B n))) ∧
          P.map (F ∘ localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε)) ≪
            P.map (F ∘ localModConstPairings α hC (ball 0 ε)) ∧
          P.map (F ∘ localModConstPairings α hC (ball 0 ε)) ≪
            P.map (F ∘ localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε))) := by
  have hscale : ∀ᵐ ω ∂P, ∀ x y, ENNReal.ofReal (D ω x y) =
      weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) x y := by
    filter_upwards [hD] with ω hω
    exact fun x y => (hω x y).2
  obtain ⟨δ, N, z, hδ, hremove⟩ :=
    h.exists_puncture_criterion_of_lqgMetric_positive_moments hAff 𝔇 h𝔇 D s α β
      hs hξ hα hαQ hβ V hball hmetric hscale
  refine ⟨δ, N, z, hδ, ?_⟩
  intro hmom
  have hpoint : ∀ᵐ ω ∂P, ∀ x ∈ V \ {0}, ∀ y ∈ V \ {0},
      internalMetric (D ω) (V \ {0}) x y = internalMetric (D ω) V x y := by
    filter_upwards [hremove hmom] with ω hω x hx y hy
    exact hω x y (by simpa using hx.2) (by simpa using hy.2)
  obtain ⟨c, G, hc, hG, hGeq⟩ :=
    h.exists_modConst_internal_singularMetric_of_point_removal 𝔇 h𝔇 hD hmetric
      hV hne hVU ψ hψ hψint hpoint
  obtain ⟨R, hR, ν, F, hF, _, heq, hf, hb⟩ :=
    h.exists_joint_normalized_smooth_shift_decoder hμ hfull hε c G hG hGeq p hp B hB hg
  exact ⟨c, R, hR.1, hR.2, hc, F, hF, heq, hf, hb⟩

#print axioms IsWholePlaneGFF.exists_joint_singular_decoder_of_diameter_moments

#print axioms IsWholePlaneGFF.exists_joint_normalized_smooth_shift_decoder

end HarmonicBalls
