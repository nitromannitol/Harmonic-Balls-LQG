import HarmonicBalls.Proofs.Sec11.ShiftedNormalizedMeasureBetween
import HarmonicBalls.Proofs.Sec11.JointContinuousBaseMetricShift

/-! # Joint metric-measure shift decoder on an enclosing ball

The smooth-shift decoding uses Leonardo Bonanno's LatticeProb formalization. -/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped ENNReal
namespace HarmonicBalls

theorem IsWholePlaneGFF.exists_joint_measure_centered_baseMetric_shift_decoder_between
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α a ε : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hfull : ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ ω U)
    (ha : 0 ≤ a) (haε : a < ε) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (ψ : ℂ → ℝ)
    (hψ : IsTestFunction univ ψ) (hψint : ∫ x, ψ x = 1)
    (p : ℕ → ℂ × ℂ) :
    ∃ R ∈ Ioo a ε,
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
  obtain ⟨R, hR, M, hM, _, hMeq⟩ := h.exists_shifted_normalized_measure_decoder_between hμ hfull ha haε
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


theorem IsWholePlaneGFF.exists_joint_measure_continuous_baseMetric_shift_decoder_between
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α a ε : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hfull : ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ ω U)
    (ha : 0 ≤ a) (haε : a < ε) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (ψ : ℂ → ℝ)
    (hψ : IsTestFunction univ ψ) (hψint : ∫ x, ψ x = 1) :
    ∃ R ∈ Ioo a ε,
      ∃ F : (LocalZeroMeanTest univ → ℝ) → Measure ℂ × C(ℂ × ℂ, ℝ), Measurable F ∧
      ∀ g : ℂ → ℝ, IsTestFunction univ g →
        (∀ᵐ ω ∂P,
          (F (localModConstPairings 0 (fun ω => addFunPairing (hC ω) g) univ ω)).1 =
            normalizedRestriction ((μ ω).withDensity
              (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R) ∧
          ∀ x y, (F (localModConstPairings 0
              (fun ω => addFunPairing (hC ω) g) univ ω)).2 (x, y) =
            Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z))) *
              (weylScaling (𝔇 (hC ω)) ξ g x y).toReal) ∧
        P.map (F ∘ localModConstPairings 0
          (fun ω => addFunPairing (hC ω) g) univ) ≪
          P.map (F ∘ localModConstPairings 0 hC univ) ∧
        P.map (F ∘ localModConstPairings 0 hC univ) ≪
          P.map (F ∘ localModConstPairings 0
            (fun ω => addFunPairing (hC ω) g) univ) := by
  let d : ℕ → ℂ × ℂ := TopologicalSpace.denseSeq (ℂ × ℂ)
  let e : C(ℂ × ℂ, ℝ) → ℕ → ℝ := fun D n => D (d n)
  have he : Measurable e := measurable_pi_iff.mpr fun n =>
    (continuous_eval_const (d n)).measurable
  have hinj : Function.Injective e := by
    intro D D' heq
    apply ContinuousMap.ext
    apply congrFun ((TopologicalSpace.denseRange_denseSeq (ℂ × ℂ)).equalizer
      D.continuous D'.continuous ?_)
    funext n
    exact congrFun heq n
  obtain ⟨decode, hdecode, hdecode_eq⟩ :=
    (he.measurableEmbedding hinj).exists_measurable_extend (g := id) measurable_id
      (fun _ => inferInstance)
  obtain ⟨R, hR, G, hG, hGshift⟩ :=
    h.exists_joint_measure_centered_baseMetric_shift_decoder_between hμ hfull ha haε 𝔇 h𝔇 ψ hψ hψint d
  let K : Measure ℂ × (ℕ → ℝ) → Measure ℂ × C(ℂ × ℂ, ℝ) :=
    fun q => (q.1, decode q.2)
  have hK : Measurable K := measurable_fst.prodMk (hdecode.comp measurable_snd)
  let F := K ∘ G
  have hF : Measurable F := hK.comp hG
  refine ⟨R, hR, F, hF, ?_⟩
  intro g hg
  obtain ⟨hgeom, hf, hb⟩ := hGshift g hg
  have hX : Measurable (localModConstPairings 0 hC univ) := by
    apply measurable_pi_iff.mpr
    intro φ
    change Measurable (fun ω => hC ω φ.1 - 0 * ∫ x, φ.1 x * Real.log ‖x‖)
    exact (h.measurable_pairing φ.1 φ.2.1).sub_const _
  have hY : Measurable (localModConstPairings 0 (fun ω => addFunPairing (hC ω) g) univ) := by
    apply measurable_pi_iff.mpr
    intro φ
    change Measurable (fun ω => (hC ω φ.1 + ∫ x, g x * φ.1 x) -
      0 * ∫ x, φ.1 x * Real.log ‖x‖)
    exact ((h.measurable_pairing φ.1 φ.2.1).add_const _).sub_const _
  have hw := ae_wholePlane_weylScaling_shift P γ ξ hC hcirc 𝔇 h𝔇 h
    (fun _ => g) (fun _ => hg.1.continuous) (fun _ => measurable_const)
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hgeom, hw] with ω heq hw
    let c := Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))
    let H : C(ℂ × ℂ, ℝ) :=
      ⟨fun p => c * 𝔇 (addFunPairing (hC ω) g) p.1 p.2,
        continuous_const.mul hw.2.1.continuous_pair⟩
    have hnonneg (x y : ℂ) : 0 ≤ 𝔇 (addFunPairing (hC ω) g) x y := by
      have ht := hw.2.1.triangle x y x
      rw [hw.2.1.self_eq_zero, hw.2.1.symm y x] at ht
      linarith
    have hval (x y : ℂ) : (weylScaling (𝔇 (hC ω)) ξ g x y).toReal =
        𝔇 (addFunPairing (hC ω) g) x y := by
      rw [← hw.2.2.2.1 x y, ENNReal.toReal_ofReal (hnonneg x y)]
    have he : (G (localModConstPairings 0
        (fun ω => addFunPairing (hC ω) g) univ ω)).2 = e H := by
      funext n
      rw [heq]
      exact congrArg (fun t => c * t) (hval (d n).1 (d n).2)
    constructor
    · exact congrArg Prod.fst heq
    · intro x y
      change decode (G (localModConstPairings 0
        (fun ω => addFunPairing (hC ω) g) univ ω)).2 (x, y) = _
      have hdecodeH : decode (e H) = H := congrFun hdecode_eq H
      rw [he, hdecodeH]
      exact congrArg (fun t => c * t) (hval x y).symm
  · have h := hf.map hK
    rw [Measure.map_map hK (hG.comp hY), Measure.map_map hK (hG.comp hX)] at h
    exact h
  · have h := hb.map hK
    rw [Measure.map_map hK (hG.comp hX), Measure.map_map hK (hG.comp hY)] at h
    exact h


#print axioms IsWholePlaneGFF.exists_joint_measure_continuous_baseMetric_shift_decoder_between
end HarmonicBalls
