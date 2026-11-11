import HarmonicBalls.Proofs.Sec11.JointCenteredBaseMetricShift
import HarmonicBalls.Steps.Sec11.ProperMetricDyadic
import HarmonicBalls.Steps.Sec11.CountableClearanceChains

/-! # Continuous joint base-metric observations under shifts

The field modulo constants determines a continuous version of the normalized
whole-plane base metric jointly with the normalized singular measure. The
Cameron–Martin argument uses Leonardo Bonanno's LatticeProb formalization.
-/

noncomputable section

namespace HarmonicBalls

open MeasureTheory Filter Set Metric
open scoped ENNReal

/-- A continuous-distance version of the joint measure and base-metric decoder.
For each fixed smooth shift, its metric values are the normalized Weyl-scaled
base metric and its law is equivalent to the unshifted law. -/
theorem IsWholePlaneGFF.exists_joint_measure_continuous_baseMetric_shift_decoder
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α ε : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hfull : ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ ω U)
    (hε : 0 < ε) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (ψ : ℂ → ℝ)
    (hψ : IsTestFunction univ ψ) (hψint : ∫ x, ψ x = 1) :
    ∃ R ∈ Ioo (0 : ℝ) ε,
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
    h.exists_joint_measure_centered_baseMetric_shift_decoder hμ hfull hε 𝔇 h𝔇 ψ hψ hψint d
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


end HarmonicBalls
