import HarmonicBalls.Proofs.Sec11.JointContinuousBaseMetricShift
import HarmonicBalls.Steps.Sec11.PinchNormalizedLocalEvent

/-! # Internal base-metric distances under smooth shifts

The continuous joint decoder gives countable internal distances on open sets.
The Cameron–Martin argument uses Leonardo Bonanno's LatticeProb formalization.
-/

noncomputable section

namespace HarmonicBalls

open MeasureTheory Filter Set Metric
open scoped ENNReal

/-- One measurable decoder returns all the prescribed internal distances of a
continuous Euclidean length metric. -/
theorem exists_measurable_internalMetric_values_decoder
    (U : ℕ → Set ℂ) (hU : ∀ n, IsOpen (U n)) (p : ℕ → ℂ × ℂ)
    (hp : ∀ n, (p n).1 ∈ U n) :
    ∃ J : C(ℂ × ℂ, ℝ) → ℕ → ℝ≥0∞, Measurable J ∧
      ∀ D : C(ℂ × ℂ, ℝ), IsEuclideanLengthMetric (fun x y => D (x, y)) →
        ∀ n, J D n = internalMetric (fun x y => D (x, y)) (U n) (p n).1 (p n).2 := by
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense ℂ
  let : Countable S := hSc.to_subtype
  let J : C(ℂ × ℂ, ℝ) → ℕ → ℝ≥0∞ := fun D n =>
    denseClearanceChainInf S (U n) (fun x y => D (x, y)) (p n).1 (p n).2
  have hJ : Measurable J := measurable_pi_iff.mpr fun n =>
    measurable_denseClearanceChainInf (p n).1 (p n).2
      (fun x y => (continuous_eval_const (x, y)).measurable)
      (fun D x => D.continuous.comp (continuous_const.prodMk continuous_id))
  refine ⟨J, hJ, ?_⟩
  intro D hD n
  have hnonneg (x y : ℂ) : 0 ≤ D (x, y) := by
    have ht := hD.triangle x y x
    rw [hD.self_eq_zero, hD.symm y x] at ht
    linarith
  exact (hD.internalMetric_eq_denseClearanceChainInf hnonneg hSd (hU n) (hp n)).symm

/-- The normalized singular measure and countably many internal distances of
the normalized base metric have a joint smooth-shift decoder. -/
theorem IsWholePlaneGFF.exists_joint_measure_internal_baseMetric_shift_decoder
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α ε : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hfull : ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ ω U)
    (hε : 0 < ε) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (ψ : ℂ → ℝ)
    (hψ : IsTestFunction univ ψ) (hψint : ∫ x, ψ x = 1)
    (U : ℕ → Set ℂ) (hU : ∀ n, IsOpen (U n)) (p : ℕ → ℂ × ℂ)
    (hp : ∀ n, (p n).1 ∈ U n) :
    ∃ R ∈ Ioo (0 : ℝ) ε,
      ∃ F : (LocalZeroMeanTest univ → ℝ) → Measure ℂ × (ℕ → ℝ≥0∞), Measurable F ∧
      ∀ g : ℂ → ℝ, IsTestFunction univ g →
        (∀ᵐ ω ∂P,
          (F (localModConstPairings 0 (fun ω => addFunPairing (hC ω) g) univ ω)).1 =
            normalizedRestriction ((μ ω).withDensity
              (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R) ∧
          ∀ n, (F (localModConstPairings 0
              (fun ω => addFunPairing (hC ω) g) univ ω)).2 n =
            ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))) *
              internalMetric (fun x y => (weylScaling (𝔇 (hC ω)) ξ g x y).toReal)
                (U n) (p n).1 (p n).2) ∧
        P.map (F ∘ localModConstPairings 0
          (fun ω => addFunPairing (hC ω) g) univ) ≪
          P.map (F ∘ localModConstPairings 0 hC univ) ∧
        P.map (F ∘ localModConstPairings 0 hC univ) ≪
          P.map (F ∘ localModConstPairings 0
            (fun ω => addFunPairing (hC ω) g) univ) := by
  obtain ⟨R, hR, G, hG, hGshift⟩ :=
    h.exists_joint_measure_continuous_baseMetric_shift_decoder hμ hfull hε 𝔇 h𝔇 ψ hψ hψint
  obtain ⟨J, hJ, hJeq⟩ := exists_measurable_internalMetric_values_decoder U hU p hp
  let K : Measure ℂ × C(ℂ × ℂ, ℝ) → Measure ℂ × (ℕ → ℝ≥0∞) :=
    fun q => (q.1, J q.2)
  have hK : Measurable K := measurable_fst.prodMk (hJ.comp measurable_snd)
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
    let D := 𝔇 (addFunPairing (hC ω) g)
    have hc : 0 < c := Real.exp_pos _
    have hval (x y : ℂ) : (weylScaling (𝔇 (hC ω)) ξ g x y).toReal = D x y := by
      have hn : 0 ≤ D x y := by
        have ht := hw.2.1.triangle x y x
        rw [hw.2.1.self_eq_zero, hw.2.1.symm y x] at ht
        linarith
      rw [← hw.2.2.2.1 x y, ENNReal.toReal_ofReal hn]
    have he : (fun x y => (G (localModConstPairings 0
        (fun ω => addFunPairing (hC ω) g) univ ω)).2 (x, y)) =
        (fun x y => c * D x y) := by
      funext x y
      rw [heq.2 x y, hval]
    have hmetric : IsEuclideanLengthMetric (fun x y => (G (localModConstPairings 0
        (fun ω => addFunPairing (hC ω) g) univ ω)).2 (x, y)) := by
      rw [he]
      exact hw.2.1.const_mul hc
    constructor
    · exact heq.1
    · intro n
      change J (G (localModConstPairings 0
        (fun ω => addFunPairing (hC ω) g) univ ω)).2 n = _
      rw [hJeq _ hmetric n, he, internalMetric_const_mul D hc]
      congr 1
      congr 1
      funext x y
      exact (hval x y).symm
  · have hh := hf.map hK
    rw [Measure.map_map hK (hG.comp hY), Measure.map_map hK (hG.comp hX)] at hh
    exact hh
  · have hh := hb.map hK
    rw [Measure.map_map hK (hG.comp hX), Measure.map_map hK (hG.comp hY)] at hh
    exact hh

#print axioms exists_measurable_internalMetric_values_decoder
#print axioms IsWholePlaneGFF.exists_joint_measure_internal_baseMetric_shift_decoder

end HarmonicBalls
