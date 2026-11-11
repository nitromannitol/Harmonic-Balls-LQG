import HarmonicBalls.Proofs.Sec11.JointInternalBaseMetricShift
import HarmonicBalls.Steps.Sec11.WeylLocality

/-! # Continuous shifted base-metric decoder

The base metric modulo constants admits one continuous-distance decoder for
all fixed continuous backgrounds. Section 8 uses Leonardo Bonanno's
LatticeProb formalization.
-/

noncomputable section

namespace HarmonicBalls

open MeasureTheory Filter Set Metric
open scoped ENNReal

/-- One measurable continuous-distance decoder works for every fixed
continuous background. The exceptional set may depend on the background. -/
theorem IsWholePlaneGFF.exists_continuous_baseMetric_shift_decoder
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction univ ψ) (hψint : ∫ x, ψ x = 1) :
    ∃ F : (LocalZeroMeanTest univ → ℝ) → C(ℂ × ℂ, ℝ), Measurable F ∧
      ∀ g : ℂ → ℝ, Continuous g → ∀ᵐ ω ∂P, ∀ x y,
        F (localModConstPairings 0 (fun ω => addFunPairing (hC ω) g) univ ω) (x, y) =
          Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z))) *
            (weylScaling (𝔇 (hC ω)) ξ g x y).toReal := by
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
  obtain ⟨G, hG, hGeq⟩ := h.exists_centered_baseMetric_shift_decoder 𝔇 h𝔇 ψ hψ hψint d
  refine ⟨decode ∘ G, hdecode.comp hG, ?_⟩
  intro g hg
  have hw := ae_wholePlane_weylScaling_shift P γ ξ hC hcirc 𝔇 h𝔇 h
    (fun _ => g) (fun _ => hg) (fun _ => measurable_const)
  filter_upwards [hGeq g hg, hw] with ω heq hw x y
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
  have he : G (localModConstPairings 0
      (fun ω => addFunPairing (hC ω) g) univ ω) = e H := by
    funext n
    rw [heq n]
    exact congrArg (fun t => c * t) (hval (d n).1 (d n).2)
  change decode (G (localModConstPairings 0
    (fun ω => addFunPairing (hC ω) g) univ ω)) (x, y) = _
  have hdecodeH : decode (e H) = H := congrFun hdecode_eq H
  rw [he, hdecodeH]
  exact congrArg (fun t => c * t) (hval x y).symm

/-- Countably many internal distances have the same continuous-background
shift decoder, simultaneously in all prescribed endpoints and domains. -/
theorem IsWholePlaneGFF.exists_internal_baseMetric_continuous_shift_decoder
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction univ ψ) (hψint : ∫ x, ψ x = 1)
    (U : ℕ → Set ℂ) (hU : ∀ n, IsOpen (U n)) (p : ℕ → ℂ × ℂ)
    (hp : ∀ n, (p n).1 ∈ U n) :
    ∃ F : (LocalZeroMeanTest univ → ℝ) → ℕ → ℝ≥0∞, Measurable F ∧
      ∀ g : ℂ → ℝ, Continuous g → ∀ᵐ ω ∂P, ∀ n,
        F (localModConstPairings 0 (fun ω => addFunPairing (hC ω) g) univ ω) n =
          ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))) *
            internalMetric (fun x y => (weylScaling (𝔇 (hC ω)) ξ g x y).toReal)
              (U n) (p n).1 (p n).2 := by
  obtain ⟨G, hG, hGeq⟩ := h.exists_continuous_baseMetric_shift_decoder 𝔇 h𝔇 ψ hψ hψint
  obtain ⟨J, hJ, hJeq⟩ := exists_measurable_internalMetric_values_decoder U hU p hp
  refine ⟨J ∘ G, hJ.comp hG, ?_⟩
  intro g hg
  have hw := ae_wholePlane_weylScaling_shift P γ ξ hC hcirc 𝔇 h𝔇 h
    (fun _ => g) (fun _ => hg) (fun _ => measurable_const)
  filter_upwards [hGeq g hg, hw] with ω heq hw n
  let c := Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))
  let D := 𝔇 (addFunPairing (hC ω) g)
  have hc : 0 < c := Real.exp_pos _
  have hval (x y : ℂ) : (weylScaling (𝔇 (hC ω)) ξ g x y).toReal = D x y := by
    have hn : 0 ≤ D x y := by
      have ht := hw.2.1.triangle x y x
      rw [hw.2.1.self_eq_zero, hw.2.1.symm y x] at ht
      linarith
    rw [← hw.2.2.2.1 x y, ENNReal.toReal_ofReal hn]
  have he : (fun x y => G (localModConstPairings 0
      (fun ω => addFunPairing (hC ω) g) univ ω) (x, y)) =
      (fun x y => c * D x y) := by
    funext x y
    rw [heq x y, hval]
  have hmetric : IsEuclideanLengthMetric (fun x y => G (localModConstPairings 0
      (fun ω => addFunPairing (hC ω) g) univ ω) (x, y)) := by
    rw [he]
    exact hw.2.1.const_mul hc
  change J (G (localModConstPairings 0
    (fun ω => addFunPairing (hC ω) g) univ ω)) n = _
  rw [hJeq _ hmetric n, he, internalMetric_const_mul D hc]
  congr 1
  congr 1
  funext x y
  exact (hval x y).symm

/-- A fixed continuous background can be built into the decoder. This is
useful for logarithmic backgrounds after a cutoff away from the origin. -/
theorem IsWholePlaneGFF.exists_internal_backgroundMetric_shift_decoder
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction univ ψ) (hψint : ∫ x, ψ x = 1)
    (f : ℂ → ℝ) (hf : Continuous f)
    (U : ℕ → Set ℂ) (hU : ∀ n, IsOpen (U n)) (p : ℕ → ℂ × ℂ)
    (hp : ∀ n, (p n).1 ∈ U n) :
    ∃ F : (LocalZeroMeanTest univ → ℝ) → ℕ → ℝ≥0∞, Measurable F ∧
      ∀ g : ℂ → ℝ, Continuous g → ∀ᵐ ω ∂P, ∀ n,
        F (localModConstPairings 0 (fun ω => addFunPairing (hC ω) g) univ ω) n =
          ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, (g z + f z) * ψ z)))) *
            internalMetric (fun x y =>
              (weylScaling (𝔇 (hC ω)) ξ (fun z => g z + f z) x y).toReal)
              (U n) (p n).1 (p n).2 := by
  obtain ⟨G, hG, hGeq⟩ := h.exists_internal_baseMetric_continuous_shift_decoder
    𝔇 h𝔇 ψ hψ hψint U hU p hp
  let S : (LocalZeroMeanTest univ → ℝ) → LocalZeroMeanTest univ → ℝ :=
    fun v φ => v φ + ∫ x, f x * φ.1 x
  have hS : Measurable S := by
    apply measurable_pi_iff.mpr
    intro φ
    exact (measurable_pi_apply φ).add_const _
  refine ⟨G ∘ S, hG.comp hS, ?_⟩
  intro g hg
  have heq (ω : Ω) : S (localModConstPairings 0
      (fun ω => addFunPairing (hC ω) g) univ ω) =
      localModConstPairings 0
        (fun ω => addFunPairing (hC ω) (fun z => g z + f z)) univ ω := by
    funext φ
    simp only [S, localModConstPairings, fieldPairing, zero_mul, sub_zero]
    change addFunPairing (addFunPairing (hC ω) g) f φ.1 =
      addFunPairing (hC ω) (fun z => g z + f z) φ.1
    exact addFunPairing_addFunPairing_apply_test (hC ω) hg hf φ.2.1
  filter_upwards [hGeq (fun z => g z + f z) (hg.add hf)] with ω hω n
  change G (S (localModConstPairings 0
    (fun ω => addFunPairing (hC ω) g) univ ω)) n = _
  rw [heq]
  exact hω n

/-- Away from the origin, a logarithmic cutoff decoder represents the
normalized singular internal metric. Its shifted values remain the internal
metric of the continuously shifted cutoff background. -/
theorem IsWholePlaneGFF.exists_internal_singularMetric_cutoff_shift_decoder
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) =
        weylScaling (𝔇 (hC ω)) ξ (fun x => -α * Real.log ‖x‖) u v)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (ψ : ℂ → ℝ) (hψ : IsTestFunction univ ψ) (hψint : ∫ x, ψ x = 1)
    {r : ℝ} (hr : 0 < r) (U : ℕ → Set ℂ) (hU : ∀ n, IsOpen (U n))
    (haway : ∀ n z, z ∈ U n → r ≤ ‖z‖)
    (p : ℕ → ℂ × ℂ) (hp : ∀ n, (p n).1 ∈ U n) :
    let f : ℂ → ℝ := fun z => -α * Real.log (max ‖z‖ r)
    ∃ F : (LocalZeroMeanTest univ → ℝ) → ℕ → ℝ≥0∞, Measurable F ∧
      (∀ᵐ ω ∂P, ∀ n, F (localModConstPairings 0 hC univ ω) n =
        ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, f z * ψ z)))) *
          internalMetric (D ω) (U n) (p n).1 (p n).2) ∧
      ∀ g : ℂ → ℝ, Continuous g → ∀ᵐ ω ∂P, ∀ n,
        F (localModConstPairings 0 (fun ω => addFunPairing (hC ω) g) univ ω) n =
          ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, (g z + f z) * ψ z)))) *
            internalMetric (fun x y =>
              (weylScaling (𝔇 (hC ω)) ξ (fun z => g z + f z) x y).toReal)
              (U n) (p n).1 (p n).2 := by
  let f : ℂ → ℝ := fun z => -α * Real.log (max ‖z‖ r)
  have hf : Continuous f := by
    apply continuous_const.mul
    apply (continuous_norm.max continuous_const).log
    intro z
    exact ne_of_gt (lt_of_lt_of_le hr (le_max_right _ _))
  obtain ⟨F, hF, hFeq⟩ := h.exists_internal_backgroundMetric_shift_decoder
    𝔇 h𝔇 ψ hψ hψint f hf U hU p hp
  have hbase := ae_wholePlane_weylScaling_shift P γ ξ hC hcirc 𝔇 h𝔇 h
    (fun _ => f) (fun _ => hf) (fun _ => measurable_const)
  have hzero : (fun ω => addFunPairing (hC ω) (fun _ => 0)) = hC := by
    funext ω φ
    simp [addFunPairing]
  have hz := hFeq (fun _ => 0) continuous_const
  simp only [hzero, zero_add] at hz
  refine ⟨F, hF, ?_, hFeq⟩
  filter_upwards [hz, hbase, hD, hmetric] with ω hz hb hd hm n
  have hcompare : internalMetric (D ω) (U n) (p n).1 (p n).2 =
      internalMetric (𝔇 (addFunPairing (hC ω) f)) (U n) (p n).1 (p n).2 :=
    hb.1.internalMetric_weylScaling_eq_of_eqOn hm hb.2.1 ξ
      (fun z => -α * Real.log ‖z‖) f (fun u v => (hd u v).2) hb.2.2.2.1
      (hU n) (fun z hz => by simp only [f, max_eq_left (haway n z hz)]) _ _
  have heq : (fun x y => (weylScaling (𝔇 (hC ω)) ξ f x y).toReal) =
      𝔇 (addFunPairing (hC ω) f) := by
    funext x y
    have hn : 0 ≤ 𝔇 (addFunPairing (hC ω) f) x y := by
      have ht := hb.2.1.triangle x y x
      rw [hb.2.1.self_eq_zero, hb.2.1.symm y x] at ht
      linarith
    rw [← hb.2.2.2.1 x y, ENNReal.toReal_ofReal hn]
  rw [hz n, heq, ← hcompare]




end HarmonicBalls
