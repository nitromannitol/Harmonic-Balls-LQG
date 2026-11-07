import HarmonicBalls.Proofs.Sec11.AbsolutePairingShiftDecoder
import HarmonicBalls.Proofs.Sec11.AbsoluteLQGMassShiftDecoder
import HarmonicBalls.Proofs.Sec11.CenteredShiftDecoder

/-! # Joint absolute mass and metric decoder

The Section 8 development uses Leonardo Bonanno's
`LatticeProb.Bonanno.LQGMetric.Field.CameronMartin` formalization.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
namespace HarmonicBalls

/-- The absolute mass of a bounded continuity set and countably many absolute
metric distances are decoded jointly from the global field modulo constants.
The identification holds after each continuous pinning-preserving shift. -/
theorem IsWholePlaneGFF.exists_joint_absolute_mass_metric_shift_decoder
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ε α γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (A : Set ℂ) (hA : MeasurableSet A) (hbounded : Bornology.IsBounded A)
    (hbuffer : ∀ n z, z ∈ A → closedBall z (dyadicScale n) ⊆ ball 0 ε)
    (hfront : ∀ᵐ ω ∂P, μ ω (frontier A) = 0)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction univ ψ) (hψint : ∫ x, ψ x = 1)
    (p : ℕ → ℂ × ℂ) :
    ∃ F : (LocalZeroMeanTest univ → ℝ) → ℝ≥0∞ × (ℕ → ℝ), Measurable F ∧
      ∀ g : ℂ → ℝ, Continuous g → Real.circleAverage g 0 1 = 0 →
        ∀ᵐ ω ∂P, F (localModConstPairings 0
          (fun ω => addFunPairing (hC ω) g) univ ω) =
          (((μ ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) A,
            fun n => (weylScaling (𝔇 (hC ω)) ξ g (p n).1 (p n).2).toReal) := by
  obtain ⟨M, hM, hMe⟩ := h.exists_global_shifted_lqgMass_decoder hμ A hA hbounded hbuffer hfront
  obtain ⟨B, hB, hBe⟩ := h.exists_global_absolute_pairing_shift_decoder ψ hψ hψint
  obtain ⟨D, hD, hDe⟩ := h.exists_centered_baseMetric_shift_decoder 𝔇 h𝔇 ψ hψ hψint p
  let Q : (LocalZeroMeanTest univ → ℝ) → LocalZeroMeanTest univ → ℝ :=
    fun v φ => v φ - α * ∫ x, φ.1 x * Real.log ‖x‖
  have hQ : Measurable Q := measurable_pi_iff.mpr fun φ => (measurable_pi_apply φ).sub_const _
  let F : (LocalZeroMeanTest univ → ℝ) → ℝ≥0∞ × (ℕ → ℝ) :=
    fun v => (M (Q v), fun n => Real.exp (ξ * B v) * D v n)
  have hF : Measurable F := by
    apply (hM.comp hQ).prodMk
    apply measurable_pi_iff.mpr
    intro n
    exact ((measurable_const.mul hB).exp).mul ((measurable_pi_apply n).comp hD)
  refine ⟨F, hF, ?_⟩
  intro g hg hpin
  filter_upwards [hMe, hBe, hDe g hg] with ω hm hb hd
  let X := localModConstPairings 0 (fun ω => addFunPairing (hC ω) g) univ ω
  have hQeq : Q X = localModConstPairings α (fun ω => addFunPairing (hC ω) g) univ ω := by
    funext φ
    simp [Q, X, localModConstPairings, fieldPairing]
  apply Prod.ext
  · change M (Q X) = _
    rw [hQeq]
    exact hm g hg hpin
  · funext n
    change Real.exp (ξ * B X) * D X n = _
    rw [hb g hg hpin, hd n, ← mul_assoc, ← Real.exp_add]
    have hz : ξ * (hC ω ψ + ∫ x, g x * ψ x) +
        ξ * (-(hC ω ψ + ∫ x, g x * ψ x)) = 0 := by ring
    rw [hz, Real.exp_zero, one_mul]

#print axioms IsWholePlaneGFF.exists_joint_absolute_mass_metric_shift_decoder

/-- The joint decoder also recovers the whole continuous metric, not merely
its distances at a prescribed countable family of endpoints. -/
theorem IsWholePlaneGFF.exists_joint_absolute_mass_continuous_metric_shift_decoder
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ε α γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (A : Set ℂ) (hA : MeasurableSet A) (hbounded : Bornology.IsBounded A)
    (hbuffer : ∀ n z, z ∈ A → closedBall z (dyadicScale n) ⊆ ball 0 ε)
    (hfront : ∀ᵐ ω ∂P, μ ω (frontier A) = 0)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction univ ψ) (hψint : ∫ x, ψ x = 1) :
    ∃ F : (LocalZeroMeanTest univ → ℝ) → ℝ≥0∞ × C(ℂ × ℂ, ℝ), Measurable F ∧
      ∀ g : ℂ → ℝ, Continuous g → Real.circleAverage g 0 1 = 0 →
        ∀ᵐ ω ∂P,
          (F (localModConstPairings 0 (fun ω => addFunPairing (hC ω) g) univ ω)).1 =
            ((μ ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) A ∧
          ∀ x y, (F (localModConstPairings 0
            (fun ω => addFunPairing (hC ω) g) univ ω)).2 (x,y) =
              𝔇 (addFunPairing (hC ω) g) x y := by
  let d : ℕ → ℂ × ℂ := TopologicalSpace.denseSeq (ℂ × ℂ)
  let e : C(ℂ × ℂ, ℝ) → ℕ → ℝ := fun D n => D (d n)
  have he : Measurable e := measurable_pi_iff.mpr fun n => (continuous_eval_const (d n)).measurable
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
  obtain ⟨G, hG, hGe⟩ := h.exists_joint_absolute_mass_metric_shift_decoder hμ A hA
    hbounded hbuffer hfront 𝔇 h𝔇 ψ hψ hψint d
  let F := fun v => ((G v).1, decode (G v).2)
  have hF : Measurable F := (measurable_fst.comp hG).prodMk (hdecode.comp (measurable_snd.comp hG))
  refine ⟨F, hF, ?_⟩
  intro g hg hpin
  have hw := ae_wholePlane_weylScaling_shift P γ ξ hC hcirc 𝔇 h𝔇 h
    (fun _ => g) (fun _ => hg) (fun _ => measurable_const)
  filter_upwards [hGe g hg hpin, hw] with ω hge hw
  let H : C(ℂ × ℂ, ℝ) :=
    ⟨fun q => 𝔇 (addFunPairing (hC ω) g) q.1 q.2, hw.2.1.continuous_pair⟩
  have hn (x y : ℂ) : 0 ≤ 𝔇 (addFunPairing (hC ω) g) x y := by
    have ht := hw.2.1.triangle x y x
    rw [hw.2.1.self_eq_zero, hw.2.1.symm y x] at ht
    linarith
  have hval (x y : ℂ) : (weylScaling (𝔇 (hC ω)) ξ g x y).toReal =
      𝔇 (addFunPairing (hC ω) g) x y := by
    rw [← hw.2.2.2.1 x y, ENNReal.toReal_ofReal (hn x y)]
  refine ⟨congrArg Prod.fst hge, ?_⟩
  intro x y
  have hvec : (G (localModConstPairings 0
      (fun ω => addFunPairing (hC ω) g) univ ω)).2 = e H := by
    funext n
    have hn' := congrFun (congrArg Prod.snd hge) n
    exact hn'.trans (hval (d n).1 (d n).2)
  change decode (G (localModConstPairings 0
    (fun ω => addFunPairing (hC ω) g) univ ω)).2 (x,y) = _
  have hdecodeH : decode (e H) = H := congrFun hdecode_eq H
  rw [hvec, hdecodeH]
  rfl

#print axioms IsWholePlaneGFF.exists_joint_absolute_mass_continuous_metric_shift_decoder
end HarmonicBalls
