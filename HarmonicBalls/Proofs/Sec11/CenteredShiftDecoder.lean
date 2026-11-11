import HarmonicBalls.Steps.Sec11.CountableCoordinateObservables
import HarmonicBalls.Steps.Sec11.ContinuousFieldShift
import HarmonicBalls.Proofs.Sec11.CanonicalPairingShift

/-! # A common decoder for centered distribution observables

The decoder applies to every field and every deterministic shift. Equality to
reference-shifted fields uses coordinatewise GFF linearity and countable
coordinate dependence. The imported Section 8 work uses Leonardo Bonanno's
LatticeProb formalization.
-/

noncomputable section

namespace HarmonicBalls

open MeasureTheory Filter Set

/-- A distribution-measurable observable of the reference-centered field
has a decoder on the full field modulo constants. -/
theorem exists_centered_distribution_decoder
    {E : Type*} [MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]
    (ψ : ℂ → ℝ) (hψ : IsTestFunction univ ψ) (hψint : ∫ x, ψ x = 1)
    (F : ((ℂ → ℝ) → ℝ) → E) (hF : Measurable[distributionMeasurableSpace] F) :
    ∃ G : (LocalZeroMeanTest univ → ℝ) → E, Measurable G ∧
      ∀ T, G (localModConstPairings 0 id univ T) = F (centeredTestPairing T ψ) := by
  let S := ((ℂ → ℝ) → ℝ)
  let m := Section6.fieldSigmaAlgebraModConst 0 (id : S → S) univ
  have hc : Measurable[m, distributionMeasurableSpace] (fun T : S => centeredTestPairing T ψ) := by
    apply measurable_iff_comap_le.mpr
    have heq : MeasurableSpace.comap (fun T : S => centeredTestPairing T ψ)
        distributionMeasurableSpace = fieldSigmaAlgebra 0
          (fun T : S => centeredTestPairing T ψ) univ := by
      simp [distributionMeasurableSpace, fieldSigmaAlgebra, fieldPairing,
        MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp, Function.comp_def]
    rw [heq]
    exact (fieldSigmaAlgebra_centeredTestPairing_eq_modConst 0 id univ ψ hψ hψint).le
  have hf : Measurable[m] (fun T : S => F (centeredTestPairing T ψ)) := hF.comp hc
  rw [show m = MeasurableSpace.comap (localModConstPairings 0 id univ) inferInstance from
    fieldSigmaAlgebraModConst_eq_comap_localModConstPairings 0 id univ] at hf
  obtain ⟨G, hG, heq⟩ := hf.exists_eq_measurable_comp
  exact ⟨G, hG, fun T => (congrFun heq T).symm⟩

/-- A fixed continuous shift can be decoded after reference centering without
assuming simultaneous linearity of all sample pairings. -/
theorem IsWholePlaneGFF.ae_centered_distribution_decoder_shift
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [StandardBorelSpace E] [Nonempty E] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction univ ψ) (hψint : ∫ x, ψ x = 1)
    (F : ((ℂ → ℝ) → ℝ) → E) (hF : Measurable[distributionMeasurableSpace] F) :
    ∃ G : (LocalZeroMeanTest univ → ℝ) → E, Measurable G ∧
      ∀ (g : ℂ → ℝ), Continuous g → ∀ᵐ ω ∂P,
        G (localModConstPairings 0 (fun ω => addFunPairing (hC ω) g) univ ω) =
        F (addFunPairing (addFunPairing (hC ω) g)
          (fun _ => -(addFunPairing (hC ω) g ψ))) := by
  obtain ⟨G, hG, hGeq⟩ := exists_centered_distribution_decoder ψ hψ hψint F hF
  obtain ⟨H, hH, hHeq⟩ := exists_common_observable_of_distribution_measurable F hF
  refine ⟨G, hG, ?_⟩
  intro g hg
  let X : Ω → GFFObservable.Admissible → ℝ := fun ω o =>
    o.1.eval (centeredTestPairing (addFunPairing (hC ω) g) ψ) (fun _ _ => 0)
  let Y : Ω → GFFObservable.Admissible → ℝ := fun ω o =>
    o.1.eval (addFunPairing (addFunPairing (hC ω) g)
      (fun _ => -(addFunPairing (hC ω) g ψ))) (fun _ _ => 0)
  have hXY (o : GFFObservable.Admissible) : ∀ᵐ ω ∂P, X ω o = Y ω o := by
    rcases o with ⟨o, ho⟩
    cases o with
    | circle r z => exact Filter.Eventually.of_forall (fun _ => rfl)
    | pairing φ =>
      have hφ : IsTestFunction univ φ := ho
      have hiφ : Integrable (fun x => g x * φ x) :=
        (hg.mul hφ.1.continuous).integrable_of_hasCompactSupport hφ.2.1.mul_left
      have hiψ : Integrable (fun x => g x * ψ x) :=
        (hg.mul hψ.1.continuous).integrable_of_hasCompactSupport hψ.2.1.mul_left
      filter_upwards [h.ae_centeredTestPairing_eq hφ hψ] with ω hω
      change centeredTestPairing (addFunPairing (hC ω) g) ψ φ =
        addFunPairing (addFunPairing (hC ω) g)
          (fun _ => -(addFunPairing (hC ω) g ψ)) φ
      simp only [centeredTestPairing, addFunPairing, integral_const_mul]
      have hintegral : (∫ x, g x * (1 * φ x + (-(∫ y, φ y)) * ψ x)) =
          (∫ x, g x * φ x) - (∫ y, φ y) * (∫ x, g x * ψ x) := by
        have heq : (fun x => g x * (1 * φ x + (-(∫ y, φ y)) * ψ x)) =
            (fun x => (g x * φ x) + (-(∫ y, φ y)) * (g x * ψ x)) := by
          funext x
          ring
        rw [heq, integral_add hiφ (hiψ.const_mul _), integral_const_mul]
        ring
      rw [hintegral]
      change centeredTestPairing (hC ω) ψ φ + _ = _
      rw [hω]
      ring
  have heq := ae_eq_measurable_comp_of_coordinatewise_ae_eq X Y hXY H hH
  filter_upwards [heq] with ω heq
  change G (localModConstPairings 0 id univ (addFunPairing (hC ω) g)) = _
  rw [hGeq]
  change H (fun o => o.1.eval (centeredTestPairing
    (addFunPairing (hC ω) g) ψ) (fun _ _ => 0)) =
    H (fun o => o.1.eval (addFunPairing (addFunPairing (hC ω) g)
      (fun _ => -(addFunPairing (hC ω) g ψ))) (fun _ _ => 0)) at heq
  rw [hHeq, hHeq] at heq
  exact heq

/-- Countably many normalized whole-plane metric distances have one field
modulo constants decoder. For each continuous background, it identifies the
Weyl-scaled metric with the reference pairing shifted as well. -/
theorem IsWholePlaneGFF.exists_centered_baseMetric_shift_decoder
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction univ ψ) (hψint : ∫ x, ψ x = 1)
    (p : ℕ → ℂ × ℂ) :
    ∃ G : (LocalZeroMeanTest univ → ℝ) → ℕ → ℝ, Measurable G ∧
      ∀ (g : ℂ → ℝ), Continuous g → ∀ᵐ ω ∂P, ∀ n,
        G (localModConstPairings 0 (fun ω => addFunPairing (hC ω) g) univ ω) n =
          Real.exp (ξ * (-(hC ω ψ + ∫ x, g x * ψ x))) *
          (weylScaling (𝔇 (hC ω)) ξ g (p n).1 (p n).2).toReal := by
  let F : ((ℂ → ℝ) → ℝ) → ℕ → ℝ := fun T n => 𝔇 T (p n).1 (p n).2
  have hF : Measurable[distributionMeasurableSpace] F := by
    let : MeasurableSpace ((ℂ → ℝ) → ℝ) := distributionMeasurableSpace
    exact measurable_pi_iff.mpr fun n => h𝔇.measurable_apply (p n).1 (p n).2
  obtain ⟨G, hG, hGeq⟩ := h.ae_centered_distribution_decoder_shift ψ hψ hψint F hF
  refine ⟨G, hG, ?_⟩
  intro g hg
  let c : Ω → ℝ := fun ω => -(hC ω ψ + ∫ x, g x * ψ x)
  have hc : Measurable c := ((h.measurable_pairing ψ hψ).add_const _).neg
  have hscale := h.ae_metric_background_add_random_constant 𝔇 h𝔇 g hg c hc
  have hw := ae_wholePlane_weylScaling_shift P γ ξ hC hcirc 𝔇 h𝔇 h
    (fun _ => g) (fun _ => hg) (fun _ => measurable_const)
  filter_upwards [hGeq g hg, hscale, hw] with ω he hs hw n
  have hmetric : 0 ≤ 𝔇 (addFunPairing (hC ω) g) (p n).1 (p n).2 := by
    have ht := hw.2.1.triangle (p n).1 (p n).2 (p n).1
    rw [hw.2.1.self_eq_zero, hw.2.1.symm (p n).2 (p n).1] at ht
    linarith
  have heq := congrFun he n
  change G (localModConstPairings 0 (fun ω => addFunPairing (hC ω) g) univ ω) n =
    𝔇 (addFunPairing (addFunPairing (hC ω) g)
      (fun _ => -(addFunPairing (hC ω) g ψ))) (p n).1 (p n).2 at heq
  have hpair : -(addFunPairing (hC ω) g ψ) = c ω := rfl
  rw [hpair, h𝔇.addFunPairing_addFunPairing (hC ω) hg continuous_const, hs] at heq
  rw [← hw.2.2.2.1 (p n).1 (p n).2, ENNReal.toReal_ofReal hmetric]
  exact heq


end HarmonicBalls
