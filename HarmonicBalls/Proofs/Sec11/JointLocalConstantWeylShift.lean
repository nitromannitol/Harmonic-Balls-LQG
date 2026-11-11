import HarmonicBalls.Proofs.Sec11.JointShiftedMeasureMetric
import HarmonicBalls.Proofs.Sec11.LocalConstantWeylShift
import HarmonicBalls.Steps.Sec11.SingularWeylBumpInverse

/-! # A joint decoder under a locally constant Weyl shift

The common normalized measure and countable internal-distance decoder has a
geometric interpretation after a shift constant on the observation set. The
imported Cameron–Martin results use Leonardo Bonanno's LatticeProb code.
-/

noncomputable section

namespace HarmonicBalls

open MeasureTheory Set
open scoped ENNReal

/-- A locally constant positive Weyl density leaves the normalized restriction
unchanged as a measure, including when the reference mass is zero or infinite. -/
theorem normalizedRestriction_withDensity_eq_of_constOn
    (μ : Measure ℂ) (γ : ℝ) (g : ℂ → ℝ) {c : ℝ} {U R : Set ℂ}
    (hR : MeasurableSet R) (hRU : R ⊆ U) (hg : ∀ x ∈ U, g x = c) :
    normalizedRestriction (μ.withDensity
      (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) R = normalizedRestriction μ R := by
  ext B hB
  simp only [normalizedRestriction, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply hB]
  have h := normalized_withDensity_apply_of_constantOn (μ := μ)
    (w := fun z => ENNReal.ofReal (Real.exp (γ * g z)))
    (a := ENNReal.ofReal (Real.exp (γ * c))) (U := U) (B := B ∩ R) (R := R)
    (hB.inter hR) hR (inter_subset_right.trans hRU) hRU
    (by intro z hz; rw [hg z hz])
    (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))) ENNReal.ofReal_ne_top
  simpa only [Measure.smul_apply, smul_eq_mul] using h

/-- When a smooth background is constant on the observation set, a joint
field decoder identifies the normalized weighted measure and every rescaled
internal distance of the Weyl-shifted metric. -/
theorem joint_local_decoder_weyl_eq_of_constOn
    {Ω : Type*} (α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (ω : Ω)
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (ξ γ : ℝ)
    (g : ℂ → ℝ) {c : ℝ} {U V R : Set ℂ} (hV : IsOpen V) (hVU : V ⊆ U)
    (hR : MeasurableSet R) (hRU : R ⊆ U) (hg : ∀ x ∈ U, g x = c)
    (hE : IsEuclideanLengthMetric (fun x y => (weylScaling D ξ g x y).toReal))
    (hscale : ∀ x y, ENNReal.ofReal (weylScaling D ξ g x y).toReal =
      weylScaling D ξ g x y) (p : ℕ → ℂ × ℂ) (b : ℝ≥0∞) (μ : Measure ℂ)
    (F : (LocalZeroMeanTest U → ℝ) → Measure ℂ × (ℕ → ℝ≥0∞))
    (hF : F (localModConstPairings α hC U ω) =
      (normalizedRestriction μ R, fun n => b * internalMetric D V (p n).1 (p n).2)) :
    F (localModConstPairings α (fun ω => addFunPairing (hC ω) g) U ω) =
      (normalizedRestriction (μ.withDensity
          (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) R,
        fun n => b * (ENNReal.ofReal (Real.exp (ξ * c)))⁻¹ *
          internalMetric (fun x y => (weylScaling D ξ g x y).toReal) V (p n).1 (p n).2) := by
  rw [localModConstPairings_observable_eq_of_eqOn α hC hg F ω, hF]
  apply Prod.ext
  · exact (normalizedRestriction_withDensity_eq_of_constOn μ γ g hR hRU hg).symm
  · funext n
    dsimp only
    rw [hD.internalMetric_weylScaling_eq_of_constOn ξ g hV
      (fun z hz => hg z (hVU hz)) hE hscale]
    have ha0 : ENNReal.ofReal (Real.exp (ξ * c)) ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
    have hatop : ENNReal.ofReal (Real.exp (ξ * c)) ≠ ∞ := ENNReal.ofReal_ne_top
    symm
    calc
      _ = b * (((ENNReal.ofReal (Real.exp (ξ * c)))⁻¹ *
          ENNReal.ofReal (Real.exp (ξ * c))) * internalMetric D V (p n).1 (p n).2) := by ac_rfl
      _ = _ := by rw [ENNReal.inv_mul_cancel ha0 hatop, one_mul]

/-- A positive real metric normalization can be moved outside every internal
distance in the joint decoder. -/
theorem joint_local_decoder_of_scaled_metric
    {Ω : Type*} (α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (ω : Ω)
    (D : ℂ → ℂ → ℝ) {c : ℝ} (hc : 0 < c) (U V R : Set ℂ)
    (p : ℕ → ℂ × ℂ) (μ : Measure ℂ)
    (F : (LocalZeroMeanTest U → ℝ) → Measure ℂ × (ℕ → ℝ≥0∞))
    (hF : F (localModConstPairings α hC U ω) =
      (normalizedRestriction μ R,
        fun n => internalMetric (fun x y => c * D x y) V (p n).1 (p n).2)) :
    F (localModConstPairings α hC U ω) =
      (normalizedRestriction μ R,
        fun n => ENNReal.ofReal c * internalMetric D V (p n).1 (p n).2) := by
  rw [hF]
  congr 1
  funext n
  exact internalMetric_const_mul D hc V (p n).1 (p n).2

/-- Under the staged singular metric-field axioms, one almost-sure event
identifies a joint local decoder for every nonpositive, compactly supported
continuous shift that is constant on the observation set. -/
theorem ae_joint_local_decoder_weyl_eq_of_constOn
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ ξ α : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (haxioms : LQGMetricFieldAxioms P γ ξ α hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α < lqgQ γ) (hD : IsLQGMetricOfField P γ ξ α hC D) (hξ : 0 ≤ ξ)
    {U V R : Set ℂ} (hV : IsOpen V) (hVU : V ⊆ U)
    (hR : MeasurableSet R) (hRU : R ⊆ U) (p : ℕ → ℂ × ℂ) (b : Ω → ℝ≥0∞)
    (F : (LocalZeroMeanTest U → ℝ) → Measure ℂ × (ℕ → ℝ≥0∞))
    (hF : ∀ᵐ ω ∂P, F (localModConstPairings α hC U ω) =
      (normalizedRestriction (μ ω) R, fun n => b ω * internalMetric (D ω) V (p n).1 (p n).2)) :
    ∀ᵐ ω ∂P, ∀ (g : ℂ → ℝ) (c : ℝ), Continuous g → HasCompactSupport g →
      (∀ z, g z ≤ 0) → (∀ z ∈ U, g z = c) →
      F (localModConstPairings α (fun ω => addFunPairing (hC ω) g) U ω) =
        (normalizedRestriction ((μ ω).withDensity
            (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) R,
          fun n => b ω * (ENNReal.ofReal (Real.exp (ξ * c)))⁻¹ *
            internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
              V (p n).1 (p n).2) := by
  filter_upwards [hF, ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α hC hcirc D
      haxioms hgff hγ hγ₂ hα hD,
    ae_singularField_weylBump_identities_of_metricFieldAxioms P γ ξ α hC hcirc D
      haxioms hgff hγ hγ₂ hα hD hξ,
    ae_singularField_negative_weylScaling_finite P γ ξ α hC hcirc D
      haxioms hgff hγ hγ₂ hα hD hξ] with ω hf hm hw hfinite
  intro g c hg hcomp hneg hconst
  exact joint_local_decoder_weyl_eq_of_constOn α hC ω hm ξ γ g hV hVU hR hRU hconst
    (hw g hg hcomp hneg).1 (fun x y => (hfinite g hneg x y).2) p (b ω) (μ ω) F hf


end HarmonicBalls
