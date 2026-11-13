import HarmonicBalls.FirstPass.Phase2.CanonicalMetricIdent
import HarmonicBalls.FirstPass.Phase2.CanonicalMeasureKernelSupport
import HarmonicBalls.FirstPass.Phase2.AlphaCanonLaw
import HarmonicBalls.FirstPass.Phase2.CanonicalDecodersCanonXi
import HarmonicBalls.Proofs.GFF.LQGMetricExistence
import LatticeProb.Bonanno.LQGMetric.Papers.LM.C1_8Len
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.StrongWeak
import LatticeProb.LQG.ContMetricLength2

/-!
# The measurable canonical decoders at the canonical exponent

For `γ ∈ (0, 2)` and `α₀ < Q`, this file assembles the canonical-exponent form of the measurable canonical decoder
existence, `LQGCanonicalDecodersMeasurableExistCanonXiStmt` (`Phase2/CanonicalDecodersCanonXi.lean`), from the
identification `lqgXi γ = γ / d_γ` of the canonical exponent with the Weyl exponent of the γ-LQG metric of
Gwynne-Miller 2021, Theorem 1.2:

* the measure half is the canonical measure kernel with its full-support set
  (`CanonicalMeasureKernel.exists_canonicalMeasureKernel_fullSupport`);
* the metric half is the canonical metric decoder of a reference γ-LQG metric (`canonMetricDecoder`,
  `ae_eq_mul_canonMetricDecoder`, `Phase2/CanonicalMetricIdent.lean`);
* the good set of the metric decoder: on every whole-plane GFF model the decoder at the canonical field is almost surely
  a positive multiple of the LQG metric, hence a length metric (`ae_isLength_canonMetricDecoderCM`). The set of
  continuous length metrics is universally measurable (analytic, by Lusin's theorem: `c18_uMeasurableSet_isLength`),
  so it contains a measurable set of full measure for the law of the decoder under one model; its preimage is a
  measurable set of canonical fields which contains the canonical field almost surely under that model, hence under
  every model, since the law of the canonical field does not depend on the model
  (`ae_alphaCanon_mem_of_isWholePlaneGFF`).
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Set Filter
open HarmonicBalls.DecoderInputsDerived

/-- The canonical metric decoder as a continuous metric (`canonMetricDecoder` is its underlying function). -/
noncomputable def canonMetricDecoderCM (𝔇₀ : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (α₀ : ℝ) (L : S11n.CanonSpace) :
    LQGMetric.ContMetric :=
  contMetricOfSample fun n => (canonSingularLimsup 𝔇₀ α₀ L (TopologicalSpace.denseSeq (ℂ × ℂ) n).1
    (TopologicalSpace.denseSeq (ℂ × ℂ) n).2).toReal

theorem canonMetricDecoder_eq_coe (𝔇₀ : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (α₀ : ℝ) (L : S11n.CanonSpace) :
    canonMetricDecoder 𝔇₀ α₀ L = (canonMetricDecoderCM 𝔇₀ α₀ L).1 := rfl

theorem measurable_canonMetricDecoderCM {γ ξ : ℝ} {𝔇₀ : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇₀ : IsLQGMetric γ ξ 𝔇₀)
    (α₀ : ℝ) : Measurable (canonMetricDecoderCM 𝔇₀ α₀) :=
  measurable_contMetricOfSample.comp
    (measurable_pi_iff.2 fun _ => (measurable_canonSingularLimsup h𝔇₀ α₀ _ _).ennreal_toReal)

/-- **The canonical metric decoder is almost surely a length metric.** On every whole-plane GFF model, the LQG metric
of `h^ℂ - α₀ log |·|` built from the reference metric `𝔇₀` is almost surely a Euclidean length metric, and the decoder at
the canonical field is almost surely its rescaling by a positive factor (`ae_eq_mul_canonMetricDecoder`). -/
theorem ae_isLength_canonMetricDecoderCM {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {𝔇₀ : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇₀ : IsLQGMetric γ (LQGMetric.xiGamma γ) 𝔇₀)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hW : IsWholePlaneGFF P hC hcirc) :
    ∀ᵐ ω ∂P, (canonMetricDecoderCM 𝔇₀ α₀ (alphaCanon α₀ hC ω)).IsLength := by
  have hreg := ae_weylScaling_singularShift_regular lqgMetricFieldAxiomsUnivFrozen_derived.{0} hW hγ hγ2 hα h𝔇₀
    (f := fun _ => 0) continuous_const
  have hz : ∀ ω, addFunPairing (hC ω) (fun _ => (0 : ℝ)) = hC ω := fun ω => funext fun φ => by simp [addFunPairing]
  let D : Ω → ℂ → ℂ → ℝ := fun ω u v =>
    (weylScaling (𝔇₀ (hC ω)) (LQGMetric.xiGamma γ) (fun z => -α₀ * Real.log ‖z‖) u v).toReal
  have hD : IsLQGMetricOfField P γ (LQGMetric.xiGamma γ) α₀ hC D := by
    refine ⟨𝔇₀, h𝔇₀, ?_⟩
    filter_upwards [hreg] with ω hr u v
    have h1 := hr.1 u v
    rw [hz ω] at h1
    exact ⟨ENNReal.toReal_nonneg, ENNReal.ofReal_toReal h1.ne⟩
  obtain ⟨C, hC0, hae⟩ := ae_eq_mul_canonMetricDecoder hγ hγ2 hα h𝔇₀ hW hD
  filter_upwards [hae, hreg] with ω hω hr
  have hEuc : IsEuclideanLengthMetric (D ω) := by
    have h2 := hr.2.1
    rw [hz ω] at h2
    exact h2
  obtain ⟨d, hd, hdl⟩ :=
    LatticeProb.LQG.exists_contMetric_of_isEuclideanLengthMetric ((LPBridge.isEuclideanLengthMetric_iff _).1 hEuc)
  have hb0 : 0 < C * Real.exp (LQGMetric.xiGamma γ * hC ω unitTest) := mul_pos hC0 (Real.exp_pos _)
  have heq : canonMetricDecoderCM 𝔇₀ α₀ (alphaCanon α₀ hC ω) = d.smulPos _ (inv_pos.2 hb0) := by
    apply Subtype.ext
    ext ⟨u, v⟩
    show canonMetricDecoder 𝔇₀ α₀ (alphaCanon α₀ hC ω) (u, v) =
      (C * Real.exp (LQGMetric.xiGamma γ * hC ω unitTest))⁻¹ * d.1 (u, v)
    rw [hd u v, hω u v, inv_mul_cancel_left₀ hb0.ne']
  rw [heq]
  exact LQGMetric.ContMetric.isLength_smulPos _ hdl

/-- **The good set of the canonical metric decoder** (hCanonX lemma B8, metric half). There is a measurable set of
canonical fields on which the canonical metric decoder is a Euclidean length metric and which contains the canonical
field of every whole-plane GFF model almost surely. -/
theorem exists_measurableSet_isEuclidean_canonMetricDecoder {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) {𝔇₀ : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇₀ : IsLQGMetric γ (LQGMetric.xiGamma γ) 𝔇₀) :
    ∃ G : Set S11n.CanonSpace, MeasurableSet G ∧
      (∀ L ∈ G, IsEuclideanLengthMetric (fun x y => canonMetricDecoder 𝔇₀ α₀ L (x, y))) ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        IsWholePlaneGFF P hC hcirc → ∀ᵐ ω ∂P, alphaCanon α₀ hC ω ∈ G := by
  by_cases hex : ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc
  swap
  · exact ⟨∅, MeasurableSet.empty, fun L hL => hL.elim,
      fun Ω _ P hC hcirc hW => (hex ⟨Ω, _, P, hC, hcirc, hW⟩).elim⟩
  obtain ⟨Ω₀, m₀, P₀, hC₀, hcirc₀, hW₀⟩ := hex
  have := hW₀.isProbabilityMeasure
  have hFm : Measurable fun ω => canonMetricDecoderCM 𝔇₀ α₀ (alphaCanon α₀ hC₀ ω) :=
    (measurable_canonMetricDecoderCM h𝔇₀ α₀).comp (measurable_alphaCanon hW₀ α₀)
  have : IsProbabilityMeasure (P₀.map fun ω => canonMetricDecoderCM 𝔇₀ α₀ (alphaCanon α₀ hC₀ ω)) :=
    (Measure.isProbabilityMeasure_map_iff hFm.aemeasurable).2 inferInstance
  obtain ⟨M, hMS, hM, hMae⟩ :=
    (LQGMetric.LM.c18_uMeasurableSet_isLength
      (P₀.map fun ω => canonMetricDecoderCM 𝔇₀ α₀ (alphaCanon α₀ hC₀ ω)) inferInstance).exists_measurable_subset_ae_eq
  obtain ⟨N, hSN, hN, hN0⟩ := exists_measurable_superset_of_null
    (show (P₀.map fun ω => canonMetricDecoderCM 𝔇₀ α₀ (alphaCanon α₀ hC₀ ω))
      ({d : LQGMetric.ContMetric | d.IsLength} \ M) = 0 from ae_le_set.1 hMae.symm.le)
  have hFM : ∀ᵐ ω ∂P₀, canonMetricDecoderCM 𝔇₀ α₀ (alphaCanon α₀ hC₀ ω) ∈ M := by
    have hN' : ∀ᵐ ω ∂P₀, canonMetricDecoderCM 𝔇₀ α₀ (alphaCanon α₀ hC₀ ω) ∉ N := by
      rw [Measure.map_apply hFm hN] at hN0
      exact measure_eq_zero_iff_ae_notMem.1 hN0
    filter_upwards [ae_isLength_canonMetricDecoderCM hγ hγ2 hα h𝔇₀ hW₀, hN'] with ω h1 h2
    by_contra h3
    exact h2 (hSN ⟨h1, h3⟩)
  refine ⟨canonMetricDecoderCM 𝔇₀ α₀ ⁻¹' M, measurable_canonMetricDecoderCM h𝔇₀ α₀ hM, fun L hL => ?_,
    fun Ω _ P hC hcirc hW => ?_⟩
  · exact (LPBridge.isEuclideanLengthMetric_iff _).2 (LatticeProb.LQG.isEuclideanLengthMetric_of_isLength _ (hMS hL))
  · have := hW.isProbabilityMeasure
    exact ae_alphaCanon_mem_of_isWholePlaneGFF hW₀ hW α₀ (measurable_canonMetricDecoderCM h𝔇₀ α₀ hM) hFM

/-- **The measurable canonical decoders at the canonical exponent**, from the identification of the canonical exponent
`lqgXi γ` with the Weyl exponent `γ / d_γ` of the γ-LQG metric (Gwynne-Miller 2021, Theorem 1.2). The kernel is the
canonical measure kernel, the metric decoder is the canonical metric decoder of a reference γ-LQG metric, and the good set
is the intersection of the full-support set of the kernel with the good set of the metric decoder. -/
theorem lqgCanonicalDecodersMeasurableExistCanonXi_of_dim
    (hDim : ∀ γ : ℝ, 0 < γ → γ < 2 → lqgXi γ = LQGMetric.xiGamma γ) :
    LQGCanonicalDecodersMeasurableExistCanonXiStmt.{0} := by
  intro γ α₀ hγ0 hγ2 hα
  obtain ⟨K, hKs, hKc, hK, hGm, hGsupp, hGae⟩ :=
    CanonicalMeasureKernel.exists_canonicalMeasureKernel_fullSupport.{0} γ α₀ hγ0 hγ2 hα
  obtain ⟨-, 𝔇₀, h𝔇₀⟩ := exists_isLQGMetric hγ0 hγ2
  obtain ⟨Gd, hGdm, hGdE, hGdae⟩ := exists_measurableSet_isEuclidean_canonMetricDecoder hγ0 hγ2 hα h𝔇₀
  refine ⟨K, canonMetricDecoder 𝔇₀ α₀, hKs, hKc, measurable_canonMetricDecoder h𝔇₀ α₀, ?_,
    CanonicalMeasureKernel.fullSupportSet K ∩ Gd, hGm.inter hGdm, ?_, ?_⟩
  · unfold S11n.LQGCanonicalIdentificationStmt
    intro Ω _ P hC hcirc μ D hW hμ hD
    rw [hDim γ hγ0 hγ2] at hD
    obtain ⟨C, hC0, hae⟩ := ae_eq_mul_canonMetricDecoder hγ0 hγ2 hα h𝔇₀ hW hD
    filter_upwards [hK Ω P hC hcirc μ hW hμ, hae] with ω hμω hDω
    obtain ⟨a, ha, hμa⟩ := hμω
    exact ⟨a, C * Real.exp (LQGMetric.xiGamma γ * hC ω unitTest), ha, mul_pos hC0 (Real.exp_pos _), hμa, hDω⟩
  · intro Ω _ P hC hcirc hW
    filter_upwards [hGae Ω P hC hcirc hW, hGdae Ω P hC hcirc hW] with ω h1 h2
    exact ⟨h1, h2⟩
  · intro L hL
    exact ⟨hGsupp L hL.1, hGdE L hL.2⟩

end HarmonicBalls
