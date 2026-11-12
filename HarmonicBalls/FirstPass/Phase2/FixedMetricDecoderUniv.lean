import HarmonicBalls.FirstPass.Phase2.FixedMetricDecoderDerived
import HarmonicBalls.FirstPass.S11aj.Mixture

/-!
# Fixed-metric normalized measurable decoder, common to all sample spaces

Target: `LocalLQGMetricNormalizedMeasurableFixedMetricFrozen` (`FirstPass/S11r/Frozen.lean:89`), with no hypothesis.

`localLQGMetricNormalizedMeasurableFixedMetric_of_univPoint` (`FirstPass/Phase2/FixedMetricDecoderDerived.lean`) reduces
it to a point decoder `Dq` of the mean-zero ball observations that is valid for every whole-plane GFF on every
probability space. On one sample space such a decoder is `fmd_factor_point` (locality of the metric, constant Weyl
scaling and measurable factorization). Here the decoder of one reference sample space is shown to serve every other one.

The argument is a mixture of sample spaces. Put a reference whole-plane GFF on `Ω₁` and an arbitrary one on `Ω₂`
side by side on `Ω₁ ⊕ Ω₂`, with the half-and-half mixture law; this is again a whole-plane GFF. Its own point decoder
`D₃` agrees almost surely with the reference decoder on the `Ω₁` branch, so the two decoders agree on a measurable set
of observations of full mass for the law of the mean-zero ball observations. This law is the same for every whole-plane
GFF, so the two decoders also agree almost surely on the `Ω₂` branch, where `D₃` is a valid decoder. No measurability of
the internal metric in the field is needed. When no whole-plane GFF lives in the universe, the statement is vacuous.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric ProbabilityTheory Filter
open scoped ENNReal

universe u

section MixtureSum

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- The half-and-half mixture `½ P.map inl + ½ P'.map inr` of two laws on the disjoint union `Ω ⊕ Ω'`. -/
noncomputable def mixMeasureSum (P : Measure Ω) (P' : Measure Ω') : Measure (Ω ⊕ Ω') :=
  (2⁻¹ : ℝ≥0∞) • P.map Sum.inl + (2⁻¹ : ℝ≥0∞) • P'.map Sum.inr

theorem isProbabilityMeasure_mixMeasureSum (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P'] : IsProbabilityMeasure (mixMeasureSum P P') := by
  constructor
  simp only [mixMeasureSum, Measure.add_apply, Measure.smul_apply,
    Measure.map_apply measurable_inl MeasurableSet.univ, Measure.map_apply measurable_inr MeasurableSet.univ,
    preimage_univ, measure_univ, smul_eq_mul, mul_one]
  exact ENNReal.inv_two_add_inv_two

/-- Almost sure properties of the mixture are the almost sure properties of the two branches. -/
theorem ae_mixMeasureSum_iff {P : Measure Ω} {P' : Measure Ω'} (p : Ω ⊕ Ω' → Prop) :
    (∀ᵐ x ∂mixMeasureSum P P', p x) ↔ (∀ᵐ ω ∂P, p (Sum.inl ω)) ∧ (∀ᵐ ω ∂P', p (Sum.inr ω)) := by
  have h2 : (2⁻¹ : ℝ≥0∞) ≠ 0 := by simp
  have eI : MeasurableEmbedding (Sum.inl : Ω → Ω ⊕ Ω') :=
    ⟨Sum.inl_injective, measurable_inl, fun _ hs => measurableSet_inl_image.2 hs⟩
  have eR : MeasurableEmbedding (Sum.inr : Ω' → Ω ⊕ Ω') :=
    ⟨Sum.inr_injective, measurable_inr, fun _ hs => measurableSet_inr_image.2 hs⟩
  rw [mixMeasureSum, ae_add_measure_iff, Measure.ae_ennreal_smul_measure_iff h2,
    Measure.ae_ennreal_smul_measure_iff h2, eI.ae_map_iff, eR.ae_map_iff]

/-- The mixture of two whole-plane GFF models on two sample spaces is a whole-plane GFF model on their disjoint
union. -/
theorem isWholePlaneGFF_mixMeasureSum {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {hCs : Ω' → (ℂ → ℝ) → ℝ}
    {hcirc_s : Ω' → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc) (hh' : IsWholePlaneGFF P' hCs hcirc_s) :
    IsWholePlaneGFF (mixMeasureSum P P') (Sum.elim hC hCs) (Sum.elim hcirc hcirc_s) := by
  have := isProbabilityMeasure_mixMeasureSum P P'
  have hpair : ∀ φ, IsTestFunction Set.univ φ → Measurable fun x => Sum.elim hC hCs x φ := by
    intro φ hφ
    have e : (fun x => Sum.elim hC hCs x φ) =
        Sum.elim (fun ω => hC ω φ) (fun ω => hCs ω φ) := by
      funext x; cases x <;> rfl
    rw [e]
    exact Measurable.sumElim (hh.measurable_pairing φ hφ) (hh'.measurable_pairing φ hφ)
  have hcirc_m : ∀ r z, 0 < r → Measurable fun x => Sum.elim hcirc hcirc_s x r z := by
    intro r z hr
    have e : (fun x => Sum.elim hcirc hcirc_s x r z) =
        Sum.elim (fun ω => hcirc ω r z) (fun ω => hcirc_s ω r z) := by
      funext x; cases x <;> rfl
    rw [e]
    exact Measurable.sumElim (hh.measurable_circle r z hr) (hh'.measurable_circle r z hr)
  have hcont : ∀ᵐ x ∂mixMeasureSum P P',
      ContinuousOn (fun p : ℝ × ℂ => Sum.elim hcirc hcirc_s x p.1 p.2) (Ioi 0 ×ˢ univ) := by
    rw [ae_mixMeasureSum_iff]
    exact ⟨hh.ae_continuousOn_circle, hh'.ae_continuousOn_circle⟩
  have hZc : Measurable fun x (o : GFFObservable.Admissible) =>
      o.1.eval (Sum.elim hC hCs x) (Sum.elim hcirc hcirc_s x) :=
    measurable_pi_iff.2 fun o => S11aj.measurable_obs_of hpair hcirc_m o
  have hlaw : (mixMeasureSum P P').map (fun x (o : GFFObservable.Admissible) =>
      o.1.eval (Sum.elim hC hCs x) (Sum.elim hcirc hcirc_s x)) =
      P.map (fun ω (o : GFFObservable.Admissible) => o.1.eval (hC ω) (hcirc ω)) := by
    have hZ' := S11aj.observable_map_eq hh hh'
    unfold mixMeasureSum
    rw [Measure.map_add _ _ hZc, Measure.map_smul _ hZc.aemeasurable, Measure.map_smul _ hZc.aemeasurable,
      Measure.map_map hZc measurable_inl, Measure.map_map hZc measurable_inr]
    have e1 : (fun x (o : GFFObservable.Admissible) => o.1.eval (Sum.elim hC hCs x) (Sum.elim hcirc hcirc_s x)) ∘
        Sum.inl = fun ω (o : GFFObservable.Admissible) => o.1.eval (hC ω) (hcirc ω) := rfl
    have e2 : (fun x (o : GFFObservable.Admissible) => o.1.eval (Sum.elim hC hCs x) (Sum.elim hcirc hcirc_s x)) ∘
        Sum.inr = fun ω (o : GFFObservable.Admissible) => o.1.eval (hCs ω) (hcirc_s ω) := rfl
    rw [e1, e2, hZ', ← add_smul, ENNReal.inv_two_add_inv_two, one_smul]
  exact S11aj.isWholePlaneGFF_of_observable_map hh hlaw hpair hcirc_m hcont

end MixtureSum

/-- The restriction of the vector of admissible observables to the pairings of `h = h^ℂ` (insertion zero) with the
mean-zero test functions supported in the ball `B_r(c)`. -/
noncomputable def meanZeroBallRestrict (c : ℂ) (r : ℝ) :
    (GFFObservable.Admissible → ℝ) → {φ : ℂ → ℝ // IsTestFunction (ball c r) φ ∧ ∫ x, φ x = 0} → ℝ :=
  fun y φ => y ⟨GFFObservable.pairing φ.1, fmd_univ_of_ball φ.2.1⟩ - 0 * ∫ x, φ.1 x * Real.log ‖x‖

theorem measurable_meanZeroBallRestrict (c : ℂ) (r : ℝ) : Measurable (meanZeroBallRestrict c r) :=
  measurable_pi_iff.2 fun _ => (measurable_pi_apply _).sub_const _

/-- The mean-zero ball observations are the restriction of the vector of admissible observables. -/
theorem localMeanZeroObs_eq_restrict {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (c : ℂ) (r : ℝ) :
    (fun ω => localMeanZeroObs 0 (ball c r) (hC ω)) =
      meanZeroBallRestrict c r ∘ fun ω (o : GFFObservable.Admissible) => o.1.eval (hC ω) (hcirc ω) :=
  rfl

/-- The mean-zero ball observations of a whole-plane GFF are measurable. -/
theorem measurable_localMeanZeroObs {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc) (c : ℂ) (r : ℝ) :
    Measurable fun ω => localMeanZeroObs 0 (ball c r) (hC ω) := by
  rw [localMeanZeroObs_eq_restrict hC hcirc c r]
  exact (measurable_meanZeroBallRestrict c r).comp
    (measurable_pi_iff.2 fun o => S11aj.measurable_obs_of hh.measurable_pairing hh.measurable_circle o)

/-- **Law of the mean-zero ball observations.** Two whole-plane GFF models, on any two sample spaces, have the same
law of the pairings with the mean-zero test functions supported in a ball. -/
theorem map_localMeanZeroObs_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
    {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P'] {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (hh' : IsWholePlaneGFF P' hC' hcirc') (c : ℂ) (r : ℝ) :
    P.map (fun ω => localMeanZeroObs 0 (ball c r) (hC ω)) =
      P'.map (fun ω => localMeanZeroObs 0 (ball c r) (hC' ω)) := by
  have hZ : Measurable fun ω (o : GFFObservable.Admissible) => o.1.eval (hC ω) (hcirc ω) :=
    measurable_pi_iff.2 fun o => S11aj.measurable_obs_of hh.measurable_pairing hh.measurable_circle o
  have hZ' : Measurable fun ω (o : GFFObservable.Admissible) => o.1.eval (hC' ω) (hcirc' ω) :=
    measurable_pi_iff.2 fun o => S11aj.measurable_obs_of hh'.measurable_pairing hh'.measurable_circle o
  rw [localMeanZeroObs_eq_restrict hC hcirc c r, localMeanZeroObs_eq_restrict hC' hcirc' c r,
    ← Measure.map_map (measurable_meanZeroBallRestrict c r) hZ,
    ← Measure.map_map (measurable_meanZeroBallRestrict c r) hZ', S11aj.observable_map_eq hh hh']

/-- **Point decoder common to all sample spaces.** For a fixed LQG metric `𝔇`, a unit-mass test function `ρ` of the
ball `B_r(c)` and a point `q` of `B_r(c) × B_r(c)`, there is one measurable functional `Dq` of the mean-zero ball
observations such that, for every whole-plane GFF on every probability space in `Type u`, almost surely
`Dq (obs_B h) = e^{-ξ ⟨h, ρ⟩} D_h(q.1, q.2; B)`. This is the hypothesis `hUnivPt` of
`localLQGMetricNormalizedMeasurableFixedMetric_of_univPoint`, stated verbatim. -/
theorem localLQGMetricNormalizedMeasurableFixedMetric_univPoint :
    ∀ (γ ξ : ℝ) (c : ℂ) (r : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (ρ : ℂ → ℝ),
      0 < γ → γ < 2 → 0 < r → (0 : ℂ) ∉ closedBall c r → IsLQGMetric γ ξ 𝔇 →
      IsTestFunction (ball c r) ρ → ∫ x, ρ x = 1 → ∀ q : ℂ × ℂ, q ∈ ball c r ×ˢ ball c r →
      ∃ Dq : ({φ : ℂ → ℝ // IsTestFunction (ball c r) φ ∧ ∫ x, φ x = 0} → ℝ) → ℝ, Measurable Dq ∧
        ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
          ∀ᵐ ω ∂P, Dq (localMeanZeroObs 0 (ball c r) (hC ω)) =
            Real.exp (ξ * (-(hC ω ρ))) * (internalMetric (𝔇 (hC ω)) (ball c r) q.1 q.2).toReal := by
  intro γ ξ c r 𝔇 ρ _ _ _ _ hLQG hρ hρint q hq
  by_cases hex : ∃ (Ω₁ : Type u) (_ : MeasurableSpace Ω₁) (P₁ : Measure Ω₁) (hC₁ : Ω₁ → (ℂ → ℝ) → ℝ)
      (hcirc₁ : Ω₁ → ℝ → ℂ → ℝ), IsProbabilityMeasure P₁ ∧ IsWholePlaneGFF P₁ hC₁ hcirc₁
  · obtain ⟨Ω₁, m₁, P₁, hC₁, hcirc₁, hP₁, hW₁⟩ := hex
    obtain ⟨Dq, hDqm, hDq⟩ := fmd_factor_point hW₁ hLQG hρ hρint q hq
    refine ⟨Dq, hDqm, ?_⟩
    intro Ω₂ m₂ P₂ hP₂ hC₂ hcirc₂ hW₂
    have hW₃ := isWholePlaneGFF_mixMeasureSum hW₁ hW₂
    obtain ⟨D₃, hD₃m, hD₃⟩ := fmd_factor_point hW₃ hLQG hρ hρint q hq
    obtain ⟨h1, h2⟩ := (ae_mixMeasureSum_iff _).1 hD₃
    have hB : MeasurableSet {y | D₃ y = Dq y} := measurableSet_eq_fun hD₃m hDqm
    have hB1 : ∀ᵐ ω ∂P₁, localMeanZeroObs 0 (ball c r) (hC₁ ω) ∈ {y | D₃ y = Dq y} := by
      filter_upwards [h1, hDq] with ω h h'
      exact h.trans h'.symm
    have hmap1 := (ae_map_iff (measurable_localMeanZeroObs hW₁ c r).aemeasurable hB).2 hB1
    rw [map_localMeanZeroObs_eq hW₁ hW₂ c r] at hmap1
    have hB2 := (ae_map_iff (measurable_localMeanZeroObs hW₂ c r).aemeasurable hB).1 hmap1
    filter_upwards [hB2, h2] with ω hb h
    exact hb.symm.trans h
  · refine ⟨0, measurable_const, ?_⟩
    intro Ω m P hP hC hcirc hW
    exact (hex ⟨Ω, m, P, hC, hcirc, hP, hW⟩).elim

/-- **The fixed-metric normalized measurable decoder, derived.** `LocalLQGMetricNormalizedMeasurableFixedMetricFrozen`
holds in every universe, with no hypothesis: `localLQGMetricNormalizedMeasurableFixedMetric_of_univPoint` with the
common point decoder `localLQGMetricNormalizedMeasurableFixedMetric_univPoint`. -/
theorem localLQGMetricNormalizedMeasurableFixedMetric_derived :
    LocalLQGMetricNormalizedMeasurableFixedMetricFrozen.{u} :=
  localLQGMetricNormalizedMeasurableFixedMetric_of_univPoint
    localLQGMetricNormalizedMeasurableFixedMetric_univPoint

end HarmonicBalls
