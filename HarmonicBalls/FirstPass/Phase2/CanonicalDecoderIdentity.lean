import HarmonicBalls.FirstPass.Phase2.RootedShiftedNullTransferDerived
import HarmonicBalls.Proposed.LQG
import HarmonicBalls.FirstPass.Phase2.RootedShiftedNullTransferLaw

/-!
# Canonical decoder identity (MQ-lh-29, input (c) of the canonical domination)

The α₀-LQG measure `μ` of the whole-plane GFF `hcirc` is almost surely the decoder of the
canonical profile: `μ ω = decoder canonicalTest γ α₀ (canonicalSel (posPart (hcirc ω)))`.
This is the missing identity (c) of the canonical rooted domination (`ShiftedDecoderNullTransferCanonicalStmt`
in `RootedShiftedNullTransferDerived.lean`), which takes it as the hypothesis `∀ᵐ ω ∂P, μ ω = ...`.

The statement `CanonicalDecoderIdentityStmt` copies the hypotheses of `ShiftedDecoderNullTransferCanonicalStmt`
(the whole-plane GFF, `0 < γ < 2`, `α₀ < Q(γ)`, the α₀-LQG measure, and the existence hypothesis
`LQGMeasureExistence P γ α₀`, which the proof does not use). The Duplantier-Sheffield (arXiv:0808.1560)
convergence of dyadic approximations identifies the limit with the decoder on the convergence locus.
-/

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal Topology

namespace HarmonicBalls

universe u

open RootedShiftedNullTransferLaw

/-- **Canonical decoder identity** (MQ-lh-29, input (c)). For every whole-plane GFF `hcirc` with
`0 < γ < 2`, `α₀ < Q(γ)`, and every α₀-LQG measure `μ` of `hcirc`, the measure `μ` is almost surely the
canonical decoder `decoder canonicalTest γ α₀` applied to the canonical selector of the positive-radius part of
`hcirc`. -/
def CanonicalDecoderIdentityStmt : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (γ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → α₀ < lqgQ γ →
    IsLQGMeasureOfField P γ α₀ hcirc μ → LQGMeasureExistence P γ α₀ hC hcirc →
    ∀ᵐ ω ∂P, μ ω = ProfileDecoderDerived.decoder canonicalTest γ α₀ (canonicalSel (posPart (hcirc ω)))


/-- **Almost sure identification of an α-LQG measure with the decoder of the selected profile**
(the α-version of `ae_reference_eq_decoder`, MQ-lh-29 step (iv), with the LQG parameter `γ` and the
α-parameter `α₀` of the field circle averages kept apart). For a selector `Sel` with `Sel (posExtend y) = y`,
almost surely `μ ω = Dec(Sel(posPart(hcirc ω)))`: the circle-average profile of `ω` is continuous on positive radii
(`ae_continuousOn_circle`), `Sel` recovers it, its convergence-locus membership follows from the LQG limit property
of `μ ω`, and `IsLQGLimit.unique` identifies the two limits. The test family `T` is arbitrary. -/
lemma ae_lqgMeasure_eq_decoder {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (T : ProfileDecoderDerived.TestFamily) (γ α₀ : ℝ) (Sel : (ℝ → ℂ → ℝ) → C(CircleParameter, ℝ))
    (hSelRec : ∀ y : C(CircleParameter, ℝ), Sel (posExtend ⇑y) = y)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (μ : Ω → Measure ℂ) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, μ ω = ProfileDecoderDerived.decoder T γ α₀ (Sel (posPart (hcirc ω))) := by
  have hμ' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α₀ (hcirc ω)) (μ ω) := hμ
  filter_upwards [hμ', hGFF.ae_continuousOn_circle] with ω hω hcont
  have hyc : Continuous (fun p : CircleParameter => hcirc ω p.1.1 p.2) := by
    have h1 : Continuous (fun p : CircleParameter => ((p.1 : ℝ), p.2)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    have h2 : ∀ p : CircleParameter, ((p.1 : ℝ), p.2) ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℂ) :=
      fun p => ⟨p.1.2, Set.mem_univ _⟩
    exact hcont.comp_continuous h1 h2
  let y : C(CircleParameter, ℝ) := ⟨fun p => hcirc ω p.1.1 p.2, hyc⟩
  have hSel : Sel (posPart (hcirc ω)) = y := by
    rw [posPart_eq_posExtend]
    exact hSelRec y
  have hmem : y ∈ ProfileDecoderDerived.convSet T γ α₀ := by
    simp only [ProfileDecoderDerived.convSet, Set.mem_ofPred_eq]
    intro m
    refine ⟨∫ x, T.D m x ∂(μ ω), ?_⟩
    refine (hω.tendsto_integral (T.D m) (T.D m).continuous (T.D m).hasCompactSupport).congr (fun k => ?_)
    unfold ProfileDecoderDerived.approxMeas
    rw [lqgApprox_congr_pos (fun r z hr => fieldCircleAverage_circleProfile_of_pos α₀ y
      (hcirc ω) (fun p => rfl) r z hr) (dyadicScale_pos k)]
  have hdec : IsLQGLimit γ (fieldCircleAverage α₀ (circleProfile y))
      (ProfileDecoderDerived.decoder T γ α₀ y) :=
    ProfileDecoderDerived.isLQGLimit_decoder T γ α₀ hmem
  have hdec' : IsLQGLimit γ (fieldCircleAverage α₀ (hcirc ω)) (ProfileDecoderDerived.decoder T γ α₀ y) :=
    isLQGLimit_congr_pos (fun r z hr => fieldCircleAverage_circleProfile_of_pos α₀ y
      (hcirc ω) (fun p => rfl) r z hr) hdec
  rw [hSel]
  exact hω.unique hdec'

/-- **Canonical decoder identity** (`CanonicalDecoderIdentityStmt`, MQ-lh-29 input (c)). The α₀-LQG measure `μ` of
the whole-plane GFF `hcirc` is almost surely the decoder of the canonical selected profile. Proof: the α-version
`ae_lqgMeasure_eq_decoder` with the canonical test family `canonicalTest` and the canonical selector `canonicalSel`,
whose recovery property is `canonicalSel_posExtend`. The existence hypothesis `LQGMeasureExistence` is not used. -/
theorem canonicalDecoderIdentityStmt_derived : CanonicalDecoderIdentityStmt.{u} := by
  intro Ω _ P _ γ α₀ hC hcirc μ hGFF _ _ _ hμ _
  exact ae_lqgMeasure_eq_decoder P canonicalTest γ α₀ canonicalSel canonicalSel_posExtend hGFF μ hμ

end HarmonicBalls
