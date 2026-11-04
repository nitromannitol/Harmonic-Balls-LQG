import HarmonicBalls.Proofs.Sec11.PinchRecenteredRootLaw
import Mathlib.MeasureTheory.Measure.GiryMonad

/-! # Recentering measure and metric observations

The comparison is formulated on the space of observations, without assuming
that spatial translation is realized by a map of the underlying sample space.
-/

namespace HarmonicBalls

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The measure and metric as seen from a root. -/
noncomputable def recenteredPinchObservation {Ω : Type*}
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ) (z : ℂ) (ω : Ω) :
    Measure ℂ × (ℂ → ℂ → ℝ) :=
  ((μ ω).map (fun y : ℂ => y - z), fun x y => D ω (x + z) (y + z))

/-- The recentered observation is almost everywhere measurable whenever the
measure is almost everywhere measurable and the metric evaluations are measurable. -/
theorem aemeasurable_recenteredPinchObservation
    {Ω : Type*} [MeasurableSpace Ω] (R : Measure Ω)
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (hμ : AEMeasurable μ R) (hD : ∀ x y, Measurable fun ω => D ω x y) (z : ℂ) :
    AEMeasurable (recenteredPinchObservation μ D z) R := by
  have hm : Measurable (fun m : Measure ℂ => m.map (fun y : ℂ => y - z)) :=
    Measure.measurable_map _ (by fun_prop)
  have hd : Measurable (fun ω x y => D ω (x + z) (y + z)) :=
    Measurable.of_eval fun x => Measurable.of_eval fun y => hD (x + z) (y + z)
  exact (hm.comp_aemeasurable hμ).prodMk hd.aemeasurable

/-- Fixed-origin density under an observation law transfers to a root whose
recentered observation law is absolutely continuous with respect to it. -/
theorem ae_internal_pinch_block_density_of_recentered_observation
    {Ω : Type*} [MeasurableSpace Ω] (R : Measure Ω)
    (Q : Measure (Measure ℂ × (ℂ → ℂ → ℝ)))
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (hμ : AEMeasurable μ R) (hD : ∀ x y, Measurable fun ω => D ω x y)
    (U T Q' Qset : Set ℂ) (M q : ℝ) (r : ℕ → ℝ) (z : ℂ)
    (hac : R.map (recenteredPinchObservation μ D z) ≪ Q)
    (hfixed : ∀ᵐ p ∂(Q), ∀ᶠ N : ℕ in atTop, q * N ≤
      ({k : ℕ | N + 1 ≤ k ∧ k ≤ 2 * N ∧
        pinchPointEventWithInternalBounds p.1 p.2 U T Q' Qset M (r k) 0}.ncard : ℝ)) :
    ∀ᵐ ω ∂(R), ∀ᶠ N : ℕ in atTop, q * N ≤
      ({k : ℕ | N + 1 ≤ k ∧ k ≤ 2 * N ∧
        pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Qset M (r k) z}.ncard : ℝ) := by
  have h := ae_of_ae_map (aemeasurable_recenteredPinchObservation R hμ hD z) (hac.ae_le hfixed)
  filter_upwards [h] with ω hω
  have hsets (N : ℕ) :
      {k : ℕ | N + 1 ≤ k ∧ k ≤ 2 * N ∧
        pinchPointEventWithInternalBounds ((μ ω).map (fun y : ℂ => y - z))
          (fun x y => D ω (x + z) (y + z)) U T Q' Qset M (r k) 0} =
      {k : ℕ | N + 1 ≤ k ∧ k ≤ 2 * N ∧
        pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Qset M (r k) z} := by
    ext k
    simp only [mem_ofPred_eq, pinchPointEventWithInternalBounds_translate]
  filter_upwards [hω] with N hN
  change q * N ≤ ({k : ℕ | N + 1 ≤ k ∧ k ≤ 2 * N ∧
    pinchPointEventWithInternalBounds ((μ ω).map (fun y : ℂ => y - z))
      (fun x y => D ω (x + z) (y + z)) U T Q' Qset M (r k) 0}.ncard : ℝ) at hN
  simpa only [hsets] using hN

/-- A fixed-origin observation law supplies one density rate for typical
points, conditional on rooted absolute continuity and domination. -/
theorem ae_ae_pinch_block_density_of_recentered_observation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (hμ : AEMeasurable μ P) (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (hD : ∀ x y, Measurable fun ω => D ω x y)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (ν : ℕ → Measure Ω) (hμν : ∀ n, AEMeasurable μ (ν n))
    (hlocν : ∀ n, ∀ᵐ ω ∂(ν n), IsLocallyFiniteMeasure (μ ω))
    (hmetricν : ∀ n, ∀ᵐ ω ∂(ν n), IsEuclideanLengthMetric (D ω))
    {U T Q' Qset : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q' Qset)
    (M q : ℝ) (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    (hpos : ∀ z, w z ≠ 0) (hfin : ∀ z, w z ≠ ∞)
    (ρ : ℕ → Measure ℂ) (shift : ℕ → ℂ × Ω → Ω)
    (hshift : ∀ n, Measurable (shift n)) (R : ℕ → ℂ → Measure Ω)
    (hrooted : ∀ n, P ⊗ₘ (unnormalizedWeightedRestrictionKernel P μ hμ
      (weightedLocalization w n) (measurableSet_weightedLocalization hw n) w hw) ≪
        shiftedRootReferenceLaw (ρ n) P (shift n))
    (hac : ∀ n, ∀ᵐ z ∂ρ n, P.map (fun ω => shift n (z, ω)) ≪ R n z)
    (hdom : ∀ n, ∀ᵐ z ∂ρ n, R n z ≪ ν n)
    (Q : Measure (Measure ℂ × (ℂ → ℂ → ℝ)))
    (hcomp : ∀ n, ∀ᵐ z ∂ρ n, (R n z).map (recenteredPinchObservation μ D z) ≪ Q)
    (hfixed : ∀ᵐ p ∂(Q), ∀ᶠ N : ℕ in atTop, q * N ≤
      ({k : ℕ | N + 1 ≤ k ∧ k ≤ 2 * N ∧
        pinchPointEventWithInternalBounds p.1 p.2 U T Q' Qset M ((2 : ℝ)⁻¹ ^ k) 0}.ncard : ℝ)) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, ∀ᶠ N : ℕ in atTop, q * N ≤
      ({k : ℕ | N + 1 ≤ k ∧ k ≤ 2 * N ∧
        pinchPointEvent (μ ω) (D ω) U T Q' Qset M ((2 : ℝ)⁻¹ ^ k) z}.ncard : ℝ) := by
  apply ae_ae_pinch_block_density_of_countably_dominated_rooted_law
    P hμ hloc hD hmetric ν hμν hlocν hmetricν hconfig M q w hw hpos hfin
    ρ shift hshift R hrooted hac hdom
  intro n
  filter_upwards [hdom n, hcomp n] with z hd hc
  exact ae_internal_pinch_block_density_of_recentered_observation (R n z) Q
    ((hμν n).mono_ac hd) hD U T Q' Qset M q (fun k => (2 : ℝ)⁻¹ ^ k) z hc hfixed

/-- An almost-sure fixed-origin density estimate passes to the law of the
measure-metric observation, provided that law has the regularity needed to
construct a measurable representative of the density event. -/
theorem ae_internal_pinch_block_density_observation_law
    {Ξ : Type*} [MeasurableSpace Ξ] (P : Measure Ξ)
    {μ : Ξ → Measure ℂ} {D : Ξ → ℂ → ℂ → ℝ}
    (hμ : AEMeasurable μ P) (hD : ∀ x y, Measurable fun ω => D ω x y)
    {U T Q' Qset : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q' Qset)
    (M q : ℝ) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hloc : ∀ᵐ p ∂(P.map (fun ω => (μ ω, D ω))), IsLocallyFiniteMeasure p.1)
    (hmetric : ∀ᵐ p ∂(P.map (fun ω => (μ ω, D ω))), IsEuclideanLengthMetric p.2)
    (hfixed : ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop, q * N ≤
      ({k : ℕ | N + 1 ≤ k ∧ k ≤ 2 * N ∧
        pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Qset M (r k) 0}.ncard : ℝ)) :
    ∀ᵐ p ∂(P.map (fun ω => (μ ω, D ω))), ∀ᶠ N : ℕ in atTop, q * N ≤
      ({k : ℕ | N + 1 ≤ k ∧ k ≤ 2 * N ∧
        pinchPointEventWithInternalBounds p.1 p.2 U T Q' Qset M (r k) 0}.ncard : ℝ) := by
  let obs : Ξ → Measure ℂ × (ℂ → ℂ → ℝ) := fun ω => (μ ω, D ω)
  have hObs : AEMeasurable obs P := hμ.prodMk
    (Measurable.of_eval fun x => Measurable.of_eval fun y => hD x y).aemeasurable
  have hd : ∀ x y, Measurable (fun p : Measure ℂ × (ℂ → ℂ → ℝ) => p.2 x y) := by
    intro x y
    exact (measurable_pi_apply y).comp ((measurable_pi_apply x).comp measurable_snd)
  obtain ⟨F, hF, hFae⟩ := exists_jointlyMeasurable_internal_pinch_block_density
    (P.map obs) hconfig M q r hr hd hmetric measurable_fst.aemeasurable hloc
  have hsource : ∀ᵐ ω ∂P, (obs ω, 0) ∈ F := by
    filter_upwards [ae_of_ae_map hObs hFae, hfixed] with ω hrep hω
    exact (hrep 0).2 hω
  have hm : MeasurableSet {p | (p, (0 : ℂ)) ∈ F} := measurable_prodMk_right hF
  have hmap : ∀ᵐ p ∂(P.map obs), (p, 0) ∈ F := (ae_map_iff hObs hm).2 hsource
  filter_upwards [hFae, hmap] with p hp hpF
  exact (hp 0).1 hpF

#print axioms ae_internal_pinch_block_density_observation_law

#print axioms ae_ae_pinch_block_density_of_recentered_observation

#print axioms aemeasurable_recenteredPinchObservation
#print axioms ae_internal_pinch_block_density_of_recentered_observation

end HarmonicBalls
