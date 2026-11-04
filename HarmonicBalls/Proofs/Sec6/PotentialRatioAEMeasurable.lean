import HarmonicBalls.Proofs.Sec6.PotentialMeasureMeasurable
import Mathlib.Topology.Order.IsLUB

/-!
# Almost-everywhere measurability of potential ratios

A countable dense set suffices to measure the extrema of an almost surely continuous
potential, even when each spatial section is only almost everywhere measurable.
-/

namespace HarmonicBalls.Section6

open MeasureTheory
open scoped ENNReal

/-- Almost surely continuous potentials have almost everywhere measurable extrema
when all spatial sections are almost everywhere measurable. -/
theorem aemeasurable_potential_extrema_ratio_of_sections
    {Θ S T : Type*} [MeasurableSpace Θ] (P : Measure Θ)
    [TopologicalSpace S] [TopologicalSpace.SeparableSpace S]
    [TopologicalSpace T] [TopologicalSpace.SeparableSpace T]
    (qS : Θ → S → ℝ) (qT : Θ → T → ℝ)
    (hS : ∀ s, AEMeasurable (fun θ => qS θ s) P)
    (hT : ∀ t, AEMeasurable (fun θ => qT θ t) P)
    (hc : ∀ᵐ θ ∂P, Continuous (qS θ) ∧ Continuous (qT θ)) :
    AEMeasurable (fun θ =>
      ((⨅ s, ENNReal.ofReal (qS θ s)) / (⨆ t, ENNReal.ofReal (qT θ t))).toReal) P := by
  classical
  obtain ⟨J, hJ, dJ⟩ := TopologicalSpace.exists_countable_dense S
  obtain ⟨K, hK, dK⟩ := TopologicalSpace.exists_countable_dense T
  have : Countable J := hJ.to_subtype
  have : Countable K := hK.to_subtype
  have hmi : AEMeasurable (fun θ => ⨅ s : J, ENNReal.ofReal (qS θ s)) P :=
    AEMeasurable.iInf fun s => ENNReal.measurable_ofReal.comp_aemeasurable (hS s)
  have hms : AEMeasurable (fun θ => ⨆ t : K, ENNReal.ofReal (qT θ t)) P :=
    AEMeasurable.iSup fun t => ENNReal.measurable_ofReal.comp_aemeasurable (hT t)
  apply (ENNReal.measurable_toReal.comp_aemeasurable (hmi.div hms)).congr
  filter_upwards [hc] with θ hθ
  change ((⨅ s : J, ENNReal.ofReal (qS θ s)) /
    (⨆ t : K, ENNReal.ofReal (qT θ t))).toReal = _
  have hi : (⨅ s : J, ENNReal.ofReal (qS θ s)) = ⨅ s, ENNReal.ofReal (qS θ s) := by
    simpa only [Function.comp_apply] using
      dJ.ciInf (ENNReal.continuous_ofReal.comp hθ.1) (OrderBot.bddBelow _)
  have hs : (⨆ t : K, ENNReal.ofReal (qT θ t)) = ⨆ t, ENNReal.ofReal (qT θ t) := by
    simpa only [Function.comp_apply] using
      dK.ciSup (ENNReal.continuous_ofReal.comp hθ.2) (OrderTop.bddAbove _)
  rw [hi, hs]

/-- A nonnegative integral against a random measure is almost everywhere measurable
if the measure of each measurable set is almost everywhere measurable. -/
theorem aemeasurable_lintegral_random_measure
    {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X] (P : Measure Θ)
    (μ : Θ → Measure X) (f : X → ℝ≥0∞) (hf : Measurable f)
    (hμ : ∀ A : Set X, MeasurableSet A → AEMeasurable (fun θ => μ θ A) P) :
    AEMeasurable (fun θ => ∫⁻ x, f x ∂(μ θ)) P := by
  simp only [lintegral_eq_iSup_eapprox_lintegral, hf, SimpleFunc.lintegral]
  refine .iSup fun n => Finset.aemeasurable_fun_sum _ fun i _ => ?_
  exact (hμ _ ((SimpleFunc.eapprox f n).measurableSet_preimage _)).const_mul _

/-- Fixed Green-potential sections are almost everywhere measurable when all
measurable-set evaluations of the random measure are. -/
theorem aemeasurable_greenPotential_of_evaluations
    {Θ : Type*} [MeasurableSpace Θ] (P : Measure Θ) (μ : Θ → Measure ℂ)
    {O : Set ℂ} (hopen : IsOpen O) (hbounded : Bornology.IsBounded O) (x : ℂ)
    (hμ : ∀ A : Set ℂ, MeasurableSet A → AEMeasurable (fun θ => μ θ A) P) :
    AEMeasurable (fun θ => greenPotential O (μ θ) x) P := by
  have hg := measurable_greenFunction hopen x
  have hlin := aemeasurable_lintegral_random_measure P μ
    (fun y => ENNReal.ofReal (greenFunction O x y))
    (ENNReal.measurable_ofReal.comp hg) hμ
  apply (ENNReal.measurable_toReal.comp_aemeasurable hlin).congr
  filter_upwards [] with θ
  exact (integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (greenFunction_nonneg hbounded x))
    hg.aestronglyMeasurable).symm

universe u

/-- The LQG Green-potential extrema ratio is almost everywhere measurable if all
measurable-set evaluations of the random measure are almost everywhere measurable. -/
theorem aemeasurable_lqg_greenPotential_ratio_of_evaluations
    (hholder : GreenPotentialHolderStmt.{u}) {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hmeas : ∀ A : Set ℂ, MeasurableSet A → AEMeasurable (fun ω => μ ω A) P)
    {O K : Set ℂ} (hO : IsSmoothBoundedOpen O) (hK : K ⊆ closure O) :
    AEMeasurable (fun ω =>
      ((⨅ z : K, ENNReal.ofReal (greenPotential O (μ ω) z)) /
        (⨆ z : O, ENNReal.ofReal (greenPotential O (μ ω) z))).toReal) P := by
  have hopen : IsOpen O := by
    obtain ⟨_, ρ, hρ, rfl, _⟩ := hO
    exact isOpen_lt hρ.continuous continuous_const
  refine aemeasurable_potential_extrema_ratio_of_sections P
    (fun ω (z : K) => greenPotential O (μ ω) z)
    (fun ω (z : O) => greenPotential O (μ ω) z)
    (fun z => aemeasurable_greenPotential_of_evaluations P μ hopen hO.1 z hmeas)
    (fun z => aemeasurable_greenPotential_of_evaluations P μ hopen hO.1 z hmeas) ?_
  filter_upwards [hholder γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hhold
  obtain ⟨_, C, r, hr, hcont⟩ := hhold O hO (fun _ => 1) (memLp_top_const (1 : ℝ))
  have hcont' : ContinuousOn (greenPotential O (μ ω)) (closure O) := by
    apply greenPotential_continuousOn_of_holder (μ ω)
    refine ⟨C, r, hr, ?_⟩
    simpa only [mul_one] using hcont
  exact ⟨(hcont'.mono hK).domRestrict, (hcont'.mono subset_closure).domRestrict⟩

/-- LQG locality makes the mass of each deterministic open set almost everywhere
measurable in the ambient probability space. -/
theorem aemeasurable_lqg_measure_open
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc) {U : Set ℂ} (hU : IsOpen U) :
    AEMeasurable (fun ω => μ ω U) P := by
  obtain ⟨Y, hY, heq⟩ := hloc hGFF hγ hγ2 hα μ hμ U hU
  exact ((hY.mono (hGFF.fieldSigmaAlgebra_le α₀ U) le_rfl).aemeasurable.congr (heq.mono fun _ h => h.symm))

end HarmonicBalls.Section6
