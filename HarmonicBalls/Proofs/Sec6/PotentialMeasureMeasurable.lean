import HarmonicBalls.Proofs.Sec6.PotentialRatioScaling
import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Measurability of Green potentials as functions of the measure

For a fixed bounded open domain and evaluation point, the Green potential is measurable
on the space of measures. This isolates the measure-valued part of the joint
measurability needed by the fine-support argument.
-/

namespace HarmonicBalls.Section6

open MeasureTheory

/-- For fixed domain and point, the Green potential is measurable in the measure. -/
theorem measurable_greenPotential_measure {O : Set ℂ} (hopen : IsOpen O)
    (hbounded : Bornology.IsBounded O) (x : ℂ) :
    Measurable fun μ : Measure ℂ => greenPotential O μ x := by
  have hg := measurable_greenFunction hopen x
  have hlin : Measurable fun μ : Measure ℂ =>
      ∫⁻ y, ENNReal.ofReal (greenFunction O x y) ∂μ :=
    Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp hg)
  have heq : (fun μ : Measure ℂ => greenPotential O μ x) =
      fun μ => (∫⁻ y, ENNReal.ofReal (greenFunction O x y) ∂μ).toReal := by
    funext μ
    exact integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (greenFunction_nonneg hbounded x)) hg.aestronglyMeasurable
  rw [heq]
  exact ENNReal.measurable_toReal.comp hlin

/-- The extrema ratio is almost everywhere measurable when the potential sections are
measurable and are continuous in the spatial variable almost surely. -/
theorem aemeasurable_potential_extrema_ratio
    {Θ S T : Type*} [MeasurableSpace Θ] (P : Measure Θ)
    [TopologicalSpace S] [TopologicalSpace.SeparableSpace S]
    [TopologicalSpace T] [TopologicalSpace.SeparableSpace T]
    (qS : Θ → S → ℝ) (qT : Θ → T → ℝ)
    (hS : ∀ s, Measurable fun θ => qS θ s) (hT : ∀ t, Measurable fun θ => qT θ t)
    (hc : ∀ᵐ θ ∂P, Continuous (qS θ) ∧ Continuous (qT θ)) :
    AEMeasurable (fun θ =>
      ((⨅ s, ENNReal.ofReal (qS θ s)) / (⨆ t, ENNReal.ofReal (qT θ t))).toReal) P := by
  classical
  obtain ⟨N, hNsub, hNmeas, hNzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hc)
  let pS : Θ → S → ℝ := fun θ s => if θ ∈ N then 0 else qS θ s
  let pT : Θ → T → ℝ := fun θ t => if θ ∈ N then 0 else qT θ t
  have hpS : ∀ s, Measurable fun θ => pS θ s := fun s =>
    measurable_const.ite hNmeas (hS s)
  have hpT : ∀ t, Measurable fun θ => pT θ t := fun t =>
    measurable_const.ite hNmeas (hT t)
  have hcont : ∀ θ, Continuous (pS θ) ∧ Continuous (pT θ) := by
    intro θ
    by_cases h : θ ∈ N
    · simp only [pS, pT, h, ↓reduceIte]
      exact ⟨continuous_const, continuous_const⟩
    · have hh : Continuous (qS θ) ∧ Continuous (qT θ) := by
        by_contra hbad
        exact h (hNsub hbad)
      simpa only [pS, pT, h, ↓reduceIte] using hh
  have hm := measurable_potential_extrema_ratio pS pT hpS (fun θ => (hcont θ).1)
    hpT (fun θ => (hcont θ).2)
  apply hm.aemeasurable.congr
  have hnot : ∀ᵐ θ ∂P, θ ∉ N := by
    apply ae_iff.mpr
    simpa only [not_not, Set.ofPred_mem_eq] using hNzero
  filter_upwards [hnot] with θ hθ
  simp only [pS, pT, hθ, ↓reduceIte]

universe u

/-- For a measurable LQG measure, the Green-potential ratio on a fixed smooth
bounded domain and fixed subset of its closure is almost everywhere measurable. -/
theorem aemeasurable_lqg_greenPotential_ratio
    (hholder : GreenPotentialHolderStmt.{u}) {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hμmeas : Measurable μ) {O K : Set ℂ} (hO : IsSmoothBoundedOpen O)
    (hK : K ⊆ closure O) :
    AEMeasurable (fun ω =>
      ((⨅ z : K, ENNReal.ofReal (greenPotential O (μ ω) z)) /
        (⨆ z : O, ENNReal.ofReal (greenPotential O (μ ω) z))).toReal) P := by
  have hopen : IsOpen O := by
    obtain ⟨_, ρ, hρ, rfl, _⟩ := hO
    exact isOpen_lt hρ.continuous continuous_const
  refine aemeasurable_potential_extrema_ratio P
    (fun ω (z : K) => greenPotential O (μ ω) z)
    (fun ω (z : O) => greenPotential O (μ ω) z)
    (fun z => (measurable_greenPotential_measure hopen hO.1 z).comp hμmeas)
    (fun z => (measurable_greenPotential_measure hopen hO.1 z).comp hμmeas) ?_
  filter_upwards [hholder γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hhold
  obtain ⟨_, C, r, hr, hcont⟩ := hhold O hO (fun _ => 1) (memLp_top_const (1 : ℝ))
  have hcont' : ContinuousOn (greenPotential O (μ ω)) (closure O) := by
    apply greenPotential_continuousOn_of_holder (μ ω)
    refine ⟨C, r, hr, ?_⟩
    simpa only [mul_one] using hcont
  exact ⟨(hcont'.mono hK).domRestrict, (hcont'.mono subset_closure).domRestrict⟩

end HarmonicBalls.Section6
