import HarmonicBalls.FirstPass.S11r.RootedJoint
import HarmonicBalls.FirstPass.Phase2.RootedLocalAgreementObs

/-!
# Campbell transfer of a measurable observation event (step 6 of the local-agreement route for `hN2`)

If a measurable event `A` of local mean-zero observations on a disk `D = ball c₂ r₂` holds almost surely for the
observation of the whole-plane field `h = h^ℂ - α log|·|` on `D`, then for Lebesgue-almost every root `z ∈ ball c₁ r₁`
(`closedBall c₁ r₁ ⊆ D`) it holds almost surely for the observation of the rooted field `g - γ log|· - z| + b`
(the reference observation `campbellReferenceObs`). This is the null-set transfer `ae_root_rootedObs_eq_zero_of_obs_null_noMeas`
applied to the complement of `A`, with the lintegral of the indicator converted to an almost-sure statement.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric
open scoped ENNReal

universe u

/-- **Campbell transfer of an event.** Almost surely `obs_D h ∈ A` implies: for a.e. root `z ∈ ball c₁ r₁`,
almost surely the reference observation at `z` lies in `A`. -/
theorem ae_root_ae_rootedObs_mem_of_ae_obs_mem (hI1 : LocalMarkedRootingIdentityWeightedFrozen.{u})
    {γ α₀ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hsub : closedBall c₁ r₁ ⊆ ball c₂ r₂) (h0 : (0 : ℂ) ∉ closedBall c₂ r₂)
    (A : Set (MeanZeroTest (ball c₂ r₂) → ℝ)) (hA : MeasurableSet A)
    (hmem : ∀ᵐ ω ∂P, localMeanZeroObs α₀ (ball c₂ r₂) (hC ω) ∈ A) :
    ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)),
      ∀ᵐ ω ∂P, (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z).2 ∈ A := by
  have h := ae_root_rootedObs_eq_zero_of_obs_null_noMeas hI1 hγ0 hγ2 hα Ω P hC hcirc μ hGFF hμ hr₁ hr₂
    hsub h0 Aᶜ hA.compl (hmem.mono fun ω hω => not_not.mpr hω)
  have hJ := measurable_campbellReferenceObs_joint P hC hcirc hGFF γ α₀ (ball c₂ r₂)
  filter_upwards [h] with z hz
  have hmz : Measurable (fun ω => campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z) :=
    hJ.comp (measurable_const.prodMk measurable_id)
  have hG : Measurable (fun ω => (univ ×ˢ Aᶜ).indicator (fun _ => (1 : ℝ≥0∞))
      (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z)) :=
    (measurable_const.indicator (MeasurableSet.univ.prod hA.compl)).comp hmz
  have h2 := (lintegral_eq_zero_iff hG).1 hz
  filter_upwards [h2] with ω hω
  by_contra hn
  have hmem' : campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z ∈ (univ ×ˢ Aᶜ : Set _) := ⟨mem_univ _, hn⟩
  simp [Set.indicator_of_mem hmem'] at hω

end HarmonicBalls
