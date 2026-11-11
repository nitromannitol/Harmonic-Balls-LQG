import HarmonicBalls.FirstPass.S11ah.LocalObsHae
import HarmonicBalls.FirstPass.S11i.Step8CorrectedMarked

/-!
# Marked observations lie in the modification set

* `ae_refObs_mem_of_rootedRefLaw_compl_null`: `rootedRefLaw Hᶜ = 0` for a measurable set `H` of observations gives,
  for a.e. root `z` in `ball c₁ r₁`, `P`-a.s. membership of the reference observation in `H` (Fubini, `Measure.ae_prod_iff_ae_ae`).
* `ae_markedObs_mem_modificationSet`: the measurable bad cylinder `{(z, ℓ) | z ∈ ball c₁ r₁, ℓ ∉ H}` is handled by the
  existing marked Campbell transfer `ae_marked_local_transfer_landed`. The cylinder is restricted to the roots `ball c₁ r₁`
  because the transfer's null hypothesis is over all of `ball 0 1`; the conclusion is the marked law `μα ω` restricted to
  `ball c₁ r₁`, the only roots that matter for the rooted identity.
-/

open MeasureTheory Filter Topology Set Metric ProbabilityTheory
open scoped ENNReal
open HarmonicBalls HarmonicBalls.S11c FirstPassS11ah HarmonicBalls.FirstPassS11ahLocalHae

universe u

namespace HarmonicBalls.FirstPassS11iStep8MarkedMem

/-- **Reference side from the rooted law.** If `rootedRefLaw Hᶜ = 0` for a measurable set `H` of local observations,
then for a.e. root `z` in the disc `ball c₁ r₁`, `P`-a.s. the rooted reference observation `campbellReferenceObs z ω` lies in `H`. -/
theorem ae_refObs_mem_of_rootedRefLaw_compl_null {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ α₀ : ℝ} {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc)
    {H : Set (FirstPassS11ahFinite.LocalObs c₂ r₂)} (hH : MeasurableSet H)
    (hPm : rootedRefLaw P γ α₀ c₁ c₂ r₁ r₂ hC Hᶜ = 0) :
    ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ᵐ ω ∂P,
      (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z).2 ∈ H := by
  have hobs : Measurable (rootedRefObs γ α₀ c₂ r₂ hC) :=
    measurable_snd.comp (measurable_campbellReferenceObs_joint P hC hcirc hG γ α₀ (ball c₂ r₂))
  unfold rootedRefLaw at hPm
  rw [Measure.map_apply hobs hH.compl] at hPm
  have hae : ∀ᵐ p ∂((volume.restrict (ball c₁ r₁)).prod P), rootedRefObs γ α₀ c₂ r₂ hC p ∈ H :=
    ae_iff.mpr hPm
  exact (Measure.ae_prod_iff_ae_ae (hobs hH)).mp hae

/-- **Marked observations lie in `H`.** Under the reference-side statement `hrefH` (for instance from
`ae_refObs_mem_of_rootedRefLaw_compl_null`), for a.e. `ω`, `μα ω`-a.e. marked observation at a root in `ball c₁ r₁`
lies in the measurable set `H`. The proof is the existing marked Campbell transfer applied to the bad cylinder
`(ball c₁ r₁ ×ˢ Hᶜ)`; no argument from the rooted law is used on the marked side. -/
theorem ae_markedObs_mem_modificationSet {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    (hWeyl : LocalLQGInsertionWeylOffOrigin.{u}) (γ α₀ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (h12 : closedBall c₁ r₁ ⊆ ball c₂ r₂) (h21 : closedBall c₂ r₂ ⊆ ball (0 : ℂ) 1)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (μ0 μα : Ω → Measure ℂ)
    (hA10 : DMSLemmaA10WholePlaneMarked P γ hC hcirc μ0)
    (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ0 : IsLQGMeasureOfField P γ 0 hcirc μ0) (hμα : IsLQGMeasureOfField P γ α₀ hcirc μα)
    (hNon0 : ∀ᵐ ω ∂P, μ0 ω {0} = 0) (hNonα : ∀ᵐ ω ∂P, μα ω {0} = 0)
    {H : Set (FirstPassS11ahFinite.LocalObs c₂ r₂)} (hH : MeasurableSet H)
    (hrefH : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ᵐ ω ∂P,
      (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z).2 ∈ H) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μα ω).restrict (ball c₁ r₁), (campbellMarkedObs α₀ (ball c₂ r₂) (hC ω) z).2 ∈ H := by
  have hball : ball c₁ r₁ ⊆ ball (0 : ℂ) 1 :=
    fun z hz => h21 (ball_subset_closedBall (h12 (ball_subset_closedBall hz)))
  have hBad : MeasurableSet ((Prod.fst ⁻¹' ball c₁ r₁) ∩ (Prod.snd ⁻¹' Hᶜ)) :=
    (measurable_fst measurableSet_ball).inter (measurable_snd hH.compl)
  have href : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ ball (0 : ℂ) 1 →
      ∀ᵐ ω ∂P, campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z ∉
        ((Prod.fst ⁻¹' ball c₁ r₁) ∩ (Prod.snd ⁻¹' Hᶜ)) := by
    filter_upwards [(ae_restrict_iff' measurableSet_ball).mp hrefH] with z hz hz01
    by_cases hzc : z ∈ ball c₁ r₁
    · filter_upwards [hz hzc] with ω hω hbad
      exact hbad.2 hω
    · exact Filter.Eventually.of_forall fun ω hbad => hzc hbad.1
  have hmark := FirstPassS11iStep8Corrected.ae_marked_local_transfer_landed hWeyl γ α₀ hγ0 hγ2 hα (ball c₂ r₂)
    μ0 μα hA10 hGFF hμ0 hμα hNon0 hNonα ((Prod.fst ⁻¹' ball c₁ r₁) ∩ (Prod.snd ⁻¹' Hᶜ)) hBad href
  filter_upwards [hmark] with ω hω
  rw [ae_restrict_iff' measurableSet_ball]
  filter_upwards [hω] with z hz hzc
  by_contra hnot
  exact hz (hball hzc) ⟨hzc, hnot⟩

end HarmonicBalls.FirstPassS11iStep8MarkedMem

