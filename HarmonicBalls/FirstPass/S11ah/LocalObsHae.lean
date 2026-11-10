import HarmonicBalls.FirstPass.S11ah.RootedLengthProperty
import HarmonicBalls.FirstPass.S11r.RootedJoint
import HarmonicBalls.FirstPass.S11ah.FiniteLocalKernel

/-!
# The almost-sure length property of the local decoders on the observation space (fp-S11i-11-13g, item (b), n3)

Operator ruling (notes/fp-gaps/CHATGPT-217-hb-11-13-n3-hBad-G4-PRO.md, section (b)): `hae` for the local decoder
`m : LocalObs c₂ r₂ → C(ball c₂ r₂ × ball c₂ r₂, ℝ)` is the observation-space form of the rooted length property. The
joint rooted-reference observation law is the pushforward `Pm = ((volume.restrict (ball c₁ r₁)).prod P).map obs₂`, with
`obs₂ (z, ω) = (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z).2`.

What is proved here:
* `rootedRefLaw`: the pushforward measure.
* `ae_isLengthMetricOn_rootedRefLaw`: `∀ᵐ ℓ ∂Pm, IsLengthMetricOn (ball c₂ r₂) (decoderOn (ball c₂ r₂) (m ℓ))`. The a.e.-in-`z`,
  a.s.-in-`ω` statement is `rootedLengthProperty` (S11ah/RootedLengthProperty.lean:57), proved from the frozen
  `RootedPhysicalMetricContinuousAtInsertionFrozen`, `IsLQGMetric` and identity (20). No `hLen` hypothesis is needed.

Named input, NOT derived: `hGood`, the measurability of the good set of observations. The ruling's step `ae_prod_mk.2 hroot`
does not exist in Mathlib, and the converse Fubini step (a.e. in `z`, a.e. in `ω` implies a.e. in the product) needs the
set `{p | good (obs p)}` to be measurable; without that, the converse can fail for non-measurable sets (Sierpinski-type
counterexample). `hGood` is the minimal explicit form of that step.
-/

open MeasureTheory ProbabilityTheory Metric Set Filter Topology
open scoped ENNReal
open HarmonicBalls HarmonicBalls.S11c FirstPassS11ah

universe u

namespace HarmonicBalls.FirstPassS11ahLocalHae

/-- The joint rooted-reference observation `(z, ω) ↦ obs_z(ω)` on the decoder disc `ball c₂ r₂`
(`campbellReferenceObs` at the root `z`, background `α₀`, identity-shift `hC ω`). -/
noncomputable def rootedRefObs {Ω : Type u} (γ α₀ : ℝ) (c₂ : ℂ) (r₂ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (p : ℂ × Ω) :
    FirstPassS11ahFinite.LocalObs c₂ r₂ :=
  (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC p.2) p.1).2

/-- The pushforward of the joint rooted-reference law `volume|_{ball c₁ r₁} ⊗ P` by the observation `rootedRefObs`. -/
noncomputable def rootedRefLaw {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) : Measure (FirstPassS11ahFinite.LocalObs c₂ r₂) :=
  ((volume.restrict (ball c₁ r₁)).prod P).map (rootedRefObs γ α₀ c₂ r₂ hC)

/-- **Almost-sure length property of the local decoders under the rooted-reference law.** For a local decoder
`m` (identity (20) holds for the rooted reference observations at a.e. root, almost surely), the decoder
`decoderOn (ball c₂ r₂) (m ℓ)` is a length metric on the disc for `rootedRefLaw`-almost every observation `ℓ`,
provided the good set of observations is measurable (`hGood`, named input). -/
theorem ae_isLengthMetricOn_rootedRefLaw {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ ξ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (hL : IsLQGMetric γ ξ 𝔇)
    (hfr : RootedPhysicalMetricContinuousAtInsertionFrozen.{0}) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (hcl : closedBall c₁ r₁ ⊆ ball c₂ r₂) (h0 : (0 : ℂ) ∉ closedBall c₂ r₂)
    (m : FirstPassS11ahFinite.LocalObs c₂ r₂ →
      ContinuousMap ↥(ball c₂ r₂ ×ˢ ball c₂ r₂ : Set (ℂ × ℂ)) ℝ)
    (hid : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧
      ∀ p : ↥(ball c₂ r₂ ×ˢ ball c₂ r₂ : Set (ℂ × ℂ)),
        ENNReal.ofReal (m (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z).2 p) =
          ENNReal.ofReal b * internalMetric (weylPhysicalE (𝔇 (hC ω)) ξ
            (fun w => -α₀ * Real.log ‖w‖ - γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖)))
            (ball c₂ r₂) p.1.1 p.1.2)
    (hGood : MeasurableSet {ℓ : FirstPassS11ahFinite.LocalObs c₂ r₂ |
      IsLengthMetricOn (ball c₂ r₂) (decoderOn (ball c₂ r₂) (m ℓ))}) :
    ∀ᵐ ℓ ∂(rootedRefLaw P γ α₀ c₁ c₂ r₁ r₂ hC),
      IsLengthMetricOn (ball c₂ r₂) (decoderOn (ball c₂ r₂) (m ℓ)) := by
  have hR : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ᵐ ω ∂P,
      IsLengthMetricOn (ball c₂ r₂) (decoderOn (ball c₂ r₂) (m (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z).2)) :=
    rootedLengthProperty hG hL hfr hγ0 hγ2 hα hcl h0 m hid
  have hobs : Measurable (rootedRefObs γ α₀ c₂ r₂ hC) :=
    measurable_snd.comp (measurable_campbellReferenceObs_joint P hC hcirc hG γ α₀ (ball c₂ r₂))
  have hmeas : MeasurableSet {p : ℂ × Ω |
      IsLengthMetricOn (ball c₂ r₂) (decoderOn (ball c₂ r₂) (m (rootedRefObs γ α₀ c₂ r₂ hC p)))} :=
    hGood.preimage hobs
  have hprod : ∀ᵐ p ∂((volume.restrict (ball c₁ r₁)).prod P),
      IsLengthMetricOn (ball c₂ r₂) (decoderOn (ball c₂ r₂) (m (rootedRefObs γ α₀ c₂ r₂ hC p))) := by
    rw [Measure.ae_prod_iff_ae_ae hmeas]
    exact hR
  unfold rootedRefLaw
  exact (ae_map_iff hobs.aemeasurable hGood).2 hprod

end HarmonicBalls.FirstPassS11ahLocalHae

#print axioms HarmonicBalls.FirstPassS11ahLocalHae.ae_isLengthMetricOn_rootedRefLaw
