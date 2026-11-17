import HarmonicBalls.Proofs.Potential.LQGSingularGreenPotentialHolder
import HarmonicBalls.Proofs.Potential.WholePlaneObservationTruncation

/-! # Signed whole-plane potentials for the actual LQG measure

On bounded observation sets, compactly concentrated finite sources have
integrable real potentials and finite extended signed potentials almost everywhere.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped ENNReal

/-- At a point where each Jordan source has no atom and the Newtonian kernel
is integrable, the separate extended signed potentials agree with their real
integrals. -/
theorem signed_wholePlane_potential_at_point {ν₁ ν₂ : Measure ℂ} {x : ℂ}
    (ha₁ : ν₁ {x} = 0) (ha₂ : ν₂ {x} = 0)
    (hi₁ : Integrable (newtonKernel x) ν₁) (hi₂ : Integrable (newtonKernel x) ν₂) :
    (∫⁻ y, (newtonKernelEReal x y).toENNReal ∂ν₁) < ⊤ ∧
    (∫⁻ y, (-newtonKernelEReal x y).toENNReal ∂ν₁) < ⊤ ∧
    (∫⁻ y, (newtonKernelEReal x y).toENNReal ∂ν₂) < ⊤ ∧
    (∫⁻ y, (-newtonKernelEReal x y).toENNReal ∂ν₂) < ⊤ ∧
    extendedSignedIntegral (newtonKernelEReal x) ν₁ = (greenPotential univ ν₁ x : EReal) ∧
    extendedSignedIntegral (newtonKernelEReal x) ν₂ = (greenPotential univ ν₂ x : EReal) := by
  have h₁ := newtonKernelEReal_parts_lt_top ha₁ hi₁
  have h₂ := newtonKernelEReal_parts_lt_top ha₂ hi₂
  refine ⟨h₁.1, h₁.2, h₂.1, h₂.2, ?_, ?_⟩
  · simpa only [greenPotential, greenFunction_univ_eq_newtonKernel] using
      extendedSignedIntegral_newtonKernel_eq ha₁ hi₁
  · simpa only [greenPotential, greenFunction_univ_eq_newtonKernel] using
      extendedSignedIntegral_newtonKernel_eq ha₂ hi₂

/-- On one actual-LQG event, the difference of the real whole-plane potentials
of any two finite compactly concentrated sources is integrable on any bounded
observation set. At almost every observation, both extended signed integrals
have finite positive and negative parts and agree with their real potentials.
The exceptional set may depend on the observation set and sources. -/
theorem IsWholePlaneGFF.ae_singular_signed_wholePlane_potential
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ) :
    ∀ᵐ ω ∂P, ∀ (K₁ K₂ S : Set ℂ) (ν₁ ν₂ : Measure ℂ),
      IsCompact K₁ → IsCompact K₂ → ν₁ K₁ᶜ = 0 → ν₂ K₂ᶜ = 0 →
      IsFiniteMeasure ν₁ → IsFiniteMeasure ν₂ → Bornology.IsBounded S →
      IntegrableOn (greenPotential univ ν₁ - greenPotential univ ν₂) S (μ ω) ∧
      (∀ᵐ x ∂(μ ω).restrict S,
        Integrable (newtonKernel x) ν₁ ∧ Integrable (newtonKernel x) ν₂ ∧
        ν₁ {x} = 0 ∧ ν₂ {x} = 0 ∧
        (∫⁻ y, (newtonKernelEReal x y).toENNReal ∂ν₁) < ⊤ ∧
        (∫⁻ y, (-newtonKernelEReal x y).toENNReal ∂ν₁) < ⊤ ∧
        (∫⁻ y, (newtonKernelEReal x y).toENNReal ∂ν₂) < ⊤ ∧
        (∫⁻ y, (-newtonKernelEReal x y).toENNReal ∂ν₂) < ⊤ ∧
        extendedSignedIntegral (newtonKernelEReal x) ν₁ = (greenPotential univ ν₁ x : EReal) ∧
        extendedSignedIntegral (newtonKernelEReal x) ν₂ = (greenPotential univ ν₂ x : EReal)) := by
  filter_upwards [hh.ae_singular_limit_and_approximant_ball_power hγ hγ2 hαQ hμ, hμ] with ω hb hlim
  let : IsLocallyFiniteMeasure (μ ω) := hlim.isLocallyFiniteMeasure
  have hup : ∀ R : ℝ, 0 < R → ∃ r₀ β : ℝ, 0 < r₀ ∧ 0 < β ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        μ ω (ball z r) ≤ ENNReal.ofReal (r ^ β) := by
    intro R _
    obtain ⟨C, β, r₀, hC, hβ, hr₀, hb⟩ := hb R
    obtain ⟨δ, hδ, hd⟩ := small_ball_power_absorb_constant hC hβ hr₀
      (fun z hz r hr hrr => (hb z hz r hr hrr).1)
    exact ⟨δ, β / 2, hδ, by positivity, hd⟩
  intro K₁ K₂ S ν₁ ν₂ hK₁ hK₂ hν₁ hν₂ hf₁ hf₂ hS
  let : IsFiniteMeasure ν₁ := hf₁
  let : IsFiniteMeasure ν₂ := hf₂
  have hi₁ := (wholePlane_observation_source_integrability hup hK₁ hν₁ hS (fun _ => ∅)).2.1
  have hi₂ := (wholePlane_observation_source_integrability hup hK₂ hν₂ hS (fun _ => ∅)).2.1
  refine ⟨hi₁.sub hi₂, ?_⟩
  obtain ⟨r, hr⟩ := hS.subset_ball (0 : ℂ)
  have ha₁ := Filter.Eventually.filter_mono (ae_mono (Measure.restrict_mono hr le_rfl))
    (ae_logPotential_of_local_upper_growth hup hK₁ hν₁ r)
  have ha₂ := Filter.Eventually.filter_mono (ae_mono (Measure.restrict_mono hr le_rfl))
    (ae_logPotential_of_local_upper_growth hup hK₂ hν₂ r)
  filter_upwards [ha₁, ha₂] with x h₁ h₂
  exact ⟨h₁.1, h₂.1, h₁.2.1, h₂.2.1,
    signed_wholePlane_potential_at_point h₁.2.1 h₂.2.1 h₁.1 h₂.1⟩

end HarmonicBalls
