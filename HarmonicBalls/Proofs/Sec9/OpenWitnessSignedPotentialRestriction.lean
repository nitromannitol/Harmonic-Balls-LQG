import HarmonicBalls.Proofs.Sec9.ActualLQGWholePlaneLiteralRepresentative
import HarmonicBalls.Proofs.Potential.GeneralDomainObservationCorrection
import HarmonicBalls.Proofs.Potential.FiniteDiscGreenReciprocity

/-! # Restriction of whole-plane potentials

Finite whole-plane sources admit harmonic corrections on bounded open sets.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set InnerProductSpace
open scoped ENNReal

/-- On a bounded open set, a finite compact source has one harmonic correction
at every uncharged point where the Newton kernel is integrable. -/
theorem exists_harmonic_wholePlane_correction_on_bounded_open
    {V K : Set ℂ} {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (hK : IsCompact K) (hKV : K ⊆ V) (hν : ν Kᶜ = 0) :
    ∃ H : ℂ → ℝ, HarmonicOnNhd H V ∧
      ∀ x ∈ V, ν {x} = 0 → Integrable (newtonKernel x) ν →
        Integrable (greenFunction V x) ν ∧
        greenPotential univ ν x = greenPotential V ν x + H x := by
  obtain ⟨r, hr⟩ := hVb.subset_ball (0 : ℂ)
  let R := max r 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hVR : V ⊆ ball (0 : ℂ) R := hr.trans (ball_subset_ball (le_max_left _ _))
  obtain ⟨H, hH, hcorr⟩ :=
    exists_harmonic_generalDomain_transposed_correction_pointwise hV hVb hK hKV hν
  refine ⟨H, hH, ?_⟩
  intro x hx ha hi
  have hib := integrable_disc_greenFunction_of_wholePlane hR hK (hKV.trans hVR)
    hν (hVR hx) ha hi
  have hiv := Section6.integrable_greenFunction_of_subset hV hVR isBounded_ball ν x hib
  have hit : Integrable (fun y => greenFunction V y x) ν := by
    simpa only [greenFunction_bounded_open_comm hV hVb] using hiv
  have hin : Integrable (fun y => newtonKernel y x) ν := by
    simpa only [newtonKernel_comm] using hi
  have heq := hcorr x hx ha hin hit
  have heq' : greenPotential V ν x = greenPotential univ ν x - H x := by
    simpa only [greenPotential, greenFunction_bounded_open_comm hV hVb] using heq
  exact ⟨hiv, by linarith⟩

/-- Whole-plane signed tests admit a representative on any bounded open
neighborhood of the cluster and the compact sources, even when the harmonic
term is only given on a larger open set. -/
theorem IsWholePlaneGFF.ae_wholePlane_signed_representative_on_bounded_open
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ) :
    ∀ᵐ ω ∂P, ∀ (Λ V K : Set ℂ) (z : ℂ) (ν₁ ν₂ : Measure ℂ)
      (q f : ℂ → ℝ), IsOpen Λ → Bornology.IsBounded Λ → z ∈ Λ →
      IsOpen V → Bornology.IsBounded V → closure Λ ⊆ V →
      IsCompact K → K ⊆ V → IsFiniteMeasure ν₁ → IsFiniteMeasure ν₂ →
      ν₁ Kᶜ = 0 → ν₂ Kᶜ = 0 → ν₁ Λ = 0 → HarmonicOnNhd q V →
      (∫⁻ y, (newtonKernelEReal z y).toENNReal ∂ν₁) < ⊤ →
      (∫⁻ y, (-newtonKernelEReal z y).toENNReal ∂ν₁) < ⊤ →
      (∫⁻ y, (newtonKernelEReal z y).toENNReal ∂ν₂) < ⊤ →
      (∫⁻ y, (-newtonKernelEReal z y).toENNReal ∂ν₂) < ⊤ →
      (∀ x ∈ Λ ∪ {z}, f x = q x +
        (extendedSignedIntegral (newtonKernelEReal x) ν₁).toReal -
        (extendedSignedIntegral (newtonKernelEReal x) ν₂).toReal) →
      ∃ g ∈ boundedSubharmonicBallTestClass Λ z,
        f z = g z ∧ f =ᵐ[(μ ω).restrict Λ] g := by
  filter_upwards [hh.ae_singular_signed_wholePlane_potential hγ hγ2 hαQ hμ] with ω hp
  intro Λ V K z ν₁ ν₂ q f hΛ hΛb hz hV hVb hΛV hK hKV hf₁ hf₂ hν₁ hν₂ hνΛ hq hp₁ hn₁ hp₂ hn₂ hrep
  let : IsFiniteMeasure ν₁ := hf₁
  let : IsFiniteMeasure ν₂ := hf₂
  obtain ⟨H₁, hH₁, hc₁⟩ := exists_harmonic_wholePlane_correction_on_bounded_open hV hVb hK hKV hν₁
  obtain ⟨H₂, hH₂, hc₂⟩ := exists_harmonic_wholePlane_correction_on_bounded_open hV hVb hK hKV hν₂
  obtain ⟨ha₁, ha₂, hi₁, hi₂, he₁, he₂⟩ :=
    signed_wholePlane_potential_of_parts_lt_top hp₁ hn₁ hp₂ hn₂
  have hzV : z ∈ V := hΛV (subset_closure hz)
  have hcenter₁ := hc₁ z hzV ha₁ hi₁
  have hcenter₂ := hc₂ z hzV ha₂ hi₂
  let Q := q + H₁ - H₂
  let g := Q + greenPotential V ν₁ - greenPotential V ν₂
  have hQ : HarmonicOnNhd Q V := (hq.add hH₁).sub hH₂
  have hg : g ∈ boundedSubharmonicBallTestClass Λ z :=
    ⟨V, K, ν₁, ν₂, Q, hV, hVb, hΛV, hK, hKV, hf₁, hf₂, hν₁, hν₂,
      hνΛ, hQ, ha₂, hcenter₂.1, rfl⟩
  refine ⟨g, hg, ?_, ?_⟩
  · rw [hrep z (mem_union_right _ (mem_singleton z)), he₁, he₂]
    simp only [EReal.toReal_coe, g, Q, Pi.add_apply, Pi.sub_apply]
    linarith [hcenter₁.2, hcenter₂.2]
  · have hae := (hp K K Λ ν₁ ν₂ hK hK hν₁ hν₂ hf₁ hf₂ hΛb).2
    filter_upwards [hae, ae_restrict_mem hΛ.measurableSet] with x hx hxΛ
    have hxV : x ∈ V := hΛV (subset_closure hxΛ)
    have h₁ := hc₁ x hxV hx.2.2.1 hx.1
    have h₂ := hc₂ x hxV hx.2.2.2.1 hx.2.1
    rw [hrep x (mem_union_left _ hxΛ), hx.2.2.2.2.2.2.2.2.1, hx.2.2.2.2.2.2.2.2.2]
    simp only [EReal.toReal_coe, g, Q, Pi.add_apply, Pi.sub_apply]
    linarith [h₁.2, h₂.2]

end HarmonicBalls
