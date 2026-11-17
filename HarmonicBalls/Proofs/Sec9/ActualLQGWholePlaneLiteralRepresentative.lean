import HarmonicBalls.Proofs.Sec9.WholePlaneCenterSignedFiniteness
import HarmonicBalls.Proofs.Potential.FiniteSourceDiscCorrection
import HarmonicBalls.Audit.GreenSubharmonicTestClass

/-! # Whole-plane signed tests and bounded representatives

Compactly concentrated whole-plane sources admit disc representatives at the
center and almost everywhere under the actual LQG measure.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set InnerProductSpace
open scoped ENNReal

/-- Integrability of the whole-plane kernel transfers to a disc containing the
compact source, provided the source has no atom at the observation point. -/
theorem integrable_disc_greenFunction_of_wholePlane
    {R : ℝ} {K : Set ℂ} {ν : Measure ℂ} [IsFiniteMeasure ν] {x : ℂ}
    (hR : 0 < R) (hK : IsCompact K) (hKB : K ⊆ ball (0 : ℂ) R)
    (hν : ν Kᶜ = 0) (hx : x ∈ ball (0 : ℂ) R)
    (ha : ν {x} = 0) (hi : Integrable (newtonKernel x) ν) :
    Integrable (greenFunction (ball 0 R) x) ν := by
  have hνae : ∀ᵐ y ∂ν, y ∈ K := ae_iff.mpr hν
  have hne : ∀ᵐ y ∂ν, x ≠ y := by
    rw [ae_iff]
    simpa [eq_comm] using ha
  have hc := integrable_discCorrectionKernel hR hK hKB hν hx
  have heq : greenFunction (ball 0 R) x =ᵐ[ν]
      fun y => newtonKernel x y - greatestHarmonicMinorantBall R y x := by
    filter_upwards [hνae, hne] with y hy hxy
    have h := greenPotential_univ_dirac_eq_ball_add_harmonic_of_ne hR (hKB hy) hx hxy
    simp only [greenPotential, integral_dirac, greenFunction_univ_eq_newtonKernel] at h
    linarith
  exact (hi.sub hc).congr heq.symm

/-- A whole-plane literal signed test with finite center parts has a bounded
representative on the common actual LQG event. -/
theorem IsWholePlaneGFF.ae_wholePlane_literal_signed_bounded_representative
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ) :
    ∀ᵐ ω ∂P, ∀ (Λ K : Set ℂ) (z : ℂ) (ν₁ ν₂ : Measure ℂ)
      (q f : ℂ → ℝ), IsOpen Λ → Bornology.IsBounded Λ → z ∈ Λ →
      IsCompact K → IsFiniteMeasure ν₁ → IsFiniteMeasure ν₂ →
      ν₁ Kᶜ = 0 → ν₂ Kᶜ = 0 → ν₁ Λ = 0 → HarmonicOnNhd q univ →
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
  intro Λ K z ν₁ ν₂ q f hΛ hΛb hz hK hf₁ hf₂ hν₁ hν₂ hνΛ hq hp₁ hn₁ hp₂ hn₂ hrep
  let : IsFiniteMeasure ν₁ := hf₁
  let : IsFiniteMeasure ν₂ := hf₂
  obtain ⟨r, hr⟩ := (hΛb.closure.union hK.isBounded).subset_ball (0 : ℂ)
  let R : ℝ := max r 1
  have hR : 0 < R := lt_of_lt_of_le (by norm_num) (le_max_right r 1)
  have hsub : closure Λ ∪ K ⊆ ball (0 : ℂ) R :=
    hr.trans (ball_subset_ball (le_max_left r 1))
  have hΛR : closure Λ ⊆ ball (0 : ℂ) R := subset_union_left.trans hsub
  have hKR : K ⊆ ball (0 : ℂ) R := subset_union_right.trans hsub
  have hzR : z ∈ ball (0 : ℂ) R := hΛR (subset_closure hz)
  have hν₁ae : ∀ᵐ y ∂ν₁, y ∈ ball (0 : ℂ) R := (ae_iff.mpr hν₁).mono hKR
  have hν₂ae : ∀ᵐ y ∂ν₂, y ∈ ball (0 : ℂ) R := (ae_iff.mpr hν₂).mono hKR
  obtain ⟨ha₁, ha₂, hi₁, hi₂, he₁, he₂⟩ :=
    signed_wholePlane_potential_of_parts_lt_top hp₁ hn₁ hp₂ hn₂
  have hib₁ := integrable_disc_greenFunction_of_wholePlane hR hK hKR hν₁ hzR ha₁ hi₁
  have hib₂ := integrable_disc_greenFunction_of_wholePlane hR hK hKR hν₂ hzR ha₂ hi₂
  have hc₁ := greenPotential_univ_eq_ball_add_discSourceCorrection hR hν₁ae hzR ha₁
    (by simpa only [greenFunction_univ_eq_newtonKernel] using hi₁) hib₁
  have hc₂ := greenPotential_univ_eq_ball_add_discSourceCorrection hR hν₂ae hzR ha₂
    (by simpa only [greenFunction_univ_eq_newtonKernel] using hi₂) hib₂
  let Q := q + discSourceCorrection R ν₁ - discSourceCorrection R ν₂
  let g := Q + greenPotential (ball 0 R) ν₁ - greenPotential (ball 0 R) ν₂
  have hQ : HarmonicOnNhd Q (ball 0 R) :=
    ((hq.mono (subset_univ _)).add (harmonicOnNhd_discSourceCorrection hR hK hKR hν₁)).sub
      (harmonicOnNhd_discSourceCorrection hR hK hKR hν₂)
  have hmem : g ∈ boundedSubharmonicBallTestClass Λ z :=
    ⟨ball 0 R, K, ν₁, ν₂, Q, isOpen_ball, isBounded_ball, hΛR, hK, hKR,
      hf₁, hf₂, hν₁, hν₂, hνΛ, hQ, ha₂, hib₂, rfl⟩
  refine ⟨g, hmem, ?_, ?_⟩
  · rw [hrep z (mem_union_right _ (mem_singleton z)), he₁, he₂]
    simp only [EReal.toReal_coe, g, Q, Pi.add_apply, Pi.sub_apply]
    linarith
  · have hae := (hp K K Λ ν₁ ν₂ hK hK hν₁ hν₂ hf₁ hf₂ hΛb).2
    filter_upwards [hae, ae_restrict_mem hΛ.measurableSet] with x hx hxΛ
    have hxR : x ∈ ball (0 : ℂ) R := hΛR (subset_closure hxΛ)
    have hb₁ := integrable_disc_greenFunction_of_wholePlane hR hK hKR hν₁ hxR hx.2.2.1 hx.1
    have hb₂ := integrable_disc_greenFunction_of_wholePlane hR hK hKR hν₂ hxR hx.2.2.2.1 hx.2.1
    have h₁ := greenPotential_univ_eq_ball_add_discSourceCorrection hR hν₁ae hxR hx.2.2.1
      (by simpa only [greenFunction_univ_eq_newtonKernel] using hx.1) hb₁
    have h₂ := greenPotential_univ_eq_ball_add_discSourceCorrection hR hν₂ae hxR hx.2.2.2.1
      (by simpa only [greenFunction_univ_eq_newtonKernel] using hx.2.1) hb₂
    rw [hrep x (mem_union_left _ hxΛ), hx.2.2.2.2.2.2.2.2.1, hx.2.2.2.2.2.2.2.2.2]
    simp only [EReal.toReal_coe, g, Q, Pi.add_apply, Pi.sub_apply]
    linarith

end HarmonicBalls
