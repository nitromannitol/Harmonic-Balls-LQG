import HarmonicBalls.Proofs.Potential.DiscSourceFreeHarmonicity
import HarmonicBalls.Proofs.Potential.TranslatedDiscFiniteSourceLaplacian
import HarmonicBalls.Proofs.Potential.BoundedSubharmonicRepresentatives
import HarmonicBalls.Proofs.Sec5.PuncturePotentialShift
import HarmonicBalls.Proofs.Sec3.ClusterCompatibility

/-! # Source-free potentials on translated discs

This analytic step uses the potential-theoretic work of Leonardo Bonanno.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter InnerProductSpace
open HarmonicBalls.Section6
open Laplacian
open scoped Topology

/-- A finite compactly concentrated source has a continuous Green potential
on a source-free open subset of a translated disc. -/
theorem continuousOn_greenPotential_translatedDisc_of_source_free_open
    {c : ℂ} {R : ℝ} {K U : Set ℂ} {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hK : IsCompact K) (hKB : K ⊆ ball c R) (hν : ν Kᶜ = 0)
    (hU : IsOpen U) (hUB : U ⊆ ball c R) (hνU : ν U = 0) :
    ContinuousOn (greenPotential (ball c R) ν) U := by
  let e : ℂ ≃ₜ ℂ := Homeomorph.subRight c
  let K₀ := e '' K
  let U₀ := e '' U
  let ν₀ := ν.map e
  have hK₀ : IsCompact K₀ := hK.image e.continuous
  have hU₀ : IsOpen U₀ := e.isOpenMap U hU
  have hK₀B : K₀ ⊆ ball (0 : ℂ) R := by
    rintro x ⟨y, hy, rfl⟩
    simpa [e, mem_ball, dist_eq_norm] using hKB hy
  have hU₀B : U₀ ⊆ ball (0 : ℂ) R := by
    rintro x ⟨y, hy, rfl⟩
    simpa [e, mem_ball, dist_eq_norm] using hUB hy
  have heK : e ⁻¹' K₀ = K := e.injective.preimage_image K
  have heU : e ⁻¹' U₀ = U := e.injective.preimage_image U
  have hν₀K : ν₀ K₀ᶜ = 0 := by
    rw [Measure.map_apply e.measurable hK₀.isClosed.measurableSet.compl]
    simpa only [preimage_compl, heK] using hν
  have hν₀U : ν₀ U₀ = 0 := by
    rw [Measure.map_apply e.measurable hU₀.measurableSet, heU]
    exact hνU
  have hc := continuousOn_greenPotential_ball_of_source_free_open
    hK₀ hK₀B hν₀K hU₀ hU₀B hν₀U
  intro x hx
  have hx₀ : e x ∈ U₀ := ⟨x, hx, rfl⟩
  have hcont := (hc (e x) hx₀).continuousAt (hU₀.mem_nhds hx₀)
  have hcomp := hcont.comp e.continuous.continuousAt
  have hp : (fun z => greenPotential (ball 0 R) ν₀ (e z)) =
      greenPotential (ball c R) ν := by
    funext z
    have h := greenPotential_translate (O := ball (0 : ℂ) R) isOpen_ball ν c (z - c)
    simpa [e, ν₀] using h.symm
  change ContinuousAt (fun z => greenPotential (ball 0 R) ν₀ (e z)) x at hcomp
  rw [hp] at hcomp
  exact hcomp.continuousWithinAt

/-- On a source-free observation set, the distributional Laplacian of a
harmonic correction plus one potential minus another is the restricted
negative source. -/
theorem hasLaplacian_changedSource_on_source_free
    {U V : Set ℂ} {η₁ η₂ : Measure ℂ} {q p₁ p₂ : ℂ → ℝ}
    (hU : IsOpen U) (hUV : U ⊆ V) (hzero : η₁ U = 0)
    (hq : HarmonicOnNhd q V) (h₁ : HasLaplacian p₁ 0 η₁ V)
    (h₂ : HasLaplacian p₂ 0 η₂ V) :
    HasLaplacian (q + p₁ - p₂) (η₂.restrict U) 0 U := by
  have hq' := hasLaplacian_zero_of_harmonicOnNhd hU (hq.mono hUV)
  have h₁' := h₁.mono_domain hUV
  have h₂' := h₂.mono_domain hUV
  refine ⟨(hq'.1.add h₁'.1).sub h₂'.1, ?_⟩
  intro φ hφ
  have hφout : ∀ x, x ∉ U → φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun ht => hx (hφ.2.2 ht))
  have hrestrict : ∀ μ : Measure ℂ, (∫ x in U, φ x ∂μ) = ∫ x, φ x ∂μ :=
    fun μ => setIntegral_eq_integral_of_forall_compl_eq_zero hφout
  have hzero' : (∫ x, φ x ∂η₁) = 0 := by
    rw [← hrestrict η₁, Measure.restrict_eq_zero.mpr hzero, integral_zero_measure]
  have hqφ := (hq'.2 φ hφ).2.2
  have h₁φ := (h₁'.2 φ hφ).2.2
  have h₂φ := (h₂'.2 φ hφ).2.2
  simp only [integral_zero_measure, zero_sub, sub_zero] at hqφ h₁φ h₂φ ⊢
  refine ⟨(h₂'.2 φ hφ).2.1.mono_measure Measure.restrict_le_self,
    integrable_zero_measure, ?_⟩
  have heq : (fun x => (q + p₁ - p₂) x * Δ φ x) =
      fun x => (q x * Δ φ x + p₁ x * Δ φ x) - p₂ x * Δ φ x := by
    funext x
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  rw [heq]
  change (∫ x, ((fun x => q x * Δ φ x) + (fun x => p₁ x * Δ φ x)) x -
    (fun x => p₂ x * Δ φ x) x) = ∫ x in U, φ x ∂η₂
  rw [integral_sub ((integrable_mul_laplacian_of_test hq'.1 hφ).add
    (integrable_mul_laplacian_of_test h₁'.1 hφ))
    (integrable_mul_laplacian_of_test h₂'.1 hφ)]
  simp only [Pi.add_apply]
  rw [integral_add (integrable_mul_laplacian_of_test hq'.1 hφ)
      (integrable_mul_laplacian_of_test h₁'.1 hφ), hqφ, h₁φ, h₂φ,
    hzero', hrestrict]
  ring

/-- No compactly concentrated finite sources on a disc can represent the
negative whole-plane point potential on the radius-two observation disc. -/
theorem no_changed_source_translatedDisc_for_large_observation
    {c : ℂ} {R : ℝ} {K₁ K₂ : Set ℂ} {η₁ η₂ : Measure ℂ} {q : ℂ → ℝ}
    [IsFiniteMeasure η₁] [IsFiniteMeasure η₂]
    (hsub : ball (0 : ℂ) 2 ⊆ ball c R)
    (hK₁ : IsCompact K₁) (hK₁V : K₁ ⊆ ball c R) (hη₁K : η₁ K₁ᶜ = 0)
    (hK₂ : IsCompact K₂) (hK₂V : K₂ ⊆ ball c R) (hη₂K : η₂ K₂ᶜ = 0)
    (hzero : η₁ (ball 0 2) = 0) (hq : HarmonicOnNhd q (ball c R)) :
    ¬ (∀ᵐ x ∂(volume + Measure.dirac (0 : ℂ)).restrict (ball 0 (2 : ℝ)),
      -greenPotential univ (Measure.dirac 0) x =
        q x + greenPotential (ball c R) η₁ x - greenPotential (ball c R) η₂ x) := by
  have h0 : (0 : ℂ) ∈ ball 0 (2 : ℝ) := mem_ball_self (by norm_num)
  have hR : 0 < R := lt_of_le_of_lt dist_nonneg (hsub h0)
  have hη₁V : ∀ᵐ y ∂η₁, y ∈ ball c R := (ae_iff.mpr hη₁K).mono hK₁V
  have hη₂V : ∀ᵐ y ∂η₂, y ∈ ball c R := (ae_iff.mpr hη₂K).mono hK₂V
  have hΔ := hasLaplacian_changedSource_on_source_free isOpen_ball hsub hzero hq
    (hasLaplacian_translatedDisc_greenPotential hR hη₁V)
    (hasLaplacian_translatedDisc_greenPotential hR hη₂V)
  intro heq
  have hvol : -greenPotential univ (Measure.dirac (0 : ℂ)) =ᵐ[
      volume.restrict (ball 0 (2 : ℝ))]
      (q + greenPotential (ball c R) η₁ - greenPotential (ball c R) η₂) := by
    rw [Measure.restrict_add, ae_add_measure_iff] at heq
    exact heq.1
  have hres := negative_source_residual_null_of_ae_and_hasLaplacian
    isOpen_ball h0 (inferInstance : IsLocallyFiniteMeasure η₂) hΔ hvol
  have hresK : (η₂.restrict {0}ᶜ) K₂ᶜ = 0 :=
    le_antisymm (((Measure.restrict_le_self : η₂.restrict {0}ᶜ ≤ η₂) K₂ᶜ).trans_eq hη₂K)
      bot_le
  have h₁c := continuousOn_greenPotential_translatedDisc_of_source_free_open
    hK₁ hK₁V hη₁K isOpen_ball hsub hzero
  have h₂c := continuousOn_greenPotential_translatedDisc_of_source_free_open
    hK₂ hK₂V hresK isOpen_ball hsub hres
  exact no_changed_source_of_local_riesz_for_large_observation isOpen_ball isBounded_ball
    hsub hK₂ hK₂V inferInstance hη₂K hq
    (h₁c.continuousAt (isOpen_ball.mem_nhds h0))
    (h₂c.continuousAt (isOpen_ball.mem_nhds h0)) hΔ heq


end HarmonicBalls
