import HarmonicBalls.Proofs.Potential.DiscFiniteSourceLaplacian
import HarmonicBalls.Proofs.Sec6.GreenTranslation

/-! # Finite-source Green potentials on translated discs

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/

namespace HarmonicBalls
open MeasureTheory Metric Set Laplacian
open HarmonicBalls.Section6

private theorem image_ball_translate (c : ℂ) (R : ℝ) :
    (fun z : ℂ => z + c) '' ball 0 R = ball c R := by
  simp

private theorem potential_translate_ball (ν : Measure ℂ) (c x : ℂ) (R : ℝ) :
    greenPotential (ball c R) ν (x + c) =
      greenPotential (ball 0 R) (ν.map (fun z => z - c)) x := by
  simpa only [image_ball_translate] using
    greenPotential_translate (O := ball 0 R) isOpen_ball ν c x

/-- A finite-source Green potential is integrable on any disc when the source
is concentrated in its closure. -/
theorem integrableOn_translatedDisc_greenPotential {ν : Measure ℂ} [IsFiniteMeasure ν]
    {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hν : ∀ᵐ y ∂ν, y ∈ closedBall c R) :
    IntegrableOn (greenPotential (ball c R) ν) (ball c R) := by
  let ν₀ := ν.map (fun z : ℂ => z - c)
  have hν₀ : ∀ᵐ y ∂ν₀, y ∈ closedBall (0 : ℂ) R := by
    apply (ae_map_iff (by fun_prop) measurableSet_closedBall).2
    filter_upwards [hν] with y hy
    simpa only [mem_closedBall, dist_eq_norm, sub_zero] using hy
  have h := integrableOn_disc_greenPotential (ν := ν₀) hR hν₀
  have hp : MeasurePreserving (fun z : ℂ => z + c) volume volume :=
    ⟨(by fun_prop), map_add_right_eq_self volume c⟩
  have ht := (hp.integrableOn_image (MeasurableEquiv.addRight c).measurableEmbedding
    (f := greenPotential (ball c R) ν) (s := ball 0 R)).2 (by
      simpa only [Function.comp_def, potential_translate_ball] using h)
  simpa only [image_ball_translate] using ht

/-- The distributional Laplacian includes arbitrary atoms in the source. -/
theorem hasLaplacian_translatedDisc_greenPotential {ν : Measure ℂ} [IsFiniteMeasure ν]
    {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hν : ∀ᵐ y ∂ν, y ∈ ball c R) :
    HasLaplacian (greenPotential (ball c R) ν) 0 ν (ball c R) := by
  let ν₀ := ν.map (fun z : ℂ => z - c)
  have hν₀ : ∀ᵐ y ∂ν₀, y ∈ ball (0 : ℂ) R := by
    apply (ae_map_iff (by fun_prop) measurableSet_ball).2
    filter_upwards [hν] with y hy
    simpa only [mem_ball, dist_eq_norm, sub_zero] using hy
  have h := hasLaplacian_disc_greenPotential (ν := ν₀) hR hν₀
  refine ⟨(integrableOn_translatedDisc_greenPotential hR
    (hν.mono fun _ hy => ball_subset_closedBall hy)).locallyIntegrableOn, ?_⟩
  intro φ hφ
  let ψ : ℂ → ℝ := fun x => φ (x + c)
  have hψ : IsTestFunction (ball 0 R) ψ := by
    refine ⟨hφ.1.comp (by fun_prop), hφ.2.1.comp_homeomorph (Homeomorph.addRight c), ?_⟩
    rw [show tsupport ψ = (fun z : ℂ => z + c) ⁻¹' tsupport φ from
      tsupport_comp_eq_preimage φ (Homeomorph.addRight c)]
    intro x hx
    have hx' := hφ.2.2 hx
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using hx'
  have ht := h.2 ψ hψ
  refine ⟨integrable_zero_measure, hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1, ?_⟩
  have hp : MeasurePreserving (fun z : ℂ => z + c) volume volume :=
    ⟨(by fun_prop), map_add_right_eq_self volume c⟩
  have hleft := hp.integral_comp (MeasurableEquiv.addRight c).measurableEmbedding
    (fun x => greenPotential (ball c R) ν x * Δ φ x)
  have hright : (∫ x, ψ x ∂ν₀) = ∫ x, φ x ∂ν := by
    rw [integral_map (by fun_prop) hψ.1.continuous.aestronglyMeasurable]
    simp only [ψ, sub_add_cancel]
  rw [integral_zero_measure, zero_sub] at ht ⊢
  rw [← hleft, ← hright]
  simpa only [ψ, potential_translate_ball, laplacian_comp_add_right] using ht.2.2


end HarmonicBalls
