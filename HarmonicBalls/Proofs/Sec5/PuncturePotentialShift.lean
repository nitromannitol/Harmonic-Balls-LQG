import HarmonicBalls.Proofs.Sec5.PuncturedDiscRemovalReduction
import HarmonicBalls.Proofs.Sec3.Basic

/-! # Point removal after the Green-potential shift

Adding the Green potential converts the measure-valued Laplacian bound into
superharmonicity. This reduces the puncture comparison to the corresponding
point-removal result for a zero right-hand side.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Laplacian

/-- A function satisfies the measure-valued Laplacian inequality precisely
when its sum with a potential of that measure has nonpositive Laplacian. -/
theorem laplacianLE_iff_add_potential {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {U : Set ℂ} {w q : ℂ → ℝ} (hq : HasLaplacian q 0 μ U) :
    LaplacianLE w μ U ↔ LaplacianLE (fun x => w x + q x) 0 U := by
  have := hμ
  have hφμ : ∀ φ : ℂ → ℝ, IsTestFunction U φ → Integrable φ μ := fun φ hφ =>
    hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1
  have hqΔ : ∀ φ : ℂ → ℝ, IsTestFunction U φ →
      ∫ x, q x * Δ φ x = -∫ x, φ x ∂μ := fun φ hφ => by
    have h := (hq.2 φ hφ).2.2
    rw [integral_zero_measure, zero_sub] at h
    exact h
  constructor
  · intro hw
    refine ⟨hw.1.add hq.1, fun φ hφ hφ0 _ => ?_⟩
    have h := hw.2 φ hφ hφ0 (hφμ φ hφ)
    have he : (fun x => (w x + q x) * Δ φ x) =
        fun x => w x * Δ φ x + q x * Δ φ x := by
      funext x
      ring
    rw [integral_zero_measure, he, integral_add (integrable_mul_laplacian_of_test hw.1 hφ)
      (integrable_mul_laplacian_of_test hq.1 hφ), hqΔ φ hφ]
    linarith
  · intro hwq
    have he : (fun x => (w x + q x) - q x) = w := funext fun x => add_sub_cancel_right _ _
    have hwloc : LocallyIntegrableOn w U := he ▸ hwq.1.sub hq.1
    refine ⟨hwloc, fun φ hφ hφ0 _ => ?_⟩
    have h := hwq.2 φ hφ hφ0 integrable_zero_measure
    rw [integral_zero_measure] at h
    have he' : (fun x => (w x + q x) * Δ φ x) =
        fun x => w x * Δ φ x + q x * Δ φ x := by
      funext x
      ring
    rw [he', integral_add (integrable_mul_laplacian_of_test hwloc hφ)
      (integrable_mul_laplacian_of_test hq.1 hφ), hqΔ φ hφ] at h
    linarith

/-- Restricting the domain preserves a distributional Laplacian identity. -/
theorem HasLaplacian.mono_domain {w : ℂ → ℝ} {μ ν : Measure ℂ} {U V : Set ℂ}
    (h : HasLaplacian w μ ν U) (hVU : V ⊆ U) : HasLaplacian w μ ν V := by
  refine ⟨h.1.mono_set hVU, fun φ hφ => h.2 φ ⟨hφ.1, hφ.2.1, hφ.2.2.trans hVU⟩⟩

/-- The measure-valued point-removal step follows from point removal for the
zero-Laplacian inequality and the continuous Green potential. -/
theorem laplacianLE_punctured_disc_of_zero_point_removal
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ} {a : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    (hremove : ∀ v : ℂ → ℝ, ContinuousOn v (ball (0 : ℂ) R) →
      LaplacianLE v 0 (ball (0 : ℂ) R \ {a}) → LaplacianLE v 0 (ball 0 R))
    {w : ℂ → ℝ} (hwc : ContinuousOn w (ball (0 : ℂ) R))
    (hw : LaplacianLE w μ (ball (0 : ℂ) R \ {a})) :
    LaplacianLE w μ (ball 0 R) := by
  let q := greenPotentialBall μ R
  have hqc : ContinuousOn q (ball (0 : ℂ) R) :=
    (greenPotentialBallContinuousStep_holds μ hμ R βm βp hR hV).mono ball_subset_closedBall
  have hq : HasLaplacian q 0 μ (ball (0 : ℂ) R) :=
    greenPotentialBallLaplacianStep_holds μ hμ R βm βp hR hV
  have hp := (laplacianLE_iff_add_potential hμ (hq.mono_domain sdiff_subset)).mp hw
  exact (laplacianLE_iff_add_potential hμ hq).mpr (hremove _ (hwc.add hqc) hp)

/-- Under zero-Laplacian point removal, the punctured cluster is the disc
cluster with the puncture deleted. -/
theorem clusterOn_punctured_disc_eq_sdiff_of_zero_point_removal
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z a : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    (ha : a ∈ ball (0 : ℂ) R) (hz : z ∈ ball (0 : ℂ) R \ {a}) (ht : 0 < t)
    (hremove : ∀ v : ℂ → ℝ, ContinuousOn v (ball (0 : ℂ) R) →
      LaplacianLE v 0 (ball (0 : ℂ) R \ {a}) → LaplacianLE v 0 (ball 0 R)) :
    clusterOn μ (ball (0 : ℂ) R \ {a}) z t = cluster μ R z t \ {a} := by
  apply clusterOn_punctured_disc_eq_sdiff_of_point_removal hμ hR hV ha hz ht
  intro w hw
  apply laplacianLE_punctured_disc_of_zero_point_removal hμ hR hV hremove
  · exact hw.1.mono (by rw [closure_punctured_disc ha]; exact ball_subset_closedBall)
  · exact hw.2.1

#print axioms laplacianLE_iff_add_potential
#print axioms HasLaplacian.mono_domain
#print axioms laplacianLE_punctured_disc_of_zero_point_removal
#print axioms clusterOn_punctured_disc_eq_sdiff_of_zero_point_removal

end HarmonicBalls
