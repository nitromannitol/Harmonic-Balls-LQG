import HarmonicBalls.Proofs.Potential.TranslatedDiscFiniteSourceLaplacian
import HarmonicBalls.Proofs.Potential.TranslatedFiniteSourceDiscCorrection
import HarmonicBalls.Proofs.Potential.BoundedSubharmonicRepresentatives
import HarmonicBalls.Proofs.Sec3.ClusterCompatibility

/-! # Whole-plane potentials of finite compactly supported measures

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Laplacian InnerProductSpace

private theorem wholePlane_on_disc {ν : Measure ℂ} [IsFiniteMeasure ν]
    {K : Set ℂ} {R : ℝ} (hR : 0 < R) (hK : IsCompact K)
    (hKB : K ⊆ ball (0 : ℂ) R) (hν : ν Kᶜ = 0) :
    HasLaplacian (greenPotential univ ν) 0 ν (ball 0 R) := by
  have hνK : ∀ᵐ y ∂ν, y ∈ K := by
    rw [ae_iff]
    exact hν
  have hνB : ∀ᵐ y ∂ν, y ∈ ball (0 : ℂ) R := hνK.mono fun _ hy => hKB hy
  have hp := hasLaplacian_translatedDisc_greenPotential hR hνB
  have hh := hasLaplacian_zero_of_harmonicOnNhd isOpen_ball
    (harmonicOnNhd_translatedDiscSourceCorrection hR hK hKB hν)
  have hs : HasLaplacian (greenPotential (ball 0 R) ν +
      translatedDiscSourceCorrection 0 R ν) 0 ν (ball 0 R) := by
    refine ⟨hp.1.add hh.1, fun φ hφ => ?_⟩
    obtain ⟨h₁, h₂, h₃⟩ := hp.2 φ hφ
    have h₄ := (hh.2 φ hφ).2.2
    rw [integral_zero_measure, sub_zero] at h₄
    refine ⟨h₁, h₂, ?_⟩
    have he : (fun x => (greenPotential (ball 0 R) ν +
        translatedDiscSourceCorrection 0 R ν) x * Δ φ x) =
        (fun x => greenPotential (ball 0 R) ν x * Δ φ x +
          translatedDiscSourceCorrection 0 R ν x * Δ φ x) := by
      funext x
      simp only [Pi.add_apply, add_mul]
    rw [he, integral_add (integrable_mul_laplacian_of_test hp.1 hφ)
      (integrable_mul_laplacian_of_test hh.1 hφ), h₄, add_zero]
    exact h₃
  apply hs.congr_ae_restrict_volume measurableSet_ball
  filter_upwards [ae_greenPotential_univ_eq_translatedDisc_add_correction hR hνB] with x hx
  exact hx.2.2.2.symm

/-- The whole-plane Green potential of a compactly carried finite measure has
its negative as distributional Laplacian, including its atomic part. -/
theorem hasLaplacian_wholePlane_greenPotential {ν : Measure ℂ} [IsFiniteMeasure ν]
    {K : Set ℂ} (hK : IsCompact K) (hν : ν Kᶜ = 0) :
    HasLaplacian (greenPotential univ ν) 0 ν univ := by
  constructor
  · intro x hx
    obtain ⟨R, hR, hsub⟩ := (hK.union isCompact_singleton).isBounded.subset_ball_lt 0 (0 : ℂ)
    have hloc := (wholePlane_on_disc hR hK (subset_union_left.trans hsub) hν).1
    have hxB : x ∈ ball (0 : ℂ) R := hsub (mem_union_right _ (mem_singleton x))
    have h := hloc x hxB
    rw [nhdsWithin_eq_nhds.2 (isOpen_ball.mem_nhds hxB)] at h
    simpa only [nhdsWithin_univ] using h
  · intro φ hφ
    obtain ⟨R, hR, hsub⟩ := (hK.union hφ.2.1).isBounded.subset_ball_lt 0 (0 : ℂ)
    have hlocal := wholePlane_on_disc hR hK (subset_union_left.trans hsub) hν
    exact hlocal.2 φ ⟨hφ.1, hφ.2.1, subset_union_right.trans hsub⟩


end HarmonicBalls
