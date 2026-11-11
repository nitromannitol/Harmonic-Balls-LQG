import HarmonicBalls.Proofs.Potential.TransposedChangedSourceObstruction
import HarmonicBalls.Proofs.Potential.UnrestrictedSourceTransposedGreenLaplacian
import HarmonicBalls.Proofs.Sec6.GreenTranslation

/-! # Translated obstruction for unrestricted transposed sources

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
The first argument of the Green kernel is the source.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Laplacian InnerProductSpace
open HarmonicBalls.Section6

/-- No finite sources can give this transposed representation on an observation
measure charging both the disc and its centre. -/
theorem no_transposed_changed_source_for_translated_observation
    {V : Set ℂ} {η₁ η₂ : Measure ℂ} {q : ℂ → ℝ} (z : ℂ)
    [IsFiniteMeasure η₁] [IsFiniteMeasure η₂]
    (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (hsub : ball z 2 ⊆ V) (hzero : η₁ (ball z 2) = 0)
    (hq : HarmonicOnNhd q V) :
    ¬ (∀ᵐ x ∂(volume + Measure.dirac z).restrict (ball z (2 : ℝ)),
      -greenPotential univ (Measure.dirac z) x =
        q x + (∫ y, greenFunction V y x ∂η₁) - (∫ y, greenFunction V y x ∂η₂)) := by
  classical
  let e : ℂ ≃ᵐ ℂ := MeasurableEquiv.subRight z
  let V₀ : Set ℂ := (fun x : ℂ => x + z) ⁻¹' V
  have hV₀ : IsOpen V₀ := hV.preimage (by fun_prop)
  have himage : (fun x : ℂ => x + z) '' V₀ = V := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨x - z, by simpa [V₀] using hx, by simp⟩
  have hV₀b : Bornology.IsBounded V₀ := by
    obtain ⟨r, hr⟩ := hVb.subset_ball z
    apply (isBounded_ball : Bornology.IsBounded (ball (0 : ℂ) r)).subset
    intro x hx
    have hh := hr hx
    simpa [mem_ball, dist_eq_norm] using hh
  have hball : e ⁻¹' ball (0 : ℂ) 2 = ball z 2 := by
    ext x
    change x - z ∈ ball (0 : ℂ) 2 ↔ x ∈ ball z 2
    simp [mem_ball, dist_eq_norm]
  have hsub₀ : ball (0 : ℂ) 2 ⊆ V₀ := by
    intro x hx
    apply hsub
    simpa [mem_ball, dist_eq_norm] using hx
  let ν₁ := (η₁.restrict V).map e
  let ν₂ := (η₂.restrict V).map e
  have hνV (η : Measure ℂ) : ((η.restrict V).map e) V₀ᶜ = 0 := by
    rw [Measure.map_apply e.measurable hV₀.measurableSet.compl]
    have hp : e ⁻¹' V₀ᶜ = Vᶜ := by
      ext x
      change ¬(x - z + z ∈ V) ↔ x ∉ V
      simp
    rw [hp, Measure.restrict_apply hV.measurableSet.compl]
    simp
  have hνzero : ν₁ (ball 0 2) = 0 := by
    dsimp only [ν₁]
    rw [Measure.map_apply e.measurable measurableSet_ball, hball]
    exact le_antisymm (((Measure.restrict_le_self : η₁.restrict V ≤ η₁) _).trans_eq hzero) bot_le
  have hq₀ : HarmonicOnNhd (fun x => q (x + z)) V₀ := by
    intro x hx
    exact harmonicAt_comp_add_right (hq (x + z) hx)
  have hobs : ((volume + Measure.dirac z).restrict (ball z (2 : ℝ))).map e =
      (volume + Measure.dirac (0 : ℂ)).restrict (ball 0 (2 : ℝ)) := by
    have hm : (volume + Measure.dirac z).map e = volume + Measure.dirac (0 : ℂ) := by
      rw [Measure.map_add _ _ e.measurable]
      have hv : volume.map e = volume := by
        change volume.map (fun x : ℂ => x - z) = volume
        simpa [sub_eq_add_neg] using map_add_right_eq_self (volume : Measure ℂ) (-z)
      rw [hv, Measure.map_dirac' e.measurable]
      change volume + Measure.dirac (z - z) = volume + Measure.dirac 0
      simp
    calc
      _ = ((volume + Measure.dirac z).restrict (e ⁻¹' ball (0 : ℂ) 2)).map e := by rw [hball]
      _ = ((volume + Measure.dirac z).map e).restrict (ball 0 2) := (e.restrict_map _ _).symm
      _ = _ := by rw [hm]
  have hk (η : Measure ℂ) (x : ℂ) :
      (∫ y, greenFunction V₀ y x ∂((η.restrict V).map e)) =
      ∫ y, greenFunction V y (x + z) ∂η := by
    rw [integral_map_equiv e]
    rw [← transposedGreen_integral_restrict_source (x + z) η]
    apply integral_congr_ae
    filter_upwards [] with y
    have ht := greenFunction_translate V₀ z (y - z) x
    change greenFunction V₀ (y - z) x = greenFunction V y (x + z)
    simpa [himage] using ht.symm
  have hp (x : ℂ) : greenPotential univ (Measure.dirac z) (x + z) =
      greenPotential univ (Measure.dirac 0) x := by
    simp only [greenPotential, integral_dirac, greenFunction_univ_eq_newtonKernel]
    simpa using newtonKernel_translate x 0 z
  intro heq
  apply no_transposed_changed_source_for_large_observation hV₀ hV₀b hsub₀
    (hνV η₁) (hνV η₂) hνzero hq₀
  have heq₀ : ∀ᵐ x ∂((volume + Measure.dirac z).restrict (ball z (2 : ℝ))).map e,
      -greenPotential univ (Measure.dirac 0) x =
        q (x + z) + (∫ y, greenFunction V₀ y x ∂ν₁) -
          (∫ y, greenFunction V₀ y x ∂ν₂) := by
    apply e.measurableEmbedding.ae_map_iff.mpr
    filter_upwards [heq] with x hx
    change -greenPotential univ (Measure.dirac 0) (x - z) =
      q (x - z + z) + (∫ y, greenFunction V₀ y (x - z) ∂((η₁.restrict V).map e)) -
        (∫ y, greenFunction V₀ y (x - z) ∂((η₂.restrict V).map e))
    rw [hk η₁, hk η₂, ← hp (x - z)]
    simpa only [sub_add_cancel] using hx
  simpa only [hobs] using heq₀


end HarmonicBalls
