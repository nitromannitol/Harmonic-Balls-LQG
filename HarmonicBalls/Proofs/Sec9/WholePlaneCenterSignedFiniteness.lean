import HarmonicBalls.Proofs.Sec9.ActualLQGSignedWholePlanePotential
import HarmonicBalls.Proofs.Sec4.GreenAwayFromPole

/-! # Finite signed whole-plane potentials at a point

Finiteness of both extended parts implies that the source has no atom at the
pole and that its Newtonian potential is given by the real integral.
-/

namespace HarmonicBalls

open MeasureTheory Set
open scoped ENNReal

/-- Finite positive and negative parts of the extended Newtonian kernel give
integrability of the real kernel and identify the whole-plane potential. -/
theorem wholePlane_potential_of_parts_lt_top {ν : Measure ℂ} {x : ℂ}
    (hp : (∫⁻ y, (newtonKernelEReal x y).toENNReal ∂ν) < ⊤)
    (hn : (∫⁻ y, (-newtonKernelEReal x y).toENNReal ∂ν) < ⊤) :
    ν {x} = 0 ∧ Integrable (newtonKernel x) ν ∧
      extendedSignedIntegral (newtonKernelEReal x) ν = (greenPotential univ ν x : EReal) := by
  have hatom : ν {x} = 0 := by
    by_contra hne
    have hle : ∫⁻ y, Set.indicator {x} (fun _ => (⊤ : ℝ≥0∞)) y ∂ν ≤
        ∫⁻ y, (newtonKernelEReal x y).toENNReal ∂ν := by
      apply lintegral_mono
      intro y
      by_cases hy : y = x
      · subst hy
        simp [newtonKernelEReal]
      · simp [hy]
    rw [lintegral_indicator_const (measurableSet_singleton x), ENNReal.top_mul hne] at hle
    exact lt_irrefl _ (lt_of_le_of_lt hle hp)
  have hae : ∀ᵐ y ∂ν, y ≠ x := ae_iff.mpr (by simpa using hatom)
  have hp' : (∫⁻ y, ENNReal.ofReal (max (newtonKernel x y) 0) ∂ν) < ⊤ := by
    convert hp using 1
    apply lintegral_congr_ae
    filter_upwards [hae] with y hy
    simp [newtonKernelEReal, hy, EReal.toENNReal, ENNReal.ofReal_max]
  have hn' : (∫⁻ y, ENNReal.ofReal (max (-newtonKernel x y) 0) ∂ν) < ⊤ := by
    convert hn using 1
    apply lintegral_congr_ae
    filter_upwards [hae] with y hy
    simp [newtonKernelEReal, hy, ← EReal.coe_neg, EReal.toENNReal, ENNReal.ofReal_max]
  have hmeas := measurable_newtonKernel x
  have hip : Integrable (fun y => max (newtonKernel x y) 0) ν :=
    ⟨(hmeas.max measurable_const).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun y => le_max_right _ _)).2 hp'⟩
  have hin : Integrable (fun y => max (-newtonKernel x y) 0) ν :=
    ⟨(hmeas.neg.max measurable_const).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun y => le_max_right _ _)).2 hn'⟩
  have hi : Integrable (newtonKernel x) ν := by
    convert hip.sub hin using 1
    ext y
    simp only [Pi.sub_apply]
    exact (max_zero_sub_max_neg_zero_eq_self _).symm
  refine ⟨hatom, hi, ?_⟩
  simpa only [greenPotential, greenFunction_univ_eq_newtonKernel] using
    extendedSignedIntegral_newtonKernel_eq hatom hi

/-- The center conclusion holds independently for both Jordan sources. -/
theorem signed_wholePlane_potential_of_parts_lt_top {ν₁ ν₂ : Measure ℂ} {x : ℂ}
    (hp₁ : (∫⁻ y, (newtonKernelEReal x y).toENNReal ∂ν₁) < ⊤)
    (hn₁ : (∫⁻ y, (-newtonKernelEReal x y).toENNReal ∂ν₁) < ⊤)
    (hp₂ : (∫⁻ y, (newtonKernelEReal x y).toENNReal ∂ν₂) < ⊤)
    (hn₂ : (∫⁻ y, (-newtonKernelEReal x y).toENNReal ∂ν₂) < ⊤) :
    ν₁ {x} = 0 ∧ ν₂ {x} = 0 ∧
    Integrable (newtonKernel x) ν₁ ∧ Integrable (newtonKernel x) ν₂ ∧
    extendedSignedIntegral (newtonKernelEReal x) ν₁ = (greenPotential univ ν₁ x : EReal) ∧
    extendedSignedIntegral (newtonKernelEReal x) ν₂ = (greenPotential univ ν₂ x : EReal) := by
  obtain ⟨ha₁, hi₁, he₁⟩ := wholePlane_potential_of_parts_lt_top hp₁ hn₁
  obtain ⟨ha₂, hi₂, he₂⟩ := wholePlane_potential_of_parts_lt_top hp₂ hn₂
  exact ⟨ha₁, ha₂, hi₁, hi₂, he₁, he₂⟩

end HarmonicBalls
