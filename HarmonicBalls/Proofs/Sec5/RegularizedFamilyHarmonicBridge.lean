import HarmonicBalls.Draft.Section5
import HarmonicBalls.Proofs.Sec4.GreenAwayFromPole

/-! # Subharmonic balls and harmonic tests

The two sub-mean inequalities give the mean-value property whenever a test and
its negative both belong to the subharmonic test class.
-/

namespace HarmonicBalls

open MeasureTheory Set InnerProductSpace

/-- Two admissible signs give the mean-value property. -/
theorem IsSubharmonicBall.hasMeanValueProperty_of_mem_and_neg_mem
    {μ : Measure ℂ} {Λ : Set ℂ} {z : ℂ} {f : ℂ → ℝ}
    (h : IsSubharmonicBall μ Λ z) (hf : f ∈ subharmonicBallTestClass Λ z)
    (hneg : -f ∈ subharmonicBallTestClass Λ z) : HasMeanValueProperty μ Λ z f := by
  have hp := h.2.2.2.2 f hf
  have hn := h.2.2.2.2 (-f) hneg
  refine ⟨hp.1, le_antisymm hp.2 ?_⟩
  change IntegrableOn (-f) Λ μ ∧ (-f) z * μ.real Λ ≤ ∫ x in Λ, (-f) x ∂μ at hn
  simp only [Pi.neg_apply, integral_neg, neg_mul] at hn
  linarith

/-- Every subharmonic ball is a harmonic ball for neighbourhood-harmonic tests. -/
theorem IsSubharmonicBall.isHarmonicBall {μ : Measure ℂ} {Λ : Set ℂ} {z : ℂ}
    (h : IsSubharmonicBall μ Λ z) : IsHarmonicBall μ Λ z := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
  intro f hf
  let O := {x : ℂ | HarmonicAt f x}
  have hO : IsOpen O := isOpen_setOfPred_harmonicAt f
  have hΛO : closure Λ ⊆ O := hf
  have hharm : HarmonicOnNhd f O := fun _ hx => hx
  exact h.hasMeanValueProperty_of_mem_and_neg_mem
    (mem_subharmonicBallTestClass_of_harmonicOnNhd hO hΛO hharm)
    (mem_subharmonicBallTestClass_of_harmonicOnNhd hO hΛO hharm.neg)

/-- A signed Green potential supported outside the ball has two admissible signs. -/
theorem IsSubharmonicBall.hasMeanValueProperty_of_greenPotentialClass
    {μ : Measure ℂ} {Λ O : Set ℂ} {z : ℂ} {f : ℂ → ℝ}
    (h : IsSubharmonicBall μ Λ z) (hO : IsOpen O) (hΛO : closure Λ ⊆ O)
    (hf : f ∈ greenPotentialClass O Λ) : HasMeanValueProperty μ Λ z f := by
  obtain ⟨K, ν₁, ν₂, hK, hKO, hν₁, hν₂, h₁, h₂, rfl⟩ := hf
  have hzO : z ∈ O := hΛO (subset_closure h.2.1)
  have hzK : z ∉ K := fun hz => (hKO hz).2 h.2.1
  have hKΛ : K ⊆ Λᶜ := fun x hx => (hKO hx).2
  have hΛK : Λ ⊆ Kᶜ := fun x hx hxK => hKΛ hxK hx
  have hn₁ : ν₁ Λ = 0 := measure_mono_null hΛK h₁
  have hn₂ : ν₂ Λ = 0 := measure_mono_null hΛK h₂
  have hz₁ : ν₁ {z} = 0 := measure_mono_null (singleton_subset_iff.mpr h.2.1) hn₁
  have hz₂ : ν₂ {z} = 0 := measure_mono_null (singleton_subset_iff.mpr h.2.1) hn₂
  have hi₁ : Integrable (greenFunction O z) ν₁ :=
    greenFunctionIntegrableAwayFromPoleStep_holds O K z ν₁ hO hzO hK
      (hKO.trans sdiff_subset) hzK hν₁ h₁
  have hi₂ : Integrable (greenFunction O z) ν₂ :=
    greenFunctionIntegrableAwayFromPoleStep_holds O K z ν₂ hO hzO hK
      (hKO.trans sdiff_subset) hzK hν₂ h₂
  apply h.hasMeanValueProperty_of_mem_and_neg_mem
  · refine ⟨O, K, ν₁, ν₂, 0, hO, hΛO, hK, hKO.trans sdiff_subset,
      hν₁, hν₂, h₁, h₂, hn₁, harmonicOnNhd_const 0, hz₂, hi₂, ?_⟩
    ext x
    simp
  · refine ⟨O, K, ν₂, ν₁, 0, hO, hΛO, hK, hKO.trans sdiff_subset,
      hν₂, hν₁, h₂, h₁, hn₂, harmonicOnNhd_const 0, hz₁, hi₁, ?_⟩
    ext x
    simp

/-- Every subharmonic ball satisfies the enlarged harmonic mean-value property. -/
theorem IsSubharmonicBall.isHarmonicBallGen {μ : Measure ℂ} {Λ : Set ℂ} {z : ℂ}
    (h : IsSubharmonicBall μ Λ z) : IsHarmonicBallGen μ Λ z := by
  refine ⟨h.isHarmonicBall, ?_⟩
  rintro f ⟨f₁, f₂, O, hf₁, hO, _, hΛO, hf₂, rfl⟩
  have h₁ := h.isHarmonicBall.2.2.2.2 f₁ hf₁
  have h₂ := h.hasMeanValueProperty_of_greenPotentialClass hO hΛO hf₂
  refine ⟨h₁.1.add h₂.1, ?_⟩
  simp only [Pi.add_apply, integral_add h₁.1 h₂.1, add_mul, h₁.2, h₂.2]

/-- Regularized cluster families satisfy the harmonic-ball family conditions. -/
theorem regularizedClusterFamily_isHarmonicBallFamily
    (μ : Measure ℂ) (Λ : ℝ → Set ℂ) (z : ℂ)
    (h : IsRegularizedClusterFamily μ Λ z) : IsHarmonicBallFamily μ Λ z :=
  ⟨fun t ht => (h.2.1 t ht).isHarmonicBallGen, h.1⟩

end HarmonicBalls
