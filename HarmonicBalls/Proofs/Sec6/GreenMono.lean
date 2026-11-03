import HarmonicBalls.Steps.Sec6.HarnackIteration

/-!
# Domain monotonicity of the Green function and of `SG` (step `GreenPotentialSupMonoStep`)

For open `O ⊆ O'` with `O'` bounded, every harmonic minorant of `log (1/|x - ·|)/(2π)` on `O'` restricts to one on
`O`, so `I_{O'} ≤ I_O` (`greatestHarmonicMinorant_anti`) and `G_O ≤ G_{O'}` on `O` off the diagonal
(`greenFunction_mono`; Armitage-Gardiner §4.1). Hence `SG(x₀; s₁, s₂) ≤ SG(x₀; s₁, s₃)` for `s₂ ≤ s₃`: the supremum
and the integral run over the larger annulus, and the kernel of the larger ball is larger
(`greenPotentialSupMonoStep_proved`, used for GRAPH G22 in Lemma 6.11).
-/

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped ENNReal

namespace Section6

theorem greatestHarmonicMinorant_anti {O O' : Set ℂ} (hOO' : O ⊆ O') (u : ℂ → EReal) (y : ℂ) :
    greatestHarmonicMinorant O' u y ≤ greatestHarmonicMinorant O u y :=
  iSup₂_le fun _ hg =>
    IsHarmonicMinorant.le_greatestHarmonicMinorant ⟨fun z hz => hg.1 z (hOO' hz), fun w hw => hg.2 w (hOO' hw)⟩ y

/-- Domain monotonicity of the Green function: `G_O(x,y) ≤ G_{O'}(x,y)` for `x ≠ y` in `O ⊆ O'`, `O'` bounded. -/
theorem greenFunction_mono {O O' : Set ℂ} (hOO' : O ⊆ O') (hO' : Bornology.IsBounded O') {x y : ℂ}
    (hx : x ∈ O) (hy : y ∈ O) (hxy : x ≠ y) : greenFunction O x y ≤ greenFunction O' x y := by
  rw [greenFunction, ite_eq_left ⟨hx, hy, hxy⟩, greenFunction, ite_eq_left ⟨hOO' hx, hOO' hy, hxy⟩]
  have hI := greatestHarmonicMinorant_anti hOO' (newtonKernelEReal x) y
  obtain ⟨R, hR⟩ := hO'.subset_closedBall x
  have hbot : greatestHarmonicMinorant O' (newtonKernelEReal x) y ≠ ⊥ :=
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _)
      ((isHarmonicMinorant_const_newtonKernelEReal hR).le_greatestHarmonicMinorant y)
  have hN : newtonKernelEReal x y ≠ ⊤ := by
    simp only [newtonKernelEReal, hxy.symm, ↓reduceIte]
    exact EReal.coe_ne_top _
  have htop : greatestHarmonicMinorant O (newtonKernelEReal x) y ≠ ⊤ :=
    ne_top_of_le_ne_top hN (greatestHarmonicMinorant_le hy)
  have := EReal.toReal_le_toReal hI hbot htop
  linarith

end Section6

open Section6

/-- `GreenPotentialSupMonoStep` (domain monotonicity of `SG`), proved. -/
theorem greenPotentialSupMonoStep_proved : GreenPotentialSupMonoStep := by
  intro μ x₀ s₁ s₂ s₃ _ _ h23
  have hsub : annulus x₀ s₁ s₂ ⊆ annulus x₀ s₁ s₃ :=
    fun _ hx => ⟨ball_subset_ball h23 hx.1, hx.2⟩
  have hmeas : MeasurableSet (annulus x₀ s₁ s₂) := isOpen_ball.measurableSet.diff measurableSet_closedBall
  unfold annulusGreenPotentialSup
  refine iSup₂_le fun x hx => le_iSup₂_of_le x (hsub hx) ?_
  calc ∫⁻ y in annulus x₀ s₁ s₂,
        (if y = x then ∞ else ENNReal.ofReal (greenFunction (ball x₀ s₂) x y)) ∂μ
      ≤ ∫⁻ y in annulus x₀ s₁ s₂,
        (if y = x then ∞ else ENNReal.ofReal (greenFunction (ball x₀ s₃) x y)) ∂μ := by
        refine setLIntegral_mono' hmeas fun y hy => ?_
        by_cases hyx : y = x
        · simp [hyx]
        · simp only [hyx, ↓reduceIte]
          exact ENNReal.ofReal_le_ofReal
            (greenFunction_mono (ball_subset_ball h23) isBounded_ball hx.1 hy.1 (Ne.symm hyx))
    _ ≤ _ := lintegral_mono_set hsub

end HarmonicBalls
