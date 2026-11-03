import HarmonicBalls.Draft.Section9

/-!
# Lemma 9.1: the quadrature inequality for subharmonic and harmonic balls

Reduction of `ObstacleComparisonStmt` (Lemma 9.1, lemma:obstacle-comp, line 2279 of
paper/lqg_harmonic_ball-corrected.tex; Sakai 1984, Shahgholian-Sjödin 2013, Theorem 2.1) to two steps, following the
proof printed at lines 2291-2313.

## Steps

* `GreenFunctionBallSymmetric` (input I4): `G_{B_R}(x,y) = G_{B_R}(y,x)`.
* `NegGreenFunctionMemSubharmonicBallTestClass`: for `x ∈ O \ {z}` and `closure Λ ⊆ O`, the function `-G_O(·,x)` is a
  test function of eq:sub-harmonic-potential (line 746) for a subharmonic ball `Λ` centred at `z`: the Green
  potential of the signed measure `ν = -δ_x` (Jordan decomposition `ν₁ = 0`, `ν₂ = δ_x`, so `ν|_Λ ≤ 0`), with `q = 0`.
  It is finite at the centre since `x ≠ z`.

## Reduction (`obstacleComparison_of_steps`)

(1) The sub-mean-value property eq:subharmonic-ball for `-G_{B_R}(·,x)` reads
`∫_Λ G_{B_R}(w,x) μ(dw) ≤ μ(Λ) G_{B_R}(z,x)`, and symmetry turns it into `f(x) ≥ 0`.
(2) For `x ∈ B_R \ Λ`, `G_{B_R}(·,x)` is in the enlarged test class `H̃_{B_R}(Λ)` (`ν = δ_x`, supported in
`B_R \ Λ`; `IsHarmonicBallGen.hasMeanValueProperty_greenFunction`), so the mean value property reads
`∫_Λ G_{B_R}(w,x) μ(dw) = μ(Λ) G_{B_R}(z,x)`, and symmetry gives `f(x) = 0`. Neither part uses the connectedness of
`Λ`, `z ∈ B_R`, or any property of `μ`: the argument is deterministic.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

/-- Step of Lemma 9.1 (input I4): the Green function of the disc `B_R(0)` is symmetric. -/
def GreenFunctionBallSymmetric : Prop :=
  ∀ (R : ℝ) (x y : ℂ), greenFunction (ball 0 R) x y = greenFunction (ball 0 R) y x

/-- Step of Lemma 9.1(1) (line 2297): for an open `O ⊇ closure Λ` and a pole `x ∈ O` different from the centre `z`,
`-G_O(·,x)` belongs to the test class eq:sub-harmonic-potential of subharmonic balls centred at `z` (`ν = -δ_x`,
`q = 0`). -/
def NegGreenFunctionMemSubharmonicBallTestClass : Prop :=
  ∀ (O Λ : Set ℂ) (z x : ℂ), IsOpen O → closure Λ ⊆ O → x ∈ O → x ≠ z →
    (fun w => -greenFunction O w x) ∈ subharmonicBallTestClass Λ z

/-- Lemma 9.1(1), deterministic form: for a subharmonic ball `Λ` centred at `z` with `closure Λ ⊆ B_R(0)`,
`μ(Λ) G_{B_R}(x,z) - ∫_Λ G_{B_R}(x,y) μ(dy) ≥ 0` for every `x ∈ B_R(0) \ {z}`. -/
theorem IsSubharmonicBall.greenPotential_le_of_steps (hsymm : GreenFunctionBallSymmetric)
    (hclass : NegGreenFunctionMemSubharmonicBallTestClass) {μ : Measure ℂ} {Λ : Set ℂ} {z : ℂ}
    (hΛ : IsSubharmonicBall μ Λ z) {R : ℝ} (hcl : closure Λ ⊆ ball 0 R) {x : ℂ} (hx : x ∈ ball (0 : ℂ) R)
    (hxz : x ≠ z) :
    0 ≤ μ.real Λ * greenFunction (ball 0 R) x z - ∫ y in Λ, greenFunction (ball 0 R) x y ∂μ := by
  have h := (hΛ.2.2.2.2 _ (hclass _ Λ z x isOpen_ball hcl hx hxz)).2
  have hint : ∫ w in Λ, greenFunction (ball 0 R) w x ∂μ = ∫ y in Λ, greenFunction (ball 0 R) x y ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun w => hsymm R w x)
  beta_reduce at h
  rw [integral_neg, hint, hsymm R z x] at h
  linarith

/-- Lemma 9.1(2), deterministic form: for a harmonic ball `Λ` centred at `z` (enlarged test class, [C7]) with
`closure Λ ⊆ B_R(0)`, `μ(Λ) G_{B_R}(x,z) - ∫_Λ G_{B_R}(x,y) μ(dy) = 0` for every `x ∈ B_R(0) \ Λ`. -/
theorem IsHarmonicBallGen.greenPotential_eq_of_steps (hsymm : GreenFunctionBallSymmetric) {μ : Measure ℂ}
    {Λ : Set ℂ} {z : ℂ} (hΛ : IsHarmonicBallGen μ Λ z) {R : ℝ} (hcl : closure Λ ⊆ ball 0 R) {x : ℂ}
    (hx : x ∈ ball (0 : ℂ) R \ Λ) :
    μ.real Λ * greenFunction (ball 0 R) x z - ∫ y in Λ, greenFunction (ball 0 R) x y ∂μ = 0 := by
  have h := (hΛ.hasMeanValueProperty_greenFunction hcl hx).2
  have hint : ∫ w in Λ, greenFunction (ball 0 R) w x ∂μ = ∫ y in Λ, greenFunction (ball 0 R) x y ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun w => hsymm R w x)
  beta_reduce at h
  rw [hint, hsymm R z x] at h
  linarith

/-- Reduction of Lemma 9.1 (`ObstacleComparisonStmt`) to the symmetry of `G_{B_R}` and the membership of
`-G_{B_R}(·,x)` in the subharmonic test class. -/
theorem obstacleComparison_of_steps (hsymm : GreenFunctionBallSymmetric)
    (hclass : NegGreenFunctionMemSubharmonicBallTestClass) : ObstacleComparisonStmt := by
  intro _ _ _ _ _ _ _ _ _ _ μ _ _ ω R _ z _ Λ _ _ hcl _
  exact ⟨fun hΛ _ hx hxz => hΛ.greenPotential_le_of_steps hsymm hclass hcl hx hxz,
    fun hΛ _ hx => hΛ.greenPotential_eq_of_steps hsymm hcl hx⟩

end HarmonicBalls
