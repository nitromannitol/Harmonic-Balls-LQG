import HarmonicBalls.Proofs.Sec6.BrownianScaling
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import Mathlib.Probability.Independence.ZeroOne

/-! # Independence of Brownian increment blocks

Increment processes indexed by mutually disjoint time intervals are independent.
This is a step towards the zero-one law for the Brownian germ at zero.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory MarkovProcess Filter
open scoped NNReal

/-- Families of increments of a real pre-Brownian motion are independent when
all intervals belonging to distinct families are disjoint and ordered. -/
theorem iIndepFun_brownian_increment_blocks
    {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : NNReal → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {S : ι → Type*} (a b : (i : ι) → S i → NNReal)
    (hab : ∀ i s, a i s ≤ b i s)
    (hdisjoint : ∀ i j, i ≠ j → ∀ s t,
      b i s ≤ a j t ∨ b j t ≤ a i s) :
    iIndepFun (fun i ω s => B (b i s) ω - B (a i s) ω) P := by
  classical
  have hg : IsGaussianProcess
      (fun (p : (i : ι) × S i) ω => B (b p.1 p.2) ω - B (a p.1 p.2) ω) P := by
    apply hB.isGaussianProcess.of_isGaussianProcess
    intro p
    refine ⟨{a p.1 p.2, b p.1 p.2},
      { toFun x := x ⟨b p.1 p.2, by simp⟩ - x ⟨a p.1 p.2, by simp⟩
        map_add' x y := by simp; abel
        map_smul' c x := by simp; ring }, ?_⟩
    simp
  apply hg.iIndepFun_of_covariance_eq_zero
  · intro i s
    exact (hB.aemeasurable _).sub (hB.aemeasurable _)
  · intro i j hij s t
    have := hB.isGaussianProcess.isProbabilityMeasure
    have hm u := (hB.isGaussianProcess.hasGaussianLaw_eval u).memLp_two
    rw [covariance_fun_sub_left, covariance_fun_sub_right, covariance_fun_sub_right,
      hB.covariance_eval, hB.covariance_eval, hB.covariance_eval, hB.covariance_eval]
    · rcases hdisjoint i j hij s t with h | h
      · have h₁ : a i s ≤ a j t := (hab i s).trans h
        have h₂ : b i s ≤ b j t := h.trans (hab j t)
        have h₃ : a i s ≤ b j t := h₁.trans (hab j t)
        simp [min_eq_left h, min_eq_left h₁, min_eq_left h₂, min_eq_left h₃]
      · have h₁ : a j t ≤ a i s := (hab j t).trans h
        have h₂ : b j t ≤ b i s := h.trans (hab i s)
        have h₃ : a j t ≤ b i s := h₁.trans (hab i s)
        simp [min_eq_right h, min_eq_right h₁, min_eq_right h₂, min_eq_right h₃]
    all_goals first | exact hm _ | exact (hm _).sub (hm _)

/-- The canonical real Brownian motion has independent increment processes on
families of pairwise disjoint time intervals. -/
theorem iIndepFun_realBrownian_increment_blocks
    {ι : Type*} {S : ι → Type*} (x : ℝ)
    (a b : (i : ι) → S i → NNReal)
    (hab : ∀ i s, a i s ≤ b i s)
    (hdisjoint : ∀ i j, i ≠ j → ∀ s t,
      b i s ≤ a j t ∨ b j t ≤ a i s) :
    iIndepFun (fun i (ω : ContinuousPath ℝ) s => ω (b i s) - ω (a i s))
      (brownianMotion x) := by
  simpa only [sub_sub_sub_cancel_right] using
    iIndepFun_brownian_increment_blocks (isPreBrownianReal_brownianMotion x)
      a b hab hdisjoint

/-- The tail sigma-algebra of disjoint Brownian increment blocks is independent
of itself. -/
theorem realBrownian_increment_block_tail_indep_self
    {S : ℕ → Type*} (x : ℝ) (a b : (i : ℕ) → S i → NNReal)
    (hab : ∀ i s, a i s ≤ b i s)
    (hdisjoint : ∀ i j, i ≠ j → ∀ s t,
      b i s ≤ a j t ∨ b j t ≤ a i s) :
    let m : ℕ → MeasurableSpace (ContinuousPath ℝ) := fun i =>
      (inferInstance : MeasurableSpace (S i → ℝ)).comap
        (fun ω s => ω (b i s) - ω (a i s))
    Indep (limsup m atTop) (limsup m atTop) (brownianMotion x) := by
  dsimp only
  apply indep_limsup_atTop_self
  · intro i
    apply Measurable.comap_le
    exact Measurable.of_eval fun s =>
      (ContinuousPath.measurable_coordinateProcess _).sub
        (ContinuousPath.measurable_coordinateProcess _)
  · exact (iIndepFun_iff_iIndep _ _ _).mp
      (iIndepFun_realBrownian_increment_blocks x a b hab hdisjoint)

end HarmonicBalls.Section6
