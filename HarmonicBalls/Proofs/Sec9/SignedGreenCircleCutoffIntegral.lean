import HarmonicBalls.Proofs.Sec9.GreenCircleCutoffIntegral
import HarmonicBalls.Proofs.Sec9.SubharmonicNullModification
import HarmonicBalls.Proofs.Potential.GreenPotentialExceptionalSet

/-!
# Signed disc Green circle integrals

Real circle-integral limits for separately finite Green source integrals.
-/

namespace HarmonicBalls

open Metric Filter Topology Set MeasureTheory

private theorem circle_integral_tendsto_greenPotential
    {R : ℝ} {x : ℂ} {r : ℕ → ℝ} {μ : Measure ℂ}
    (hx : x ∈ ball (0 : ℂ) R) (hμ : μ (ball (0 : ℂ) R)ᶜ = 0)
    (hr : ∀ n, 0 < r n) (hanti : Antitone r) (hrlim : Tendsto r atTop (𝓝 0))
    (hsub : ∀ n, closedBall x (r n) ⊆ ball 0 R)
    (hi : Integrable (greenFunction (ball 0 R) x) μ)
    (hf : (∫⁻ y, Function.update (fun y => ENNReal.ofReal |greenFunction (ball 0 R) x y|)
      x ⊤ y ∂μ) < ⊤) :
    μ {x} = 0 ∧ (∀ n, Integrable (fun y =>
      Real.circleAverage (greenFunction (ball 0 R) y) x (r n)) μ) ∧ Tendsto (fun n => ∫ y,
      Real.circleAverage (greenFunction (ball 0 R) y) x (r n) ∂μ) atTop
      (𝓝 (greenPotential (ball 0 R) μ x)) := by
  have hatom := measure_singleton_eq_zero_of_extended_green_integral_lt_top (ball 0 R) x μ hf
  have hbound : Bornology.IsBounded (ball (0 : ℂ) R) := isBounded_ball
  have heq : (∫⁻ y, (if x = y then ⊤ else
      ENNReal.ofReal (greenFunction (ball 0 R) y x)) ∂μ) =
      ENNReal.ofReal (greenPotential (ball 0 R) μ x) := by
    rw [← lintegral_greenKernelExtended_eq hbound hatom hi]
    apply lintegral_congr
    intro y
    simp only [greenKernelExtended, eq_comm, greenFunction_ball_comm R y x]
  have ht := lintegral_circleAverage_greenFunction_ball_tendsto hx hμ hr hanti hrlim hsub
  rw [heq] at ht
  have hreal := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp ht
  rw [ENNReal.toReal_ofReal (greenPotential_nonneg hbound μ x)] at hreal
  have hball : ∀ᵐ y ∂μ, y ∈ ball (0 : ℂ) R := by
    rw [ae_iff]
    exact hμ
  have hm : ∀ n, AEStronglyMeasurable (fun y =>
      Real.circleAverage (greenFunction (ball 0 R) y) x (r n)) μ := by
    intro n
    let f : ℂ → ℝ := fun y => -(2 * Real.pi)⁻¹ * Real.log (max (r n) ‖y - x‖) -
      greatestHarmonicMinorantBall R y x
    have hf' : Measurable f := by
      dsimp [f, greatestHarmonicMinorantBall]
      fun_prop
    apply hf'.aestronglyMeasurable.congr
    filter_upwards [hball] with y hy
    exact (circleAverage_greenFunction_ball_eq_log_max (hr n) hy (hsub n)).symm
  have hn : ∀ n, ∀ᵐ y ∂μ, 0 ≤ Real.circleAverage (greenFunction (ball 0 R) y) x (r n) :=
    fun _ => Filter.Eventually.of_forall fun y => Real.circleAverage_nonneg_of_nonneg
      (fun z _ => greenFunction_nonneg hbound y z)
  have hae : ∀ᵐ y ∂μ, y ≠ x := ae_iff.mpr (by simpa using hatom)
  have hle : ∀ n, ∀ᵐ y ∂μ, Real.circleAverage (greenFunction (ball 0 R) y) x (r n) ≤
      greenFunction (ball 0 R) x y := by
    intro n
    filter_upwards [hball, hae, hn n] with y hy hne _
    have hc := circleAverage_greenFunction_ball_monotone_tendsto hx hy hr hanti hrlim hsub
    have hc' := hc.1.ge_of_tendsto hc.2 n
    simp only [Ne.symm hne, ↓reduceIte, greenFunction_ball_comm R y x] at hc'
    exact (ENNReal.ofReal_le_ofReal_iff (greenFunction_nonneg hbound x y)).mp hc'
  refine ⟨hatom, fun n => hi.mono_nonneg (hm n) (hn n) (hle n), ?_⟩
  apply hreal.congr'
  filter_upwards [] with n
  exact (integral_eq_lintegral_of_nonneg_ae (hn n) (hm n)).symm

/-- Separate finite signed source integrals converge to the difference of real Green potentials.
The infinite diagonal forces both source measures to have no atom at the center. -/
theorem signed_circle_integral_tendsto_greenPotential
    {R : ℝ} {x : ℂ} {r : ℕ → ℝ} {ν₁ ν₂ : Measure ℂ}
    (hx : x ∈ ball (0 : ℂ) R)
    (hν₁ : ν₁ (ball (0 : ℂ) R)ᶜ = 0) (hν₂ : ν₂ (ball (0 : ℂ) R)ᶜ = 0)
    (hfin₁ : IsFiniteMeasure ν₁) (hfin₂ : IsFiniteMeasure ν₂)
    (hr : ∀ n, 0 < r n) (hanti : Antitone r) (hrlim : Tendsto r atTop (𝓝 0))
    (hsub : ∀ n, closedBall x (r n) ⊆ ball 0 R)
    (hi₁ : Integrable (greenFunction (ball 0 R) x) ν₁)
    (hi₂ : Integrable (greenFunction (ball 0 R) x) ν₂)
    (hf₁ : (∫⁻ y, Function.update (fun y => ENNReal.ofReal |greenFunction (ball 0 R) x y|)
      x ⊤ y ∂ν₁) < ⊤)
    (hf₂ : (∫⁻ y, Function.update (fun y => ENNReal.ofReal |greenFunction (ball 0 R) x y|)
      x ⊤ y ∂ν₂) < ⊤) :
    ν₁ univ < ⊤ ∧ ν₂ univ < ⊤ ∧ ν₁ {x} = 0 ∧ ν₂ {x} = 0 ∧
    (∀ n, Integrable (fun y => Real.circleAverage (greenFunction (ball 0 R) y) x (r n)) ν₁) ∧
    (∀ n, Integrable (fun y => Real.circleAverage (greenFunction (ball 0 R) y) x (r n)) ν₂) ∧
    Tendsto (fun n => (∫ y, Real.circleAverage (greenFunction (ball 0 R) y) x (r n) ∂ν₁) -
      ∫ y, Real.circleAverage (greenFunction (ball 0 R) y) x (r n) ∂ν₂) atTop
      (𝓝 (greenPotential (ball 0 R) ν₁ x - greenPotential (ball 0 R) ν₂ x)) := by
  obtain ⟨ha₁, hc₁, ht₁⟩ := circle_integral_tendsto_greenPotential hx hν₁ hr hanti hrlim hsub hi₁ hf₁
  obtain ⟨ha₂, hc₂, ht₂⟩ := circle_integral_tendsto_greenPotential hx hν₂ hr hanti hrlim hsub hi₂ hf₂
  exact ⟨hfin₁.measure_univ_lt_top, hfin₂.measure_univ_lt_top, ha₁, ha₂, hc₁, hc₂,
    ht₁.sub ht₂⟩

end HarmonicBalls
