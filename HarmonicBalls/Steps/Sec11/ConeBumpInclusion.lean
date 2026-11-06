import HarmonicBalls.Steps.Sec11.PinchMeasureWeylShift
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! # The bump inclusion for the cone mass event -/

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped ENNReal ContDiff

/-- A bump which is constant on the inner annulus and vanishes on the outer
annulus multiplies the cone mass and leaves the Green supremum unchanged. -/
theorem coneMassEvent_of_bump
    (μ : Measure ℂ) (Q : Set ℂ) (M r γ c : ℝ) (z : ℂ) (f : ℂ → ℝ)
    (hQ : MeasurableSet Q)
    (hinner : ∀ x ∈ annulus z r (2 * r), f x = c)
    (houter : ∀ x ∈ annulus z (3 * r) (6 * r), f x = 0)
    {C₁ C₂ : ℝ≥0∞}
    (hmass : C₁ ≤ μ (annulus z r (2 * r) ∩ coneAt Q z))
    (hgreen : annulusGreenPotentialSup μ z (3 * r) (6 * r) ≤ C₂)
    (hheight : ENNReal.ofReal M * C₂ ≤ ENNReal.ofReal (Real.exp (γ * c)) * C₁) :
    coneMassEvent (μ.withDensity (fun x => ENNReal.ofReal (Real.exp (γ * f x)))) Q M r z := by
  let S := annulus z r (2 * r) ∩ coneAt Q z
  have hS : MeasurableSet S := by
    apply MeasurableSet.inter (measurableSet_ball.diff measurableSet_closedBall)
    exact (Homeomorph.addRight z).measurableEmbedding.measurableSet_image.mpr hQ
  have hrestrict := restrict_withDensity_exp_eq_of_eq_zero μ γ f
    (measurableSet_ball.diff measurableSet_closedBall) houter
  have hg := (annulusGreenPotentialSup_eq_of_restrict_eq z (3 * r) (6 * r) hrestrict)
  have hm : (μ.withDensity (fun x => ENNReal.ofReal (Real.exp (γ * f x)))) S =
      ENNReal.ofReal (Real.exp (γ * c)) * μ S := by
    rw [withDensity_apply _ hS]
    rw [lintegral_congr_ae (show (fun x => ENNReal.ofReal (Real.exp (γ * f x))) =ᵐ[μ.restrict S]
      (fun _ => ENNReal.ofReal (Real.exp (γ * c))) from by
        filter_upwards [ae_restrict_mem hS] with x hx
        rw [hinner x hx.1])]
    simp
  change ENNReal.ofReal M * annulusGreenPotentialSup _ z (3 * r) (6 * r) ≤ _
  rw [hg, hm]
  calc
    _ ≤ ENNReal.ofReal M * C₂ := by gcongr
    _ ≤ ENNReal.ofReal (Real.exp (γ * c)) * C₁ := hheight
    _ ≤ ENNReal.ofReal (Real.exp (γ * c)) * μ S := by gcongr

/-- A smooth nonnegative bump of prescribed height, equal to that height on
 the inner annulus and zero on the outer annulus. -/
theorem exists_cone_smooth_bump (z : ℂ) {r c : ℝ} (hr : 0 < r) (hc : 0 ≤ c) :
    ∃ f : ℂ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      (∀ x, 0 ≤ f x) ∧ (∀ x ∈ annulus z r (2 * r), f x = c) ∧
      (∀ x ∈ annulus z (3 * r) (6 * r), f x = 0) := by
  let S : Set ℂ := ball z (5 * r / 2) \ closedBall z (r / 2)
  let K : Set ℂ := closedBall z (2 * r) \ ball z r
  have hS : IsOpen S := isOpen_ball.sdiff isClosed_closedBall
  have hK : IsClosed K := isClosed_closedBall.sdiff isOpen_ball
  have hKS : K ⊆ S := by
    intro x hx
    have h1 : dist x z ≤ 2 * r := hx.1
    have h2 : r ≤ dist x z := le_of_not_gt hx.2
    constructor
    · change dist x z < 5 * r / 2
      linarith
    · change ¬ dist x z ≤ r / 2
      linarith
  obtain ⟨ψ, hψ, hψrange, hψsupp, hψone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hS hK hKS
  have hcompact : HasCompactSupport ψ := by
    change IsCompact (closure (Function.support ψ))
    rw [hψsupp]
    apply isCompact_of_isClosed_isBounded isClosed_closure
    exact (isBounded_ball.subset (sdiff_subset : S ⊆ ball z (5 * r / 2))).closure
  refine ⟨fun x => c * ψ x, contDiff_const.mul hψ, hcompact.mul_left, ?_, ?_, ?_⟩
  · intro x
    exact mul_nonneg hc (hψrange (mem_range_self x)).1
  · intro x hx
    have hxK : x ∈ K := by
      refine ⟨?_, ?_⟩
      · exact le_of_lt (show dist x z < 2 * r from hx.1)
      ·
        intro hball
        apply hx.2
        change dist x z ≤ r
        exact le_of_lt hball
    simp [(hψone x).1 hxK]
  · intro x hx
    have hxS : x ∉ S := by
      intro h
      have h1 : dist x z < 5 * r / 2 := h.1
      have h2 : 3 * r < dist x z := lt_of_not_ge hx.2
      linarith
    have hxzero : ψ x = 0 := by
      by_contra hn
      have : x ∈ Function.support ψ := hn
      rw [hψsupp] at this
      exact hxS this
    simp [hxzero]

/-- A nonnegative bump height can make a positive lower mass threshold
 dominate any nonnegative finite Green threshold. -/
theorem exists_cone_bump_height {γ a b : ℝ} (hγ : 0 < γ) (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ c : ℝ, 0 ≤ c ∧ b ≤ Real.exp (γ * c) * a := by
  let t := 1 + b / a
  have ht : 1 ≤ t := by
    dsimp [t]
    have := div_nonneg hb ha.le
    linarith
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  refine ⟨Real.log t / γ, div_nonneg (Real.log_nonneg ht) hγ.le, ?_⟩
  have heq : γ * (Real.log t / γ) = Real.log t := by field_simp
  rw [heq, Real.exp_log htpos]
  dsimp [t]
  have h : b / a * a = b := div_mul_cancel₀ b (ne_of_gt ha)
  nlinarith

end HarmonicBalls

#print axioms HarmonicBalls.coneMassEvent_of_bump
#print axioms HarmonicBalls.exists_cone_smooth_bump
#print axioms HarmonicBalls.exists_cone_bump_height
