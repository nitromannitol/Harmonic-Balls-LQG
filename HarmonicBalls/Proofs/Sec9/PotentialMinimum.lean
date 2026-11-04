import HarmonicBalls.Proofs.Sec9.AuxiliaryPotential
import HarmonicBalls.Proofs.Potential.DiscPoisson

/-! # Minimum principle for the auxiliary potential -/

namespace HarmonicBalls

open Complex Metric Real Filter Topology Set MeasureTheory InnerProductSpace

/-- A continuous function which is superharmonic on an open subset of a closed disc and
nonnegative on its complement is nonnegative throughout the disc. -/
theorem nonneg_on_closedBall_of_superharmonicOn {u : ℂ → ℝ} {A : Set ℂ} {R : ℝ}
    (hR : 0 < R) (hA : IsOpen A) (hcont : ContinuousOn u (closedBall 0 R))
    (hsup : IsSuperharmonicOn A u) (hsub : A ⊆ ball 0 R)
    (hout : ∀ x ∈ closedBall (0 : ℂ) R \ A, 0 ≤ u x) :
    ∀ x ∈ closedBall (0 : ℂ) R, 0 ≤ u x := by
  intro x hx
  by_contra hneg
  have hux : u x < 0 := lt_of_not_ge hneg
  set η : ℝ := -u x / (2 * (R ^ 2 + 1))
  have hη : 0 < η := div_pos (by linarith) (by positivity)
  have hηR : η * R ^ 2 < -u x := by
    have : η * (R ^ 2 + 1) = -u x / 2 := by
      simp only [η]; field_simp
    nlinarith
  set w : ℂ → ℝ := fun y => u y - η * ‖y‖ ^ 2
  have hwc : ContinuousOn w (closedBall 0 R) := by
    apply hcont.sub
    fun_prop
  obtain ⟨y, hy, hymin⟩ := hwc.lowerSemicontinuousOn.exists_isMinOn
    ⟨0, mem_closedBall_self hR.le⟩ (isCompact_closedBall 0 R)
  have hwyx : w y ≤ u x := by
    have h := hymin hx
    change w y ≤ w x at h
    dsimp [w] at h ⊢
    nlinarith [sq_nonneg ‖x‖]
  have hyA : y ∈ A := by
    by_contra hyA
    have hnonneg := hout y ⟨hy, hyA⟩
    have hynorm : ‖y‖ ≤ R := by simpa [dist_eq_norm] using hy
    have hbound : -(η * R ^ 2) ≤ w y := by
      simp only [w]
      have hsq : ‖y‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hynorm 2
      nlinarith
    linarith
  obtain ⟨ρ, hρ, hρA⟩ := Metric.isOpen_iff.1 hA y hyA
  have hr : 0 < ρ / 2 := by linarith
  have hrsub : closedBall y (ρ / 2) ⊆ A :=
    (closedBall_subset_ball (by linarith)).trans hρA
  obtain ⟨hci, hle⟩ := hsup.2 y hyA (ρ / 2) hr hrsub
  have hpt : ∀ y' ∈ sphere y |ρ / 2|,
      u y + η * (‖y'‖ ^ 2 - ‖y‖ ^ 2) ≤ u y' := by
    intro y' hy'
    rw [abs_of_pos hr] at hy'
    have hy'A : y' ∈ A := hrsub (sphere_subset_closedBall hy')
    have hy'K : y' ∈ closedBall (0 : ℂ) R := ball_subset_closedBall (hsub hy'A)
    have h := hymin hy'K
    change w y ≤ w y' at h
    dsimp [w] at h
    nlinarith
  have hcq : CircleIntegrable (fun y' : ℂ => u y + η * (‖y'‖ ^ 2 - ‖y‖ ^ 2)) y (ρ / 2) :=
    (by fun_prop : Continuous fun y' : ℂ => u y + η * (‖y'‖ ^ 2 - ‖y‖ ^ 2)).continuousOn.circleIntegrable'
  have hmono := circleAverage_mono hcq hci hpt
  have havg : Real.circleAverage (fun y' : ℂ => u y + η * (‖y'‖ ^ 2 - ‖y‖ ^ 2)) y (ρ / 2) =
      u y + η * (ρ / 2) ^ 2 := by
    have e : (fun y' : ℂ => u y + η * (‖y'‖ ^ 2 - ‖y‖ ^ 2)) =
        fun y' => (u y - η * ‖y‖ ^ 2) + η • ‖y' - (0 : ℂ)‖ ^ 2 := by
      ext y'; simp only [smul_eq_mul, sub_zero]; ring
    rw [e, circleAverage_fun_add continuousOn_const.circleIntegrable'
      ((by fun_prop : Continuous fun y' : ℂ => η • ‖y' - (0 : ℂ)‖ ^ 2).continuousOn.circleIntegrable'),
      circleAverage_const, circleAverage_fun_smul, circleAverage_norm_sub_sq, smul_eq_mul]
    simp only [sub_zero]
    ring
  rw [havg] at hmono
  have : 0 < η * (ρ / 2) ^ 2 := by positivity
  linarith

/-- Step 1 of Lemma 9.3: the auxiliary potential is nonnegative on the whole disc. -/
theorem IsHarmonicBallGen.auxiliary_greenPotential_nonneg
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {A B : Set ℂ} {z : ℂ}
    (hA : IsHarmonicBallGen μ A z) (hB : IsSubharmonicBall μ B z)
    {R βm βp : ℝ} (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    (hAcl : closure A ⊆ ball 0 R) (hBcl : closure B ⊆ ball 0 R)
    (hmass : μ.real A = μ.real B) {x : ℂ} (hx : x ∈ closedBall 0 R) :
    0 ≤ (∫ y in A, greenFunction (ball 0 R) x y ∂μ) -
      ∫ y in B, greenFunction (ball 0 R) x y ∂μ := by
  have hAsub : A ⊆ ball (0 : ℂ) R := subset_closure.trans hAcl
  have hBsub : B ⊆ ball (0 : ℂ) R := subset_closure.trans hBcl
  obtain ⟨hc, _⟩ := auxiliary_greenPotential_regular hμ hR hV hAsub hBsub
  have hsup := auxiliary_greenPotential_superharmonicOn hμ hR hV hA.1.1 hAsub hBsub
  apply nonneg_on_closedBall_of_superharmonicOn hR hA.1.1 hc hsup hAsub ?_ x hx
  intro y hy
  by_cases hyball : y ∈ ball (0 : ℂ) R
  · exact hA.greenPotential_sub_nonneg_of_isSubharmonicBall hB hAcl hBcl hmass ⟨hyball, hy.2⟩
  · simp only [greenFunction_of_notMem_left hyball, integral_zero, sub_self, le_refl]

end HarmonicBalls
