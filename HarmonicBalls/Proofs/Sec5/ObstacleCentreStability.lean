import HarmonicBalls.Proofs.Sec5.ObstaclePotentialStability
import HarmonicBalls.Proofs.SecA.ObstacleLeastSuperharmonicMajorant

/-! # Stability of the obstacle problem under a change of pole -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped Topology

/-- The positive part of the obstacle, with its singular pole assigned zero.
Every shifted supersolution dominates it on the closed ball. -/
noncomputable def truncatedShiftedObstacle (μ : Measure ℂ) (R : ℝ) (z : ℂ)
    (t : ℝ) (y : ℂ) : ℝ :=
  if y = z then 0 else max 0 (obstacle μ R z t y)

/-- The minimum principle makes every shifted supersolution nonnegative. -/
theorem shiftedSupersolution_nonneg_on_closedBall
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βminus βplus : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) {t : ℝ} (ht : 0 < t)
    {w : ℂ → ℝ} (hw : w ∈ shiftedSupersolutions μ R z t)
    {y : ℂ} (hy : y ∈ closedBall (0 : ℂ) R) : 0 ≤ w y := by
  have hsup := superharmonicOfLaplacianLEStep_holds _ w isOpen_ball
    (hw.1.mono ball_subset_closedBall) hw.2.1
  exact obstacleLeastSuperharmonicMajorantStep1_holds μ hμ R βminus βplus hR hV
    z hz t ht w ⟨hsup, hw.2.2⟩ y hy

/-- A nonnegative supersolution dominates the truncated obstacle, including at the pole. -/
theorem truncatedShiftedObstacle_le_of_mem_shiftedSupersolutions
    {μ : Measure ℂ} {R t : ℝ} {z y : ℂ} {w : ℂ → ℝ}
    (hw : w ∈ shiftedSupersolutions μ R z t) (hy : y ∈ closedBall (0 : ℂ) R)
    (hnonneg : 0 ≤ w y) : truncatedShiftedObstacle μ R z t y ≤ w y := by
  by_cases hyz : y = z
  · simpa only [truncatedShiftedObstacle, hyz, ite_true] using hnonneg
  · simp only [truncatedShiftedObstacle, ite_eq_right hyz]
    exact max_le hnonneg (hw.2.2 y hy hyz)

/-- A uniform one-sided bound on truncated obstacles gives the same bound on
least majorants at points away from both poles. -/
theorem shiftedLeastSupersolution_le_of_truncatedShiftedObstacle_le_add
    {μ : Measure ℂ} {R t c : ℝ} {z z' x : ℂ}
    (hne : (shiftedSupersolutions μ R z t).Nonempty)
    (hnonneg : ∀ w ∈ shiftedSupersolutions μ R z t,
      ∀ y ∈ closedBall (0 : ℂ) R, 0 ≤ w y)
    (hobs : ∀ y ∈ closedBall (0 : ℂ) R,
      truncatedShiftedObstacle μ R z' t y ≤ truncatedShiftedObstacle μ R z t y + c)
    (hx : x ∈ closedBall (0 : ℂ) R) (hxz' : x ≠ z') :
    shiftedLeastSupersolution μ R z' t x ≤ shiftedLeastSupersolution μ R z t x + c := by
  have hcomp : ∀ w ∈ shiftedSupersolutions μ R z t,
      (fun y => w y + c) ∈ shiftedSupersolutions μ R z' t := by
    intro w hw
    refine ⟨hw.1.add continuousOn_const, ?_, ?_⟩
    · have hzero : HasLaplacian (fun _ : ℂ => (1 : ℝ)) 0 0 (ball 0 R) :=
        hasLaplacian_zero_of_harmonicOnNhd isOpen_ball (InnerProductSpace.harmonicOnNhd_const 1)
      simpa using hw.2.1.add_const_mul_of_hasLaplacian_zero hzero c
    · intro y hy hyz'
      have h₁ : obstacle μ R z' t y ≤ truncatedShiftedObstacle μ R z' t y := by
        simp only [truncatedShiftedObstacle, ite_eq_right hyz']
        exact le_max_right _ _
      have h₂ := hobs y hy
      have h₃ := truncatedShiftedObstacle_le_of_mem_shiftedSupersolutions hw hy (hnonneg w hw y hy)
      linarith
  have hbound : shiftedLeastSupersolution μ R z' t x - c ≤
      shiftedLeastSupersolution μ R z t x := by
    apply le_csInf (hne.image _)
    rintro _ ⟨w, hw, rfl⟩
    have := shiftedLeastSupersolution_le (hcomp w hw) hx hxz'
    linarith
  linarith

/-- The least majorant is 1-Lipschitz in the uniform distance between the
truncated obstacles, at a point away from both poles. -/
theorem abs_shiftedLeastSupersolution_sub_le_of_truncatedShiftedObstacle
    {μ : Measure ℂ} {R t c : ℝ} {z z' x : ℂ}
    (hne : (shiftedSupersolutions μ R z t).Nonempty)
    (hne' : (shiftedSupersolutions μ R z' t).Nonempty)
    (hnonneg : ∀ w ∈ shiftedSupersolutions μ R z t,
      ∀ y ∈ closedBall (0 : ℂ) R, 0 ≤ w y)
    (hnonneg' : ∀ w ∈ shiftedSupersolutions μ R z' t,
      ∀ y ∈ closedBall (0 : ℂ) R, 0 ≤ w y)
    (hobs : ∀ y ∈ closedBall (0 : ℂ) R,
      |truncatedShiftedObstacle μ R z t y - truncatedShiftedObstacle μ R z' t y| ≤ c)
    (hx : x ∈ closedBall (0 : ℂ) R) (hxz : x ≠ z) (hxz' : x ≠ z') :
    |shiftedLeastSupersolution μ R z t x - shiftedLeastSupersolution μ R z' t x| ≤ c := by
  have h₁ := shiftedLeastSupersolution_le_of_truncatedShiftedObstacle_le_add (c := c) hne' hnonneg'
    (fun y hy => by have h := (abs_le.mp (hobs y hy)).2; linarith) hx hxz
  have h₂ := shiftedLeastSupersolution_le_of_truncatedShiftedObstacle_le_add (c := c) hne hnonneg
    (fun y hy => by have h := (abs_le.mp (hobs y hy)).1; linarith) hx hxz'
  apply abs_le.mpr
  constructor <;> linarith

/-- Away from the pole, uniform stability of truncated obstacles and pointwise
continuity of the Green function imply local persistence of non-coincidence
when the pole moves. -/
theorem nonCoincidenceSet_mem_nhds_of_truncatedShiftedObstacle
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βminus βplus : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βminus βplus)
    {z x : ℂ} (hz : z ∈ ball (0 : ℂ) R) {t : ℝ} (ht : 0 < t)
    (hx : x ∈ nonCoincidenceSet μ R z t) (hxz : x ≠ z)
    (htrunc : ∀ ε : ℝ, 0 < ε → ∀ᶠ z' in 𝓝 z,
      ∀ y ∈ closedBall (0 : ℂ) R,
        truncatedShiftedObstacle μ R z t y ≤ truncatedShiftedObstacle μ R z' t y + ε) :
    {z' : ℂ | x ∈ nonCoincidenceSet μ R z' t} ∈ 𝓝 z := by
  have hxball : x ∈ ball (0 : ℂ) R := hx.1
  have hgap : 0 < shiftedLeastSupersolution μ R z t x - obstacle μ R z t x := by
    rcases hx.2 with h | h
    · exact (hxz h).elim
    · linarith
  let ε := (shiftedLeastSupersolution μ R z t x - obstacle μ R z t x) / 4
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hq' : ∀ z', (shiftedSupersolutions μ R z' t).Nonempty := by
    intro z'
    exact ⟨greenPotentialBall μ R,
      greenPotentialBall_mem_shiftedSupersolutions ht.le
        (greenPotentialBallContinuousStep_holds μ hμ R βminus βplus hR hV)
        (greenPotentialBallLaplacianStep_holds μ hμ R βminus βplus hR hV).laplacianLE⟩
  have hgreen : ContinuousAt (fun z' => greenFunction (ball 0 R) z' x) z := by
    have hc := (continuousOn_greenFunction_ball hxball).continuousAt
      (isOpen_compl_singleton.mem_nhds (show z ∈ ({x} : Set ℂ)ᶜ from Ne.symm hxz))
    have heq : (fun z' => greenFunction (ball 0 R) z' x) =
        greenFunction (ball 0 R) x := by
      funext z'
      exact greenFunction_ball_comm R z' x
    rw [heq]
    exact hc
  have hpoint : ContinuousAt (fun z' => obstacle μ R z' t x) z := by
    unfold obstacle
    exact (continuousAt_const.mul hgreen).add continuousAt_const
  have hp : ∀ᶠ z' in 𝓝 z, obstacle μ R z' t x < obstacle μ R z t x + ε :=
    hpoint.eventually (isOpen_Iio.mem_nhds (by linarith :
      obstacle μ R z t x < obstacle μ R z t x + ε))
  filter_upwards [htrunc ε hε, hp, isOpen_ball.mem_nhds hz] with z' htr hp hz'
  refine ⟨hxball, ?_⟩
  by_cases hxz' : x = z'
  · exact Or.inl hxz'
  · right
    have hnonneg : ∀ w ∈ shiftedSupersolutions μ R z' t,
        ∀ y ∈ closedBall (0 : ℂ) R, 0 ≤ w y := by
      intro w hw y hy
      exact shiftedSupersolution_nonneg_on_closedBall hμ hR hV hz' ht hw hy
    have hle := shiftedLeastSupersolution_le_of_truncatedShiftedObstacle_le_add
      (c := ε) (hq' z') hnonneg htr (ball_subset_closedBall hxball) hxz
    dsimp [ε] at hle hp
    linarith

end HarmonicBalls
