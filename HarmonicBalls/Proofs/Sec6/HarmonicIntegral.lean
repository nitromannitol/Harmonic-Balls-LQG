import HarmonicBalls.Proofs.Sec6.HarmonicCompactExtension
import HarmonicBalls.Proofs.Sec4.Sweep

/-! # Integrals of harmonic functions

Poisson modification and integration yield harmonicity of a continuous
integral of locally uniformly bounded harmonic functions.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter MarkovProcess Metric InnerProductSpace Function
open scoped NNReal Topology ZeroAtInfty

/-- A continuous integral of a jointly measurable family of harmonic functions
is harmonic when the family is uniformly bounded on each admissible circle. -/
theorem harmonicOnNhd_integral_of_circle_bounds
    {U : Set ℂ} (hU : IsOpen U) {μ : Measure ℂ} [IsFiniteMeasure μ]
    {F : ℂ → ℂ → ℝ} (hF : ∀ x, HarmonicOnNhd (F x) U)
    (hFm : Measurable (uncurry F))
    (hq : ContinuousOn (fun z => ∫ x, F x z ∂μ) U)
    (hbound : ∀ c : ℂ, ∀ r : ℝ, 0 < r → closedBall c r ⊆ U →
      ∃ B : ℝ, ∀ x, ∀ z ∈ sphere c r, |F x z| ≤ B) :
    HarmonicOnNhd (fun z => ∫ x, F x z ∂μ) U := by
  intro z hz
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp hU z hz
  let r := δ / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hsub : closedBall z r ⊆ U :=
    (closedBall_subset_ball (by dsimp [r]; linarith)).trans hδU
  have hdisc : IsSweepDisc U z r := ⟨hr, hsub⟩
  obtain ⟨B, hB⟩ := hbound z r hr hsub
  let q : ℂ → ℝ := fun w => ∫ x, F x w ∂μ
  have hfix : discSweep U z r q = q := by
    funext w
    rw [(discSweep_integral (m := μ) hFm (c := z) (ρ := r)
      (B := B) (fun _ => hB)).2 w]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => congrFun (discSweep_harmonic (hF x)) w
  have hc : CircleIntegrable q z r :=
    (hq.mono (sphere_subset_closedBall.trans hsub)).circleIntegrable hr.le
  have heq : q =ᶠ[𝓝 z] discPoissonIntegral q z r := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with w hw
    rw [← congrFun hfix w, discSweep_of_mem hdisc hw]
  exact (harmonicAt_congr_nhds heq).2 (harmonicOnNhd_discPoissonIntegral hc z (mem_ball_self hr))

/-- The restricted Green potential is harmonic off a compact set when the
kernel is jointly measurable, harmonic off each pole, and locally uniformly
bounded away from the poles. -/
theorem harmonicOnNhd_restricted_greenPotential_of_kernel
    {U L : Set ℂ} (hU : IsOpen U) (hL : IsCompact L)
    {μ : Measure ℂ} (hfinite : μ L < ⊤)
    (hkernel : ∀ x ∈ L, HarmonicOnNhd (fun z => greenFunction U z x) (U \ L))
    (hmeas : Measurable (fun p : ℂ × ℂ => greenFunction U p.2 p.1))
    (hcont : ContinuousOn (fun z => ∫ x in L, greenFunction U z x ∂μ) (U \ L))
    (hbound : ∀ c : ℂ, ∀ r : ℝ, 0 < r → closedBall c r ⊆ U \ L →
      ∃ B : ℝ, ∀ x ∈ L, ∀ z ∈ sphere c r, |greenFunction U z x| ≤ B) :
    HarmonicOnNhd (fun z => ∫ x in L, greenFunction U z x ∂μ) (U \ L) := by
  classical
  let m := μ.restrict L
  let : IsFiniteMeasure m := isFiniteMeasure_restrict.2 hfinite.ne
  let F : ℂ → ℂ → ℝ := fun x z => L.indicator (fun x => greenFunction U z x) x
  have hF : ∀ x, HarmonicOnNhd (F x) (U \ L) := by
    intro x
    by_cases hx : x ∈ L
    · simpa only [F, indicator_of_mem hx] using hkernel x hx
    · simpa only [F, indicator_of_notMem hx] using harmonicOnNhd_const (0 : ℝ)
  have hFm : Measurable (uncurry F) := by
    have heq : uncurry F = (L ×ˢ (univ : Set ℂ)).indicator
        (fun p : ℂ × ℂ => greenFunction U p.2 p.1) := by
      funext p
      by_cases hp : p.1 ∈ L <;> simp [F, Function.uncurry, hp]
    rw [heq]
    exact hmeas.indicator (hL.measurableSet.prod MeasurableSet.univ)
  have heq : (fun z => ∫ x, F x z ∂m) =
      fun z => ∫ x in L, greenFunction U z x ∂μ := by
    funext z
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hL.measurableSet] with x hx
    exact indicator_of_mem hx _
  rw [← heq] at hcont ⊢
  apply harmonicOnNhd_integral_of_circle_bounds (hU.sdiff hL.isClosed) hF hFm hcont
  intro c r hr hsub
  obtain ⟨B, hB⟩ := hbound c r hr hsub
  refine ⟨max B 0, ?_⟩
  intro x z hz
  by_cases hx : x ∈ L
  · simpa only [F, indicator_of_mem hx] using (hB x hx z hz).trans (le_max_left B 0)
  · simpa only [F, indicator_of_notMem hx, abs_zero] using le_max_right B 0

/-- Hölder regularity supplies the continuity required for harmonicity of the
restricted potential under the stated Green-kernel properties. -/
theorem harmonicOnNhd_restricted_greenPotential_of_kernel_and_holder
    {U L : Set ℂ} (hU : IsOpen U) (hL : IsCompact L) (hLU : L ⊆ U)
    {μ : Measure ℂ} (hfinite : μ L < ⊤)
    (hholder : ∀ f : ℂ → ℝ, MemLp f ⊤ (μ.restrict (closure U)) →
      (∀ x ∈ closure U, IntegrableOn (fun y => greenFunction U x y * f y) U μ) ∧
      ∃ C t : ℝ≥0, 0 < t ∧
        HolderOnWith C t (fun x => ∫ y in U, greenFunction U x y * f y ∂μ) (closure U))
    (hkernel : ∀ x ∈ L, HarmonicOnNhd (fun z => greenFunction U z x) (U \ L))
    (hmeas : Measurable (fun p : ℂ × ℂ => greenFunction U p.2 p.1))
    (hbound : ∀ c : ℂ, ∀ r : ℝ, 0 < r → closedBall c r ⊆ U \ L →
      ∃ B : ℝ, ∀ x ∈ L, ∀ z ∈ sphere c r, |greenFunction U z x| ≤ B) :
    HarmonicOnNhd (fun z => ∫ x in L, greenFunction U z x ∂μ) (U \ L) := by
  obtain ⟨_, C, t, ht, hc⟩ := hholder (L.indicator (fun _ => 1))
    ((memLp_top_const (1 : ℝ)).indicator hL.measurableSet)
  have heq : (fun z => ∫ y in U, greenFunction U z y * L.indicator (fun _ => 1) y ∂μ) =
      fun z => ∫ y in L, greenFunction U z y ∂μ := by
    funext z
    have hind : (fun y => greenFunction U z y * L.indicator (fun _ => 1) y) =
        L.indicator (greenFunction U z) := by
      funext y
      by_cases hy : y ∈ L <;> simp [hy]
    rw [hind, integral_indicator hL.measurableSet, Measure.restrict_restrict_of_subset hLU]
  rw [heq] at hc
  exact harmonicOnNhd_restricted_greenPotential_of_kernel hU hL hfinite hkernel hmeas
    ((hc.continuousOn ht).mono (sdiff_subset.trans subset_closure)) hbound

end HarmonicBalls.Section6
