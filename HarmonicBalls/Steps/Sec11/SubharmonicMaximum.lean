import HarmonicBalls.Steps.SecA.Basic
import HarmonicBalls.Steps.Sec11.AnnulusComparison

/-!
# Circle averages at a maximum

For the maximum principle used in Lemma 11.6, a continuous subharmonic
function that reaches a maximum has to be constant on each sufficiently
small circle about that point.  The first step is the equality case for a
circle average bounded above by a constant.
-/

namespace HarmonicBalls

open Metric Real Set

/-- A continuous function on a circle, bounded above by its circle average,
is constant on that circle. -/
theorem eqOn_sphere_of_circleAverage_eq_of_le (u : ℂ → ℝ) (c : ℂ) (r M : ℝ)
    (hu : ContinuousOn u (sphere c |r|))
    (hle : ∀ w ∈ sphere c |r|, u w ≤ M)
    (havg : circleAverage u c r = M) :
    EqOn u (fun _ => M) (sphere c |r|) := by
  intro w hw
  by_contra hne
  have hlt : u w < M := lt_of_le_of_ne (hle w hw) hne
  obtain ⟨θ, hθ, hθw⟩ : ∃ θ ∈ Ioc (0 : ℝ) (2 * π), circleMap c r θ = w := by
    rw [← image_circleMap_Ioc] at hw
    exact hw
  have hcont : ContinuousOn (fun θ => u (circleMap c r θ)) (Icc (0 : ℝ) (2 * π)) := by
    apply hu.comp (continuous_circleMap c r).continuousOn
    intro x hx
    exact circleMap_mem_sphere' c r x
  have hint := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    two_pi_pos hcont continuousOn_const
    (fun θ _ => hle _ (circleMap_mem_sphere' c r θ))
    ⟨θ, ⟨hθ.1.le, hθ.2⟩, by simpa only [hθw] using hlt⟩
  have h := mul_lt_mul_of_pos_left hint (inv_pos.mpr two_pi_pos)
  change circleAverage u c r < (2 * π)⁻¹ * ∫ _ in (0 : ℝ)..(2 * π), M at h
  rw [havg] at h
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero, ← mul_assoc,
    inv_mul_cancel₀ two_pi_pos.ne', one_mul] at h
  exact lt_irrefl M h

/-- A continuous subharmonic function which reaches its maximum on a closed
disk at its center is constant on the boundary circle. -/
theorem IsSubharmonicOn.eqOn_sphere_of_maximum {U : Set ℂ} {u : ℂ → ℝ}
    (hsub : IsSubharmonicOn U u) (hcont : ContinuousOn u U)
    {c : ℂ} (hc : c ∈ U) {r : ℝ} (hr : 0 < r)
    (hball : closedBall c r ⊆ U)
    (hmax : ∀ w ∈ closedBall c r, u w ≤ u c) :
    EqOn u (fun _ => u c) (sphere c r) := by
  have hsphere : sphere c r ⊆ U := sphere_subset_closedBall.trans hball
  have hcontSphere : ContinuousOn u (sphere c |r|) := by
    rw [abs_of_pos hr]
    exact hcont.mono hsphere
  have hle : ∀ w ∈ sphere c |r|, u w ≤ u c := by
    rw [abs_of_pos hr]
    exact fun w hw => hmax w (sphere_subset_closedBall hw)
  have hint : CircleIntegrable u c r := hcontSphere.circleIntegrable'
  have hupper : circleAverage u c r ≤ u c := circleAverage_mono_on_of_le_circle hint hle
  have hneg : circleAverage (-u) c r = -circleAverage u c r := by
    rw [← neg_one_smul ℝ u, circleAverage_smul, neg_one_smul]
  have hlower : u c ≤ circleAverage u c r := by
    have hmean := (hsub.2 c hc r hr hball).2
    rw [hneg] at hmean
    simpa only [Pi.neg_apply, neg_le_neg_iff] using hmean
  have heq := le_antisymm hupper hlower
  have := eqOn_sphere_of_circleAverage_eq_of_le u c r (u c) hcontSphere hle heq
  simpa only [abs_of_pos hr] using this

/-- Strong maximum principle for a continuous subharmonic function on a
preconnected open set, expressed using an attained upper bound. -/
theorem IsSubharmonicOn.eqOn_of_attains_upper_bound {U : Set ℂ} {u : ℂ → ℝ}
    (hsub : IsSubharmonicOn U u) (hcont : ContinuousOn u U)
    (hU : IsOpen U) (hconn : IsPreconnected U) {c : ℂ} (hc : c ∈ U)
    (hmax : ∀ x ∈ U, u x ≤ u c) : EqOn u (fun _ => u c) U := by
  let A : Set ℂ := U ∩ u ⁻¹' {u c}
  let B : Set ℂ := U ∩ u ⁻¹' Iio (u c)
  have hA : IsOpen A := by
    rw [Metric.isOpen_iff]
    intro x hx
    have hxU : x ∈ U := hx.1
    have hxu : u x = u c := hx.2
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x hxU
    refine ⟨ε / 2, half_pos hε, ?_⟩
    intro y hy
    have hclosed : closedBall x (ε / 2) ⊆ U :=
      (closedBall_subset_ball (half_lt_self hε)).trans hεU
    have hyclosed : y ∈ closedBall x (ε / 2) := ball_subset_closedBall hy
    have hyU : y ∈ U := hclosed hyclosed
    refine ⟨hyU, ?_⟩
    change u y = u c
    by_cases hyx : y = x
    · simpa only [hyx] using hxu
    · have hd : 0 < dist y x := dist_pos.mpr hyx
      have hdr : dist y x ≤ ε / 2 := mem_closedBall.mp hyclosed
      have hball : closedBall x (dist y x) ⊆ U :=
        (closedBall_subset_closedBall hdr).trans hclosed
      have hmax' : ∀ w ∈ closedBall x (dist y x), u w ≤ u x := by
        intro w hw
        rw [hxu]
        exact hmax w (hball hw)
      have heq := hsub.eqOn_sphere_of_maximum hcont hxU hd hball hmax'
        (mem_sphere.mpr rfl)
      exact heq.trans hxu
  have hB : IsOpen B := hcont.isOpen_inter_preimage hU isOpen_Iio
  have hdis : Disjoint A B := by
    refine disjoint_left.mpr ?_
    intro x hxA hxB
    have hxeq : u x = u c := hxA.2
    have hxlt : u x < u c := hxB.2
    exact (ne_of_lt hxlt) hxeq
  have hcover : U ⊆ A ∪ B := by
    intro x hx
    rcases (hmax x hx).eq_or_lt with heq | hlt
    · exact Or.inl ⟨hx, heq⟩
    · exact Or.inr ⟨hx, hlt⟩
  have hAne : (U ∩ A).Nonempty := ⟨c, hc, hc, rfl⟩
  have hUA := hconn.subset_left_of_subset_union hA hB hdis hcover hAne
  intro x hx
  exact (hUA hx).2

/-- A continuous function which is subharmonic in a disk attains its maximum
over the closed disk at a boundary point. -/
theorem IsSubharmonicOn.exists_maximum_on_sphere {u : ℂ → ℝ} {z : ℂ} {R : ℝ}
    (hR : 0 < R) (hsub : IsSubharmonicOn (ball z R) u)
    (hcont : ContinuousOn u (closedBall z R)) :
    ∃ y ∈ sphere z R, ∀ x ∈ closedBall z R, u x ≤ u y := by
  obtain ⟨c, hc, hmax⟩ := (isCompact_closedBall z R).exists_isMaxOn
    ⟨z, mem_closedBall_self hR.le⟩ hcont
  by_cases hcinside : c ∈ ball z R
  · have hconstant : EqOn u (fun _ => u c) (ball z R) :=
      hsub.eqOn_of_attains_upper_bound (hcont.mono ball_subset_closedBall)
        isOpen_ball (convex_ball z R).isPreconnected hcinside
        (fun x hx => hmax (ball_subset_closedBall hx))
    have hconstantClosed : EqOn u (fun _ => u c) (closedBall z R) :=
      hconstant.of_subset_closure hcont continuousOn_const ball_subset_closedBall
        (by rw [closure_ball z hR.ne'])
    obtain ⟨y, hy⟩ := (NormedSpace.sphere_nonempty (x := z) (r := R)).2 hR.le
    refine ⟨y, hy, fun x hx => ?_⟩
    rw [hconstantClosed (sphere_subset_closedBall hy)]
    exact hmax hx
  · have hcsphere : c ∈ sphere z R := by
      apply mem_sphere.mpr
      have hle := mem_closedBall.mp hc
      have hnlt : ¬ dist c z < R := hcinside
      exact le_antisymm hle (le_of_not_gt hnlt)
    exact ⟨c, hcsphere, fun x hx => hmax hx⟩

/-- The annular form of the maximum principle used in the proof of
Lemma 11.6. -/
theorem IsSubharmonicOn.iSup_annulus_le_iSup_sphere {u : ℂ → ℝ} {z : ℂ}
    {a b : ℝ} (hb : 0 < b) (hsub : IsSubharmonicOn (ball z b) u)
    (hcont : ContinuousOn u (closedBall z b)) :
    (⨆ w ∈ annulus z a b, ENNReal.ofReal (u w)) ≤
      ⨆ w ∈ sphere z b, ENNReal.ofReal (u w) := by
  obtain ⟨y, hy, hmax⟩ := hsub.exists_maximum_on_sphere hb hcont
  refine iSup_le fun w => iSup_le fun hw => ?_
  exact (ENNReal.ofReal_le_ofReal (hmax w (ball_subset_closedBall hw.1))).trans
    (le_iSup_of_le y (le_iSup_of_le hy le_rfl))

/-- The deterministic comparison chain with its maximum estimate supplied by
subharmonicity. The two annular comparison estimates remain explicit. -/
theorem annulus_mass_le_of_subharmonic_comparison_bounds (μ : MeasureTheory.Measure ℂ)
    (Λ : Set ℂ) (u : ℂ → ℝ) (z : ℂ) {r : ℝ} (hr : 0 < r)
    (C₁ C₂ : ENNReal)
    (hsub : IsSubharmonicOn (ball z (4 * r)) u)
    (hcont : ContinuousOn u (ball z (5 * r)))
    (hmass : μ (annulus z r (2 * r) ∩ Λ) ≤
      C₁ * (⨆ w ∈ annulus z ((1 / 2) * r) (4 * r), ENNReal.ofReal (u w)))
    (houter : (⨆ w ∈ annulus z (4 * r) (5 * r), ENNReal.ofReal (u w)) ≤
      C₂ * annulusGreenPotentialSup μ z (3 * r) (6 * r)) :
    μ (annulus z r (2 * r) ∩ Λ) ≤
      (C₁ * C₂) * annulusGreenPotentialSup μ z (3 * r) (6 * r) := by
  apply annulus_mass_le_of_comparison_bounds μ Λ (fun w => ENNReal.ofReal (u w))
    z hr C₁ C₂ _ hmass _ houter
  · intro w hw
    have hwball : w ∈ ball z (5 * r) := by
      rw [mem_sphere] at hw
      exact mem_ball.mpr (hw.trans_lt (by linarith))
    exact ENNReal.continuous_ofReal.continuousAt.comp
      (hcont.continuousAt (isOpen_ball.mem_nhds hwball))
  · exact hsub.iSup_annulus_le_iSup_sphere (by positivity)
      (hcont.mono (closedBall_subset_ball (by linarith)))

end HarmonicBalls
