import HarmonicBalls.Steps.SecA.ObstacleMonotone
import HarmonicBalls.Proofs.SecA.ObstacleNonCoincidenceHarmonic

/-!
# Lemma A.3: proof of Step 1 (the truncated competitor)

Proof of `ObstacleMonotoneStep1` of `Steps/SecA/ObstacleMonotone.lean` (lines 3743-3763 with the repair of the pole
issue, GRAPH.md A.3), for a general radius `R > 0` and pole `z ∈ B_R`. For `0 < t₁ < t₂` the printed competitor
`s̃ = ṽ_{t₂} + (t₂ - t₁) G_{B_R}(z,·)` has a `+∞` pole at `z`; the truncation `w = min (s̃, M)` (value `M` at the
pole), with `M ≥ max_{closedBall} |q_{B_R}|`, lies in `S̃(t₁)`:

* continuity: `s̃` is continuous off the pole (Lemma A.1, Prop 2.3) and `s̃ → +∞` at the pole
  (`ObstacleTendstoAtBotStep` for `β_{t₂ - t₁}`, `ṽ_{t₂} ≥ 0`), so `w = M` near the pole;
* superharmonicity: near the pole `w` is constant; off the pole `M(w; x, r) ≤ min (M(s̃; x, r), M) ≤ w(x)` on small
  circles (`ṽ_{t₂}` superharmonic, `G_{B_R}(z,·)` harmonic off the pole); the local super-mean-value property is
  global (`circleAverage_le_of_localSuperMean`), and `Δw ≤ 0` by `laplacianLEOfSuperharmonicStep_holds`;
* obstacle: `β_{t₁} = β_{t₂} + (t₂ - t₁) G ≤ s̃` and `β_{t₁} ≤ q_{B_R} ≤ M` (`G ≥ 0`).
-/

namespace HarmonicBalls

open MeasureTheory Metric Filter Topology Set

/-- **Lemma A.3, Step 1** (the truncated competitor), given Lemma A.1 (general form). -/
theorem obstacleMonotoneStep1_of (hA1 : ObstacleLeastSuperharmonicMajorantGeneral) : ObstacleMonotoneStep1 := by
  intro μ hμ R βm βp hR hV z hz t₁ t₂ ht₁ ht₁₂
  have ht₂ : 0 < t₂ := ht₁.trans ht₁₂
  obtain ⟨-, hvc, hvS, hv0, -⟩ := hA1 μ hμ R βm βp hR hV z hz t₂ ht₂
  set v := shiftedLeastSupersolution μ R z t₂ with hvdef
  set G := greenFunction (ball (0 : ℂ) R) z with hGdef
  set q := greenPotentialBall μ R with hqdef
  set c := t₂ - t₁ with hcdef
  have hc : 0 < c := sub_pos.2 ht₁₂
  have hqc : ContinuousOn q (closedBall 0 R) := greenPotentialBallContinuousStep_holds μ hμ R βm βp hR hV
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn hqc
  set M := max B 0 with hMdef
  have hGc : ContinuousOn G {z}ᶜ := continuousOn_greenFunction_ball hz
  have hG0 : ∀ x, 0 ≤ G x := fun x => greenFunction_nonneg (isBounded_ball (x := (0 : ℂ)) (r := R)) z x
  have hvsh : IsSuperharmonicOn (ball 0 R) v :=
    superharmonicOfLaplacianLEStep_holds _ v isOpen_ball (hvc.mono ball_subset_closedBall) hvS.2.1
  -- near the pole the competitor exceeds `M`
  have hbig : ∀ᶠ y in 𝓝[≠] z, M ≤ v y + c * G y := by
    have hβ := (obstacleTendstoAtBotStep_holds μ R z c hR hz hc hqc).eventually
      (eventually_lt_atBot (-(M + B)))
    filter_upwards [hβ, nhdsWithin_le_nhds (isOpen_ball.mem_nhds hz)] with y hy hyb
    have hyc : y ∈ closedBall (0 : ℂ) R := ball_subset_closedBall hyb
    have hqy : -B ≤ q y := by
      have := hB y hyc
      rw [Real.norm_eq_abs] at this
      linarith [neg_abs_le (q y)]
    have hvy := hv0 y hyc
    rw [obstacle, ← hGdef, ← hqdef] at hy
    linarith
  set w : ℂ → ℝ := fun x => if x = z then M else min (v x + c * G x) M with hwdef
  have hwz : w z = M := by simp [hwdef]
  have hwne : ∀ x, x ≠ z → w x = min (v x + c * G x) M := fun x hx => by simp [hwdef, hx]
  have hwev : w =ᶠ[𝓝 z] fun _ => M := by
    rw [eventually_nhdsWithin_iff] at hbig
    filter_upwards [hbig] with y hy
    by_cases hyz : y = z
    · rw [hyz, hwz]
    · rw [hwne y hyz]
      exact min_eq_right (hy hyz)
  -- continuity
  have hwc : ContinuousOn w (closedBall 0 R) := by
    intro x hx
    by_cases hxz : x = z
    · subst hxz
      exact (continuousAt_const.congr hwev.symm).continuousWithinAt
    · have hGx : ContinuousAt G x := hGc.continuousAt (isOpen_compl_singleton.mem_nhds hxz)
      have hs : ContinuousWithinAt (fun y => min (v y + c * G y) M) (closedBall 0 R) x :=
        ((hvc x hx).add (continuousWithinAt_const.mul hGx.continuousWithinAt)).min continuousWithinAt_const
      refine hs.congr_of_eventuallyEq ?_ (hwne x hxz)
      filter_upwards [nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hxz)] with y hy
      exact hwne y hy
  have hwci : ∀ {x : ℂ} {r : ℝ}, 0 < r → closedBall x r ⊆ ball 0 R → CircleIntegrable w x r :=
    fun hr hsub => (hwc.mono ((sphere_subset_closedBall.trans hsub).trans ball_subset_closedBall)).circleIntegrable
      hr.le
  -- local super-mean-value property
  have hloc : ∀ x ∈ ball (0 : ℂ) R, ∃ r₀ > 0, ∀ r ∈ Ioo 0 r₀,
      CircleIntegrable w x r ∧ Real.circleAverage w x r ≤ w x := by
    intro x hx
    by_cases hxz : x = z
    · subst hxz
      obtain ⟨ε, hε, hεw⟩ := Metric.eventually_nhds_iff.1 hwev
      obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.1 isOpen_ball x hx
      refine ⟨min ε ρ, lt_min hε hρ, fun r hr => ?_⟩
      have hrsub : closedBall x r ⊆ ball 0 R :=
        (closedBall_subset_ball (lt_of_lt_of_le hr.2 (min_le_right _ _))).trans hρsub
      refine ⟨hwci hr.1 hrsub, ?_⟩
      have hsph : EqOn w (fun _ => M) (sphere x |r|) := fun y hy => by
        rw [abs_of_pos hr.1] at hy
        exact hεw (lt_of_le_of_lt (le_of_eq (mem_sphere.1 hy)) (lt_of_lt_of_le hr.2 (min_le_left _ _)))
      rw [Real.circleAverage_congr_sphere hsph, Real.circleAverage_const, hwz]
    · obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.1 (isOpen_ball.sdiff isClosed_singleton) x ⟨hx, hxz⟩
      refine ⟨ρ, hρ, fun r hr => ?_⟩
      have hsubz : closedBall x r ⊆ ball 0 R \ {z} := (closedBall_subset_ball hr.2).trans hρsub
      have hrsub : closedBall x r ⊆ ball 0 R := fun y hy => (hsubz hy).1
      have hsph : sphere x r ⊆ closedBall x r := sphere_subset_closedBall
      have hwi := hwci hr.1 hrsub
      have hvcs : ContinuousOn v (sphere x r) :=
        hvc.mono ((hsph.trans hrsub).trans ball_subset_closedBall)
      have hGcs : ContinuousOn G (sphere x r) := hGc.mono fun y hy => (hsubz (hsph hy)).2
      have hvi : CircleIntegrable v x r := hvcs.circleIntegrable hr.1.le
      have hcGi : CircleIntegrable (fun y => c * G y) x r :=
        (continuousOn_const.mul hGcs).circleIntegrable hr.1.le
      have hsi : CircleIntegrable (fun y => v y + c * G y) x r :=
        (hvcs.add (continuousOn_const.mul hGcs)).circleIntegrable hr.1.le
      have hGeq : Real.circleAverage G x r = G x :=
        InnerProductSpace.HarmonicOnNhd.circleAverage_eq
          ((harmonicOnNhd_greenFunction_ball hz).mono (by rw [abs_of_pos hr.1]; exact hsubz))
      have hcG : Real.circleAverage (fun y => c * G y) x r = c * Real.circleAverage G x r := by
        have := Real.circleAverage_fun_smul (f := G) (c := x) (R := r) (a := c)
        simpa [smul_eq_mul] using this
      have hvsup : Real.circleAverage v x r ≤ v x := (hvsh.2 x hx r hr.1 hrsub).2
      have hne : ∀ y ∈ sphere x |r|, y ≠ z := fun y hy => by
        rw [abs_of_pos hr.1] at hy
        exact (hsubz (hsph hy)).2
      have h1 : Real.circleAverage w x r ≤ Real.circleAverage (fun y => v y + c * G y) x r :=
        Real.circleAverage_mono hwi hsi fun y hy => by
          rw [hwne y (hne y hy)]
          exact min_le_left _ _
      have h2 : Real.circleAverage w x r ≤ M := by
        have := Real.circleAverage_mono hwi (continuousOn_const.circleIntegrable' (f := fun _ : ℂ => M))
          fun y hy => by
            show w y ≤ M
            rw [hwne y (hne y hy)]
            exact min_le_right _ _
        rwa [Real.circleAverage_const] at this
      rw [Real.circleAverage_fun_add hvi hcGi, hcG, hGeq] at h1
      refine ⟨hwi, ?_⟩
      rw [hwne x hxz]
      exact le_min (by linarith) h2
  have hlsc : LowerSemicontinuousOn w (ball 0 R) := (hwc.mono ball_subset_closedBall).lowerSemicontinuousOn
  have hwsh : IsSuperharmonicOn (ball 0 R) w := ⟨hlsc, fun x hx r hr hsub =>
    ⟨hwci hr hsub, circleAverage_le_of_localSuperMean hlsc hloc hr hsub (hwci hr hsub)⟩⟩
  have hwLE : LaplacianLE w 0 (ball 0 R) :=
    laplacianLEOfSuperharmonicStep_holds _ w isOpen_ball (hwc.mono ball_subset_closedBall) hwsh
  refine ⟨w, ⟨hwc, hwLE, fun x hx hxz => ?_⟩, fun x hx hxz => ?_⟩
  · rw [hwne x hxz]
    have h2 := hvS.2.2 x hx hxz
    have hqx : q x ≤ B := by
      have := hB x hx
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans this
    have hGx := hG0 x
    have htG := mul_nonneg ht₁.le hGx
    rw [obstacle, ← hGdef, ← hqdef] at h2 ⊢
    have hexp : c * G x = t₂ * G x - t₁ * G x := by rw [hcdef]; ring
    refine le_min (by linarith) ?_
    linarith [le_max_left B 0]
  · rw [hwne x hxz]
    exact min_le_left _ _

end HarmonicBalls
