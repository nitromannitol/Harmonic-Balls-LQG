import HarmonicBalls.Proofs.Sec3.ClusterCompatibility

/-!
# Lemma A.5: Step 1 (the odometer is subharmonic off the pole)

`obstacleConservationOfMassStep1_holds`: `Δ v_t ≥ 0` on `B_R \ {z}` for the odometer `v_t = ṽ_t - β_t`. On
`Λ_t \ {z}`, `v_t = ṽ_t + t G_{B_R}(z,·) - q_{B_R}` has the sub-mean-value property (Lemma A.2 Step 2, harmonicity of
`G_{B_R}(z,·)` off the pole, superharmonicity of `q_{B_R}`); off `Λ_t`, `v_t = 0 ≤ M(v_t; x, r)` since `v_t ≥ 0`. The
local sub-mean-value property is global (AG01 Thm 3.2.2) and gives `Δ v_t ≥ 0` by the converse of Weyl's lemma.
-/

namespace HarmonicBalls

open MeasureTheory Metric Filter Topology Set Laplacian

/-- **Lemma A.5, Step 1** (`ObstacleConservationOfMassStep1`). -/
theorem obstacleConservationOfMassStep1_holds : ObstacleConservationOfMassStep1 := by
  intro μ hμ R βm βp hR hV z hz t ht
  obtain ⟨-, hvc, hvS, -, -⟩ := obstacleLeastSuperharmonicMajorantGeneral_holds μ hμ R βm βp hR hV z hz t ht
  set v := shiftedLeastSupersolution μ R z t with hvdef
  set β := obstacle μ R z t with hβdef
  set q := greenPotentialBall μ R with hqdef
  set G := greenFunction (ball (0 : ℂ) R) z with hGdef
  set U := ball (0 : ℂ) R \ {z} with hUdef
  have hUo : IsOpen U := isOpen_ball.sdiff isClosed_singleton
  have hqc : ContinuousOn q (closedBall 0 R) := greenPotentialBallContinuousStep_holds μ hμ R βm βp hR hV
  have hqsh := isSuperharmonicOn_greenPotentialBall hμ hR hV
  have hβc : ContinuousOn β (closedBall 0 R \ {z}) := continuousOn_obstacle (t := t) greenFunctionBall hR hz hqc
  have h2 := obstacleNonCoincidenceHarmonicStep2_holds μ hμ R βm βp hR hV z hz t ht
  have hΛo := isOpen_nonCoincidenceSet_of obstacleLeastSuperharmonicMajorantGeneral_holds hμ hR hV hz ht
  set o : ℂ → ℝ := fun x => v x - β x with hodef
  have hUcl : U ⊆ closedBall 0 R \ {z} := fun x hx => ⟨ball_subset_closedBall hx.1, hx.2⟩
  have hoc : ContinuousOn o U := (hvc.mono fun x hx => (hUcl hx).1).sub (hβc.mono hUcl)
  have ho0 : ∀ x ∈ closedBall (0 : ℂ) R, x ≠ z → 0 ≤ o x := fun x hx hxz => by
    have := hvS.2.2 x hx hxz
    show 0 ≤ v x - β x
    linarith
  have hoci : ∀ {x : ℂ} {r : ℝ}, 0 < r → closedBall x r ⊆ U → CircleIntegrable o x r := fun hr hsub =>
    (hoc.mono (sphere_subset_closedBall.trans hsub)).circleIntegrable hr.le
  -- local sub-mean-value property of `o` on `U`
  have hloc : ∀ x ∈ U, ∃ r₀ > 0, ∀ r ∈ Ioo 0 r₀,
      CircleIntegrable (-o) x r ∧ Real.circleAverage (-o) x r ≤ (-o) x := by
    intro x hx
    by_cases hxΛ : x ∈ nonCoincidenceSet μ R z t
    · obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.1 (hΛo.inter hUo) x ⟨hxΛ, hx⟩
      refine ⟨ρ, hρ, fun r hr => ?_⟩
      have hsub : closedBall x r ⊆ nonCoincidenceSet μ R z t ∩ U := (closedBall_subset_ball hr.2).trans hρsub
      have hsubΛ : closedBall x r ⊆ nonCoincidenceSet μ R z t := fun y hy => (hsub hy).1
      have hsubU : closedBall x r ⊆ U := fun y hy => (hsub hy).2
      have hsubB : closedBall x r ⊆ ball 0 R := fun y hy => (hsubU hy).1
      have hsph : sphere x r ⊆ closedBall x r := sphere_subset_closedBall
      have hvi : CircleIntegrable v x r :=
        (hvc.mono ((hsph.trans hsubB).trans ball_subset_closedBall)).circleIntegrable hr.1.le
      have hGi : CircleIntegrable G x r :=
        ((continuousOn_greenFunction_ball hz).mono fun y hy => (hsubU (hsph hy)).2).circleIntegrable hr.1.le
      have hqi : CircleIntegrable q x r :=
        (hqc.mono ((hsph.trans hsubB).trans ball_subset_closedBall)).circleIntegrable hr.1.le
      have hβi : CircleIntegrable β x r := (hβc.mono fun y hy => hUcl (hsubU (hsph hy))).circleIntegrable hr.1.le
      have hvsub : v x ≤ Real.circleAverage v x r := by
        have := (h2.2 x (hsubΛ (mem_closedBall_self hr.1.le)) r hr.1 hsubΛ).2
        rw [circleAverage_neg_fun, Pi.neg_apply] at this
        linarith
      have hGeq : Real.circleAverage G x r = G x :=
        InnerProductSpace.HarmonicOnNhd.circleAverage_eq
          ((harmonicOnNhd_greenFunction_ball hz).mono (by rw [abs_of_pos hr.1]; exact hsubU))
      have hqsup : Real.circleAverage q x r ≤ q x := (hqsh.2 x (hsubB (mem_closedBall_self hr.1.le)) r hr.1 hsubB).2
      have hβfun : β = fun y => (-t) • G y + q y := by
        funext y
        simp only [hβdef, obstacle, hGdef, hqdef, smul_eq_mul]
      have hGi' : CircleIntegrable (fun y => (-t) • G y) x r := hGi.const_smul
      have hβavg : Real.circleAverage β x r = -t * G x + Real.circleAverage q x r := by
        rw [hβfun, Real.circleAverage_fun_add hGi' hqi, Real.circleAverage_fun_smul, hGeq, smul_eq_mul]
      have hβx : β x = -t * G x + q x := by simp only [hβdef, obstacle, hGdef, hqdef]
      have hoavg : Real.circleAverage o x r = Real.circleAverage v x r - Real.circleAverage β x r :=
        Real.circleAverage_fun_sub hvi hβi
      refine ⟨(hoci hr.1 hsubU).neg, ?_⟩
      rw [circleAverage_neg_fun, Pi.neg_apply, hoavg]
      show -(Real.circleAverage v x r - Real.circleAverage β x r) ≤ -(v x - β x)
      linarith
    · have hxz : x ≠ z := hx.2
      have hox : o x = 0 := by
        have hle : ¬ (β x < v x) := fun h => hxΛ ⟨hx.1, Or.inr h⟩
        have := ho0 x (ball_subset_closedBall hx.1) hxz
        show v x - β x = 0
        have : v x - β x ≤ 0 := by linarith [not_lt.1 hle]
        linarith [ho0 x (ball_subset_closedBall hx.1) hxz]
      obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.1 hUo x hx
      refine ⟨ρ, hρ, fun r hr => ?_⟩
      have hsubU : closedBall x r ⊆ U := (closedBall_subset_ball hr.2).trans hρsub
      have hoi := hoci hr.1 hsubU
      refine ⟨hoi.neg, ?_⟩
      have hmono := Real.circleAverage_mono (continuousOn_const.circleIntegrable' (f := fun _ : ℂ => (0 : ℝ))) hoi
        fun y hy => ho0 y (hUcl (hsubU (sphere_subset_closedBall (by rwa [abs_of_pos hr.1] at hy)))).1
          (hUcl (hsubU (sphere_subset_closedBall (by rwa [abs_of_pos hr.1] at hy)))).2
      rw [Real.circleAverage_const] at hmono
      rw [circleAverage_neg_fun, Pi.neg_apply, hox]
      linarith
  have hlsc : LowerSemicontinuousOn (-o) U := hoc.neg.lowerSemicontinuousOn
  have hsh : IsSuperharmonicOn U (-o) := ⟨hlsc, fun x hx r hr hsub =>
    ⟨(hoci hr hsub).neg, circleAverage_le_of_localSuperMean hlsc hloc hr hsub (hoci hr hsub).neg⟩⟩
  have hGE := LaplacianGE.of_laplacianLE_neg (laplacianLEOfSuperharmonicStep_holds U (-o) hUo hoc.neg hsh)
  exact hGE

end HarmonicBalls
