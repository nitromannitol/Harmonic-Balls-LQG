import HarmonicBalls.Steps.Sec4.Basic

/-!
# Proposition 4.1 (prop:lower-bound, line 673): reduction to Sections 2-3 and Appendix A

`clusterLowerBound_of_steps : ClusterLowerBoundStmt` from the statements of Sections 2-3 and steps of Appendix A.

## The printed proof (lines 691-713)

Let `q_1` be the expected exit time of LBM from `B_1`, `Δ q_1 = -μ_h` in `B_1`, `q_1 = 0` on `∂B_1`. Since
`Δ v^z_t ≤ μ_h` (Lemma 3.1), `v^z_t + q_1` is superharmonic in `B_1` and `≥ 0` on `∂B_1`, so `v^z_t ≥ -q_1` on the
closed ball (minimum principle). As `q_1` is finite (Proposition 2.5) and the obstacle `-t G_{B_1}(z,·)` tends to
`-∞` at `z` (the printed `t log |x - z|`, lines 704-708, is the obstacle up to the normalization and a bounded
term), `v^z_t > -t G_{B_1}(z,·)` near `z`, i.e. `B_ε(z) ⊆ Λ^z_t`. "Similarly" `B_{1-δ}(z) ⊆ Λ^z_t` for
`t ≥ t(δ)`. The last claim takes `t⁺ = μ_h(B_1)` and cites Lemma 3.4.

## Route in Lean

* **`v ≥ -q_1`** (`neg_greenPotentialBall_le_leastSupersolution`). In Lean `q_1 = q_{B_1}` is the Green potential
  `greenPotentialBall μ 1` of Appendix A (eq:expected-exit-time, line 3532). The minimum principle argument is the
  by-product `ṽ_t ≥ 0` of Lemma A.1 (general form, `ObstacleLeastSuperharmonicMajorantGeneral`; its Step 1 is the
  minimum principle for superharmonic majorants of the obstacle) and the substitution `v = ṽ_t - q_{B_1}`
  (`ObstacleCompatibilityShiftStep`, lines 3574-3578).
* **`q_1` bounded.** The paper's "`q_1` is finite" is not enough for a uniform bound; `q_{B_1}` is continuous on the
  closed ball (property 1 of `q_{B_R}`, line 3538, `GreenPotentialBallContinuousStep`; its body is proved as
  `greenPotentialBall_continuousOn` in Proofs/Potential/GreenPotentialHolder.lean), hence bounded by some `M`.
* **First two claims** (`ball_subset_cluster_of_general`). `G_{B_1}(z,x) ≥ (2π)⁻¹ log (ρ/|x - z|)` near `z`
  (`log_div_le_greenFunction`), and `G_{B_1}(z,·) ≥ c > 0` on `B_{1-δ}(z) \ {z}` for `δ > |z|`
  (`exists_pos_le_greenFunction_ball`: Proposition 2.3 and compactness). Then `t G_{B_1}(z,x) > M ≥ q_1(x) ≥ -v(x)`
  for `x` in `B_ε(z)`, resp. in `B_{1-δ}(z)` when `t ≥ t(δ) = (M+1)/c`.
* **Last claim** (`closure_cluster_inter_sphere_nonempty`). The equality case of Lemma 3.4 needs
  `μ_h(∂Λ^z_t) = 0`, which is not available. The claim follows instead from the mass
  identity `μ_h(Λ) + ν(∂Λ) = t` for `closure Λ ⊆ B_1`, which is the equality case of Lemma A.5, Step 3
  (`ObstacleConservationOfMassStep3`: `σ(B_R) = t` when `v` vanishes off a compact subset of `B_R`; no condition
  on `∂Λ`), applied to the odometer with the measure `σ = μ_h|_Λ + ν|_{∂Λ}` of Lemma 3.2. Since `ν ≤ μ_h` on `B_1`
  and `Λ ∩ ∂Λ = ∅`, `t = σ(B_1) ≤ μ_h(B_1)`. Hence `t⁺ = μ_h(B_1) + 1` works (the printed `t⁺ = μ_h(B_1)` would need
  a strict inequality; any `t⁺ > μ_h(B_1)` does). `μ_h(B_1) < ∞` since `μ_h` is Radon.

## Hypotheses consumed

Input I2 (`LQGVolumeGrowthAllScalesStmt`), Proposition 2.3 (`GreenFunctionBallStmt`), Lemmas 3.1, 3.2, 3.4
(`LeastSupersolutionMemStmt`, `ClusterOpenLaplacianStmt`, `ClusterConservationOfMassStmt`), and from Appendix A:
`ObstacleLeastSuperharmonicMajorantGeneral`, `ObstacleCompatibilityShiftStep`, `GreenPotentialBallContinuousStep`,
`ObstacleConservationOfMassStep3`.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

universe u

section Deterministic

variable {μ : Measure ℂ} {r βm βp : ℝ} {z : ℂ} {t : ℝ}

/-- **`v_{B_r;z}(t) ≥ -q_{B_r}` on the closed ball** (lines 701-703): Lemma A.1 (general form) gives `ṽ_t ≥ 0`, and
`v = ṽ_t - q_{B_r}` (the substitution of lines 3574-3578). -/
theorem neg_greenPotentialBall_le_leastSupersolution (hA1 : ObstacleLeastSuperharmonicMajorantGeneral)
    (hS : ObstacleCompatibilityShiftStep) (hμ : IsLocallyFiniteMeasure μ) (hr : 0 < r)
    (hV : VolumeGrowth μ r βm βp) (hz : z ∈ ball (0 : ℂ) r) (ht : 0 < t) {x : ℂ}
    (hx : x ∈ closedBall (0 : ℂ) r) :
    -greenPotentialBall μ r x ≤ leastSupersolution μ r z t x := by
  obtain ⟨-, -, -, hnn, -⟩ := hA1 μ hμ r βm βp hr hV z hz t ht
  obtain ⟨-, hv, -, -⟩ := hS μ hμ r βm βp hr hV z hz t ht
  rw [hv x hx]
  linarith [hnn x hx]

/-- `q_{B_r}` is bounded above on the closed ball (continuity, property 1 of `q_{B_R}`, line 3538). -/
theorem exists_greenPotentialBall_le (hcont : GreenPotentialBallContinuousStep) (hμ : IsLocallyFiniteMeasure μ)
    (hr : 0 < r) (hV : VolumeGrowth μ r βm βp) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ closedBall (0 : ℂ) r, greenPotentialBall μ r x ≤ M := by
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn (hcont μ hμ r βm βp hr hV)
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  have h := hC x hx
  rw [Real.norm_eq_abs] at h
  exact (le_abs_self _).trans (h.trans (le_max_left _ _))

/-- A point `x ≠ z` of `B_r` with `t G_{B_r}(z,x) > M ≥ q_{B_r}` lies in the cluster (eq:lower-bound-green,
line 707). -/
theorem mem_cluster_of_lt_mul_greenFunction (hA1 : ObstacleLeastSuperharmonicMajorantGeneral)
    (hS : ObstacleCompatibilityShiftStep) (hμ : IsLocallyFiniteMeasure μ) (hr : 0 < r)
    (hV : VolumeGrowth μ r βm βp) (hz : z ∈ ball (0 : ℂ) r) (ht : 0 < t) {M : ℝ}
    (hM : ∀ x ∈ closedBall (0 : ℂ) r, greenPotentialBall μ r x ≤ M) {x : ℂ} (hx : x ∈ ball (0 : ℂ) r)
    (hlt : M < t * greenFunction (ball 0 r) z x) : x ∈ cluster μ r z t := by
  refine ⟨hx, Or.inr ?_⟩
  have h1 := neg_greenPotentialBall_le_leastSupersolution hA1 hS hμ hr hV hz ht (ball_subset_closedBall hx)
  have h2 := hM x (ball_subset_closedBall hx)
  linarith

theorem mem_ball_zero_of_mem_ball {s : ℝ} {x : ℂ} (hx : x ∈ ball z s) (hs : ‖z‖ + s ≤ 1) :
    x ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball, dist_eq_norm] at hx
  rw [mem_ball_zero_iff]
  calc ‖x‖ = ‖(x - z) + z‖ := by rw [sub_add_cancel]
    _ ≤ ‖x - z‖ + ‖z‖ := norm_add_le _ _
    _ < 1 := by linarith

/-- **Proposition 4.1, first two claims, deterministic form** (lines 699-710), for a Radon measure with the volume
growth condition on `B_1`. -/
theorem ball_subset_cluster_of_general (hA1 : ObstacleLeastSuperharmonicMajorantGeneral)
    (hS : ObstacleCompatibilityShiftStep) (hcont : GreenPotentialBallContinuousStep) (h23 : GreenFunctionBallStmt)
    (hμ : IsLocallyFiniteMeasure μ) (hV : VolumeGrowth μ 1 βm βp) (hz : z ∈ ball (0 : ℂ) 1) :
    (∀ t : ℝ, 0 < t → ∃ ε : ℝ, 0 < ε ∧ ball z ε ⊆ cluster μ 1 z t) ∧
    (∀ δ ∈ Ioo ‖z‖ 1, ∃ tδ : ℝ, 0 < tδ ∧ ∀ t : ℝ, tδ ≤ t → ball z (1 - δ) ⊆ cluster μ 1 z t) := by
  obtain ⟨M, hM0, hM⟩ := exists_greenPotentialBall_le hcont hμ one_pos hV
  refine ⟨fun t ht => ?_, fun δ hδ => ?_⟩
  · obtain ⟨ε, hε, hεz, hnear⟩ := exists_le_greenFunction_ball_near_pole hz ((M + 1) / t)
    refine ⟨ε, hε, fun x hx => ?_⟩
    have hx1 := mem_ball_zero_of_mem_ball hx (by linarith)
    by_cases hxz : x = z
    · rw [hxz]
      exact self_mem_cluster hz
    refine mem_cluster_of_lt_mul_greenFunction hA1 hS hμ one_pos hV hz ht hM hx1 ?_
    rw [mem_ball, dist_eq_norm] at hx
    have h := hnear x (norm_pos_iff.2 (sub_ne_zero.2 hxz)) hx
    rw [div_le_iff₀ ht] at h
    linarith
  · obtain ⟨hδ1, hδ2⟩ := hδ
    obtain ⟨c, hc, hlow⟩ := exists_pos_le_greenFunction_ball h23 hz (s := 1 - δ) (by linarith)
    have htδ : 0 < (M + 1) / c := div_pos (by linarith) hc
    refine ⟨(M + 1) / c, htδ, fun t ht x hx => ?_⟩
    have htpos : 0 < t := htδ.trans_le ht
    have hx1 := mem_ball_zero_of_mem_ball hx (by linarith)
    by_cases hxz : x = z
    · rw [hxz]
      exact self_mem_cluster hz
    refine mem_cluster_of_lt_mul_greenFunction hA1 hS hμ one_pos hV hz htpos hM hx1 ?_
    have hG := hlow x hx hxz
    have h : M + 1 ≤ t * greenFunction (ball 0 1) z x :=
      calc M + 1 = (M + 1) / c * c := by field_simp
        _ ≤ t * greenFunction (ball 0 1) z x := mul_le_mul ht hG hc.le htpos.le
    linarith

/-- **Proposition 4.1, last claim** (lines 711-712). If `t > μ(B_1)`, the closure of `Λ = Λ^z_t` meets
`∂B_1`. Otherwise `closure Λ` is a compact subset of `B_1` off which the odometer vanishes, and the equality case
of Lemma A.5, Step 3 (`ObstacleConservationOfMassStep3`) gives `t = (μ|_Λ + ν|_{∂Λ})(B_1) ≤ μ(B_1)` for the
measure of Lemma 3.2. -/
theorem closure_cluster_inter_sphere_nonempty (hStep3 : ObstacleConservationOfMassStep3) {ν : Measure ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) (ht : 0 < t) (hfin : μ (ball (0 : ℂ) 1) ≠ ⊤)
    (htμ : (μ (ball (0 : ℂ) 1)).toReal < t) (hopen : IsOpen (cluster μ 1 z t))
    (hle : ν.restrict (ball 0 1) ≤ μ.restrict (ball 0 1))
    (hLap : HasLaplacian (odometer μ 1 z t)
      (μ.restrict (cluster μ 1 z t) + ν.restrict (frontier (cluster μ 1 z t)))
      (ENNReal.ofReal t • Measure.dirac z) (ball 0 1))
    (hcont : ContinuousOn (odometer μ 1 z t) (closedBall 0 1 \ {z}))
    (hsph : ∀ x ∈ sphere (0 : ℂ) 1, odometer μ 1 z t x = 0) :
    (closure (cluster μ 1 z t) ∩ sphere (0 : ℂ) 1).Nonempty := by
  set Λ := cluster μ 1 z t with hΛ
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have hcl : closure Λ ⊆ closedBall (0 : ℂ) 1 :=
    closure_minimal (cluster_subset_ball.trans ball_subset_closedBall) isClosed_closedBall
  have hclb : closure Λ ⊆ ball (0 : ℂ) 1 := by
    intro x hx
    have h1 := mem_closedBall_zero_iff.1 (hcl hx)
    rw [mem_ball_zero_iff]
    refine lt_of_le_of_ne h1 fun h => ?_
    have : x ∈ closure Λ ∩ sphere (0 : ℂ) 1 := ⟨hx, mem_sphere_zero_iff_norm.2 h⟩
    rw [hne] at this
    exact this
  have hK : IsCompact (closure Λ) :=
    (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset isClosed_closure hcl
  have h3 := hStep3 1 z t _ (odometer μ 1 z t) one_pos hz ht.le hLap
    (fun x hx hxz => odometer_nonneg ht.le (ball_subset_closedBall hx) hxz) hcont hsph
  have heq := h3.2 ⟨closure Λ, hK, hclb, fun x hx =>
    odometer_eq_zero_of_notMem_cluster ht.le hx.1 fun h => hx.2 (subset_closure h)⟩
  have hσ : (μ.restrict Λ + ν.restrict (frontier Λ)) (ball 0 1) ≤ μ (ball 0 1) := by
    have h := Measure.le_iff'.1 (restrict_add_restrict_frontier_le hopen measurableSet_ball hle) univ
    rwa [Measure.restrict_apply_univ, Measure.restrict_apply_univ] at h
  rw [heq] at hσ
  exact absurd hσ (not_le.2 ((ENNReal.lt_ofReal_iff_toReal_lt hfin).2 htμ))

end Deterministic

/-- **Proposition 4.1 from Sections 2-3 and Appendix A** (lines 691-713, with the repair of the last claim). -/
theorem clusterLowerBound_of_steps (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h23 : GreenFunctionBallStmt)
    (h31 : LeastSupersolutionMemStmt.{u}) (h32 : ClusterOpenLaplacianStmt.{u})
    (h34 : ClusterConservationOfMassStmt.{u}) (hA1 : ObstacleLeastSuperharmonicMajorantGeneral)
    (hS : ObstacleCompatibilityShiftStep) (hcont : GreenPotentialBallContinuousStep)
    (hStep3 : ObstacleConservationOfMassStep3) : ClusterLowerBoundStmt.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨βm, βp, hae⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hae, h31 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ, h32 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    h34 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hω h1 h2 h4
  intro z hz
  have := hω.1
  obtain ⟨ha, hb⟩ := ball_subset_cluster_of_general hA1 hS hcont h23 hω.1 (hω.2 1 one_pos) hz
  refine ⟨ha, hb, (μ ω (ball 0 1)).toReal + 1, by positivity, fun t ht => ?_⟩
  have htpos : 0 < t := by
    have := ENNReal.toReal_nonneg (a := μ ω (ball 0 1))
    linarith
  obtain ⟨hopen, -, ν, -, -, hle, -, hLap⟩ := h2 t 1 htpos one_pos z hz
  exact closure_cluster_inter_sphere_nonempty hStep3 hz htpos measure_ball_lt_top.ne (by linarith) hopen hle
    hLap (continuousOn_odometer h23 one_pos hz (h1 t 1 htpos one_pos z hz).2.1)
    (h4 1 t one_pos htpos z hz).2.1

end HarmonicBalls
