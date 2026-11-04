import HarmonicBalls.Proofs.Sec5.UniformCentreExhaustion
import HarmonicBalls.Steps.Sec4.ClusterLowerBound
import HarmonicBalls.Proofs.Sec5.LocalMeasureEvaluations

/-! # Uniform exhaustion of compact subsets

A uniform lower bound on the disc Green function away from the boundary gives
one entry time for both the centre and target point in compact subsets.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

/-- The Green function has a uniform positive lower bound when both arguments
lie in a fixed smaller closed disc and are distinct. -/
theorem greenFunction_ball_uniform_pos {R ρ : ℝ} (hρ : 0 ≤ ρ) (hρR : ρ < R) :
    ∃ c : ℝ, 0 < c ∧ ∀ z ∈ closedBall (0 : ℂ) ρ,
      ∀ x ∈ closedBall (0 : ℂ) ρ, x ≠ z → c ≤ greenFunction (ball 0 R) z x := by
  have hR : 0 < R := lt_of_le_of_lt hρ hρR
  let d : ℝ := R ^ 2 - ρ ^ 2
  have hd : 0 < d := by dsimp [d]; nlinarith
  let b : ℝ := 4 * R ^ 4
  have hb : 0 < b := by dsimp [b]; positivity
  let c : ℝ := (4 * Real.pi)⁻¹ * Real.log (1 + d ^ 2 / b)
  have hc : 0 < c := by
    dsimp [c]
    exact mul_pos (by positivity) (Real.log_pos (lt_add_of_pos_right 1 (div_pos (sq_pos_of_pos hd) hb)))
  refine ⟨c, hc, ?_⟩
  intro z hz x hx hxz
  have hzρ : ‖z‖ ≤ ρ := mem_closedBall_zero_iff.mp hz
  have hxρ : ‖x‖ ≤ ρ := mem_closedBall_zero_iff.mp hx
  have hzR : z ∈ ball (0 : ℂ) R := mem_ball_zero_iff.mpr (hzρ.trans_lt hρR)
  have hxR : x ∈ ball (0 : ℂ) R := mem_ball_zero_iff.mpr (hxρ.trans_lt hρR)
  have hdist : ‖z - x‖ ≤ 2 * R := by
    calc
      ‖z - x‖ ≤ ‖z‖ + ‖x‖ := norm_sub_le _ _
      _ ≤ 2 * R := by linarith
  let A : ℝ := ‖(R : ℂ) ^ 2 - starRingEnd ℂ z * x‖
  let B : ℝ := R * ‖z - x‖
  have hA : 0 < A := norm_sub_conj_mul_pos hR (hzρ.trans_lt hρR) (hxρ.trans hρR.le)
  have hB : 0 < B := mul_pos hR (norm_pos_iff.mpr (sub_ne_zero.mpr hxz.symm))
  have hBbound : B ^ 2 ≤ b := by
    dsimp [B, b]
    have hnorm : 0 ≤ ‖z - x‖ := norm_nonneg _
    have hsq : ‖z - x‖ ^ 2 ≤ (2 * R) ^ 2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hsq (sq_nonneg R)
    nlinarith
  have hdiffz : d ≤ R ^ 2 - ‖z‖ ^ 2 := by dsimp [d]; nlinarith [norm_nonneg z]
  have hdiffx : d ≤ R ^ 2 - ‖x‖ ^ 2 := by dsimp [d]; nlinarith [norm_nonneg x]
  have hprod : d ^ 2 ≤ (R ^ 2 - ‖z‖ ^ 2) * (R ^ 2 - ‖x‖ ^ 2) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hdiffz) (sub_nonneg.mpr hdiffx)]
  have hsq : B ^ 2 + d ^ 2 ≤ A ^ 2 := by
    have hi := norm_sq_sub_conj_mul R z x
    dsimp [A, B]
    rw [mul_pow]
    linarith
  have hratio : 1 + d ^ 2 / b ≤ (A / B) ^ 2 := by
    have hb2 : 0 < B ^ 2 := sq_pos_of_pos hB
    have hfrac : d ^ 2 / b ≤ d ^ 2 / B ^ 2 :=
      div_le_div_of_nonneg_left (sq_nonneg d) hb2 hBbound
    have hfrac2 : 1 + d ^ 2 / B ^ 2 ≤ A ^ 2 / B ^ 2 := by
      rw [le_div_iff₀ hb2]
      have he : (1 + d ^ 2 / B ^ 2) * B ^ 2 = B ^ 2 + d ^ 2 := by field_simp
      rw [he]
      exact hsq
    rw [div_pow]
    linarith
  have hlog := Real.log_le_log (by positivity : 0 < 1 + d ^ 2 / b) hratio
  have hlog2 : Real.log ((A / B) ^ 2) = 2 * Real.log (A / B) := by
    rw [Real.log_pow]
    norm_num
  rw [hlog2] at hlog
  have hgreen : greenFunction (ball 0 R) z x = (2 * Real.pi)⁻¹ * Real.log (A / B) := by
    rw [greenFunction_ball_eq_max hzR hxz, max_eq_left (greenBall_nonneg hR (hzρ.trans hρR.le) (hxρ.trans hρR.le))]
    rfl
  rw [hgreen]
  dsimp [c]
  have hp : 0 < Real.pi := Real.pi_pos
  field_simp at hlog ⊢
  nlinarith

/-- A fixed smaller closed disc enters every cluster centred there by a
common time. -/
theorem exists_uniform_closedBall_entry_time_of_volumeGrowth
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R ρ βm βp : ℝ}
    (hρ : 0 ≤ ρ) (hρR : ρ < R) (hV : VolumeGrowth μ R βm βp) :
    ∃ T : ℝ, 0 < T ∧ ∀ z ∈ closedBall (0 : ℂ) ρ, ∀ t : ℝ, T ≤ t →
      closedBall (0 : ℂ) ρ ⊆ cluster μ R z t := by
  have hR : 0 < R := hρ.trans_lt hρR
  obtain ⟨c, hc, hgreen⟩ := greenFunction_ball_uniform_pos hρ hρR
  obtain ⟨M, hM0, hM⟩ := exists_greenPotentialBall_le greenPotentialBallContinuousStep_holds hμ hR hV
  let T := (M + 1) / c
  have hT : 0 < T := by dsimp [T]; positivity
  refine ⟨T, hT, ?_⟩
  intro z hz t ht x hx
  have hzR : z ∈ ball (0 : ℂ) R := (closedBall_subset_ball hρR) hz
  have hxR : x ∈ ball (0 : ℂ) R := (closedBall_subset_ball hρR) hx
  by_cases hxz : x = z
  · rw [hxz]
    exact self_mem_cluster hzR
  · apply mem_cluster_of_lt_mul_greenFunction obstacleLeastSuperharmonicMajorantGeneral_holds
      obstacleCompatibilityShiftStep_holds hμ hR hV hzR (hT.trans_le ht) hM hxR
    have hG := hgreen z hz x hx hxz
    have hbound : M + 1 ≤ t * greenFunction (ball (0 : ℂ) R) z x := by
      calc
        M + 1 = T * c := by dsimp [T]; field_simp
        _ ≤ t * greenFunction (ball (0 : ℂ) R) z x :=
          mul_le_mul ht hG hc.le (hT.trans_le ht).le
    linarith

/-- Compact sets of centres and target points have a common exact entry time. -/
theorem exists_uniform_compact_entry_time_of_volumeGrowth
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {K L : Set ℂ} (hK : IsCompact K) (hL : IsCompact L)
    (hKsub : K ⊆ ball (0 : ℂ) R) (hLsub : L ⊆ ball (0 : ℂ) R) :
    ∃ T : ℝ, 0 < T ∧ ∀ z ∈ K, ∀ t : ℝ, T ≤ t → L ⊆ cluster μ R z t := by
  obtain ⟨n, hn⟩ := (compact_subset_ball_iff_closedBall_exhaustion (hK.union hL)).mp
    (union_subset hKsub hLsub)
  let ρ : ℝ := max 0 (R - 1 / ((n : ℝ) + 1))
  have hρ : 0 ≤ ρ := le_max_left _ _
  have hρR : ρ < R := by
    dsimp [ρ]
    apply max_lt hR
    have hp : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
    linarith
  have hsub : K ∪ L ⊆ closedBall (0 : ℂ) ρ :=
    hn.trans (closedBall_subset_closedBall (le_max_right _ _))
  obtain ⟨T, hT, hentry⟩ := exists_uniform_closedBall_entry_time_of_volumeGrowth hμ hρ hρR hV
  refine ⟨T, hT, ?_⟩
  intro z hz t ht x hx
  exact hentry z (hsub (Or.inl hz)) t ht (hsub (Or.inr hx))

universe u

/-- The common compact-centre and compact-target entry time exists almost
surely and simultaneously for all disc radii, under volume growth. -/
theorem ae_uniform_compact_entry_time
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R → ∀ K L : Set ℂ, IsCompact K → IsCompact L →
      K ⊆ ball 0 R → L ⊆ ball 0 R →
      ∃ T : ℝ, 0 < T ∧ ∀ z ∈ K, ∀ t : ℝ, T ≤ t → L ⊆ cluster (μ ω) R z t := by
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV] with ω hω
  intro R hR K L hK hL hKsub hLsub
  exact exists_uniform_compact_entry_time_of_volumeGrowth hω.1 hR (hω.2 R hR)
    hK hL hKsub hLsub


end HarmonicBalls
