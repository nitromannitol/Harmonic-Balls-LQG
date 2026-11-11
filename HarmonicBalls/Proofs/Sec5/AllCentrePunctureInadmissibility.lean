import HarmonicBalls.Proofs.Sec5.PunctureInadmissibilityAllTimes
import HarmonicBalls.Proofs.Sec5.OpenHorizonPositivity

/-! # Puncture inadmissibility for all disc centres

The scaled small-time bound supplies an earlier time at which a prescribed
puncture has not entered the disc cluster. The proposed
field invariance and coordinate-change inputs are explicit.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped Pointwise

universe u

/-- If a point has not entered a disc cluster at some positive time, the
least supersolution is strictly negative there at every later time. -/
theorem leastSupersolution_lt_zero_of_earlier_not_mem_cluster
    {μ : Measure ℂ} {R s t : ℝ} {z a : ℂ}
    (hz : z ∈ ball (0 : ℂ) R) (ha : a ∈ ball (0 : ℂ) R) (haz : a ≠ z)
    (hs : 0 < s) (hst : s ≤ t) (hna : a ∉ cluster μ R z s) :
    leastSupersolution μ R z t a < 0 := by
  have hzero := odometer_eq_zero_of_notMem_cluster hs.le ha hna
  change leastSupersolution μ R z s a + s * greenFunction (ball 0 R) z a = 0 at hzero
  have hg := greenFunction_ball_pos hz ha haz.symm
  have hneg : leastSupersolution μ R z s a < 0 := by nlinarith
  exact lt_of_le_of_lt (leastSupersolution_antitone_time (μ := μ) hs.le hst
    (ball_subset_closedBall ha) haz) hneg

/-- The scaled small-time bound gives arbitrarily small disc clusters,
simultaneously for every centre of the unit disc. The field inputs are staged. -/
theorem ae_disc_cluster_small_open_neighborhoods_all_centres
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ U : Set ℂ, IsOpen U → z ∈ U →
      ∃ t : ℝ, 0 < t ∧ closure (cluster (μ ω) 1 z t) ⊆ U := by
  let hC' := affinePairing hC hcirc (2 : ℂ) 0
  let hcirc' : Ω → ℝ → ℂ → ℝ := fun ω r z =>
    hcirc ω (2 * r) ((2 : ℝ) • z) - hcirc ω 2 0
  have hGFF' : IsWholePlaneGFF P hC' hcirc' := by
    have hcirc_eq : hcirc' = affineCircle hcirc (2 : ℂ) 0 := by
      funext ω r z
      simp [hcirc', affineCircle, Complex.real_smul]
    rw [hcirc_eq]
    exact hAff hGFF (2 : ℂ) (by norm_num) 0
  have hμ' : IsLQGMeasureOfField P γ α₀ hcirc'
      (fun ω => normalizedPullbackMeasure γ α₀ 2 (hcirc ω) (μ ω)) :=
    isLQGMeasureOfField_normalizedPullback hCC hGFF hγ hγ2 hα hμ (by norm_num)
  have hevent : ∀ n : ℕ, ∀ᵐ ω ∂P, ∃ T : ℝ, 0 < T ∧
      ∀ t ∈ Ioc (0 : ℝ) T, ∀ z ∈ ball (0 : ℂ) (1 / 2),
        closure (cluster (normalizedPullbackMeasure γ α₀ 2 (hcirc ω) (μ ω)) 1 z t) ⊆
          ball z (((2 : ℝ)⁻¹ ^ n / 2) / 2) := by
    intro n
    have hr : ((2 : ℝ)⁻¹ ^ n / 2) ∈ Ioo (0 : ℝ) 1 := by
      constructor
      · positivity
      · have hp : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        linarith
    have h := h71 γ α₀ hγ hγ2 hα Ω P hC' hcirc' _ hGFF' hμ' _ hr
    filter_upwards [h.ae_eventually_dyadic] with ω hω
    obtain ⟨m, hm⟩ := hω.exists
    exact ⟨(2 : ℝ)⁻¹ ^ m, by positivity, hm⟩
  filter_upwards [ae_all_iff.mpr hevent] with ω hsmall
  intro z hz U hU hzU
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU z hzU
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (half_pos hε)
    (by norm_num : (2 : ℝ)⁻¹ < 1)
  obtain ⟨T, hT, hbound⟩ := hsmall n
  have hz' : ((2 : ℝ)⁻¹ • z) ∈ ball (0 : ℂ) (1 / 2) := by
    rw [mem_ball_zero_iff] at hz ⊢
    rw [norm_smul, Real.norm_eq_abs]
    norm_num at *
    linarith
  let c : ℝ := Real.exp (γ * (lqgQ γ * Real.log 2 + fieldCircleAverage α₀ (hcirc ω) 2 0))
  have hc : 0 < c := Real.exp_pos _
  let t : ℝ := c * (T / 2)
  have ht : 0 < t := mul_pos hc (half_pos hT)
  have htdiv : t / c = T / 2 := by dsimp [t]; field_simp
  have hcl := hbound (T / 2) ⟨half_pos hT, (half_lt_self hT).le⟩ ((2 : ℝ)⁻¹ • z) hz'
  have hsmul : (2 : ℝ) • ((2 : ℝ)⁻¹ • z) = z := by
    rw [smul_smul, mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_smul]
  have hscale := cluster_normalizedPullback_smul (γ := γ) (α₀ := α₀) (k := 2) (R := 1) (t := t)
    (hcirc := hcirc ω) (μ := μ ω) (z := (2 : ℝ)⁻¹ • z) (by norm_num) ht.le
  change (2 : ℝ) • cluster (normalizedPullbackMeasure γ α₀ 2 (hcirc ω) (μ ω)) 1
    ((2 : ℝ)⁻¹ • z) (t / c) = cluster (μ ω) (2 * 1) ((2 : ℝ) • ((2 : ℝ)⁻¹ • z)) t at hscale
  rw [htdiv, mul_one, hsmul] at hscale
  have hball : (2 : ℝ) • ball ((2 : ℝ)⁻¹ • z) (((2 : ℝ)⁻¹ ^ n / 2) / 2) =
      ball z (2 * (((2 : ℝ)⁻¹ ^ n / 2) / 2)) := by
    change (fun x : ℂ => (2 : ℝ) • x) '' _ = _
    simpa only [hsmul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
      (Metric.smul_image_ball (by norm_num : (2 : ℝ) ≠ 0) ((2 : ℝ)⁻¹ • z)
        (((2 : ℝ)⁻¹ ^ n / 2) / 2))
  have hcl' : closure (cluster (μ ω) 2 z t) ⊆
      ball z (2 * (((2 : ℝ)⁻¹ ^ n / 2) / 2)) := by
    rw [← hscale, closure_smul₀' (by norm_num : (2 : ℝ) ≠ 0), ← hball]
    exact smul_set_mono hcl
  refine ⟨t, ht, ?_⟩
  apply (closure_mono (cluster_subset_cluster_larger_disc (μ := μ ω)
    (by norm_num : (1 : ℝ) < 2) hz ht.le)).trans
  apply hcl'.trans
  apply (ball_subset_ball ?_).trans hεU
  linarith

/-- The disc least supersolution is strictly negative at every positive time
away from the pole, simultaneously for all disc centres. The field inputs are staged. -/
theorem ae_leastSupersolution_lt_zero_all_centres
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ a ∈ ball (0 : ℂ) 1,
      a ≠ z → ∀ t : ℝ, 0 < t → leastSupersolution (μ ω) 1 z t a < 0 := by
  filter_upwards [ae_disc_cluster_small_open_neighborhoods_all_centres
      h71 hAff hCC hγ hγ2 hα hGFF hμ,
    clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ]
    with ω hsmall hmono
  intro z hz a ha haz t ht
  have hzU : z ∈ ball (0 : ℂ) 1 \ ({a} : Set ℂ) := ⟨hz, by simpa using haz.symm⟩
  obtain ⟨s₀, hs₀, hsub⟩ := hsmall z hz (ball (0 : ℂ) 1 \ {a})
    (isOpen_ball.sdiff isClosed_singleton) hzU
  have hdisc : a ∉ cluster (μ ω) 1 z s₀ := by
    intro hac
    exact (hsub (subset_closure hac)).2 (by simp)
  let s := min s₀ t
  have hs : 0 < s := lt_min hs₀ ht
  have hst : s ≤ t := min_le_right _ _
  have hss₀ : s ≤ s₀ := min_le_left _ _
  have hna : a ∉ cluster (μ ω) 1 z s := fun h => hdisc (hmono s s₀ 1 hs hss₀ zero_lt_one z hz h)
  exact leastSupersolution_lt_zero_of_earlier_not_mem_cluster hz ha haz hs hst hna

/-- Almost surely every deleted point is a discontinuity of the pointwise
infimum, for every centre in the disc and every positive time. -/
theorem ae_locally_finite_puncture_discontinuous_all_centres
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ K : Set ℂ,
      K ⊆ ball (0 : ℂ) 1 →
      (∀ ρ : ℝ, ρ < 1 → (K ∩ closedBall (0 : ℂ) ρ).Finite) → z ∉ K →
      ∀ a ∈ K, ∀ t : ℝ, 0 < t →
        ¬ ContinuousWithinAt (leastSupersolutionOn (μ ω) (ball (0 : ℂ) 1 \ K) z t)
          (ball (0 : ℂ) 1 \ K) a := by
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV, ae_leastSupersolution_lt_zero_all_centres
    hI2 h71 hAff hCC hγ hγ2 hα hGFF hμ] with ω hvol hneg
  intro z hz K hKR hKloc hzK a ha t ht hc
  have haz : a ≠ z := fun h => hzK (h ▸ ha)
  have heq := (continuousWithinAt_locally_finite_punctured_infimum_iff hvol.1 zero_lt_one
    (hvol.2 1 zero_lt_one) K hKloc hKR ha ⟨hz, hzK⟩ ht).mp hc
  exact (ne_of_lt (hneg z hz a (hKR ha) haz t ht)) heq

/-- Every nonempty locally finite deletion has an inadmissible pointwise
infimum, for every centre in the disc and every positive time. -/
theorem ae_locally_finite_puncture_inadmissible_all_centres
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ K : Set ℂ,
      K ⊆ ball (0 : ℂ) 1 → K.Nonempty →
      (∀ ρ : ℝ, ρ < 1 → (K ∩ closedBall (0 : ℂ) ρ).Finite) → z ∉ K →
      ∀ t : ℝ, 0 < t →
      leastSupersolutionOn (μ ω) (ball (0 : ℂ) 1 \ K) z t ∉
        supersolutionsOn (μ ω) (ball (0 : ℂ) 1 \ K) z t := by
  filter_upwards [ae_locally_finite_puncture_discontinuous_all_centres
    hI2 h71 hAff hCC hγ hγ2 hα hGFF hμ] with ω hdisc
  intro z hz K hKR hne hKloc hzK t ht hadm
  obtain ⟨a, ha⟩ := hne
  have hac : a ∈ closure (ball (0 : ℂ) 1 \ K) := by
    rw [closure_sdiff_locally_finite_ball zero_lt_one hKloc]
    exact ball_subset_closedBall (hKR ha)
  exact hdisc z hz K hKR hKloc hzK a ha t ht ((hadm.1 a hac).mono subset_closure)


end HarmonicBalls
