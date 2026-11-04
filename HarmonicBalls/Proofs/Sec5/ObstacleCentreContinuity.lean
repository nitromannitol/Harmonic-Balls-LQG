import HarmonicBalls.Proofs.Sec5.ObstacleCentreStability
import HarmonicBalls.Proofs.Sec5.PotentialMeasurableDecoder

/-! # Continuity of the obstacle as its pole moves -/

namespace HarmonicBalls

universe u

open MeasureTheory Metric Set Filter TopologicalSpace
open scoped Topology

/-- The truncated obstacle vanishes in a neighborhood of its pole. -/
theorem truncatedShiftedObstacle_eq_zero_near_pole
    {μ : Measure ℂ} {R t : ℝ} {z : ℂ}
    (hR : 0 < R) (hz : z ∈ ball (0 : ℂ) R) (ht : 0 < t)
    (hq : ContinuousOn (greenPotentialBall μ R) (closedBall 0 R)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ ball z δ, truncatedShiftedObstacle μ R z t y = 0 := by
  have hev := (obstacleTendstoAtBotStep_holds μ R z t hR hz ht hq).eventually
    (eventually_lt_atBot (0 : ℝ))
  obtain ⟨δ, hδ, hβ⟩ := Metric.mem_nhdsWithin_iff.1 hev
  refine ⟨δ, hδ, ?_⟩
  intro y hy
  by_cases hyz : y = z
  · simp [truncatedShiftedObstacle, hyz]
  · have h := hβ ⟨hy, by simpa using hyz⟩
    change obstacle μ R z t y < 0 at h
    simp only [truncatedShiftedObstacle, ite_eq_right hyz, max_eq_left h.le]

/-- The truncated obstacle varies uniformly on the closed disc when its pole
moves inside the disc. -/
theorem eventually_truncatedShiftedObstacle_le_add
    {μ : Measure ℂ} {R t : ℝ} {z : ℂ}
    (hR : 0 < R) (hz : z ∈ ball (0 : ℂ) R) (ht : 0 < t)
    (hq : ContinuousOn (greenPotentialBall μ R) (closedBall 0 R))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z' in 𝓝 z, ∀ y ∈ closedBall (0 : ℂ) R,
      truncatedShiftedObstacle μ R z t y ≤ truncatedShiftedObstacle μ R z' t y + ε := by
  obtain ⟨δ, hδ, hzero⟩ := truncatedShiftedObstacle_eq_zero_near_pole hR hz ht hq
  let K : ℝ := t * Real.pi⁻¹ * (δ⁻¹ + (δ / 2)⁻¹)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let η : ℝ := min (δ / 2) (ε / (K + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  have hnear : ∀ᶠ z' in 𝓝 z, z' ∈ ball z η := ball_mem_nhds z hη
  filter_upwards [hnear, isOpen_ball.mem_nhds hz] with z' hz'near hz'ball
  have hdist : ‖z' - z‖ < η := by simpa [mem_ball, dist_eq_norm] using hz'near
  have hsmall : ‖z' - z‖ < δ / 2 := hdist.trans_le (min_le_left _ _)
  have hsmallε : ‖z' - z‖ * K < ε := by
    have h1 : ‖z' - z‖ * (K + 1) < ε := by
      have h2 := hdist.trans_le (min_le_right (δ / 2) (ε / (K + 1)))
      exact (lt_div_iff₀ (by linarith : 0 < K + 1)).mp h2
    nlinarith [norm_nonneg (z' - z)]
  intro y hy
  by_cases hynear : y ∈ ball z δ
  · rw [hzero y hynear]
    have hnonneg : 0 ≤ truncatedShiftedObstacle μ R z' t y := by
      by_cases h : y = z' <;> simp [truncatedShiftedObstacle, h]
    linarith
  · have hyfar : δ ≤ ‖z - y‖ := by
      have h : δ ≤ dist y z := le_of_not_gt hynear
      simpa [dist_eq_norm, norm_sub_rev] using h
    have hyfar' : δ / 2 ≤ ‖z' - y‖ := by
      have htri : ‖z - y‖ ≤ ‖z - z'‖ + ‖z' - y‖ := by
        convert norm_add_le (z - z') (z' - y) using 1; ring_nf
      rw [norm_sub_rev z z'] at htri
      linarith
    have hzy : z ≠ y := by
      intro h; subst y; simp at hyfar; linarith
    have hz'y : z' ≠ y := by
      intro h; subst y; simp at hyfar'; linarith
    have hi : ‖z - y‖⁻¹ ≤ δ⁻¹ := (inv_le_inv₀ (by linarith : 0 < ‖z - y‖) hδ).2 hyfar
    have hi' : ‖z' - y‖⁻¹ ≤ (δ / 2)⁻¹ :=
      (inv_le_inv₀ (by linarith : 0 < ‖z' - y‖) (by linarith : 0 < δ / 2)).2 hyfar'
    have hg := abs_greenFunction_ball_sub_le (R := R) (α := 1) (by norm_num) (by norm_num)
      (ball_subset_closedBall hz) (ball_subset_closedBall hz'ball) hzy hz'y
    simp only [Real.rpow_one, Real.rpow_neg_one, mul_one] at hg
    have hgbound : |greenFunction (ball 0 R) z y - greenFunction (ball 0 R) z' y| ≤
        Real.pi⁻¹ * (‖z' - z‖ * (δ⁻¹ + (δ / 2)⁻¹)) := by
      rw [norm_sub_rev] at hg
      exact hg.trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (add_le_add hi hi') (norm_nonneg _)) (by positivity))
    have habs : |obstacle μ R z t y - obstacle μ R z' t y| < ε := by
      have hβ : obstacle μ R z t y - obstacle μ R z' t y =
          -t * (greenFunction (ball 0 R) z y - greenFunction (ball 0 R) z' y) := by
        simp only [obstacle]; ring
      rw [hβ, abs_mul, abs_neg, abs_of_pos ht]
      have hle := mul_le_mul_of_nonneg_left hgbound ht.le
      dsimp [K] at hsmallε
      nlinarith
    have hyz : y ≠ z := Ne.symm hzy
    have hyz' : y ≠ z' := Ne.symm hz'y
    simp only [truncatedShiftedObstacle, ite_eq_right hyz, ite_eq_right hyz']
    have hb := (abs_lt.mp habs).2
    have hm := le_max_right (0 : ℝ) (obstacle μ R z' t y)
    have h0 := le_max_left (0 : ℝ) (obstacle μ R z' t y)
    exact max_le (by linarith) (by linarith)

/-- A point remains in the non-coincidence set when its pole moves slightly
away from that point. -/
theorem self_mem_nonCoincidenceSet_centre_nhds
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βminus βplus : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) {t : ℝ} (ht : 0 < t) :
    {z' : ℂ | z ∈ nonCoincidenceSet μ R z' t} ∈ 𝓝 z := by
  have hq := greenPotentialBallContinuousStep_holds μ hμ R βminus βplus hR hV
  have hq_at : ContinuousAt (greenPotentialBall μ R) z :=
    hq.continuousAt (mem_of_superset (isOpen_ball.mem_nhds hz) ball_subset_closedBall)
  have hq_near : ∀ᶠ z' in 𝓝 z, greenPotentialBall μ R z - 1 < greenPotentialBall μ R z' :=
    hq_at.eventually (isOpen_Ioi.mem_nhds (by linarith :
      greenPotentialBall μ R z - 1 < greenPotentialBall μ R z))
  have hβ := (obstacleTendstoAtBotStep_holds μ R z t hR hz ht hq).eventually
    (eventually_lt_atBot (-1 : ℝ))
  obtain ⟨δ, hδ, hδβ⟩ := Metric.mem_nhdsWithin_iff.1 hβ
  filter_upwards [hq_near, ball_mem_nhds z hδ, isOpen_ball.mem_nhds hz] with z' hqz' hnear hz'
  refine ⟨hz, ?_⟩
  by_cases h : z' = z
  · exact Or.inl h.symm
  · right
    have hb := hδβ ⟨hnear, by simpa using h⟩
    change obstacle μ R z t z' < -1 at hb
    have hnonneg := (obstacleLeastSuperharmonicMajorantGeneral_holds μ hμ R βminus βplus
      hR hV z' hz' t ht).2.2.2.1 z (ball_subset_closedBall hz)
    have hgreen := greenFunction_ball_comm R z z'
    simp only [obstacle] at hb ⊢
    rw [← hgreen]
    linarith

/-- The set of poles whose non-coincidence set contains a given point is
open relative to the disc. -/
theorem isOpen_nonCoincidenceSet_centre_section
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βminus βplus : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βminus βplus)
    {t : ℝ} (ht : 0 < t) (x : ℂ) :
    IsOpen {z : ball (0 : ℂ) R | x ∈ nonCoincidenceSet μ R z t} := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  have hlocal : {z' : ℂ | x ∈ nonCoincidenceSet μ R z' t} ∈ 𝓝 (z : ℂ) := by
    by_cases hxz : x = (z : ℂ)
    · subst x
      exact self_mem_nonCoincidenceSet_centre_nhds hμ hR hV z.property ht
    · apply nonCoincidenceSet_mem_nhds_of_truncatedShiftedObstacle hμ hR hV z.property ht hz hxz
      intro ε hε
      exact eventually_truncatedShiftedObstacle_le_add hR z.property ht
        (greenPotentialBallContinuousStep_holds μ hμ R βminus βplus hR hV) hε
  exact continuous_subtype_val.continuousAt.eventually hlocal

/-- The corresponding centre section of the cluster is open. -/
theorem isOpen_cluster_centre_section
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βminus βplus : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βminus βplus)
    {t : ℝ} (ht : 0 < t) (x : ℂ) :
    IsOpen {z : ball (0 : ℂ) R | x ∈ cluster μ R z t} := by
  have heq : {z : ball (0 : ℂ) R | x ∈ cluster μ R z t} =
      {z : ball (0 : ℂ) R | x ∈ nonCoincidenceSet μ R z t} := by
    ext z
    change x ∈ cluster μ R z t ↔ x ∈ nonCoincidenceSet μ R z t
    rw [(obstacleCompatibilityShiftStep_holds μ hμ R βminus βplus hR hV z z.property t ht).2.2.1]
  rw [heq]
  exact isOpen_nonCoincidenceSet_centre_section hμ hR hV ht x

/-- Cofinal regularized local intervals follow from the numbered inputs and
staged affine field and coordinate-change inputs. -/
theorem cofinalRegularizedClusterIntervals_of_volumeGrowth
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h53 : ClusterBoundaryMeasureZeroStmt.{u}) (h54 : RegularizedClusterHarmonicBallsStmt.{u})
    (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hAff : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) :
    CofinalRegularizedClusterIntervalsStep.{u} := by
  let J := ball (0 : ℂ) (1 / 2)
  let : Nonempty J := ⟨⟨0, by simp [J]⟩⟩
  let e : ℕ → J := denseSeq J
  have he : DenseRange e := denseRange_denseSeq J
  apply cofinalRegularizedClusterIntervals_of_volumeGrowth_and_countableCentres
    hI2 h32 h33 h53 h54 h71 hAff hCC e
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ h hμ
  obtain ⟨βm, βp, hgood⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα h hμ
  filter_upwards [hgood, h32 γ α₀ hγ hγ2 hα Ω P hC hcirc μ h hμ] with ω hω hopen
  apply countableCentres_coverage_of_dense_point_sections e he
    (fun j t => cluster (μ ω) 1 j t)
  · intro j n
    exact (hopen (reciprocalTime n) 1 (reciprocalTime n).property zero_lt_one j
      (ball_subset_ball (by norm_num : (1 : ℝ) / 2 ≤ 1) j.property)).1
  · intro n m
    let f : J → ball (0 : ℂ) 1 := fun j =>
      ⟨j, ball_subset_ball (by norm_num : (1 : ℝ) / 2 ≤ 1) j.property⟩
    have hf : Continuous f := continuous_subtype_val.subtype_mk _
    exact (isOpen_cluster_centre_section hω.1 zero_lt_one (hω.2 1 zero_lt_one)
      (reciprocalTime n).property (denseSeq ℂ m)).preimage hf

/-- Theorem 5.5 follows from the numbered cluster results and the staged
affine field and coordinate-change inputs. -/
theorem existenceHarmonicBalls_of_volumeGrowth
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h35 : ClusterCompatibilityStmt.{u}) (h43 : ClusterSubharmonicBallStmt.{u})
    (h53 : ClusterBoundaryMeasureZeroStmt.{u}) (h54 : RegularizedClusterHarmonicBallsStmt.{u})
    (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hAff : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) :
    ExistenceHarmonicBallsStmt.{u} :=
  existenceHarmonicBalls_of_cofinalIntervals
    (cofinalRegularizedClusterIntervals_of_volumeGrowth hI2 h32 h33 h53 h54 h71 hAff hCC)
    h35 h32 h43

end HarmonicBalls
