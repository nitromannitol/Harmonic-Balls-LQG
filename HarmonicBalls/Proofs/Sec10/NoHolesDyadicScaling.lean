import HarmonicBalls.Proofs.Sec10.HarmonicBallNoHoles
import HarmonicBalls.Proofs.Sec9.AffinePairingCovariance
import HarmonicBalls.Proofs.Sec9.LQGSpatialDilation

/-! # Connected complements and dyadic scaling -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open scoped Pointwise

universe u

/-- Lemma 10.5 implies connected closed-cluster complements at each fixed
radius. The transfer uses dyadic scaling and cluster compatibility. -/
theorem ae_cluster_compl_connected_of_crossing_dyadic
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h5 : CrossingComponentContainsClusterCrossingStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ r : ℝ, 0 < r → ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) r,
      closure (cluster (μ ω) r z t) ⊆ ball 0 r →
      IsConnected (closure (cluster (μ ω) r z t))ᶜ := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ r hr
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt r (by norm_num : (1 : ℝ) < 2)
  let k : ℝ := (2 : ℝ) ^ m
  have hk : 0 < k := by dsimp [k]; positivity
  let hC' := affinePairing hC hcirc (k : ℂ) 0
  let hcirc' : Ω → ℝ → ℂ → ℝ := fun ω s z =>
    hcirc ω (k * s) (k • z) - hcirc ω k 0
  have hGFF' : IsWholePlaneGFF P hC' hcirc' := by
    have hcirc_eq : hcirc' = affineCircle hcirc (k : ℂ) 0 := by
      funext ω s z
      simp [hcirc', affineCircle, Complex.real_smul, abs_of_pos hk]
    rw [hcirc_eq]
    exact hGFF.complex_affine (by exact_mod_cast hk.ne') 0
  have hμ' : IsLQGMeasureOfField P γ α₀ hcirc'
      (fun ω => normalizedPullbackMeasure γ α₀ k (hcirc ω) (μ ω)) := by
    exact isLQGMeasureOfField_normalizedPullback_dyadic hGFF hγ.ne' hμ m
  have hunit := ae_cluster_compl_closure_connected_of_crossing_containment hI2 h5
    γ hγ hγ2 α₀ hα Ω P hC' hcirc'
    (fun ω => normalizedPullbackMeasure γ α₀ k (hcirc ω) (μ ω)) hGFF' hμ'
  have hscale := clusterPathwiseScaleStep_proved γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ k hk
  have hcompat := clusterCompatibility_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ k hk
  filter_upwards [hunit, hscale, hcompat] with ω hu hs hc
  have hj := cluster_compl_connected_of_normalized_scale γ α₀ k hk (hcirc ω) (μ ω) hu hs
  intro t ht z hz hcl
  have heq := hc t ht r hm.le z hz r ⟨le_rfl, hm.le⟩ hcl k ⟨hm.le, le_rfl⟩
  have hz' : z ∈ ball (0 : ℂ) k := ball_subset_ball hm.le hz
  have hcl' : closure (cluster (μ ω) k z t) ⊆ ball 0 k := by
    rw [heq]
    exact hcl.trans (ball_subset_ball hm.le)
  rw [← heq]
  exact hj t ht z hz' hcl'

/-- One almost-sure event covers all radii, centres, and positive times. -/
theorem ae_cluster_compl_connected_all_radii_of_crossing_dyadic
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h5 : CrossingComponentContainsClusterCrossingStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ r : ℝ, 0 < r → ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) r,
      closure (cluster (μ ω) r z t) ⊆ ball 0 r →
      IsConnected (closure (cluster (μ ω) r z t))ᶜ := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  have hall : ∀ n : ℕ, ∀ᵐ ω ∂P, 0 < n →
      (∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) n,
        closure (cluster (μ ω) n z t) ⊆ ball 0 n →
        IsConnected (closure (cluster (μ ω) n z t))ᶜ) ∧
      (∀ t : ℝ, 0 < t → ∀ s₁ : ℝ, s₁ ≤ n → ∀ z ∈ ball (0 : ℂ) s₁,
        ∀ s₂ ∈ Icc s₁ n, closure (cluster (μ ω) s₂ z t) ⊆ ball 0 s₁ →
          ∀ s ∈ Icc s₁ n, cluster (μ ω) s z t = cluster (μ ω) s₂ z t) := by
    intro n
    by_cases hn : 0 < n
    · have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
      filter_upwards [ae_cluster_compl_connected_of_crossing_dyadic hI2 h5
        γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ n hn',
        clusterCompatibility_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ n hn']
        with ω hconn hcompat _
      exact ⟨hconn, hcompat⟩
    · exact Filter.Eventually.of_forall fun _ h => (hn h).elim
  filter_upwards [ae_all_iff.mpr hall] with ω hω
  intro r hr t ht z hz hcl
  obtain ⟨n, hn⟩ := exists_nat_gt r
  have hnpos : 0 < n := by exact_mod_cast (lt_trans hr hn)
  obtain ⟨hconn, hc⟩ := hω n hnpos
  have heq := hc t ht r hn.le z hz r ⟨le_rfl, hn.le⟩ hcl n ⟨hn.le, le_rfl⟩
  have hz' : z ∈ ball (0 : ℂ) n := ball_subset_ball hn.le hz
  have hcl' : closure (cluster (μ ω) n z t) ⊆ ball 0 n := by
    rw [heq]
    exact hcl.trans (ball_subset_ball hn.le)
  rw [← heq]
  exact hconn t ht z hz' hcl'

/-- Lemma 10.5 implies connected complements for harmonic balls and their
closures, assuming volume growth and existence of harmonic balls. -/
theorem ae_harmonicBall_compl_connected_of_crossing_dyadic
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hexists : ExistenceHarmonicBallsStmt.{u})
    (h5 : CrossingComponentContainsClusterCrossingStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ Λ : Ω → ℂ → ℝ → Set ℂ, (∀ᵐ ω ∂P, ∀ z : ℂ, IsHarmonicBallFamily (μ ω) (Λ ω z) z) →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z : ℂ,
      IsConnected (closure (Λ ω z t))ᶜ ∧ IsConnected (Λ ω z t)ᶜ := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ Λ hΛ
  classical
  have hfull := lqgMeasureFullSupportStmt_of_volumeGrowth hI2
  have hunique := uniquenessHarmonicBalls_of_boundary_and_fullSupport
    (harmonicBallBoundarySubset_of_volumeGrowth hI2) (regularOpenEqOfAEEq hfull) hfull
  let Λhat : Ω → ℂ → ℝ → Set ℂ := fun ω z =>
    if h : ∃ A : ℝ → Set ℂ, IsRegularizedClusterFamily (μ ω) A z then
      Classical.choose h else fun _ => ∅
  have hhat : ∀ᵐ ω ∂P, ∀ z, IsRegularizedClusterFamily (μ ω) (Λhat ω z) z := by
    filter_upwards [hexists γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hω
    intro z
    dsimp only [Λhat]
    split
    next h => exact Classical.choose_spec h
    next h => exact (h (hω z)).elim
  filter_upwards [hhat, hΛ,
    hunique γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ Λhat hhat,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    ae_cluster_compl_connected_all_radii_of_crossing_dyadic hI2 h5
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hω hΛω huniq hopen hconnected
  intro t ht z
  obtain ⟨n, hn, hz, hcl, heq⟩ := (hω z).exists_integer_cluster_closure ht
    (fun n hn hz => (hopen t n ht (by exact_mod_cast hn) z hz).1)
  have heqΛ : Λ ω z t = Λhat ω z t := huniq z (Λ ω z) (hΛω z) ht
  have hcompl : IsConnected (closure (Λ ω z t))ᶜ := by
    rw [heqΛ, heq]
    exact hconnected n (by exact_mod_cast hn) t ht z hz hcl
  refine ⟨hcompl, ?_⟩
  have hclosure := hcompl.closure
  rw [closure_compl, (hΛω z).2.isRegularOpen t ht] at hclosure
  exact hclosure

end HarmonicBalls
