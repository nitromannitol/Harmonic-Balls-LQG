import HarmonicBalls.Proofs.Sec10.CrossingImpliesNoHoles
import HarmonicBalls.Proofs.Sec10.ScalingAssembly

/-!
# Connected complements implied by Lemma 10.5

The no-hole consequence of Lemma 10.5 transfers to harmonic-ball families
using cluster scaling, existence and uniqueness. The affine field invariance
and coordinate-change inputs are staged and await source review.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open scoped Pointwise

universe u

/-- Connectedness of the complement transfers from the unit-disc cluster
under the pathwise normalized scaling identity. -/
theorem cluster_compl_connected_of_normalized_scale
    (γ α₀ k : ℝ) (hk : 0 < k) (hcirc : ℝ → ℂ → ℝ) (μ : Measure ℂ)
    (hunit : ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (normalizedPullbackMeasure γ α₀ k hcirc μ) 1 z t) ⊆ ball 0 1 →
      IsConnected (closure (cluster (normalizedPullbackMeasure γ α₀ k hcirc μ) 1 z t))ᶜ)
    (hscale : ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
      cluster (normalizedPullbackMeasure γ α₀ k hcirc μ) 1 z t =
        k⁻¹ • cluster μ k (k • z)
          (Real.exp (γ * (lqgQ γ * Real.log k + fieldCircleAverage α₀ hcirc k 0)) * t)) :
    ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) k,
      closure (cluster μ k z t) ⊆ ball 0 k →
      IsConnected (closure (cluster μ k z t))ᶜ := by
  intro t ht z hz hcl
  let A : ℝ := Real.exp (γ * (lqgQ γ * Real.log k + fieldCircleAverage α₀ hcirc k 0))
  have hA : 0 < A := Real.exp_pos _
  have hball : (k⁻¹ : ℝ) • ball (0 : ℂ) k = ball 0 1 := by
    rw [_root_.smul_ball (inv_ne_zero hk.ne')]
    simp [Real.norm_eq_abs, abs_of_pos hk, hk.ne']
  have hz' : k⁻¹ • z ∈ ball (0 : ℂ) 1 := by
    rw [← hball]
    exact smul_mem_smul_set hz
  have hzscale : k • (k⁻¹ • z) = z := by simp [hk.ne']
  have htscale : A * (t / A) = t := by field_simp
  have heq := hscale (k⁻¹ • z) hz' (t / A) (div_pos ht hA)
  rw [hzscale, htscale] at heq
  have hcl' : closure (cluster (normalizedPullbackMeasure γ α₀ k hcirc μ) 1
      (k⁻¹ • z) (t / A)) ⊆ ball 0 1 := by
    rw [heq, closure_smul₀' (inv_ne_zero hk.ne'), ← hball]
    exact smul_set_mono hcl
  have hc := hunit (t / A) (div_pos ht hA) (k⁻¹ • z) hz' hcl'
  rw [heq, closure_smul₀' (inv_ne_zero hk.ne')] at hc
  let e : ℂ ≃ₜ ℂ := Homeomorph.smulOfNeZero k hk.ne'
  have himage : e '' (k⁻¹ • closure (cluster μ k z t)) = closure (cluster μ k z t) := by
    change k • (k⁻¹ • closure (cluster μ k z t)) = _
    rw [smul_smul, mul_inv_cancel₀ hk.ne', one_smul]
  have h := hc.image e e.continuous.continuousOn
  rwa [e.image_compl, himage] at h

/-- At each fixed radius, the frozen Lemma 10.5 implies connected
complements for all compactly contained clusters on a common event. -/
theorem ae_cluster_compl_connected_of_crossing_scaled
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h5 : CrossingComponentContainsClusterCrossingStmt.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ k : ℝ, 0 < k → ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) k,
      closure (cluster (μ ω) k z t) ⊆ ball 0 k →
      IsConnected (closure (cluster (μ ω) k z t))ᶜ := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ k hk
  let hC' := affinePairing hC hcirc (k : ℂ) 0
  let hcirc' : Ω → ℝ → ℂ → ℝ := fun ω r z =>
    hcirc ω (k * r) (k • z) - hcirc ω k 0
  have hGFF' : IsWholePlaneGFF P hC' hcirc' := by
    have hcirc_eq : hcirc' = affineCircle hcirc (k : ℂ) 0 := by
      funext ω r z
      simp [hcirc', affineCircle, Complex.real_smul, abs_of_pos hk]
    rw [hcirc_eq]
    exact hAff Ω P hC hcirc hGFF (k : ℂ) (by exact_mod_cast hk.ne') 0
  have hμ' : IsLQGMeasureOfField P γ α₀ hcirc'
      (fun ω => normalizedPullbackMeasure γ α₀ k (hcirc ω) (μ ω)) := by
    exact isLQGMeasureOfField_normalizedPullback (hCC Ω P γ α₀ hC hcirc)
      hGFF hγ hγ2 hα hμ hk
  have hunit := ae_cluster_compl_closure_connected_of_crossing_containment hI2 h5
    γ hγ hγ2 α₀ hα Ω P hC' hcirc'
    (fun ω => normalizedPullbackMeasure γ α₀ k (hcirc ω) (μ ω)) hGFF' hμ'
  filter_upwards [hunit, clusterPathwiseScaleStep_proved γ α₀ hγ hγ2 hα
    Ω P hC hcirc μ hGFF hμ k hk] with ω hu hs
  exact cluster_compl_connected_of_normalized_scale γ α₀ k hk (hcirc ω) (μ ω) hu hs

/-- Under the frozen Lemma 10.5, every harmonic ball and its closure have connected complements. The two field inputs are staged pending review;
existence is also an explicit hypothesis. -/
theorem ae_harmonicBall_compl_closure_connected_of_crossing
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hexists : ExistenceHarmonicBallsStmt.{u})
    (h5 : CrossingComponentContainsClusterCrossingStmt.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) :
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
  have hcount : ∀ᵐ ω ∂P, ∀ n : ℕ, 0 < n → ∀ t : ℝ, 0 < t →
      ∀ z ∈ ball (0 : ℂ) n, closure (cluster (μ ω) n z t) ⊆ ball 0 n →
        IsConnected (closure (cluster (μ ω) n z t))ᶜ := by
    rw [ae_all_iff]
    intro n
    by_cases hn : 0 < n
    · filter_upwards [ae_cluster_compl_connected_of_crossing_scaled hI2 h5 hAff hCC
        γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ n (by exact_mod_cast hn)] with ω hω _
      exact hω
    · exact Filter.Eventually.of_forall fun _ h => (hn h).elim
  filter_upwards [hhat, hΛ,
    hunique γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ Λhat hhat,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    hcount] with ω hω hΛω huniq hopen hconnected
  intro t ht z
  obtain ⟨n, hn, hz, hcl, heq⟩ := (hω z).exists_integer_cluster_closure ht
    (fun n hn hz => (hopen t n ht (by exact_mod_cast hn) z hz).1)
  have heqΛ : Λ ω z t = Λhat ω z t := huniq z (Λ ω z) (hΛω z) ht
  have hcompl : IsConnected (closure (Λ ω z t))ᶜ := by
    rw [heqΛ, heq]
    exact hconnected n hn t ht z hz hcl
  refine ⟨hcompl, ?_⟩
  have hclosure := hcompl.closure
  rw [closure_compl, (hΛω z).2.isRegularOpen t ht] at hclosure
  exact hclosure

end HarmonicBalls
