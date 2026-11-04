import HarmonicBalls.Draft.Section10
import HarmonicBalls.Draft.Section5
import HarmonicBalls.Proofs.Sec3.OpenLaplacian
import HarmonicBalls.Proofs.Sec5.NoEntryPropagation
import HarmonicBalls.Proofs.Sec9.HarmonicBoundaryAssembly
import HarmonicBalls.Proofs.Sec9.RegularOpenEqOfAEEq

/-!
# Complementary boundaries at integer radii

Proposition 10.7 follows from existence and uniqueness of harmonic ball families,
cluster openness, and the simultaneous-centre Jordan statement at integer radii.
The last statement remains a separate proof obligation: the fixed-centre law in
Lemma 5.7 does not by itself give the required simultaneous event.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- The integer-radius form of Proposition 10.6, with time and centre simultaneous. -/
def ClusterJordanIntegerRadii : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
  IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ n : ℕ, 0 < n → ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) n,
    closure (cluster (μ ω) n z t) ⊆ ball 0 n →
    ∀ C ∈ connectedComponentsIn (closure (cluster (μ ω) n z t))ᶜ,
      IsSimpleLoop (frontier C)

/-- The fixed-radius form of Proposition 10.6, with time and centre simultaneous. -/
def ClusterJordanFixedRadius : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
  IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ r : ℝ, 0 < r → ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) r,
    closure (cluster (μ ω) r z t) ⊆ ball 0 r →
    ∀ C ∈ connectedComponentsIn (closure (cluster (μ ω) r z t))ᶜ,
      IsSimpleLoop (frontier C)

/-- Countably many fixed-radius events give the simultaneous integer-radius event. -/
theorem clusterJordanIntegerRadii_of_fixedRadius
    (hfixed : ClusterJordanFixedRadius.{u}) : ClusterJordanIntegerRadii.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  have hall : ∀ n : ℕ, ∀ᵐ ω ∂P, 0 < n → ∀ t : ℝ, 0 < t →
      ∀ z ∈ ball (0 : ℂ) n, closure (cluster (μ ω) n z t) ⊆ ball 0 n →
      ∀ C ∈ connectedComponentsIn (closure (cluster (μ ω) n z t))ᶜ,
        IsSimpleLoop (frontier C) := by
    intro n
    by_cases hn : 0 < n
    · filter_upwards [hfixed γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ n
        (by exact_mod_cast hn)] with ω hω
      exact fun _ => hω
    · exact Filter.Eventually.of_forall (fun _ hn' => (hn hn').elim)
  exact ae_all_iff.mpr hall

/-- A regularized cluster family agrees in closure with a cluster in a sufficiently
large integer-radius ball, provided that cluster is open. -/
theorem IsRegularizedClusterFamily.exists_integer_cluster_closure
    {μ : Measure ℂ} {Λ : ℝ → Set ℂ} {z : ℂ}
    (hfam : IsRegularizedClusterFamily μ Λ z) {t : ℝ} (ht : 0 < t)
    (hopen : ∀ n : ℕ, 0 < n → z ∈ ball (0 : ℂ) n → IsOpen (cluster μ n z t)) :
    ∃ n : ℕ, 0 < n ∧ z ∈ ball (0 : ℂ) n ∧
      closure (cluster μ n z t) ⊆ ball 0 n ∧
      closure (Λ t) = closure (cluster μ n z t) := by
  obtain ⟨s, hs⟩ := ((hfam.1.isBounded t ht).closure).subset_ball (0 : ℂ)
  obtain ⟨n, hn⟩ := exists_nat_gt (max s 0 + 1)
  have hspos : 0 < max s 0 + 1 := by have := le_max_right s 0; linarith
  have hnpos : 0 < n := by exact_mod_cast (lt_trans hspos hn)
  have hsn : s ≤ (n : ℝ) := by have := le_max_left s 0; linarith
  have h0n : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hz : z ∈ ball (0 : ℂ) n :=
    (hs.trans (ball_subset_ball hsn)) (subset_closure (hfam.1.mem t ht))
  have hΛ : Λ t = regularizedCluster μ n z t :=
    hfam.2.2 t ht (n : ℝ) h0n (hs.trans (ball_subset_ball hsn)) n le_rfl
  have hc : closure (regularizedCluster μ n z t) = closure (cluster μ n z t) := by
    apply Subset.antisymm
    · simpa [regularizedCluster] using
        (closure_mono (interior_subset : interior (closure (cluster μ n z t)) ⊆
          closure (cluster μ n z t)))
    · exact closure_mono ((hopen n hnpos hz).subset_interior_iff.mpr subset_closure)
  refine ⟨n, hnpos, hz, ?_, ?_⟩
  · rw [← hc, ← hΛ]
    exact hs.trans (ball_subset_ball hsn)
  · rw [hΛ, hc]

/-- Proposition 10.7 from the preceding numbered results and the integer-radius
form of Proposition 10.6. All inputs remain explicit proof obligations. -/
theorem harmonicBallComplementBoundaryJordan_of_integerRadii
    (hopen : ClusterOpenLaplacianStmt.{u})
    (hexists : ExistenceHarmonicBallsStmt.{u})
    (hunique : UniquenessHarmonicBallsStmt.{u})
    (hjordan : ClusterJordanIntegerRadii.{u}) :
    HarmonicBallComplementBoundaryJordanStmt.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ Λ hΛ
  classical
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
    hopen γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    hjordan γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hω hΛω huniq hopenω hjordanω
  intro t ht z C hC
  obtain ⟨n, hn, hz, hcl, heq⟩ := (hω z).exists_integer_cluster_closure ht
    (fun n hn hz => (hopenω t n ht (by exact_mod_cast hn) z hz).1)
  have heqΛ : Λ ω z t = Λhat ω z t := huniq z (Λ ω z) (hΛω z) ht
  rw [heqΛ, heq] at hC
  exact hjordanω n hn t ht z hz hcl C hC

/-- Proposition 10.7 using the Section 3 proof of cluster openness from I2. -/
theorem harmonicBallComplementBoundaryJordan_of_volumeGrowth_and_integerRadii
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hexists : ExistenceHarmonicBallsStmt.{u})
    (hunique : UniquenessHarmonicBallsStmt.{u})
    (hjordan : ClusterJordanIntegerRadii.{u}) :
    HarmonicBallComplementBoundaryJordanStmt.{u} :=
  harmonicBallComplementBoundaryJordan_of_integerRadii
    (clusterOpenLaplacian_proved hI2) hexists hunique hjordan

/-- Proposition 10.7 from volume growth, existence, and the integer-radius
Jordan event. Uniqueness is supplied by Lemmas 9.3 and 9.4 and full support. -/
theorem harmonicBallComplementBoundaryJordan_of_volumeGrowth
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hexists : ExistenceHarmonicBallsStmt.{u})
    (hjordan : ClusterJordanIntegerRadii.{u}) :
    HarmonicBallComplementBoundaryJordanStmt.{u} := by
  have hfull := lqgMeasureFullSupportStmt_of_volumeGrowth hI2
  exact harmonicBallComplementBoundaryJordan_of_volumeGrowth_and_integerRadii hI2 hexists
    (uniquenessHarmonicBalls_of_boundary_and_fullSupport
      (harmonicBallBoundarySubset_of_volumeGrowth hI2) (regularOpenEqOfAEEq hfull) hfull)
    hjordan

/-- The fixed-radius Jordan events suffice for Proposition 10.7. -/
theorem harmonicBallComplementBoundaryJordan_of_fixedRadius
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hexists : ExistenceHarmonicBallsStmt.{u})
    (hfixed : ClusterJordanFixedRadius.{u}) :
    HarmonicBallComplementBoundaryJordanStmt.{u} :=
  harmonicBallComplementBoundaryJordan_of_volumeGrowth hI2 hexists
    (clusterJordanIntegerRadii_of_fixedRadius hfixed)

end HarmonicBalls
