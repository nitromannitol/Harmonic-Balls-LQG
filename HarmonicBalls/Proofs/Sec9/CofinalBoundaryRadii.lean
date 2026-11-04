import HarmonicBalls.Proofs.Sec9.BoundaryRadii

/-!
# Reduction of boundary nullity to cofinal radii

Compatibility of clusters allows a countable cofinal family of discs to replace all discs
in the boundary-nullity criterion for weak uniqueness.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

universe u

/-- Boundary nullity at a prescribed sequence of radii, on one event. -/
def ClusterBoundaryNullCofinalRadii (r : ℕ → ℝ) : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) (r n),
    closure (cluster (μ ω) (r n) z t) ⊆ ball 0 (r n) →
      μ ω (frontier (cluster (μ ω) (r n) z t)) = 0

/-- A positive cofinal sequence of radii suffices for boundary nullity at all radii. -/
theorem clusterBoundaryNullAllRadii_of_cofinalRadii
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hcofinal : ∀ R : ℝ, ∃ n, R ≤ r n) (hseq : ClusterBoundaryNullCofinalRadii.{u} r) :
    ClusterBoundaryNullAllRadii.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  have hcompat : ∀ᵐ ω ∂P, ∀ n : ℕ,
      ∀ t : ℝ, 0 < t → ∀ s₁ : ℝ, s₁ ≤ r n → ∀ z ∈ ball (0 : ℂ) s₁,
        ∀ s₂ ∈ Icc s₁ (r n), closure (cluster (μ ω) s₂ z t) ⊆ ball 0 s₁ →
          ∀ s ∈ Icc s₁ (r n), cluster (μ ω) s z t = cluster (μ ω) s₂ z t := by
    rw [ae_all_iff]
    intro n
    exact clusterCompatibility_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ
      (r n) (hr n)
  filter_upwards [hseq γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ, hcompat] with ω hω hc
  intro R t hR ht z hz hcl
  obtain ⟨n, hn⟩ := hcofinal R
  have heq := hc n t ht R hn z hz R ⟨le_rfl, hn⟩ hcl (r n) ⟨hn, le_rfl⟩
  have hnz : z ∈ ball (0 : ℂ) (r n) := ball_subset_ball hn hz
  have hncl : closure (cluster (μ ω) (r n) z t) ⊆ ball 0 (r n) := by
    rw [heq]
    exact hcl.trans (ball_subset_ball hn)
  simpa only [heq] using hω n t ht z hnz hncl

/-- Weak Proposition 9.2 from boundary nullity on any positive cofinal sequence. -/
theorem subharmonicBallUniquenessWeak_of_cofinalRadii
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hcofinal : ∀ R : ℝ, ∃ n, R ≤ r n) (hseq : ClusterBoundaryNullCofinalRadii.{u} r) :
    SubharmonicBallUniquenessWeakStmt.{u} :=
  subharmonicBallUniquenessWeak_of_boundaryNull hI2
    (clusterBoundaryNullAllRadii_of_cofinalRadii hI2 r hr hcofinal hseq)

/-- The dyadic radii suffice for weak Proposition 9.2. -/
theorem subharmonicBallUniquenessWeak_of_dyadicRadii
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hdyadic : ClusterBoundaryNullCofinalRadii.{u} (fun n => (2 : ℝ) ^ n)) :
    SubharmonicBallUniquenessWeakStmt.{u} := by
  apply subharmonicBallUniquenessWeak_of_cofinalRadii hI2 (fun n => (2 : ℝ) ^ n)
  · intro n
    exact pow_pos (by norm_num) n
  · intro R
    have ht := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually_gt_atTop R
    obtain ⟨n, hn⟩ := ht.exists
    exact ⟨n, hn.le⟩
  · exact hdyadic

end HarmonicBalls
