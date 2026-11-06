import HarmonicBalls.Proofs.Sec6.SingularRootDeterministicTransfer
import HarmonicBalls.Proofs.Sec6.PhaseGridApprox

/-! # Deterministic shifted meshes at singular LQG roots

The imported Section 6 iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal Topology
universe u

/-- For prescribed radii, one deterministic sequence of dyadic meshes works
at almost every singular-mass sampled root, simultaneously for every lattice
phase. The mesh sequence can depend on the radius sequence and the law. -/
theorem exists_singularRoot_zero_eventually_phase_goodAnnulus_transfer
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ μ₀ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hμ₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀)
    (κ : Kernel Ω ℂ) [IsFiniteMeasure (P ⊗ₘ κ)] (hac : ∀ᵐ ω ∂P, κ ω ≪ μ ω)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    {a a' amid b b' : ℝ} {d ε : ℝ≥0∞} (hd : 0 < d) (hε : 0 < ε)
    (hbudget : ENNReal.ofReal b + 2 * ε + ε ≤ ENNReal.ofReal b')
    (hmid : ENNReal.ofReal amid < ENNReal.ofReal a)
    (hslack : ENNReal.ofReal a' + (ENNReal.ofReal a' + 1) * d ≤ ENNReal.ofReal amid) :
    ∃ m : ℕ → ℕ, ∀ᵐ p ∂(P ⊗ₘ κ), ∀ᶠ n in atTop, ∀ phase : ℂ, ∃ y : ℂ,
      y - phase ∈ scaledLattice (dyadicScale (m n)) ∧
      dist p.2 y < 2 * dyadicScale (m n) ∧
      (IsGoodAnnulus (μ₀ p.1) (r n) p.2 a b →
        IsGoodAnnulus (μ₀ p.1) (r n) y a' b') := by
  classical
  obtain ⟨δ, hδ, htransfer⟩ := exists_singularRoot_zero_eventually_goodAnnulus_transfer
    hgrowth hγ hγ2 hα h hμ hμ₀ κ hac r hr hd hε hbudget hmid hslack
  have hex (n : ℕ) : ∃ m : ℕ, dyadicScale m < δ n * r n / 2 := by
    have hp : 0 < δ n * r n / 2 := div_pos (mul_pos (hδ n) (hr n)) (by norm_num)
    exact ((tendsto_dyadicScale_nhdsGT.mono_right nhdsWithin_le_nhds).eventually
      (Iio_mem_nhds hp)).exists
  choose m hm using hex
  refine ⟨m, ?_⟩
  filter_upwards [htransfer] with p hp
  filter_upwards [hp] with n hn phase
  obtain ⟨y, hy, hdist⟩ := exists_phase_scaledLattice_dist_lt p.2 phase (dyadicScale_pos (m n))
  refine ⟨y, hy, hdist, ?_⟩
  intro hg
  apply hn y ?_ hg
  rw [dist_comm]
  linarith [hm n]

end HarmonicBalls.Section6
