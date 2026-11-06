import HarmonicBalls.Proofs.Sec6.WeightedRootNearbyDyadicCounts
import HarmonicBalls.Proofs.Sec6.PhaseGridApprox

/-! # Fine shifted lattices near weighted LQG roots

The countable-centre iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
universe u

/-- For each dyadic window, sufficiently fine lattices of every phase contain
nearby centres satisfying the relaxed count bound. The mesh threshold may depend
on the field, root, scale and window. -/
theorem exists_ae_all_weightedMass_eventually_phase_lattice_goodAnnuli_count
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {b : ℝ} (hb : 0 < b) (β : ℝ) (hβ : β ∈ Ioo (0 : ℝ) 1)
    (s : ℕ → ℝ) (hs : ∀ i, 0 < s i) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ᵐ ω ∂P, ∀ wgt : ℂ → ℝ≥0∞,
      ∀ᵐ z ∂((μ ω).withDensity wgt).restrict (ball 0 1), ∀ i, ∀ᶠ n : ℕ in atTop,
      ∀ᶠ m : ℕ in atTop, ∀ phase : ℂ, ∃ y : ℂ,
        y - phase ∈ scaledLattice (dyadicScale m) ∧ dist z y < 2 * dyadicScale m ∧
        (β / 16) * Real.logb 7 ((dyadicScale n) ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc (dyadicScale n) ((dyadicScale n) ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
          IsGoodAnnulus (μ ω) (s i * r) y (a / 2) (b + 2)}.ncard : ℝ) := by
  obtain ⟨a, ha, ht⟩ :=
    exists_ae_all_weightedMass_eventually_nearby_dyadic_goodAnnuli_count
      hgrowth hγ hγ2 h hμ hb β hβ s hs
  refine ⟨a, ha, ?_⟩
  filter_upwards [ht] with ω hω
  intro wgt
  filter_upwards [hω wgt] with z hz i
  filter_upwards [hz i] with n hn
  obtain ⟨δ, hδ, hnear⟩ := hn
  have hm : ∀ᶠ m : ℕ in atTop, dyadicScale m < δ / 2 :=
    (tendsto_dyadicScale_nhdsGT.mono_right nhdsWithin_le_nhds).eventually
      (Iio_mem_nhds (by linarith : (0 : ℝ) < δ / 2))
  filter_upwards [hm] with m hm phase
  obtain ⟨y, hy, hd⟩ := exists_phase_scaledLattice_dist_lt z phase (dyadicScale_pos m)
  refine ⟨y, hy, hd, hnear y ?_⟩
  rw [dist_comm]
  linarith

end HarmonicBalls.Section6
