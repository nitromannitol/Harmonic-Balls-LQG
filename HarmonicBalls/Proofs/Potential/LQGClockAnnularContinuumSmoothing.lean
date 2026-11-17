import HarmonicBalls.Proofs.Potential.LQGClockAnnularGlobalMeasurableLimit
import HarmonicBalls.Proofs.Potential.LQGFineScaleGrid

/-! # Fine radial regularity on an annulus

The inserted circle averages inherit a uniform fine-scale radial modulus away from the origin.
-/

open MeasureTheory Filter LatticeProb.LQG
open scoped Topology

namespace HarmonicBalls

/-- At sufficiently small scales, the inserted field has the same radial modulus as the
uninserted field uniformly on a positive-cutoff annulus. -/
theorem ae_eventually_inserted_circle_radial_modulus
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (α : ℝ)
    {δ a : ℝ} (hδ : 0 < δ) (ha : 0 < a) :
    ∃ β : ℝ, 0 < β ∧ ∀ᵐ ω ∂P, ∀ᶠ k in atTop,
      ∀ z : ℂ, δ ≤ ‖z‖ → ‖z‖ ≤ 1 / 2 → ∀ s t : ℝ,
        dyadicScale k / 2 ≤ s → s ≤ dyadicScale k →
        dyadicScale k / 2 ≤ t → t ≤ dyadicScale k →
        |s - t| < dyadicScale k * dyadicScale k ^ a →
        |LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) s z -
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) t z| ≤ dyadicScale k ^ β := by
  obtain ⟨β, hβ, hmod⟩ := hh.ae_eventually_abs_circle_sub_le ha (1 / 2)
  refine ⟨β, hβ, ?_⟩
  have hsmall : ∀ᶠ k in atTop, dyadicScale k < δ :=
    LatticeProb.LQG.LQGSingularScaledLimit.tendsto_dyadicScale_zero.eventually
      (Iio_mem_nhds hδ)
  filter_upwards [hmod, ae_recentered_inserted_circle_average hh α] with ω hmod hrec
  filter_upwards [hmod, hsmall] with k hk hs z hz hz' s t hs1 hs2 ht1 ht2 hst
  have hd : 0 < dyadicScale k := dyadicScale_pos k
  have hspos : 0 < s := by linarith
  have htpos : 0 < t := by linarith
  have hsmax : max s ‖z‖ = ‖z‖ := max_eq_right (by linarith)
  have htmax : max t ‖z‖ = ‖z‖ := max_eq_right (by linarith)
  rw [← hrec s z hspos, ← hrec t z htpos, hsmax, htmax]
  have heq : hcirc ω s z - hcirc ω 1 0 - α * Real.log ‖z‖ -
      (hcirc ω t z - hcirc ω 1 0 - α * Real.log ‖z‖) =
      hcirc ω s z - hcirc ω t z := by ring
  rw [heq]
  exact hk z hz' s t hs1 hs2 ht1 ht2 hst

end HarmonicBalls
