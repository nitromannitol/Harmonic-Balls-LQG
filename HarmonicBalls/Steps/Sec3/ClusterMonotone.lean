import HarmonicBalls.Steps.Sec3.Basic

/-!
# Lemma 3.3 from Appendix A

`ClusterMonotoneStmt` (Draft/Section3.lean; lemma:monotonicity, line 644): a.s., for all `t₁ ≤ t₂`, `r > 0` and
`z ∈ B_r`, `Λ_{B_r;z}(t₁) ⊆ Λ_{B_r;z}(t₂)`. From Lemma A.3 (line 3731) via `Λ_{B_r;z}(t) = Λ_t` (lines 3574-3578).

## Steps consumed

* `ObstacleMonotoneGeneral` (Steps/SecA/ObstacleMonotone.lean) — Lemma A.3 for every radius and pole.
* `ObstacleCompatibilityShiftStep` (Steps/SecA/ObstacleCompatibility.lean) — the substitution, at `t₁` and `t₂`.
* `LQGVolumeGrowthAllScalesStmt` (Input I2) — the a.s. event.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

universe u

/-- **Lemma 3.3, deterministic form** (for a Radon measure with the volume growth condition on `B_r`). -/
theorem cluster_subset_of_general (hA3 : ObstacleMonotoneGeneral) (hS : ObstacleCompatibilityShiftStep)
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {r βm βp : ℝ} (hr : 0 < r) (hV : VolumeGrowth μ r βm βp)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) r) {t₁ t₂ : ℝ} (ht₁ : 0 < t₁) (ht : t₁ ≤ t₂) :
    cluster μ r z t₁ ⊆ cluster μ r z t₂ := by
  rw [(hS μ hμ r βm βp hr hV z hz t₁ ht₁).2.2.1, (hS μ hμ r βm βp hr hV z hz t₂ (ht₁.trans_le ht)).2.2.1]
  exact (hA3 μ hμ r βm βp hr hV z hz t₁ t₂ ht₁ ht).2

/-- **Lemma 3.3 from Appendix A** (line 614, lines 3574-3578). -/
theorem clusterMonotone_of_steps (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hA3 : ObstacleMonotoneGeneral)
    (hS : ObstacleCompatibilityShiftStep) : ClusterMonotoneStmt.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨βm, βp, hae⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hae] with ω hω
  intro t₁ t₂ r ht₁ ht hr z hz
  exact cluster_subset_of_general hA3 hS hω.1 hr (hω.2 r hr) hz ht₁ ht

end HarmonicBalls
