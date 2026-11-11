import HarmonicBalls.Proofs.Sec6.SizeRatioGeneralComparison
import HarmonicBalls.Draft.Section11

/-! # Cone events under locally comparable measures -/

namespace HarmonicBalls

/-! The cone-probability development uses Leonardo Bonanno's
Lattice-Probability formalization, including its Cameron-Martin port through
the local smooth-shift and fixed-shift decoder developments. -/

open MeasureTheory Metric Set
open scoped ENNReal

/-- Local measure comparison transfers a cone event, with its threshold
multiplied by the distortion. No finiteness of the masses is required. -/
theorem coneMassEvent_of_comparableWith
    {μ ν : Measure ℂ} {B Q : Set ℂ} {c K : ℝ≥0∞} {M M' r : ℝ} {z : ℂ}
    (h : Section6.IsComparableOnWith μ ν B c K)
    (hinner : annulus z r (2 * r) ∩ coneAt Q z ⊆ B)
    (houter : annulus z (3 * r) (6 * r) ⊆ B)
    (hthreshold : ENNReal.ofReal M * K ≤ ENNReal.ofReal M')
    (hevent : coneMassEvent ν Q M' r z) : coneMassEvent μ Q M r z := by
  have hg : Section6.IsComparableOnWith μ ν (annulus z (3 * r) (6 * r)) c K := by
    refine ⟨h.scale_ne_zero, h.scale_ne_top, h.distortion_ne_zero, h.distortion_ne_top, ?_, ?_⟩
    · have ht := Measure.restrict_mono (subset_refl (annulus z (3 * r) (6 * r))) h.lower
      rwa [Measure.restrict_smul, Measure.restrict_restrict_of_subset houter,
        Measure.restrict_restrict_of_subset houter] at ht
    · have ht := Measure.restrict_mono (subset_refl (annulus z (3 * r) (6 * r))) h.upper
      rwa [Measure.restrict_smul, Measure.restrict_restrict_of_subset houter,
        Measure.restrict_restrict_of_subset houter] at ht
  have hgreen := (Section6.annulusGreenPotentialSup_comparableWith hg).2
  change ENNReal.ofReal M * annulusGreenPotentialSup μ z (3 * r) (6 * r) ≤
    μ (annulus z r (2 * r) ∩ coneAt Q z)
  calc
    _ ≤ ENNReal.ofReal M * (K * c * annulusGreenPotentialSup ν z (3 * r) (6 * r)) := by gcongr
    _ = c * ((ENNReal.ofReal M * K) * annulusGreenPotentialSup ν z (3 * r) (6 * r)) := by ac_rfl
    _ ≤ c * (ENNReal.ofReal M' * annulusGreenPotentialSup ν z (3 * r) (6 * r)) := by gcongr
    _ ≤ c * ν (annulus z r (2 * r) ∩ coneAt Q z) := by
      gcongr
      exact hevent
    _ ≤ μ (annulus z r (2 * r) ∩ coneAt Q z) := h.le_apply hinner

end HarmonicBalls
