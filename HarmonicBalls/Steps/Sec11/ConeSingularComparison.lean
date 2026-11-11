import HarmonicBalls.Steps.Sec11.ConeSingularGeometry
import HarmonicBalls.Steps.Sec11.ConeComparison

/-! # Cone-event transfer for the singular Weyl weight -/

namespace HarmonicBalls

/-! The cone-probability development uses Leonardo Bonanno's
Lattice-Probability formalization, including its Cameron-Martin port through
the local smooth-shift and fixed-shift decoder developments. -/

open MeasureTheory Metric Set
open scoped ENNReal

/-- The singular weight gives locally comparable measures on a separated
cone annulus. The squared distortion comes from the chosen anchor point. -/
theorem cone_annulus_comparable_of_singular_weight
    {μ ν : Measure ℂ} {r e : ℝ} {z : ℂ}
    (hr : 0 < r) (hd : r / 100 ≤ infDist (0 : ℂ) (annulus z r (6 * r)))
    (hμ : μ.restrict {0}ᶜ = (ν.withDensity fun x => ENNReal.ofReal (‖x‖ ^ e)).restrict {0}ᶜ) :
    ∃ c : ℝ≥0∞, Section6.IsComparableOnWith μ ν (annulus z r (6 * r)) c
      (ENNReal.ofReal (((1201 : ℝ) ^ |e|) ^ 2)) := by
  have hne : (annulus z r (6 * r)).Nonempty := by
    refine ⟨z + ((2 * r : ℝ) : ℂ), ?_⟩
    have hdist : dist (z + ((2 * r : ℝ) : ℂ)) z = 2 * r := by
      simp [dist_eq_norm, hr.le]
    change dist (z + ((2 * r : ℝ) : ℂ)) z < 6 * r ∧
      ¬ dist (z + ((2 * r : ℝ) : ℂ)) z ≤ r
    rw [hdist]
    constructor <;> linarith
  obtain ⟨p, hp⟩ := hne
  let t : ℝ := (1201 : ℝ) ^ |e|
  let c : ℝ≥0∞ := ENNReal.ofReal (‖p‖ ^ e / t)
  have ht : 0 < t := Real.rpow_pos_of_pos (by norm_num) _
  have hp0 : 0 < ‖p‖ := (norm_le_of_mem_cone_annulus hr hd hp hp).1
  have hc : 0 < ‖p‖ ^ e / t := div_pos (Real.rpow_pos_of_pos hp0 e) ht
  have hsub : annulus z r (6 * r) ⊆ ({0} : Set ℂ)ᶜ := by
    intro x hx h0
    have hx0 := (norm_le_of_mem_cone_annulus hr hd hx hp).1
    have : x = 0 := by simpa using h0
    simp [this] at hx0
  have hrestrict : μ.restrict (annulus z r (6 * r)) =
      (ν.withDensity fun x => ENNReal.ofReal (‖x‖ ^ e)).restrict (annulus z r (6 * r)) := by
    rw [← Measure.restrict_restrict_of_subset hsub, hμ, Measure.restrict_restrict_of_subset hsub]
  refine ⟨c, Section6.isComparableOnWith_of_withDensity
    (isOpen_ball.measurableSet.diff isClosed_closedBall.measurableSet)
    hrestrict (ENNReal.ofReal_ne_zero_iff.2 hc) ENNReal.ofReal_ne_top
    (ENNReal.ofReal_ne_zero_iff.2 (sq_pos_of_pos ht)) ENNReal.ofReal_ne_top ?_⟩
  intro x hx
  have hxp := rpow_norm_le_of_mem_cone_annulus (e := e) hr hd hx hp
  have hpx := rpow_norm_le_of_mem_cone_annulus (e := e) hr hd hp hx
  constructor
  · apply ENNReal.ofReal_le_ofReal
    apply (div_le_iff₀ ht).2
    simpa [t, mul_comm] using hpx
  · rw [← ENNReal.ofReal_mul (sq_nonneg t)]
    apply ENNReal.ofReal_le_ofReal
    have hId : t ^ 2 * (‖p‖ ^ e / t) = t * ‖p‖ ^ e := by field_simp
    change ‖x‖ ^ e ≤ t * ‖p‖ ^ e at hxp
    simpa only [hId] using hxp

/-- A cone event for the ordinary measure implies one for its singular Weyl
weight, with a fixed distortion depending only on the exponent. -/
theorem coneMassEvent_of_singular_weight
    {μ ν : Measure ℂ} {r e M : ℝ} {z : ℂ} {Q : Set ℂ}
    (hr : 0 < r) (hM : 0 ≤ M)
    (hd : r / 100 ≤ infDist (0 : ℂ) (annulus z r (6 * r)))
    (hμ : μ.restrict {0}ᶜ = (ν.withDensity fun x => ENNReal.ofReal (‖x‖ ^ e)).restrict {0}ᶜ)
    (hevent : coneMassEvent ν Q (M * ((1201 : ℝ) ^ |e|) ^ 2) r z) :
    coneMassEvent μ Q M r z := by
  obtain ⟨c, hc⟩ := cone_annulus_comparable_of_singular_weight hr hd hμ
  apply coneMassEvent_of_comparableWith hc ?_ ?_ ?_ hevent
  · intro x hx
    have hx1 : dist x z < 2 * r := hx.1.1
    have hx2 : ¬ dist x z ≤ r := hx.1.2
    constructor <;> simp only [mem_ball, mem_closedBall] at * <;> linarith
  · intro x hx
    have hx1 : dist x z < 6 * r := hx.1
    have hx2 : ¬ dist x z ≤ 3 * r := hx.2
    constructor <;> simp only [mem_ball, mem_closedBall] at * <;> linarith
  · rw [ENNReal.ofReal_mul hM]

end HarmonicBalls
