import HarmonicBalls.Proofs.Sec6.GoodAnnulusComparison

/-!
# Singular weights on admissible annuli

The logarithmic singularity changes LQG area by the density `‖x‖ ^ e`. On an annulus whose
distance from the origin is at least `r / 100`, its oscillation is bounded uniformly in the
radius and center. This is the geometric part of the reduction in Lemma 6.4, with the
dependence on the singularity exponent retained (GRAPH G19).
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set
open scoped ENNReal

/-- Any two points of an admissible annulus have comparable distances from the origin. -/
theorem norm_le_of_mem_admissible_annulus {r : ℝ} {z x y : ℂ}
    (hr : 0 < r) (hd : r / 100 ≤ infDist (0 : ℂ) (annulus z (3 * r) (5 * r)))
    (hx : x ∈ annulus z (3 * r) (5 * r))
    (hy : y ∈ annulus z (3 * r) (5 * r)) :
    0 < ‖x‖ ∧ ‖y‖ ≤ 1001 * ‖x‖ := by
  have hx0 : r / 100 ≤ ‖x‖ := by
    simpa [dist_zero_left] using hd.trans (infDist_le_dist_of_mem hx)
  have hxz : dist x z < 5 * r := mem_ball.1 hx.1
  have hyz : dist y z < 5 * r := mem_ball.1 hy.1
  have hxy : dist y x < 10 * r := by
    have h := dist_triangle y z x
    rw [dist_comm z x] at h
    linarith
  have hn : ‖y‖ ≤ ‖x‖ + dist y x := by
    simpa [dist_zero_right, dist_comm y x, add_comm] using dist_triangle y x (0 : ℂ)
  constructor
  · linarith
  · linarith

/-- The ratio of the power weights on an admissible annulus is uniformly bounded. -/
theorem rpow_norm_le_of_mem_admissible_annulus {r e : ℝ} {z x y : ℂ}
    (hr : 0 < r) (hd : r / 100 ≤ infDist (0 : ℂ) (annulus z (3 * r) (5 * r)))
    (hx : x ∈ annulus z (3 * r) (5 * r))
    (hy : y ∈ annulus z (3 * r) (5 * r)) :
    ‖x‖ ^ e ≤ (1001 : ℝ) ^ |e| * ‖y‖ ^ e := by
  obtain ⟨hx0, hyx⟩ := norm_le_of_mem_admissible_annulus hr hd hx hy
  obtain ⟨hy0, hxy⟩ := norm_le_of_mem_admissible_annulus hr hd hy hx
  have hratio : ‖x‖ ^ e / ‖y‖ ^ e = (‖x‖ / ‖y‖) ^ e := by
    rw [Real.div_rpow hx0.le hy0.le]
  have hb : (‖x‖ / ‖y‖) ^ e ≤ (1001 : ℝ) ^ |e| := by
    by_cases he : 0 ≤ e
    · rw [abs_of_nonneg he]
      exact Real.rpow_le_rpow (div_nonneg hx0.le hy0.le) ((div_le_iff₀ hy0).2 hxy) he
    · have he' : 0 ≤ -e := by linarith
      have heq := Real.rpow_neg_eq_inv_rpow (‖x‖ / ‖y‖) (-e)
      simp only [neg_neg, inv_div] at heq
      rw [abs_of_nonpos (le_of_not_ge he), heq]
      exact Real.rpow_le_rpow (div_nonneg hy0.le hx0.le) ((div_le_iff₀ hx0).2 hyx) he'
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hy0 e)).1
  rw [hratio]
  exact hb

/-- An admissible annulus contains a point at distance `4r` from its center. -/
theorem admissible_annulus_nonempty {r : ℝ} {z : ℂ} (hr : 0 < r) :
    (annulus z (3 * r) (5 * r)).Nonempty := by
  refine ⟨z + ((4 * r : ℝ) : ℂ), ?_⟩
  have hdist : dist (z + ((4 * r : ℝ) : ℂ)) z = 4 * r := by
    simp [dist_eq_norm, hr.le]
  change dist (z + ((4 * r : ℝ) : ℂ)) z < 5 * r ∧
    ¬ dist (z + ((4 * r : ℝ) : ℂ)) z ≤ 3 * r
  rw [hdist]
  constructor <;> linarith

/-- Removing a logarithmic singularity transfers the bad-annulus outer-probability bound.
The threshold loss depends only on the singularity exponent, not on the radius or center. -/
theorem badGoodAnnulus_measure_le_of_singular_weight
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {μ ν : Ω → Measure ℂ}
    {r e a b : ℝ} {z : ℂ} (hr : 0 < r)
    (hd : r / 100 ≤ infDist (0 : ℂ) (annulus z (3 * r) (5 * r)))
    (hμ : ∀ᵐ ω ∂P, (μ ω).restrict {0}ᶜ =
      ((ν ω).withDensity fun x => ENNReal.ofReal (‖x‖ ^ e)).restrict {0}ᶜ) :
    P {ω | ¬ IsGoodAnnulus (μ ω) r z (a / ((1001 : ℝ) ^ |e|) ^ 2) b} ≤
      P {ω | ¬ IsGoodAnnulus (ν ω) r z a b} := by
  obtain ⟨p, hp⟩ := admissible_annulus_nonempty (z := z) hr
  let t : ℝ := (1001 : ℝ) ^ |e|
  let c : ℝ≥0∞ := ENNReal.ofReal (‖p‖ ^ e / t)
  have ht : 0 < t := Real.rpow_pos_of_pos (by norm_num) _
  have hp0 : 0 < ‖p‖ := (norm_le_of_mem_admissible_annulus hr hd hp hp).1
  have hc : 0 < ‖p‖ ^ e / t := div_pos (Real.rpow_pos_of_pos hp0 e) ht
  have hsub : annulus z (3 * r) (5 * r) ⊆ ({0} : Set ℂ)ᶜ := by
    intro x hx h0
    have hx0 := (norm_le_of_mem_admissible_annulus hr hd hx hp).1
    have : x = 0 := by simpa using h0
    simp [this] at hx0
  have hrestrict : ∀ᵐ ω ∂P, (μ ω).restrict (annulus z (3 * r) (5 * r)) =
      ((ν ω).withDensity fun x => ENNReal.ofReal (‖x‖ ^ e)).restrict (annulus z (3 * r) (5 * r)) := by
    filter_upwards [hμ] with ω hω
    rw [← Measure.restrict_restrict_of_subset hsub, hω, Measure.restrict_restrict_of_subset hsub]
  apply badGoodAnnulus_measure_le_of_withDensity_bounds P (c := c)
    (ENNReal.ofReal_ne_zero_iff.2 hc) ENNReal.ofReal_ne_top (sq_pos_of_pos ht) _ hrestrict
  intro x hx
  have hxp := rpow_norm_le_of_mem_admissible_annulus (e := e) hr hd hx hp
  have hpx := rpow_norm_le_of_mem_admissible_annulus (e := e) hr hd hp hx
  constructor
  · apply ENNReal.ofReal_le_ofReal
    apply (div_le_iff₀ ht).2
    simpa [t, mul_comm] using hpx
  · rw [← ENNReal.ofReal_mul (sq_nonneg t)]
    apply ENNReal.ofReal_le_ofReal
    have hId : t ^ 2 * (‖p‖ ^ e / t) = t * ‖p‖ ^ e := by
      field_simp
    change ‖x‖ ^ e ≤ t * ‖p‖ ^ e at hxp
    simpa only [hId] using hxp

end HarmonicBalls.Section6
