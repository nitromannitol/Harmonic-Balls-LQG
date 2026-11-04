import HarmonicBalls.Proofs.Sec6.SizeRatioGeneralComparison
import HarmonicBalls.Proofs.Sec6.SingularWeight

/-! # Singular weight on a very good annulus -/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set
open scoped ENNReal

/-- Distances to the origin on an admissible size annulus have bounded ratio. -/
theorem norm_le_of_mem_size_annulus {ρ : ℝ} {x₀ x y : ℂ}
    (hρ : 0 < ρ) (hd : ρ / 100 ≤ infDist (0 : ℂ) (annulus x₀ (ρ / 4) (2 * ρ)))
    (hx : x ∈ annulus x₀ (ρ / 4) (2 * ρ))
    (hy : y ∈ annulus x₀ (ρ / 4) (2 * ρ)) :
    0 < ‖x‖ ∧ ‖y‖ ≤ 401 * ‖x‖ := by
  have hx0 : ρ / 100 ≤ ‖x‖ := by
    simpa [dist_zero_left] using hd.trans (infDist_le_dist_of_mem hx)
  have hxz : dist x x₀ < 2 * ρ := mem_ball.1 hx.1
  have hyz : dist y x₀ < 2 * ρ := mem_ball.1 hy.1
  have hxy : dist y x < 4 * ρ := by
    have h := dist_triangle y x₀ x
    rw [dist_comm x₀ x] at h
    linarith
  have hn : ‖y‖ ≤ ‖x‖ + dist y x := by
    simpa [dist_zero_right, dist_comm y x, add_comm] using dist_triangle y x (0 : ℂ)
  constructor <;> linarith

/-- The power weight oscillates by a constant depending only on its exponent. -/
theorem rpow_norm_le_of_mem_size_annulus {ρ e : ℝ} {x₀ x y : ℂ}
    (hρ : 0 < ρ) (hd : ρ / 100 ≤ infDist (0 : ℂ) (annulus x₀ (ρ / 4) (2 * ρ)))
    (hx : x ∈ annulus x₀ (ρ / 4) (2 * ρ))
    (hy : y ∈ annulus x₀ (ρ / 4) (2 * ρ)) :
    ‖x‖ ^ e ≤ (401 : ℝ) ^ |e| * ‖y‖ ^ e := by
  obtain ⟨hx0, hyx⟩ := norm_le_of_mem_size_annulus hρ hd hx hy
  obtain ⟨hy0, hxy⟩ := norm_le_of_mem_size_annulus hρ hd hy hx
  have hratio : ‖x‖ ^ e / ‖y‖ ^ e = (‖x‖ / ‖y‖) ^ e := by
    rw [Real.div_rpow hx0.le hy0.le]
  have hb : (‖x‖ / ‖y‖) ^ e ≤ (401 : ℝ) ^ |e| := by
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

/-- The size annulus is nonempty at every positive scale. -/
theorem size_annulus_nonempty {ρ : ℝ} {x₀ : ℂ} (hρ : 0 < ρ) :
    (annulus x₀ (ρ / 4) (2 * ρ)).Nonempty := by
  refine ⟨x₀ + (ρ : ℂ), ?_⟩
  have hdist : dist (x₀ + (ρ : ℂ)) x₀ = ρ := by
    simp [dist_eq_norm, hρ.le]
  change dist (x₀ + (ρ : ℂ)) x₀ < 2 * ρ ∧ ¬ dist (x₀ + (ρ : ℂ)) x₀ ≤ ρ / 4
  rw [hdist]
  constructor <;> linarith

/-- The Weyl density is comparable on the size annulus, with distortion independent of
its center and scale. The origin may lie in the hole. -/
theorem isComparableOnWith_size_annulus_of_weight {μ ν : Measure ℂ} {ρ e : ℝ} {x₀ : ℂ}
    (hρ : 0 < ρ) (hd : ρ / 100 ≤ infDist (0 : ℂ) (annulus x₀ (ρ / 4) (2 * ρ)))
    (hμ : μ.restrict {0}ᶜ = (ν.withDensity fun x => ENNReal.ofReal (‖x‖ ^ e)).restrict {0}ᶜ) :
    ∃ c : ℝ≥0∞, IsComparableOnWith μ ν (annulus x₀ (ρ / 4) (2 * ρ)) c
      (ENNReal.ofReal (((401 : ℝ) ^ |e|) ^ 2)) := by
  obtain ⟨p, hp⟩ := size_annulus_nonempty (x₀ := x₀) hρ
  let t : ℝ := (401 : ℝ) ^ |e|
  let c : ℝ≥0∞ := ENNReal.ofReal (‖p‖ ^ e / t)
  have ht : 0 < t := Real.rpow_pos_of_pos (by norm_num) _
  have hp0 : 0 < ‖p‖ := (norm_le_of_mem_size_annulus hρ hd hp hp).1
  have hc : 0 < ‖p‖ ^ e / t := div_pos (Real.rpow_pos_of_pos hp0 e) ht
  have hsub : annulus x₀ (ρ / 4) (2 * ρ) ⊆ ({0} : Set ℂ)ᶜ := by
    intro x hx h0
    have hx0 := (norm_le_of_mem_size_annulus hρ hd hx hp).1
    have : x = 0 := by simpa using h0
    simp [this] at hx0
  have hrestrict : μ.restrict (annulus x₀ (ρ / 4) (2 * ρ)) =
      (ν.withDensity fun x => ENNReal.ofReal (‖x‖ ^ e)).restrict (annulus x₀ (ρ / 4) (2 * ρ)) := by
    rw [← Measure.restrict_restrict_of_subset hsub, hμ, Measure.restrict_restrict_of_subset hsub]
  refine ⟨c, isComparableOnWith_of_withDensity (isOpen_ball.measurableSet.diff isClosed_closedBall.measurableSet)
    hrestrict (ENNReal.ofReal_ne_zero_iff.2 hc) ENNReal.ofReal_ne_top
    (ENNReal.ofReal_ne_zero_iff.2 (sq_pos_of_pos ht)) ENNReal.ofReal_ne_top ?_⟩
  intro x hx
  have hxp := rpow_norm_le_of_mem_size_annulus (e := e) hρ hd hx hp
  have hpx := rpow_norm_le_of_mem_size_annulus (e := e) hρ hd hp hx
  constructor
  · apply ENNReal.ofReal_le_ofReal
    apply (div_le_iff₀ ht).2
    simpa [t, mul_comm] using hpx
  · rw [← ENNReal.ofReal_mul (sq_nonneg t)]
    apply ENNReal.ofReal_le_ofReal
    have hId : t ^ 2 * (‖p‖ ^ e / t) = t * ‖p‖ ^ e := by field_simp
    change ‖x‖ ^ e ≤ t * ‖p‖ ^ e at hxp
    simpa only [hId] using hxp


/-- Both size windows transfer across the Weyl density with a uniform distortion. -/
theorem size_windows_of_singular_weight {μ ν : Measure ℂ} {ρ e β : ℝ} {x₀ : ℂ}
    {lo₁ hi₁ lo₂ hi₂ : ℝ≥0∞}
    (hρ : 0 < ρ) (hd : ρ / 100 ≤ infDist (0 : ℂ) (annulus x₀ (ρ / 4) (2 * ρ)))
    (hμ : μ.restrict {0}ᶜ = (ν.withDensity fun x => ENNReal.ofReal (‖x‖ ^ e)).restrict {0}ᶜ)
    (hM : annulusBallMassSize ν β ρ x₀ / ν (annulus x₀ (ρ / 4) (2 * ρ)) ∈ Icc lo₁ hi₁)
    (hG : annulusGreenPotentialSup ν x₀ (ρ / 4) (2 * ρ) /
      ν (annulus x₀ (ρ / 4) (2 * ρ)) ∈ Icc lo₂ hi₂) :
    let K := ENNReal.ofReal (((401 : ℝ) ^ |e|) ^ 2)
    annulusBallMassSize μ β ρ x₀ / μ (annulus x₀ (ρ / 4) (2 * ρ)) ∈ Icc (lo₁ / K) (K * hi₁) ∧
    annulusGreenPotentialSup μ x₀ (ρ / 4) (2 * ρ) /
      μ (annulus x₀ (ρ / 4) (2 * ρ)) ∈ Icc (lo₂ / K) (K * hi₂) := by
  obtain ⟨c, hc⟩ := isComparableOnWith_size_annulus_of_weight hρ hd hμ
  exact veryGood_size_windows_of_comparableWith_on_annulus hc hρ hM hG

end HarmonicBalls.Section6
