import HarmonicBalls.Proofs.Sec6.SizeRatioSingularWeight

/-! # Local comparison for the good-annulus count -/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal

/-- At sufficiently fine dyadic scales, five times the maximal radius fits
between the middle and outer annuli. -/
theorem sqrt_dyadicScale_le_one_twentieth {n : ℕ} (hn : 9 ≤ n) :
    Real.sqrt (dyadicScale n) ≤ 1 / 20 := by
  rw [Real.sqrt_le_left (by norm_num)]
  unfold dyadicScale
  calc (2 : ℝ)⁻¹ ^ n ≤ (2 : ℝ)⁻¹ ^ 9 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
    _ ≤ (1 / 20) ^ 2 := by norm_num

/-- Good annuli tested at fine scales lie in the size annulus. -/
theorem goodAnnulus_subset_size_annulus {ρ r : ℝ} {x₀ z : ℂ}
    (_hρ : 0 < ρ) (hz : z ∈ annulus x₀ (ρ / 2) ρ) (hr : 5 * r ≤ ρ / 4) :
    annulus z (3 * r) (5 * r) ⊆ annulus x₀ (ρ / 4) (2 * ρ) := by
  intro y hy
  have hzouter : dist z x₀ < ρ := hz.1
  have hzinner : ρ / 2 < dist z x₀ := lt_of_not_ge hz.2
  have hyz : dist y z < 5 * r := hy.1
  have htri₁ := dist_triangle y z x₀
  have htri₂ := dist_triangle z y x₀
  have hsym : dist z y = dist y z := dist_comm z y
  constructor
  · change dist y x₀ < 2 * ρ
    linarith
  · change ¬ dist y x₀ ≤ ρ / 4
    linarith

/-- A general measure comparison on the size annulus transfers criterion three
at fine scales, with the threshold divided by its distortion. -/
theorem veryGoodCriterionThree_of_comparableWith
    {μ ν : Measure ℂ} {x₀ : ℂ} {ρ t : ℝ} {c : ℝ≥0∞}
    (h : IsComparableOnWith μ ν (annulus x₀ (ρ / 4) (2 * ρ)) c (ENNReal.ofReal t))
    (hρ : 0 < ρ) (ht : 0 < t) {N₀ : ℕ} (hN₀ : 9 ≤ N₀) {a b C₃ : ℝ}
    (hv : VeryGoodCriterionThree ν ρ x₀ N₀ a b C₃) :
    VeryGoodCriterionThree μ ρ x₀ N₀ (a / t) b C₃ := by
  intro n hn z hz
  have hε : 0 < dyadicScale n := by unfold dyadicScale; positivity
  have hsq := sqrt_dyadicScale_le_one_twentieth (hN₀.trans hn)
  refine (hv n hn z hz).trans ?_
  norm_cast
  refine Set.ncard_le_ncard (fun r hr => ⟨hr.1, hr.2.1, ?_⟩) ?_
  · have hbound : 5 * r ≤ ρ / 4 := by
      have h1 := mul_le_mul_of_nonneg_right hsq hρ.le
      linarith [hr.1.2]
    have hsub := goodAnnulus_subset_size_annulus hρ hz.2 hbound
    apply isGoodAnnulus_of_measure_comparison h.scale_ne_zero h.scale_ne_top ht
      (fun s hs => h.le_apply (hs.trans hsub)) (h.apply_le hsub) hr.2.2
  · refine finite_of_geometric (q := (7 : ℝ)⁻¹) (A := ρ) (lo := dyadicScale n * ρ)
      (by norm_num) (by norm_num) (by positivity) fun r hr => ⟨hr.1.1, ?_⟩
    obtain ⟨k, -, hk⟩ := hr.2.1
    exact ⟨k, hk⟩

/-- Criterion three transfers through the singular Weyl density on an
admissible size annulus, even when the origin lies in its hole. -/
theorem veryGoodCriterionThree_of_singular_weight
    {μ ν : Measure ℂ} {x₀ : ℂ} {ρ e : ℝ} {N₀ : ℕ} {a b C₃ : ℝ}
    (hρ : 0 < ρ) (hd : ρ / 100 ≤ infDist (0 : ℂ) (annulus x₀ (ρ / 4) (2 * ρ)))
    (hN₀ : 9 ≤ N₀)
    (hμ : μ.restrict {0}ᶜ = (ν.withDensity fun x => ENNReal.ofReal (‖x‖ ^ e)).restrict {0}ᶜ)
    (hv : VeryGoodCriterionThree ν ρ x₀ N₀ a b C₃) :
    VeryGoodCriterionThree μ ρ x₀ N₀ (a / (((401 : ℝ) ^ |e|) ^ 2)) b C₃ := by
  obtain ⟨c, hc⟩ := isComparableOnWith_size_annulus_of_weight hρ hd hμ
  exact veryGoodCriterionThree_of_comparableWith hc hρ
    (sq_pos_of_pos (Real.rpow_pos_of_pos (by norm_num) _)) hN₀ hv


/-- The failure probability of criterion three under a singular weight is at
most the corresponding whole-plane failure probability. -/
theorem measure_not_criterionThree_le_of_singular_weight
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {μ ν : Ω → Measure ℂ}
    {x₀ : ℂ} {ρ e : ℝ} {N₀ : ℕ} {a b C₃ : ℝ}
    (hρ : 0 < ρ) (hd : ρ / 100 ≤ infDist (0 : ℂ) (annulus x₀ (ρ / 4) (2 * ρ)))
    (hN₀ : 9 ≤ N₀)
    (hμ : ∀ᵐ ω ∂P, (μ ω).restrict {0}ᶜ =
      ((ν ω).withDensity fun x => ENNReal.ofReal (‖x‖ ^ e)).restrict {0}ᶜ) :
    P {ω | ¬ VeryGoodCriterionThree (μ ω) ρ x₀ N₀
      (a / (((401 : ℝ) ^ |e|) ^ 2)) b C₃} ≤
      P {ω | ¬ VeryGoodCriterionThree (ν ω) ρ x₀ N₀ a b C₃} := by
  apply measure_mono_ae
  filter_upwards [hμ] with ω hω hbad
  intro hv
  exact hbad (veryGoodCriterionThree_of_singular_weight hρ hd hN₀ hω hv)

end HarmonicBalls.Section6
