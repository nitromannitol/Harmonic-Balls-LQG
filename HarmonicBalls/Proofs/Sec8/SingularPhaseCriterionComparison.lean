import HarmonicBalls.Proofs.Sec8.PhaseCriterionTranslation
import HarmonicBalls.Proofs.Sec6.CriterionThreeLocalComparison

/-! # Phase criterion under a singular Weyl weight -/

open MeasureTheory Metric Set Filter
open scoped ENNReal

namespace HarmonicBalls

/-- A comparison on the size annulus transports the phase-shifted
criterion, with the mass threshold divided by the comparison distortion. -/
theorem phaseVeryGoodCriterionThree_of_comparableWith
    {μ ν : Measure ℂ} {x₀ : ℂ} {ρ t : ℝ} {c : ℝ≥0∞}
    (h : Section6.IsComparableOnWith μ ν (annulus x₀ (ρ / 4) (2 * ρ)) c (ENNReal.ofReal t))
    (hρ : 0 < ρ) (ht : 0 < t) {N₀ : ℕ} (hN₀ : 9 ≤ N₀) {a b C₃ : ℝ}
    {phase : ℕ → ℂ} (hv : PhaseVeryGoodCriterionThree ν ρ x₀ N₀ a b C₃ phase) :
    PhaseVeryGoodCriterionThree μ ρ x₀ N₀ (a / t) b C₃ phase := by
  intro n hn z hz hphase
  have hε : 0 < dyadicScale n := by unfold dyadicScale; positivity
  have hsq := Section6.sqrt_dyadicScale_le_one_twentieth (hN₀.trans hn)
  refine (hv n hn z hz hphase).trans ?_
  norm_cast
  refine Set.ncard_le_ncard (fun r hr => ⟨hr.1, hr.2.1, ?_⟩) ?_
  · have hbound : 5 * r ≤ ρ / 4 := by
      have h1 := mul_le_mul_of_nonneg_right hsq hρ.le
      linarith [hr.1.2]
    have hsub := Section6.goodAnnulus_subset_size_annulus hρ hz hbound
    apply Section6.isGoodAnnulus_of_measure_comparison h.scale_ne_zero h.scale_ne_top ht
      (fun s hs => h.le_apply (hs.trans hsub)) (h.apply_le hsub) hr.2.2
  · refine Section6.finite_of_geometric (q := (7 : ℝ)⁻¹) (A := ρ) (lo := dyadicScale n * ρ)
      (by norm_num) (by norm_num) (by positivity) fun r hr => ⟨hr.1.1, ?_⟩
    obtain ⟨k, -, hk⟩ := hr.2.1
    exact ⟨k, hk⟩

/-- A logarithmic Weyl weight transfers every prescribed phase sequence on
an annulus separated from the singularity. -/
theorem phaseVeryGoodCriterionThree_of_singular_weight
    {μ ν : Measure ℂ} {x₀ : ℂ} {ρ e : ℝ} {N₀ : ℕ} {a b C₃ : ℝ}
    {phase : ℕ → ℂ} (hρ : 0 < ρ)
    (hd : ρ / 100 ≤ infDist (0 : ℂ) (annulus x₀ (ρ / 4) (2 * ρ))) (hN₀ : 9 ≤ N₀)
    (hμ : μ.restrict {0}ᶜ = (ν.withDensity fun x => ENNReal.ofReal (‖x‖ ^ e)).restrict {0}ᶜ)
    (hv : PhaseVeryGoodCriterionThree ν ρ x₀ N₀ a b C₃ phase) :
    PhaseVeryGoodCriterionThree μ ρ x₀ N₀ (a / (((401 : ℝ) ^ |e|) ^ 2)) b C₃ phase := by
  obtain ⟨c, hc⟩ := Section6.isComparableOnWith_size_annulus_of_weight hρ hd hμ
  exact phaseVeryGoodCriterionThree_of_comparableWith hc hρ
    (sq_pos_of_pos (Real.rpow_pos_of_pos (by norm_num) _)) hN₀ hv

/-- The singular-weight criterion failure probability is bounded by the
failure probability for the unweighted measure at the same phases. -/
theorem measure_not_phaseVeryGoodCriterionThree_le_of_singular_weight
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {μ ν : Ω → Measure ℂ}
    {x₀ : ℂ} {ρ e : ℝ} {N₀ : ℕ} {a b C₃ : ℝ} {phase : ℕ → ℂ}
    (hρ : 0 < ρ) (hd : ρ / 100 ≤ infDist (0 : ℂ) (annulus x₀ (ρ / 4) (2 * ρ)))
    (hN₀ : 9 ≤ N₀)
    (hμ : ∀ᵐ ω ∂P, (μ ω).restrict {0}ᶜ =
      ((ν ω).withDensity fun x => ENNReal.ofReal (‖x‖ ^ e)).restrict {0}ᶜ) :
    P {ω | ¬ PhaseVeryGoodCriterionThree (μ ω) ρ x₀ N₀
      (a / (((401 : ℝ) ^ |e|) ^ 2)) b C₃ phase} ≤
      P {ω | ¬ PhaseVeryGoodCriterionThree (ν ω) ρ x₀ N₀ a b C₃ phase} := by
  apply measure_mono_ae
  filter_upwards [hμ] with ω hω hbad
  intro hv
  exact hbad (phaseVeryGoodCriterionThree_of_singular_weight hρ hd hN₀ hω hv)

end HarmonicBalls
