import HarmonicBalls.Proofs.Sec8.PullbackRegularity
import HarmonicBalls.Proofs.Sec8.LQGRandomGoodAnnulus

/-! # Stationarity of very-good indicators up to null sets -/

open Set Metric MeasureTheory Filter ProbabilityTheory
open scoped ENNReal NNReal

namespace HarmonicBalls

universe u

open Classical MarkovProcess in
/-- For positive mass parameter, the joint very-good and comparison process
is stationary using its Borel representative on regular measures. Point
avoidance and the staged LQG inputs are explicit hypotheses. -/
theorem identDistrib_lqg_veryGoodComparable_of_ae_point_avoidance
    (hfull : LQGMeasureFullSupportStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hatom : LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m : ℝ) (ha : 0 < a)
    (hpolar : ∀ (u x : ℂ), x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x) :
    IdentDistrib
      (fun ω n => if IsVeryGoodAnnulus (μ ω) β (dyadicScale n) 0 N₀
        a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) n 0 m then (1 : ℝ) else 0)
      (fun ω n => if IsVeryGoodAnnulus (μ ω) β (dyadicScale (1 + n)) 0 N₀
        a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) (1 + n) 0 m then (1 : ℝ) else 0)
      P P := by
  have hchoose : ∀ n : ℕ, ∃ G : Set (Measure ℂ), MeasurableSet G ∧ ∀ (ν : Measure ℂ),
      (∀ x : ℂ, ν {x} = 0) → IsLocallyFiniteMeasure ν →
      (∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < ν U) →
      (ν ∈ G ↔ IsVeryGoodAnnulus ν β (dyadicScale n) 0 N₀ a b C₁m C₁p C₂m C₂p C₃) :=
    fun n => exists_measurable_isVeryGoodAnnulus_on_fullSupport β (dyadicScale n)
      (dyadicScale_pos n) N₀ a b C₁m C₁p C₂m C₂p C₃ ha hpolar
  choose G hG hrep using hchoose
  let F : Measure ℂ → ℕ → ℝ := fun ν n =>
    if ν ∈ G n ∧ AnnulusBallComparison ν n 0 m then 1 else 0
  have hF : Measurable F := by
    apply Measurable.of_eval
    intro n
    exact measurable_const.piecewise ((hG n).inter
      (measurableSet_annulusBallComparison n 0 m)) measurable_const
  have hd := (hGFF.identDistrib_normalizedPullback hAff hCC hγ hγ2 hα hμ
    (dyadicScale_pos 1)).comp hF
  have hregular : ∀ᵐ ω ∂P, (∀ x : ℂ, μ ω {x} = 0) ∧
      IsLocallyFiniteMeasure (μ ω) ∧
      ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ ω U := by
    filter_upwards [hatom hGFF hγ hγ2 hα μ hμ, hμ,
      hfull γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω haω hlω hfω
    exact ⟨haω, hlω.isLocallyFiniteMeasure, hfω⟩
  have heq₁ : (F ∘ μ) =ᵐ[P] (fun ω n => if IsVeryGoodAnnulus (μ ω) β (dyadicScale n) 0 N₀
      a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) n 0 m then (1 : ℝ) else 0) := by
    filter_upwards [hregular] with ω hω
    funext n
    simp only [Function.comp_apply, F, hrep n (μ ω) hω.1 hω.2.1 hω.2.2]
  have heq₂ : (F ∘ fun ω => normalizedPullbackMeasure γ α₀ (dyadicScale 1) (hcirc ω) (μ ω)) =ᵐ[P]
      (fun ω n => if IsVeryGoodAnnulus (μ ω) β (dyadicScale (1 + n)) 0 N₀
        a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) (1 + n) 0 m then (1 : ℝ) else 0) := by
    filter_upwards [hregular] with ω hω
    funext n
    let ν := normalizedPullbackMeasure γ α₀ (dyadicScale 1) (hcirc ω) (μ ω)
    have hv := normalizedPullbackMeasure_regular (μ ω) γ α₀ (dyadicScale 1)
      (dyadicScale_pos 1) (hcirc ω) hω.1 hω.2.1 hω.2.2
    have ht : IsVeryGoodAnnulus ν β (dyadicScale n) 0 N₀ a b C₁m C₁p C₂m C₂p C₃ ↔
        IsVeryGoodAnnulus (μ ω) β (dyadicScale (1 + n)) 0 N₀ a b C₁m C₁p C₂m C₂p C₃ := by
      rw [isVeryGoodAnnulus_normalizedPullback, isVeryGoodAnnulus_map_inv_smul _ (dyadicScale_pos 1)]
      simp only [dyadicScale, pow_add]
    have hc : AnnulusBallComparison ν n 0 m ↔ AnnulusBallComparison (μ ω) (1 + n) 0 m := by
      simp only [ν, normalizedPullbackMeasure]
      rw [annulusBallComparison_smul, annulusBallComparison_map_dyadic]
      · apply ne_of_gt
        apply ENNReal.ofReal_pos.mpr
        positivity
      · exact ENNReal.ofReal_ne_top
    change (if ν ∈ G n ∧ AnnulusBallComparison ν n 0 m then (1 : ℝ) else 0) = _
    rw [hrep n ν hv.1 hv.2.1 hv.2.2, ht, hc]
  exact ((IdentDistrib.of_ae_eq hd.aemeasurable_fst heq₁).symm.trans hd).trans
    (IdentDistrib.of_ae_eq hd.aemeasurable_snd heq₂)

end HarmonicBalls
