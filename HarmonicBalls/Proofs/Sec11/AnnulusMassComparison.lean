import HarmonicBalls.Proofs.Sec11.IntegerAnnulusOuter
import HarmonicBalls.Steps.Sec11.IntegerRadiusCluster
import HarmonicBalls.Draft.Section11

/-!
# The annulus mass comparison

The proof uses the Section 5 existence and uniqueness statements, the unit
comparison statements from Section 6, integer-radius boundary nullity and
volume growth. The affine invariance and coordinate-change assumptions are
staged in `HarmonicBalls.Proposed.LQG` and remain pending source review.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Section6

universe u

/-- Lemma 11.6 from the Section 5 existence and uniqueness statements,
Lemmas 6.8 and 6.10, integer-radius boundary nullity, and volume growth. -/
theorem annulusMassBoundByHarmonicChainStmt_of_integerBounds
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h68 : AnnulusMassBoundByOdometerStmt.{u})
    (h610 : OdometerBoundByAnnulusMassStmt.{u})
    (hnull : ClusterBoundaryNullIntegerRadii.{u})
    (hexist : ExistenceHarmonicBallsStmt.{u})
    (hunique : UniquenessHarmonicBallsStmt.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) :
    AnnulusMassBoundByHarmonicChainStmt.{u} := by
  obtain ⟨C₁, hC₁, hmass⟩ := integer_annulus_mass_bound_of_scaledField_original hI2 h68 hAff hCC
  obtain ⟨C₂, hC₂, houter⟩ := integer_annulus_odometer_bound_of_scaledField_original h610 hAff hCC
  refine ⟨C₁ * C₂, mul_pos hC₁ hC₂, ?_⟩
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ Λ hΛ
  obtain ⟨βminus, βplus, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  classical
  let Λhat : Ω → ℂ → ℝ → Set ℂ := fun ω z =>
    if h : ∃ A : ℝ → Set ℂ, IsRegularizedClusterFamily (μ ω) A z then Classical.choose h
    else fun _ => ∅
  have he : ∀ᵐ ω ∂P, ∀ z : ℂ, IsRegularizedClusterFamily (μ ω) (Λhat ω z) z := by
    filter_upwards [hexist γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hω
    intro z
    have h := hω z
    simp only [Λhat, dite_eq_left h]
    exact Classical.choose_spec h
  have hu := hunique γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ Λhat he
  filter_upwards [hV, he, hu, hΛ,
    hnull γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    hmass γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    houter γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hV he hu hΛ hnull hmass houter
  intro t ht r hr z havoid hbad
  have heq : Λ ω t = Λhat ω 0 t := hu 0 (Λ ω) hΛ ht
  have hbad' : (annulus z (4 * r) (5 * r) ∩ (Λhat ω 0 t)ᶜ).Nonempty := by
    simpa only [← heq] using hbad
  have hm := (he 0).annulus_mass_le_of_integer_comparison_bounds ht hV.1 hV.2
    (fun n hn hcompact => by
      have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
      exact hnull n hn t ht 0 (mem_ball_self hnreal) hcompact)
    z hr havoid hbad' (ENNReal.ofReal C₁) (ENNReal.ofReal C₂)
    (fun n hn hclosed => by
      have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
      apply hmass n hn 0 (mem_ball_self hnreal) t ht r hr z
      intro x hx
      apply hclosed
      apply (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith : 4 * r ≤ 6 * r)))
      exact hx.1)
    (fun n hn hclosed hbadn => by
      have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
      apply houter n hn 0 (mem_ball_self hnreal) t ht r hr z ?_ hbadn
      exact (sdiff_subset.trans ball_subset_closedBall).trans hclosed)
  rw [heq, ENNReal.ofReal_mul hC₁.le]
  exact hm

/-- Lemma 11.6 with integer-radius boundary nullity derived from Proposition
8.1 and pathwise cluster scaling. -/
theorem annulusMassBoundByHarmonicChainStmt_of_scaledField
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h68 : AnnulusMassBoundByOdometerStmt.{u})
    (h610 : OdometerBoundByAnnulusMassStmt.{u})
    (h8 : BoundaryMeasureZeroOfCompactClusterStmt.{u})
    (hexist : ExistenceHarmonicBallsStmt.{u})
    (hunique : UniquenessHarmonicBallsStmt.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) :
    AnnulusMassBoundByHarmonicChainStmt.{u} :=
  annulusMassBoundByHarmonicChainStmt_of_integerBounds hI2 h68 h610
    (clusterBoundaryNullIntegerRadii_of_scaledField h8 clusterPathwiseScaleStep_proved hAff hCC)
    hexist hunique hAff hCC

end HarmonicBalls
