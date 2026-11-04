import HarmonicBalls.Proofs.Sec9.MassOrderedBalls

/-! # Mass distance between subharmonic balls

For same-centre balls inside the unit disc, the measure of their symmetric
difference is exactly the distance between their masses in the measure algebra.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped symmDiff

/-- If the first measurable set is contained in the second almost everywhere,
their symmetric difference has measure equal to their mass gap. -/
theorem measure_symmDiff_of_ae_subset {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAfin : μ A ≠ ⊤) (hnull : μ (A \ B) = 0) :
    μ (A ∆ B) = μ B - μ A := by
  have hinter : μ (B ∩ A) = μ A := by
    have hsplit := measure_sdiff_add_inter (μ := μ) A hB
    rw [hnull, zero_add, inter_comm] at hsplit
    exact hsplit
  have hdiff : μ (B \ A) = μ B - μ A := by
    apply ENNReal.eq_sub_of_add_eq hAfin
    rw [← hinter]
    exact measure_sdiff_add_inter B hA
  rw [measure_symmDiff_eq hA.nullMeasurableSet hB.nullMeasurableSet, hnull, zero_add, hdiff]

universe u

/-- Almost surely, same-centre subharmonic balls compactly contained in the
unit disc have symmetric-difference mass equal to the gap between their
masses. This holds simultaneously for all such balls and centres. -/
theorem ae_subharmonicBall_symmDiff_mass_inside_unit_disc
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (A B : Set ℂ) (z : ℂ),
      closure A ⊆ ball 0 1 → closure B ⊆ ball 0 1 →
      IsSubharmonicBall (μ ω) A z → IsSubharmonicBall (μ ω) B z →
      μ ω (A ∆ B) = (μ ω A - μ ω B) + (μ ω B - μ ω A) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_subharmonicBall_order_inside_unit_disc hI2 h82
    γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω horder
  intro A B z hAcl hBcl hA hB
  rcases le_total (μ ω A) (μ ω B) with hmass | hmass
  · have hnull := (horder A B z hAcl hBcl hA hB hmass).2.2.1
    have hdiff := measure_symmDiff_of_ae_subset (μ ω) hA.1.measurableSet
      hB.1.measurableSet (ne_of_lt hA.2.2.2.1) hnull
    simpa only [tsub_eq_zero_of_le hmass, zero_add] using hdiff
  · have hnull := (horder B A z hBcl hAcl hB hA hmass).2.2.1
    have hdiff := measure_symmDiff_of_ae_subset (μ ω) hB.1.measurableSet
      hA.1.measurableSet (ne_of_lt hB.2.2.2.1) hnull
    rw [symmDiff_comm] at hdiff
    simpa only [tsub_eq_zero_of_le hmass, add_zero] using hdiff

/-- The same mass-distance identity for all bounded same-centre subharmonic
balls, using the staged affine-invariance and coordinate-change inputs. -/
theorem ae_bounded_subharmonicBall_symmDiff_mass
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (A B : Set ℂ) (z : ℂ), Bornology.IsBounded A → Bornology.IsBounded B →
      IsSubharmonicBall (μ ω) A z → IsSubharmonicBall (μ ω) B z →
      μ ω (A ∆ B) = (μ ω A - μ ω B) + (μ ω B - μ ω A) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_bounded_subharmonicBall_order_of_weak_uniqueness hI2
      (subharmonicBallUniquenessWeak_of_volumeGrowth_and_typical_scales hI2 h82 hAff hCC)
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    ae_bounded_subharmonicBall_restrict_eq_of_volumeGrowth hI2 h82 hAff hCC
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω horder hfront
  intro A B z hAb hBb hA hB
  have hnull : ∀ (D E : Set ℂ), Bornology.IsBounded D → Bornology.IsBounded E →
      IsSubharmonicBall (μ ω) D z → IsSubharmonicBall (μ ω) E z → μ ω D ≤ μ ω E →
      μ ω (D \ E) = 0 := by
    intro D E hDb hEb hD hE hmass
    have hDE := (horder D E z hDb hEb hD hE hmass).1
    have hzero := (hfront E E z hEb hEb hE hE rfl).1
    apply measure_mono_null _ hzero
    rw [hE.1.frontier_eq]
    intro x hx
    exact ⟨interior_subset (hDE hx.1), hx.2⟩
  rcases le_total (μ ω A) (μ ω B) with hmass | hmass
  · have hdiff := measure_symmDiff_of_ae_subset (μ ω) hA.1.measurableSet
      hB.1.measurableSet (ne_of_lt hA.2.2.2.1) (hnull A B hAb hBb hA hB hmass)
    simpa only [tsub_eq_zero_of_le hmass, zero_add] using hdiff
  · have hdiff := measure_symmDiff_of_ae_subset (μ ω) hB.1.measurableSet
      hA.1.measurableSet (ne_of_lt hB.2.2.2.1) (hnull B A hBb hAb hB hA hmass)
    rw [symmDiff_comm] at hdiff
    simpa only [tsub_eq_zero_of_le hmass, add_zero] using hdiff

end HarmonicBalls
