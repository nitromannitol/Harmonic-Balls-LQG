import HarmonicBalls.Proofs.Sec6.MeasureEvaluation

/-!
# One-scale annulus comparison probability

A positive measurable annulus-to-ball mass ratio admits a deterministic
threshold with arbitrarily small failure probability. Equal lower-tail laws
then make the bound uniform over dyadic scales.
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal

namespace HarmonicBalls

/-- The real annulus-to-ball mass ratio at a dyadic scale. -/
noncomputable def annulusBallMassRatio (μ : Measure ℂ) (n : ℕ) (z : ℂ) : ℝ :=
  (μ (annulus z (dyadicScale (n + 1)) (dyadicScale n)) /
    μ (ball z (dyadicScale n))).toReal

/-- Almost-everywhere measurability of the two mass evaluations gives
almost-everywhere measurability of the ratio. -/
theorem aemeasurable_annulusBallMassRatio {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (μ : Ω → Measure ℂ) (n : ℕ) (z : ℂ)
    (ha : AEMeasurable (fun ω => μ ω (annulus z (dyadicScale (n + 1)) (dyadicScale n))) P)
    (hb : AEMeasurable (fun ω => μ ω (ball z (dyadicScale n))) P) :
    AEMeasurable (fun ω => annulusBallMassRatio (μ ω) n z) P := by
  exact (ha.div hb).ennreal_toReal

/-- A positive finite annulus mass and a positive finite ball mass give a
positive annulus-to-ball ratio. -/
theorem annulusBallMassRatio_pos (μ : Measure ℂ) (n : ℕ) (z : ℂ)
    (ha : μ (annulus z (dyadicScale (n + 1)) (dyadicScale n)) ≠ 0)
    (hatop : μ (annulus z (dyadicScale (n + 1)) (dyadicScale n)) ≠ ∞)
    (hb : μ (ball z (dyadicScale n)) ≠ 0)
    (hbtop : μ (ball z (dyadicScale n)) ≠ ∞) :
    0 < annulusBallMassRatio μ n z := by
  unfold annulusBallMassRatio
  exact ENNReal.toReal_pos (ENNReal.div_pos ha hbtop).ne' (ENNReal.div_ne_top hatop hb)

/-- A lower bound for the real mass ratio implies the annulus-ball
comparison when the ball mass is positive and finite. -/
theorem annulusBallComparison_of_le_massRatio (μ : Measure ℂ) (n : ℕ) (z : ℂ) (m : ℝ)
    (hb : μ (ball z (dyadicScale n)) ≠ 0)
    (hbtop : μ (ball z (dyadicScale n)) ≠ ∞)
    (hm : m ≤ annulusBallMassRatio μ n z) : AnnulusBallComparison μ n z m := by
  unfold AnnulusBallComparison
  calc
    ENNReal.ofReal m * μ (ball z (dyadicScale n)) ≤
        ENNReal.ofReal (annulusBallMassRatio μ n z) * μ (ball z (dyadicScale n)) :=
      by gcongr
    _ ≤ (μ (annulus z (dyadicScale (n + 1)) (dyadicScale n)) /
        μ (ball z (dyadicScale n))) * μ (ball z (dyadicScale n)) :=
      by
        unfold annulusBallMassRatio
        gcongr
        exact ENNReal.ofReal_toReal_le
    _ = μ (annulus z (dyadicScale (n + 1)) (dyadicScale n)) :=
      ENNReal.div_mul_cancel hb hbtop

/-- Equal lower-tail laws and a positive reference ratio yield a deterministic
comparison threshold with uniformly small failure probability. -/
theorem exists_annulusBallComparison_threshold_of_equal_lower_tails
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (μ : Ω → Measure ℂ) (z : ℂ)
    (hmeas : AEMeasurable (fun ω => annulusBallMassRatio (μ ω) 0 z) P)
    (hpos : ∀ᵐ ω ∂P, 0 < annulusBallMassRatio (μ ω) 0 z)
    (hball : ∀ n, ∀ᵐ ω ∂P, μ ω (ball z (dyadicScale n)) ≠ 0 ∧
      μ ω (ball z (dyadicScale n)) ≠ ∞)
    (hlaw : ∀ n a, P {ω | annulusBallMassRatio (μ ω) n z < a} =
      P {ω | annulusBallMassRatio (μ ω) 0 z < a})
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ m ∈ Ioo (0 : ℝ) 1, ∀ n,
      P {ω | ¬ AnnulusBallComparison (μ ω) n z m} ≤ δ := by
  obtain ⟨m, hm, hsmall⟩ :=
    Section6.exists_small_threshold_of_aemeasurable P hmeas hpos hδ
  refine ⟨m, hm, fun n => ?_⟩
  calc
    P {ω | ¬ AnnulusBallComparison (μ ω) n z m} ≤
        P {ω | annulusBallMassRatio (μ ω) n z < m} := by
      apply measure_mono_ae
      filter_upwards [hball n] with ω ⟨hb, hbtop⟩ hbad
      by_contra hnot
      exact hbad (annulusBallComparison_of_le_massRatio (μ ω) n z m hb hbtop
        (le_of_not_gt hnot))
    _ = P {ω | annulusBallMassRatio (μ ω) 0 z < m} := hlaw n m
    _ ≤ δ := hsmall

end HarmonicBalls
