import HarmonicBalls.Proofs.Sec2.Assembly
import HarmonicBalls.Proofs.Sec3.OpenLaplacian
import HarmonicBalls.Proofs.Sec3.ClusterCompatibility

/-!
# Section 3 from the literature inputs

Lemmas 3.1, 3.2, 3.3 and 3.5 with I2 (`LQGVolumeGrowthAllScalesStmt`) discharged by
`lqgVolumeGrowthAllScalesStmt_of_literature` (Proofs/Sec2/Assembly.lean, worker c2): the results depend only on the
staged literature inputs Ding-Gwynne 2020, Lemma 3.8 (`WholePlaneLQGBallMassBounds`), the affine invariance of the
whole-plane GFF (`WholePlaneGFFAffineInvariance`) and Fact 2.1 (`LQGMeasureCoordChange`, `LQGMeasureWeylScaling`,
`LQGMeasureExistence`, `LQGMeasureNonatomic`).
-/

namespace HarmonicBalls

universe u

section FromLiterature


variable
  (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
  (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
  (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
  (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
  (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
  (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)

include hDG hAff hCC hW hE hN

/-- **Lemma 3.1** (lemma:basic-properties) from the staged literature inputs. -/
theorem leastSupersolutionMem_of_literature : LeastSupersolutionMemStmt.{u} :=
  leastSupersolutionMem_proved (lqgVolumeGrowthAllScalesStmt_of_literature hDG hAff hCC hW hE hN)

/-- **Lemma 3.2** (lemma:non-coincidence-open-harmonic) from the staged literature inputs. -/
theorem clusterOpenLaplacian_of_literature : ClusterOpenLaplacianStmt.{u} :=
  clusterOpenLaplacian_proved (lqgVolumeGrowthAllScalesStmt_of_literature hDG hAff hCC hW hE hN)

/-- **Lemma 3.3** (lemma:monotonicity) from the staged literature inputs. -/
theorem clusterMonotone_of_literature : ClusterMonotoneStmt.{u} :=
  clusterMonotone_proved (lqgVolumeGrowthAllScalesStmt_of_literature hDG hAff hCC hW hE hN)

/-- **Lemma 3.5** (lemma:cluster-compatibility) from the staged literature inputs. -/
theorem clusterCompatibility_of_literature : ClusterCompatibilityStmt.{u} :=
  clusterCompatibility_proved (lqgVolumeGrowthAllScalesStmt_of_literature hDG hAff hCC hW hE hN)

end FromLiterature

end HarmonicBalls
