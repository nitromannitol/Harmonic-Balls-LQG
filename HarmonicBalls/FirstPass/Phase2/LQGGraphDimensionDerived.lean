import HarmonicBalls.Proposed.LQGDimension
import HarmonicBalls.FirstPass.Phase2.LiouvilleGraphDistanceDZZ
import HarmonicBalls.FirstPass.LPBridge.M1
import HarmonicBalls.FirstPass.LPBridge.M4
import HarmonicBalls.Proofs.GFF.CoordinateModification
import LatticeProb.LQG.LGDExponentZeroOne
import LatticeProb.Bonanno.LQGMetric.Papers.DG.L3_1C3
import LatticeProb.Bonanno.LQGMetric.Papers.DG.XiQBound
import LatticeProb.Bonanno.LQGMetric.Field.GFFInvariance
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg

/-!
# The Liouville graph-distance dimension of the whole-plane GFF

This file proves `WholePlaneLQGGraphDimension` (Ding--Gwynne, arXiv:1807.01072v3, Theorem 1.4,
equation (1.8), with the positivity of Theorem 1.1): for `0 < γ < 2` there is one positive
dimension `d` such that, for every normalized whole-plane GFF on any probability space and its
`γ`-LQG measure `μ`, almost surely the Liouville graph distance of `μ` between `0` and `1` has
dimension `d`. The dimension is `d_γ = 2 / χ`, where `χ = chiDZZ γ` is the Ding--Zeitouni--Zhang
graph-distance exponent.

## Route

* The model: the white noise on `ℕ → ℝ` and its whole-plane GFF `h₀`
  (`LQGMetric.DG.exists_wn_wholePlaneGFF`), normalized to `h₁ = h₀ - (h₀)_1(0)`; the normalized
  field supplies a whole-plane GFF `(hC₀, hcirc₀)` in the sense of this project whose circle
  averages are almost surely those of `h₁` (`normalizedGFF_exists_projectGFF`), that is, those of
  `h₀` minus `(h₀)_1(0)`.
* The exponent: `LatticeProb.LQG.ae_tendsto_lgdRatio_zero_one_of_model`, fed with this model,
  gives `log D_δ(μ)(0, 1) / log δ⁻¹ → χ` almost surely for every whole-plane GFF and its LQG
  measure, through the bridges `LPBridge.isWholePlaneGFF_iff` and
  `LPBridge.isLQGMeasureOfField_iff`.
* The dimension: `isLiouvilleGraphDimension_of_tendsto_lgdDZZ` turns the exponent `χ > 0` into
  the graph-distance dimension `2 / χ`.

## Main results

* `HarmonicBalls.normalizedModel_circleAvg`: the normalized model.
* `HarmonicBalls.wholePlaneLQGGraphDimension_derived`: `WholePlaneLQGGraphDimension`.
-/

open MeasureTheory Filter Topology

namespace HarmonicBalls

/-- **A normalized whole-plane GFF model carried by white noise.** On the coordinate space
`ℕ → ℝ` with its standard Gaussian product measure there are a white noise `W`, the whole-plane
GFF `h₀` it determines, and a whole-plane GFF `(hC₀, hcirc₀)` whose circle averages are, for each
radius and centre, almost surely those of `h₀ - (h₀)_1(0)`. -/
theorem normalizedModel_circleAvg :
    ∃ (W : LQGMetric.WhiteNoise.WNSpace → (ℕ → ℝ) → ℝ) (h₀ : (ℕ → ℝ) → LQGMetric.DistC)
      (hC₀ : (ℕ → ℝ) → (ℂ → ℝ) → ℝ) (hcirc₀ : (ℕ → ℝ) → ℝ → ℂ → ℝ),
      LQGMetric.WhiteNoise.IsWhiteNoise LQGDimension.ExistAsm.stdP W ∧
      LQGMetric.IsWholePlaneGFF h₀ LQGDimension.ExistAsm.stdP ∧
      (∀ φ : LQGMetric.TestC, (fun ω => h₀ ω φ) =ᵐ[LQGDimension.ExistAsm.stdP]
        W (LQGMetric.GFFExist.testL2 φ)) ∧
      LatticeProb.Gauss.IsWholePlaneGFF LQGDimension.ExistAsm.stdP hC₀ hcirc₀ ∧
      ∀ r : ℝ, 0 < r → ∀ z : ℂ, (fun ω => hcirc₀ ω r z)
        =ᵐ[LQGDimension.ExistAsm.stdP]
          fun ω => LQGMetric.circleAvg (h₀ ω) r z - LQGMetric.circleAvg (h₀ ω) 1 0 := by
  obtain ⟨W, h₀, hW, hh₀, hae⟩ := LQGMetric.DG.exists_wn_wholePlaneGFF
  have := hW.isProbabilityMeasure
  let a : (ℕ → ℝ) → ℝ := fun ω => LQGMetric.circleAvg (h₀ ω) 1 0
  have ham : Measurable a := (LQGMetric.measurable_circleAvg_left 1 0).comp hh₀.measurable
  have h1 : LQGMetric.IsWholePlaneGFF (fun ω => LQGMetric.addConst (h₀ ω) (-a ω))
      LQGDimension.ExistAsm.stdP :=
    hh₀.addConst ham.neg
  have h2 : LQGMetric.IsNormalizedWPGFF (fun ω => LQGMetric.addConst (h₀ ω) (-a ω))
      LQGDimension.ExistAsm.stdP := by
    refine ⟨h1, ?_⟩
    filter_upwards [LQGMetric.CircleAvg.ae_circleAvg_addConst_one_zero hh₀] with ω hω
    rw [hω]
    exact add_neg_cancel _
  obtain ⟨hC₀, hcirc₀, hGFF, -, hcirc⟩ := normalizedGFF_exists_projectGFF h2
  refine ⟨W, h₀, hC₀, hcirc₀, hW, hh₀, hae, (LPBridge.isWholePlaneGFF_iff _ _ _).1 hGFF, ?_⟩
  intro r hr z
  filter_upwards [hcirc r hr z, LQGMetric.CircleAvg.ae_circleAvg_addConst hh₀ z hr,
    LQGMetric.CircleAvg.ae_circleAvg_addConst_one_zero hh₀] with ω hω hrz h10
  rw [hω, LQGMetric.CircleAvg.cInc, hrz, h10]
  ring

/-- **The Liouville graph-distance dimension of the whole-plane GFF** (Ding--Gwynne,
arXiv:1807.01072v3, Theorem 1.4 and Theorem 1.1): for `0 < γ < 2`, the dimension
`d_γ = 2 / χ`, with `χ = chiDZZ γ` the Ding--Zeitouni--Zhang exponent, characterizes the Liouville
graph distance between `0` and `1` almost surely, for every normalized whole-plane GFF and its
`γ`-LQG measure. -/
theorem wholePlaneLQGGraphDimension_derived : WholePlaneLQGGraphDimension := by
  intro γ hγ hγ2
  obtain ⟨W, h₀, hC₀, hcirc₀, hW, hh₀, hae, hG₀, hcirc₀_eq⟩ := normalizedModel_circleAvg
  have := hW.isProbabilityMeasure
  have hχ : 0 < LQGMetric.chiDZZ γ := LQGMetric.DG.chiDZZ_pos γ
  refine ⟨2 / LQGMetric.chiDZZ γ, div_pos two_pos hχ, ?_⟩
  intro Ω _ P _ hC hcirc μ hG hμ
  have hlim := LatticeProb.LQG.ae_tendsto_lgdRatio_zero_one_of_model hW hh₀ hh₀.measurable hae
    hG₀ hcirc₀_eq ((LPBridge.isWholePlaneGFF_iff P hC hcirc).1 hG) hγ hγ2
    ((LPBridge.isLQGMeasureOfField_iff P γ 0 hcirc μ).1 hμ)
  filter_upwards [hlim] with ω hω
  exact isLiouvilleGraphDimension_of_tendsto_lgdDZZ hχ hω

end HarmonicBalls
