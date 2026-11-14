import HarmonicBalls.FirstPass.Phase2.WeylExponentOfWeakMetric
import LatticeProb.Probability.WeakLQGMetricExponent

/-!
# The Weyl exponent identification from the comparison of scales and point-to-point tightness

`HarmonicBalls/FirstPass/Phase2/WeylExponentOfWeakMetric.lean` derives the forall-`ξ` forms of
Lemma 11.13, Proposition 11.11 and Theorem 1.2 from one input `hexp`: every weak LQG metric with
parameter `ξ` and exponent `Q` has `Q = Q(ξ)`, the LFPP distance exponent `distExp 2 ξ`.

The Lattice-Probability theorem
`LQGMetric.HeatCircle.distExp_eq_of_isWeakLQGMetric_of_pointTight` proves exactly `hexp` from
* `hPL`: Pfeffer's Proposition 1.9 in the form `SupercriticalLQGUniqueness.B2.Iface.PLThm19`
  (arXiv:2104.04020, p. 7: for a weak LQG metric whose scaling constants are `c_r`, and `Q` the
  LFPP distance exponent, `c_r` is comparable to `r ^ (ξ Q)` uniformly in `r`);
* `hR1`: the point-to-point tightness of Ding-Gwynne (Section 4): for every LFPP exponent and
  every choice of LFPP normalizers, the renormalized LFPP crossing lengths between two distinct
  points of a connected open set are tight in both directions.

The theorems below restate the four consequences of `hexp` with `hexp` supplied, so that the
forall-`ξ` rows take `hPL` and `hR1` instead of `hexp`.

## Main statements

* `HarmonicBalls.xi_eq_xiGamma_of_plThm19_pointTight`: every γ-LQG metric has `ξ = γ / d_γ`.
* `HarmonicBalls.correctedLemma11_13_of_plThm19_pointTight`,
  `HarmonicBalls.firstPass_11_11_of_plThm19_pointTight`,
  `HarmonicBalls.firstPass_1_2_of_plThm19_pointTight`: the forall-`ξ` rows.
-/

open MeasureTheory

namespace HarmonicBalls

universe u

section PointTightness

variable
  (hPL : SupercriticalLQGUniqueness.B2.Iface.PLThm19)
  (hR1 : ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, SupercriticalLQGUniqueness.IsLFPPExponent ξ Q →
    ∀ m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ),
      (∀ ε, SupercriticalLQGUniqueness.IsLFPPNormalizer ξ ε (m ε)) →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → LQGMetric.DistC),
        SupercriticalLQGUniqueness.IsNormalizedWholePlaneGFF h P →
        ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ),
          (∀ ε, SupercriticalLQGUniqueness.IsHeatSmoothing P h ε (X ε)) →
          ∀ U : TopologicalSpace.Opens ℂ, IsConnected (U : Set ℂ) →
            ∀ z w : ℂ, z ∈ U → w ∈ U → z ≠ w →
              SupercriticalLQGUniqueness.IsTwoSidedTight P (fun (ε : Set.Ioo (0 : ℝ) 1) ω =>
                ENNReal.ofReal (m ⟨ε, ε.property.1⟩ : ℝ)⁻¹ *
                  LQGMetric.DDDF.crossLenIn ξ (X ⟨ε, ε.property.1⟩ ω)
                    U {z} {w}))

include hPL hR1

/-- **Every γ-LQG metric has Weyl exponent `ξ_γ = γ / d_γ`**, given Pfeffer's Proposition 1.9
(`hPL`) and the point-to-point tightness of Ding-Gwynne (`hR1`). -/
theorem xi_eq_xiGamma_of_plThm19_pointTight :
    ∀ γ ξ : ℝ, 0 < γ → γ < 2 → ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
      ξ = LQGMetric.xiGamma γ :=
  xi_eq_xiGamma_of_weakLQGMetricExponent
    (LQGMetric.HeatCircle.distExp_eq_of_isWeakLQGMetric_of_pointTight hPL hR1)

/-- **Lemma 11.13 (corrected, every `ξ`, every universe)** from Pfeffer's Proposition 1.9 (`hPL`)
and the point-to-point tightness of Ding-Gwynne (`hR1`). -/
theorem correctedLemma11_13_of_plThm19_pointTight : CorrectedLemma11_13Stmt.{u} :=
  correctedLemma11_13_of_weakLQGMetricExponent
    (LQGMetric.HeatCircle.distExp_eq_of_isWeakLQGMetric_of_pointTight hPL hR1)

/-- **Proposition 11.11 (every `ξ`, every universe)** from Pfeffer's Proposition 1.9 (`hPL`) and
the point-to-point tightness of Ding-Gwynne (`hR1`). -/
theorem firstPass_11_11_of_plThm19_pointTight : HarmonicBallNotMetricBallStmt.{u} :=
  firstPass_11_11_of_weakLQGMetricExponent
    (LQGMetric.HeatCircle.distExp_eq_of_isWeakLQGMetric_of_pointTight hPL hR1)

/-- **Theorem 1.2 (every `ξ`, every universe)** from Pfeffer's Proposition 1.9 (`hPL`) and the
point-to-point tightness of Ding-Gwynne (`hR1`). -/
theorem firstPass_1_2_of_plThm19_pointTight : HarmonicBallNoveltyStmt.{u} :=
  firstPass_1_2_of_weakLQGMetricExponent
    (LQGMetric.HeatCircle.distExp_eq_of_isWeakLQGMetric_of_pointTight hPL hR1)

end PointTightness

end HarmonicBalls
