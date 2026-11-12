import HarmonicBalls.Proofs.GFF.DistMetricPairingAxioms
import LatticeProb.Bonanno.LQGMetric.Assembly.MainFinal
import LatticeProb.Bonanno.LQGMetric.Papers.DG.XiQBound

/-! # Existence of a γ-LQG metric on pairing functionals

A γ-LQG metric `D` on distributions in the sense of Gwynne-Miller 2021 (Section 1.2, p. 6;
`LQGMetric.IsStrongLQGMetric`) induces the map `pairingMetric D` on pairing functionals. It is
measurable in the pairings (`measurable_pairingMetric_apply`) and satisfies axioms I-IV for every
whole-plane GFF plus a random continuous function (`satisfiesLQGMetricAxioms_pairingMetric`), so it is
a γ-LQG metric with Weyl exponent `ξ = γ / d_γ` in the sense of `IsLQGMetric`.

By Gwynne-Miller 2021, Theorem 1.2 (p. 6) (`LQGMetric.theorem12_proved`), a strong γ-LQG metric on
distributions exists for `γ ∈ (0, 2)`; hence so does a γ-LQG metric on pairing functionals with Weyl
exponent `ξ = γ / d_γ > 0`. This is the existence half of `LQGMetricExistenceUniqueness`. -/

noncomputable section
open MeasureTheory
namespace HarmonicBalls

/-- The metric induced on pairing functionals by a γ-LQG metric on distributions is a γ-LQG metric
with Weyl exponent `ξ = γ / d_γ`. -/
theorem isLQGMetric_pairingMetric {γ : ℝ} {D : LQGMetric.DistC → LQGMetric.ContMetric}
    (hD : LQGMetric.IsStrongLQGMetric γ D) :
    IsLQGMetric γ (LQGMetric.xiGamma γ) (pairingMetric D) where
  measurable_apply := measurable_pairingMetric_apply hD.measurable
  satisfiesLQGMetricAxioms _ _ _ _ _ f hh hf hm :=
    hh.satisfiesLQGMetricAxioms_pairingMetric hD f hf hm

/-- **Existence of the γ-LQG metric** (Gwynne-Miller 2021, Theorem 1.2, p. 6): for `γ ∈ (0, 2)` the
Weyl exponent `ξ = γ / d_γ` is positive and there is a γ-LQG metric with Weyl exponent `ξ`. -/
theorem exists_isLQGMetric {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    0 < LQGMetric.xiGamma γ ∧
      ∃ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ (LQGMetric.xiGamma γ) 𝔇 := by
  obtain ⟨⟨D, hD, -⟩, -⟩ := LQGMetric.theorem12_proved γ hγ hγ2
  exact ⟨LQGMetric.DG.xiGamma_pos hγ, pairingMetric D, isLQGMetric_pairingMetric hD⟩

end HarmonicBalls
