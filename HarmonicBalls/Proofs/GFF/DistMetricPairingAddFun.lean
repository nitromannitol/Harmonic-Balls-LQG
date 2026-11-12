import HarmonicBalls.Proofs.GFF.DistMetricPairingPullback

/-! # The distribution reconstructed from a shifted pairing functional

If a pairing functional `T` agrees with a distribution `S` on all test functions, then the distribution
reconstructed from the pairing functional of `T + f`, with `f` a continuous function, is `S + f`: the
reconstruction `pairingDistribution` only sees the pairings with test functions, and these are
`S φ + ∫ f φ`. Unlike `IsWholePlaneGFF.ae_pairingDistribution_addFunPairing`, no randomness is involved. -/

noncomputable section
open MeasureTheory
namespace HarmonicBalls

/-- The distribution reconstructed from `T + f` is `S + f` as soon as `T` pairs like `S` with every test
function. The hypothesis `hS` is needed: the reconstruction is a left inverse of the pairing map only on
its range. -/
theorem pairingDistribution_addFunPairing_of_eq (T : (ℂ → ℝ) → ℝ) (S : LQGMetric.DistC)
    (hS : ∀ φ : LQGMetric.TestC, T φ = S φ) (f : C(ℂ, ℝ)) :
    pairingDistribution (addFunPairing T f) = S + LQGMetric.ofCont f := by
  have he : testRestriction (addFunPairing T f) = fun φ => (S + LQGMetric.ofCont f) φ := by
    funext φ
    change T φ + ∫ x, f x * φ x = S φ + LQGMetric.ofCont f φ
    rw [LQGMetric.ofCont_apply, hS φ]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  rw [pairingDistribution, he, fullTestDistributionVersion_pairings]

end HarmonicBalls
