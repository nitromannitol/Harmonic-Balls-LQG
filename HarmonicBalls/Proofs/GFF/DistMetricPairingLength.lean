import HarmonicBalls.Proofs.GFF.DistMetricPairingPullback
import HarmonicBalls.FirstPass.LPBridge.M5a
import LatticeProb.LQG.ContMetricLength
import LatticeProb.Bonanno.LQGMetric.Statement.LQGMetric

/-! # Axiom I for the metric induced on pairing functionals

Let `D` be a γ-LQG metric on distributions in the sense of Gwynne-Miller 2021 (Section 1.2, p. 6;
`LQGMetric.IsStrongLQGMetric`), and let `pairingMetric D` be the induced map on pairing functionals
(the metric of the distribution reconstructed from the pairings). For a whole-plane GFF `h^ℂ` plus a
random continuous function `f`, the induced metric of `h^ℂ + f` is almost surely a length metric
inducing the Euclidean topology (axiom I of `SatisfiesLQGMetricAxioms`): almost surely it is the
metric of the distribution-valued version of `h^ℂ + f`, a continuous length metric by axiom I of `D`,
and a continuous length metric is a Euclidean length metric. -/

noncomputable section
open MeasureTheory
namespace HarmonicBalls

/-- If the distribution reconstructed from a pairing functional `T` is `S` and `D S` is a length
metric, then the induced metric of `T` is a length metric inducing the Euclidean topology. -/
theorem isEuclideanLengthMetric_pairingMetric_of_eq
    (D : LQGMetric.DistC → LQGMetric.ContMetric) (T : (ℂ → ℝ) → ℝ) (S : LQGMetric.DistC)
    (hT : pairingDistribution T = S) (hS : (D S).IsLength) :
    IsEuclideanLengthMetric (pairingMetric D T) := by
  have he : pairingMetric D T = fun u v => (D S).1 (u, v) := by
    funext u v
    rw [pairingMetric, hT]
  rw [he]
  exact (LPBridge.isEuclideanLengthMetric_iff _).2
    (LatticeProb.LQG.isEuclideanLengthMetric_of_isLength _ hS)

/-- Axiom I (Euclidean topology and length metric) for the induced metric of a whole-plane GFF plus
a random continuous function, from axiom I of a γ-LQG metric on distributions. -/
theorem IsWholePlaneGFF.ae_isEuclideanLengthMetric_pairingMetric
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ} {D : LQGMetric.DistC → LQGMetric.ContMetric}
    (hD : LQGMetric.IsStrongLQGMetric γ D)
    (f : Ω → ℂ → ℝ) (hf : ∀ ω, Continuous (f ω)) (hm : ∀ z, Measurable fun ω => f ω z) :
    ∀ᵐ ω ∂P, IsEuclideanLengthMetric (pairingMetric D (addFunPairing (hC ω) (f ω))) := by
  have := hh.isProbabilityMeasure
  obtain ⟨hH, hae⟩ := hh.isGFFPlusCont_and_ae_pairingDistribution f hf hm
  filter_upwards [hae, hD.length P _ hH] with ω hω hlen
  exact isEuclideanLengthMetric_pairingMetric_of_eq D _ _ hω hlen

end HarmonicBalls
