import HarmonicBalls.Proofs.GFF.DistMetricPairingWeyl
import HarmonicBalls.FirstPass.LPBridge.M5a
import LatticeProb.LQG.ContMetricWeyl
import LatticeProb.Bonanno.LQGMetric.Statement.LQGMetric

/-! # Axiom III for the metric induced on pairing functionals

Let `D` be a γ-LQG metric on distributions in the sense of Gwynne-Miller 2021 (Section 1.2, p. 6;
`LQGMetric.IsStrongLQGMetric`) and `pairingMetric D` the induced map on pairing functionals. For a
whole-plane GFF `h^ℂ` plus a random continuous function `f`, write `H` for the distribution-valued
version of `h^ℂ + f`. Almost surely, simultaneously for every continuous `g`:

* the induced metric of `h^ℂ + f + g` is `D_{H + g}` (`ae_pairingMetric_addFunPairing_addFun`);
* axiom III (Weyl scaling) of `D` gives `D_{H + g} = e^{ξ g} · D_H` with `ξ = γ / d_γ`;
* the induced metric of `h^ℂ + f` is `D_H` (`ae_pairingMetric_addFunPairing`);
* the Weyl scaling of the continuous metric `D_H` by `g` is the Weyl scaling of the real function
  `(u, v) ↦ D_H(u, v)` (`LatticeProb.LQG.weylScaling_contMetric`).

Together these give axiom III of `SatisfiesLQGMetricAxioms` for `pairingMetric D`. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace HarmonicBalls

/-- Axiom III (Weyl scaling) for the induced metric of a whole-plane GFF plus a random continuous
function: almost surely, for every continuous `g` and all `u, v`,
`D_{h + g}(u, v) = (e^{ξ g} · D_h)(u, v)` with `ξ = γ / d_γ` and `h = h^ℂ + f`. This is the
`ae_weylScaling` field of `SatisfiesLQGMetricAxioms` for `pairingMetric D`. -/
theorem IsWholePlaneGFF.ae_weylScaling_pairingMetric
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ} {D : LQGMetric.DistC → LQGMetric.ContMetric}
    (hD : LQGMetric.IsStrongLQGMetric γ D)
    (f : Ω → ℂ → ℝ) (hf : ∀ ω, Continuous (f ω)) (hm : ∀ z, Measurable fun ω => f ω z) :
    ∀ᵐ ω ∂P, ∀ g : ℂ → ℝ, Continuous g → ∀ u v,
      ENNReal.ofReal (pairingMetric D (addFunPairing (addFunPairing (hC ω) (f ω)) g) u v) =
        weylScaling (pairingMetric D (addFunPairing (hC ω) (f ω))) (LQGMetric.xiGamma γ) g u v := by
  have := hh.isProbabilityMeasure
  obtain ⟨hH, -⟩ := hh.isGFFPlusCont_and_ae_pairingDistribution f hf hm
  filter_upwards [hh.ae_pairingMetric_addFunPairing_addFun D f hf, hD.weyl P _ hH,
    hh.ae_pairingMetric_addFunPairing D f hf] with ω h1 h2 h3 g hg u v
  have he : pairingMetric D (addFunPairing (hC ω) (f ω)) =
      fun u v => (D (shiftedReconstructedGFF hC f hf ω)).1 (u, v) :=
    funext fun u => funext fun v => h3 u v
  rw [h1 g hg u v, he, LPBridge.weylScaling_eq, ← h2 ⟨g, hg⟩ u v]
  exact (LatticeProb.LQG.weylScaling_contMetric (D (shiftedReconstructedGFF hC f hf ω))
    (LQGMetric.xiGamma γ) ⟨g, hg⟩ u v).symm

end HarmonicBalls
