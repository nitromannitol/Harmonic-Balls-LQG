import HarmonicBalls.Proofs.GFF.DistMetricPairingPullback
import HarmonicBalls.FirstPass.LPBridge.M5a
import LatticeProb.LQG.ContMetricLength
import LatticeProb.Bonanno.LQGMetric.Statement.LQGMetric
import LatticeProb.Gauss.DistributionOfPairing

/-! # Axiom II for the metric induced on pairing functionals

Let `D` be a γ-LQG metric on distributions in the sense of Gwynne-Miller 2021 (Section 1.2, p. 6;
`LQGMetric.IsStrongLQGMetric`) and `pairingMetric D` the induced map on pairing functionals. For a
whole-plane GFF `h^ℂ` plus a random continuous function `f`, axiom II (locality) of `D` gives a
measurable `F` with `D_H(·, ·; U) = F (H|_U)` almost surely, `H` the distribution-valued version of
`h^ℂ + f`. Almost surely `H|_U` is the decoding on `U` of the pairings of `h^ℂ + f` with the test
functions supported in `U`, which is measurable for `σ(h|_U)`; so `ω ↦ F (decoding on U)` witnesses
the locality axiom of `SatisfiesLQGMetricAxioms` for `pairingMetric D`. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace HarmonicBalls

/-- For a whole-plane GFF plus a random continuous function, the restriction to an open set `U` of
the distribution-valued version is almost surely the decoding on `U` of the raw pairings. -/
theorem IsWholePlaneGFF.ae_distOnOfPairing_eq_restrictTo
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (f : Ω → ℂ → ℝ) (hf : ∀ ω, Continuous (f ω))
    (U : TopologicalSpace.Opens ℂ) :
    ∀ᵐ ω ∂P, LatticeProb.Gauss.distOnOfPairing U (addFunPairing (hC ω) (f ω)) =
      LQGMetric.restrictTo U (shiftedReconstructedGFF hC f hf ω) := by
  refine LatticeProb.Gauss.ae_distOnOfPairing_eq fun φ => ?_
  let ψ : LQGMetric.TestC := TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := U) (Ω₂ := ⊤) φ
  have hψ : (ψ : ℂ → ℝ) = φ := by
    ext x
    simp only [TestFunction.monoCLM_apply, le_top, and_self, ↓reduceIte, ψ]
  filter_upwards [hh.ae_shiftedReconstructedGFF_apply f hf ψ] with ω hω
  change addFunPairing (hC ω) (f ω) φ = shiftedReconstructedGFF hC f hf ω ψ
  rw [hω, hψ]

/-- Axiom II (locality) for the induced metric of a whole-plane GFF plus a random continuous
function, from axiom II of a γ-LQG metric on distributions. -/
theorem IsWholePlaneGFF.locality_pairingMetric
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ} {D : LQGMetric.DistC → LQGMetric.ContMetric}
    (hD : LQGMetric.IsStrongLQGMetric γ D)
    (f : Ω → ℂ → ℝ) (hf : ∀ ω, Continuous (f ω)) (hm : ∀ z, Measurable fun ω => f ω z) :
    ∀ U : Set ℂ, IsOpen U → ∃ G : Ω → ℂ → ℂ → ℝ≥0∞,
      (∀ z w, Measurable[pairingSigmaAlgebra (fun ω => addFunPairing (hC ω) (f ω)) U]
        fun ω => G ω z w) ∧
      ∀ᵐ ω ∂P, ∀ z ∈ U, ∀ w ∈ U,
        internalMetric (pairingMetric D (addFunPairing (hC ω) (f ω))) U z w = G ω z w := by
  intro U hU
  have := hh.isProbabilityMeasure
  obtain ⟨hH, hae⟩ := hh.isGFFPlusCont_and_ae_pairingDistribution f hf hm
  obtain ⟨F, hF, hloc⟩ := hD.locality P _ hH ⟨U, hU⟩
  refine ⟨fun ω => F (LatticeProb.Gauss.distOnOfPairing ⟨U, hU⟩ (addFunPairing (hC ω) (f ω))),
    fun z w => ?_, ?_⟩
  · exact (measurable_pi_apply w).comp ((measurable_pi_apply z).comp
      (hF.comp (LatticeProb.Gauss.measurable_distOnOfPairing_pairingSigmaAlgebra
        (fun ω => addFunPairing (hC ω) (f ω)) ⟨U, hU⟩)))
  · filter_upwards [hae, hloc, hh.ae_distOnOfPairing_eq_restrictTo f hf ⟨U, hU⟩]
      with ω hω hl hr z hz w hw
    have he : pairingMetric D (addFunPairing (hC ω) (f ω)) =
        fun u v => (D (shiftedReconstructedGFF hC f hf ω)).1 (u, v) := by
      funext u v
      rw [pairingMetric, hω]
    rw [he, LPBridge.internalMetric_eq, LatticeProb.LQG.internalMetric_contMetric, hr]
    exact hl z hz w hw

end HarmonicBalls
