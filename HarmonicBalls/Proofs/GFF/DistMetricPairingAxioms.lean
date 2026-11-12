import HarmonicBalls.Proofs.GFF.DistMetricPairingLength
import HarmonicBalls.Proofs.GFF.DistMetricPairingLocality
import HarmonicBalls.Proofs.GFF.DistMetricPairingWeylAxiom
import HarmonicBalls.Proofs.GFF.DistMetricPairingCoord

/-! # Axiom IV, and axioms I-IV, for the metric induced on pairing functionals

Let `D` be a γ-LQG metric on distributions in the sense of Gwynne-Miller 2021 (Section 1.2, p. 6;
`LQGMetric.IsStrongLQGMetric`) and `pairingMetric D` the induced map on pairing functionals. For a
whole-plane GFF `h^ℂ` plus a random continuous function `f`, write `h = h^ℂ + f` (raw pairings) and
`H` for its distribution-valued version.

Axiom IV. Fix `r > 0` and `z`. Almost surely the raw pairings of `h(r · + z)` agree with those of
`H(r · + z)` at the countably many test functions `LQGMetric.comb ⊤ c`, since their affine pullbacks
are test functions; so the distribution reconstructed from the pairings of `h(r · + z) + Q log r`
is `H(r · + z) + Q log r`, and axiom IV of `D` gives the coordinate change.

Together with axioms I (`ae_isEuclideanLengthMetric_pairingMetric`), II (`locality_pairingMetric`)
and III (`ae_weylScaling_pairingMetric`) this shows that `pairingMetric D` satisfies
`SatisfiesLQGMetricAxioms` with Weyl exponent `ξ = γ / d_γ` for every whole-plane GFF plus a random
continuous function. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace HarmonicBalls

/-- For a whole-plane GFF plus a random continuous function and fixed `r > 0`, `z`, the affine
pullback of the raw pairings agrees almost surely with the affine composition of the
distribution-valued version at all the test functions `LQGMetric.comb ⊤ c` simultaneously. -/
theorem IsWholePlaneGFF.ae_affinePullbackPairing_comb
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (f : Ω → ℂ → ℝ) (hf : ∀ ω, Continuous (f ω))
    {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ∀ᵐ ω ∂P, ∀ c : LQGMetric.CoordJ,
      affinePullbackPairing (addFunPairing (hC ω) (f ω)) r z (LQGMetric.comb ⊤ c) =
        LQGMetric.affineComp r z (shiftedReconstructedGFF hC f hf ω) (LQGMetric.comb ⊤ c) := by
  refine ae_all_iff.mpr fun c => ?_
  filter_upwards [hh.ae_shiftedReconstructedGFF_apply f hf
    (LQGMetric.testAffinePull r z (LQGMetric.comb ⊤ c))] with ω hω
  rw [← affinePullbackPairing_distributionPairingExtension_test _ hr z]
  have hfun : (fun y => (LQGMetric.comb ⊤ c : ℂ → ℝ) ((y - z) / r)) =
      ⇑(LQGMetric.testAffinePull r z (LQGMetric.comb ⊤ c)) := by
    funext y
    rw [LQGMetric.testAffinePull_apply r z hr.ne']
  simp only [affinePullbackPairing, hfun, distributionPairingExtension_test, hω]

/-- Axiom IV (coordinate change for scaling and translation) for the induced metric of a whole-plane
GFF plus a random continuous function: for `r > 0` and `z`, almost surely
`D_h(r u + z, r v + z) = D_{h(r · + z) + Q log r}(u, v)` for all `u, v`. This is the `coordChange`
field of `SatisfiesLQGMetricAxioms` for `pairingMetric D`. -/
theorem IsWholePlaneGFF.coordChange_pairingMetric
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ} {D : LQGMetric.DistC → LQGMetric.ContMetric}
    (hD : LQGMetric.IsStrongLQGMetric γ D)
    (f : Ω → ℂ → ℝ) (hf : ∀ ω, Continuous (f ω)) (hm : ∀ z, Measurable fun ω => f ω z) :
    ∀ r : ℝ, 0 < r → ∀ z : ℂ, ∀ᵐ ω ∂P, ∀ u v : ℂ,
      pairingMetric D (addFunPairing (hC ω) (f ω)) (r * u + z) (r * v + z) =
        pairingMetric D (addFunPairing (affinePullbackPairing (addFunPairing (hC ω) (f ω)) r z)
          fun _ => lqgQ γ * Real.log r) u v := by
  intro r hr z
  have := hh.isProbabilityMeasure
  obtain ⟨hH, -⟩ := hh.isGFFPlusCont_and_ae_pairingDistribution f hf hm
  filter_upwards [hh.ae_pairingMetric_addFunPairing D f hf, hD.coord P _ hH r hr z,
    hh.ae_affinePullbackPairing_comb f hf hr z] with ω h3 hc hk u v
  have he : pairingDistribution (addFunPairing
      (affinePullbackPairing (addFunPairing (hC ω) (f ω)) r z) fun _ => lqgQ γ * Real.log r) =
      LQGMetric.addConst (LQGMetric.affineComp r z (shiftedReconstructedGFF hC f hf ω))
        (LQGMetric.Q γ * Real.log r) :=
    pairingDistribution_addFunPairing_of_comb _ _ hk (ContinuousMap.const ℂ _)
  rw [h3, hc u v, pairingMetric, he]

/-- A γ-LQG metric on distributions (Gwynne-Miller 2021, Section 1.2, p. 6) induces on pairing
functionals a map satisfying axioms I-IV (`SatisfiesLQGMetricAxioms`), with Weyl exponent
`ξ = γ / d_γ`, for every whole-plane GFF plus a random continuous function. -/
theorem IsWholePlaneGFF.satisfiesLQGMetricAxioms_pairingMetric
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ} {D : LQGMetric.DistC → LQGMetric.ContMetric}
    (hD : LQGMetric.IsStrongLQGMetric γ D)
    (f : Ω → ℂ → ℝ) (hf : ∀ ω, Continuous (f ω)) (hm : ∀ z, Measurable fun ω => f ω z) :
    SatisfiesLQGMetricAxioms P γ (LQGMetric.xiGamma γ) (pairingMetric D)
      fun ω => addFunPairing (hC ω) (f ω) where
  ae_isEuclideanLengthMetric := hh.ae_isEuclideanLengthMetric_pairingMetric hD f hf hm
  locality := hh.locality_pairingMetric hD f hf hm
  ae_weylScaling := hh.ae_weylScaling_pairingMetric hD f hf hm
  coordChange := hh.coordChange_pairingMetric hD f hf hm

end HarmonicBalls
