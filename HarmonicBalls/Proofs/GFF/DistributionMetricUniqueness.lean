import HarmonicBalls.Proofs.GFF.DistributionMetricAxioms
import HarmonicBalls.Proofs.GFF.MetricAnnulusScaleLaw

/-! # The γ-LQG metric on distributions induced by a γ-LQG metric on pairing functionals

The space of distributions, the continuous metrics and the strong γ-LQG metrics used here are from
Leonardo Bonanno's LatticeProb formalization.

A γ-LQG metric `𝔇` on pairing functionals with Weyl exponent `ξ = γ / d_γ` (`IsLQGMetric`) induces the
metric assignment `distributionMetric 𝔇` on distributions, which satisfies the axioms I-IV of
Gwynne-Miller 2021 (*Existence and uniqueness of the Liouville quantum gravity metric for γ ∈ (0, 2)*,
arXiv:1905.00383), Section 1.2, p. 6 (`DistributionMetricAxioms.lean`); it is therefore a strong γ-LQG
metric (`isStrongLQGMetric_distributionMetric`). For a whole-plane GFF `h^ℂ` plus a random continuous
function `f`, the induced metric of the distribution-valued version of `h^ℂ + f` is almost surely the
metric `𝔇` of the pairing functional of `h^ℂ + f`, at all pairs of points
(`IsWholePlaneGFF.ae_distributionMetric_shiftedReconstructedGFF`). This is what transfers the uniqueness
of strong γ-LQG metrics (Gwynne-Miller 2021, Theorem 1.2) to pairing functionals.

Two general facts enter as hypotheses: `hcm`, every Euclidean length metric is a continuous length
metric in the sense of `LQGMetric.ContMetric`, and `hgen`, two random pairing functionals that agree
almost surely at each test function agree almost surely at every function measurable for the σ-algebra
of test-function pairings.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace HarmonicBalls

variable {γ : ℝ}

/-- The metric assignment on distributions induced by a γ-LQG metric on pairing functionals with Weyl
exponent `ξ = γ / d_γ` is a strong γ-LQG metric in the sense of Gwynne-Miller 2021, Section 1.2. -/
theorem isStrongLQGMetric_distributionMetric {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ}
    (h𝔇 : IsLQGMetric γ (LQGMetric.xiGamma γ) 𝔇)
    (hcm : ∀ D : ℂ → ℂ → ℝ, LatticeProb.LQG.IsEuclideanLengthMetric D →
      ∃ d : LQGMetric.ContMetric, (∀ u v, d.1 (u, v) = D u v) ∧ d.IsLength) :
    LQGMetric.IsStrongLQGMetric γ (distributionMetric 𝔇) where
  measurable := measurable_distributionMetric h𝔇.measurable_apply
  length := by
    intro Ω _ P _ h hh
    exact ae_isLength_distributionMetric h𝔇 hcm hh
  locality := by
    intro Ω _ P _ h hh U
    exact locality_distributionMetric h𝔇 hcm hh U
  weyl := by
    intro Ω _ P _ h hh
    exact ae_weylScale_distributionMetric h𝔇 hcm hh
  coord := by
    intro Ω _ P _ h hh r hr z
    exact ae_coord_distributionMetric h𝔇 hcm hh hr z

/-- For a whole-plane GFF `h^ℂ` plus a random continuous function `f`, almost surely the metric
assignment on distributions induced by a γ-LQG metric `𝔇` on pairing functionals, evaluated at the
distribution-valued version of `h^ℂ + f`, is `𝔇` of the pairing functional of `h^ℂ + f` at all pairs
of points. -/
theorem IsWholePlaneGFF.ae_distributionMetric_shiftedReconstructedGFF {ξ : ℝ}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hcm : ∀ D : ℂ → ℂ → ℝ, LatticeProb.LQG.IsEuclideanLengthMetric D →
      ∃ d : LQGMetric.ContMetric, (∀ u v, d.1 (u, v) = D u v) ∧ d.IsLength)
    (hgen : ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} (X Y : Ω → (ℂ → ℝ) → ℝ),
      (∀ φ : ℂ → ℝ, IsTestFunction Set.univ φ → ∀ᵐ ω ∂P, X ω φ = Y ω φ) →
      ∀ F : ((ℂ → ℝ) → ℝ) → ℝ, Measurable[distributionMeasurableSpace] F →
        ∀ᵐ ω ∂P, F (X ω) = F (Y ω))
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (f : Ω → ℂ → ℝ)
    (hf : ∀ ω, Continuous (f ω)) (hm : ∀ z, Measurable fun ω => f ω z) :
    ∀ᵐ ω ∂P, ∀ u v : ℂ, (distributionMetric 𝔇 (shiftedReconstructedGFF hC f hf ω)).1 (u, v) =
      𝔇 (addFunPairing (hC ω) (f ω)) u v := by
  have := hh.isProbabilityMeasure
  obtain ⟨hGP, -⟩ := hh.isGFFPlusCont_and_ae_pairingDistribution f hf hm
  -- a field `h^ℂ₂ + g` whose pairing functional agrees with the version at every test function
  obtain ⟨hC2, hcirc2, g, hh2, hgc, hgm, hproj⟩ := exists_projectGFF_of_isGFFPlusCont hGP
  have hA := (h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc f hh hf hm).ae_isEuclideanLengthMetric
  have hA2 := (h𝔇.satisfiesLQGMetricAxioms Ω P hC2 hcirc2 g hh2 hgc hgm).ae_isEuclideanLengthMetric
  -- the two pairing functionals agree almost surely at each test function
  have htest : ∀ φ : ℂ → ℝ, IsTestFunction Set.univ φ → ∀ᵐ ω ∂P,
      addFunPairing (hC ω) (f ω) φ = addFunPairing (hC2 ω) (g ω) φ := by
    intro φ hφ
    filter_upwards [hh.ae_shiftedReconstructedGFF_apply f hf ⟨φ, hφ.1, hφ.2.1, hφ.2.2⟩] with ω hω
    exact hω.symm.trans (hproj ω _)
  -- hence their metrics agree almost surely at each pair of points
  have hpt : ∀ p : ℂ × ℂ, ∀ᵐ ω ∂P,
      𝔇 (addFunPairing (hC ω) (f ω)) p.1 p.2 = 𝔇 (addFunPairing (hC2 ω) (g ω)) p.1 p.2 :=
    fun p => hgen (fun ω => addFunPairing (hC ω) (f ω)) (fun ω => addFunPairing (hC2 ω) (g ω))
      htest (fun T => 𝔇 T p.1 p.2) (h𝔇.measurable_apply p.1 p.2)
  -- and simultaneously on a countable dense set of pairs
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense (ℂ × ℂ)
  have : Countable S := hSc.to_subtype
  have hS : ∀ᵐ ω ∂P, ∀ p : S,
      𝔇 (addFunPairing (hC ω) (f ω)) p.1.1 p.1.2 = 𝔇 (addFunPairing (hC2 ω) (g ω)) p.1.1 p.1.2 :=
    ae_all_iff.2 fun p => hpt p
  filter_upwards [hA, hA2, hS] with ω hE hE2 hSω
  -- both metrics are continuous, so they agree at all pairs of points
  have heq : (fun p : ℂ × ℂ => 𝔇 (addFunPairing (hC ω) (f ω)) p.1 p.2) =
      fun p => 𝔇 (addFunPairing (hC2 ω) (g ω)) p.1 p.2 :=
    Continuous.ext_on hSd (isEuclideanLengthMetric_continuous hE)
      (isEuclideanLengthMetric_continuous hE2) fun p hp => hSω ⟨p, hp⟩
  obtain ⟨d, hd1, -⟩ := hcm _ hE2.toLatticeProb
  have hdist : distributionMetric 𝔇 (shiftedReconstructedGFF hC f hf ω) = d :=
    distributionMetric_eq_of_testPairing h𝔇.measurable_apply
      (H := addFunPairing (hC2 ω) (g ω)) (fun φ => hproj ω φ) fun u v => by rw [hd1]
  intro u v
  rw [hdist, hd1]
  exact (congrFun heq (u, v)).symm

end HarmonicBalls
