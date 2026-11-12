import HarmonicBalls.Proofs.GFF.DistributionMetricUniqueness
import HarmonicBalls.Proofs.GFF.LQGMetricExistence
import HarmonicBalls.Proposed.LQG
import LatticeProb.LQG.ContMetricLength2

/-! # Existence and uniqueness of the γ-LQG metric on pairing functionals

By Gwynne-Miller 2021 (*Existence and uniqueness of the Liouville quantum gravity metric for
γ ∈ (0, 2)*, arXiv:1905.00383), Theorem 1.2, p. 6 (`LQGMetric.theorem12_proved`, from Leonardo Bonanno's
LatticeProb formalization), two strong γ-LQG metrics on distributions differ by a deterministic positive
constant. A γ-LQG metric on pairing functionals with Weyl exponent `ξ = γ / d_γ` induces a strong γ-LQG
metric on distributions which, on a whole-plane GFF plus a random continuous function, almost surely
reproduces it (`DistributionMetricUniqueness.lean`); hence uniqueness transfers to pairing functionals
(`exists_pos_ae_eq_const_mul_of_isLQGMetric`). With the existence half (`exists_isLQGMetric`) this gives
`LQGMetricExistenceUniqueness`, from the general measure-theoretic fact `hgen` of
`DistributionMetricUniqueness.lean`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace HarmonicBalls

variable {γ : ℝ}

/-- **Uniqueness of the γ-LQG metric on pairing functionals** (Gwynne-Miller 2021, Theorem 1.2, p. 6):
for `γ ∈ (0, 2)`, two γ-LQG metrics `𝔇, 𝔇'` with Weyl exponent `ξ = γ / d_γ` differ by a deterministic
positive constant: almost surely `𝔇'_{h^ℂ + f} = C 𝔇_{h^ℂ + f}` for every whole-plane GFF `h^ℂ` and
random continuous function `f`. -/
theorem exists_pos_ae_eq_const_mul_of_isLQGMetric (hγ : 0 < γ) (hγ2 : γ < 2)
    {𝔇 𝔇' : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ (LQGMetric.xiGamma γ) 𝔇)
    (h𝔇' : IsLQGMetric γ (LQGMetric.xiGamma γ) 𝔇')
    (hcm : ∀ D : ℂ → ℂ → ℝ, LatticeProb.LQG.IsEuclideanLengthMetric D →
      ∃ d : LQGMetric.ContMetric, (∀ u v, d.1 (u, v) = D u v) ∧ d.IsLength)
    (hgen : ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} (X Y : Ω → (ℂ → ℝ) → ℝ),
      (∀ φ : ℂ → ℝ, IsTestFunction Set.univ φ → ∀ᵐ ω ∂P, X ω φ = Y ω φ) →
      ∀ F : ((ℂ → ℝ) → ℝ) → ℝ, Measurable[distributionMeasurableSpace] F →
        ∀ᵐ ω ∂P, F (X ω) = F (Y ω)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (f : Ω → ℂ → ℝ), IsWholePlaneGFF P hC hcirc → (∀ ω, Continuous (f ω)) →
      (∀ x, Measurable fun ω => f ω x) → ∀ᵐ ω ∂P, ∀ u v : ℂ,
        𝔇' (addFunPairing (hC ω) (f ω)) u v = C * 𝔇 (addFunPairing (hC ω) (f ω)) u v := by
  obtain ⟨C, hC0, hCeq⟩ := (LQGMetric.theorem12_proved γ hγ hγ2).2 (distributionMetric 𝔇')
    (distributionMetric 𝔇) (isStrongLQGMetric_distributionMetric h𝔇' hcm)
    (isStrongLQGMetric_distributionMetric h𝔇 hcm)
  refine ⟨C, hC0, fun Ω _ P hC hcirc f hh hf hm => ?_⟩
  have := hh.isProbabilityMeasure
  filter_upwards [hCeq P _ (hh.isGFFPlusCont_and_ae_pairingDistribution f hf hm).1,
    hh.ae_distributionMetric_shiftedReconstructedGFF h𝔇 hcm hgen f hf hm,
    hh.ae_distributionMetric_shiftedReconstructedGFF h𝔇' hcm hgen f hf hm] with ω h1 h2 h3 u v
  rw [← h2 u v, ← h3 u v]
  exact h1 u v

/-- **Existence and uniqueness of the γ-LQG metric** on pairing functionals (Gwynne-Miller 2021,
Theorem 1.2, p. 6), with Weyl exponent `ξ = γ / d_γ`, from the general measure-theoretic fact `hgen`
(the hypothesis `hcm` of `DistributionMetricUniqueness.lean` is supplied by
`LatticeProb.LQG.exists_contMetric_of_isEuclideanLengthMetric`). -/
theorem lqgMetricExistenceUniqueness_of_ae_eq
    (hgen : ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} (X Y : Ω → (ℂ → ℝ) → ℝ),
      (∀ φ : ℂ → ℝ, IsTestFunction Set.univ φ → ∀ᵐ ω ∂P, X ω φ = Y ω φ) →
      ∀ F : ((ℂ → ℝ) → ℝ) → ℝ, Measurable[distributionMeasurableSpace] F →
        ∀ᵐ ω ∂P, F (X ω) = F (Y ω)) :
    LQGMetricExistenceUniqueness := by
  intro γ hγ hγ2
  obtain ⟨hξ, 𝔇, h𝔇⟩ := exists_isLQGMetric hγ hγ2
  exact ⟨LQGMetric.xiGamma γ, hξ, ⟨𝔇, h𝔇⟩, fun _ _ h h' =>
    exists_pos_ae_eq_const_mul_of_isLQGMetric hγ hγ2 h h'
      (fun _ hD => LatticeProb.LQG.exists_contMetric_of_isEuclideanLengthMetric hD) hgen⟩

end HarmonicBalls
