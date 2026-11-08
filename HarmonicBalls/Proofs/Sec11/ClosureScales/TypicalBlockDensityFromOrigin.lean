import HarmonicBalls.Proofs.Sec11.PinchRecenteredRootLaw
import HarmonicBalls.Proofs.Sec11.ClosureScales.InternalOriginDensity

/-!
# Typical-point block density from an origin law (Lemma 11.13, draft lines 565-649)

The rooted transfer of the written argument (draft 565-649) is the existing theorem
`ae_ae_pinch_block_density_of_recentered_rooted_law` (`PinchRecenteredRootLaw.lean`), which takes as hypothesis
`hfixed`: the internal block density at the origin under the common comparison law `Q`. This file discharges
`hfixed` by the origin statement `internal_block_density_of_stationary_germ_law` (`InternalOriginDensity.lean`).

What is reduced: the conclusion `∀ᵐ ω, ∀ᵐ z ∂μ ω, eventually δ N ≤ frozen count at z` now follows from the rooted
comparison data (`hrooted`, `hac`, `hdom`, `hcomp`, `heq`, the recentering `recenter`) together with properties of ONE
probability law `Q` on the sample space: measurability and germ-measurability of the internal indicators, germ
triviality, stationarity of the indicator law, and the rate bound `δ < Q(internal pinch at scale 1)`.

Explicit hypotheses (open, not literature inputs): all of the above. The rooted comparison families are the
obligations shared with Lemma 8.2 (`RootedComparisonWeakUniqueness.lean`), extended to the metric in `heq`
(draft 583-634). The pointwise ergodic theorem is LatticeProb's (Leonardo Bonanno), used in
`HarmonicBalls.Proposed.Birkhoff`.
-/

namespace HarmonicBalls

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

open Classical in
/-- Lemma 11.13 typical-point transfer with the origin statement discharged (draft 565-649). For the rate `δ`
chosen below the scale-one internal pinch probability of the common law `Q`, the frozen block density holds for
`μ_ω`-a.e. `z`, almost surely. -/
theorem ae_ae_pinch_block_density_of_origin_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (hμ : AEMeasurable μ P) (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (hD : ∀ x y, Measurable fun ω => D ω x y)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (ν : ℕ → Measure Ω) (hμν : ∀ n, AEMeasurable μ (ν n))
    (hlocν : ∀ n, ∀ᵐ ω ∂(ν n), IsLocallyFiniteMeasure (μ ω))
    (hmetricν : ∀ n, ∀ᵐ ω ∂(ν n), IsEuclideanLengthMetric (D ω))
    {U T Q' Qset : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q' Qset)
    (M δ : ℝ) (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    (hpos : ∀ z, w z ≠ 0) (hfin : ∀ z, w z ≠ ∞)
    (ρ : ℕ → Measure ℂ) (shift : ℕ → ℂ × Ω → Ω)
    (hshift : ∀ n, Measurable (shift n)) (R : ℕ → ℂ → Measure Ω)
    (hrooted : ∀ n, P ⊗ₘ (unnormalizedWeightedRestrictionKernel P μ hμ
      (weightedLocalization w n) (measurableSet_weightedLocalization hw n) w hw) ≪
        shiftedRootReferenceLaw (ρ n) P (shift n))
    (hac : ∀ n, ∀ᵐ z ∂ρ n, P.map (fun ω => shift n (z, ω)) ≪ R n z)
    (hdom : ∀ n, ∀ᵐ z ∂ρ n, R n z ≪ ν n)
    (recenter : ℂ → Ω → Ω) (hrec : ∀ n, ∀ᵐ z ∂ρ n, AEMeasurable (recenter z) (R n z))
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (hcomp : ∀ n, ∀ᵐ z ∂ρ n, (R n z).map (recenter z) ≪ Q)
    (heq : ∀ n, ∀ᵐ z ∂ρ n, ∀ᵐ ω ∂(R n z),
      μ (recenter z ω) = (μ ω).map (fun y : ℂ => y - z) ∧
        ∀ x y, D (recenter z ω) x y = D ω (x + z) (y + z))
    (X : ℕ → Ω → ℝ) (germ : ℝ → MeasurableSpace Ω) (hgle : ∀ ε, 0 < ε → germ ε ≤ mΩ)
    (hX : ∀ n ω, X n ω = if pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Qset M
      ((2 : ℝ)⁻¹ ^ n) 0 then (1 : ℝ) else 0)
    (hXm : ∀ n, Measurable (X n))
    (hXgerm : ∀ ε, 0 < ε → ∃ K, ∀ n, K ≤ n → @Measurable Ω ℝ (germ ε) _ (X n))
    (htrivial : ∀ A : Set Ω, (∀ ε, 0 < ε → MeasurableSet[germ ε] A) → Q A = 0 ∨ Q A = 1)
    (hstat : Q.map (fun ω n => X (n + 1) ω) = Q.map (fun ω n => X n ω))
    (hδ : δ < (Q {ω | pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Qset M
      ((2 : ℝ)⁻¹ ^ 0) 0}).toReal) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), ∀ᶠ N : ℕ in atTop,
      δ * N ≤ ({k : ℕ | N + 1 ≤ k ∧ k ≤ 2 * N ∧
        pinchPointEvent (μ ω) (D ω) U T Q' Qset M ((2 : ℝ)⁻¹ ^ k) z}.ncard : ℝ) := by
  have hfixed := internal_block_density_of_stationary_germ_law Q μ D U T Q' Qset M X germ hgle hX hXm
    hXgerm htrivial hstat δ hδ
  exact ae_ae_pinch_block_density_of_recentered_rooted_law P hμ hloc hD hmetric ν hμν hlocν hmetricν
    hconfig M δ w hw hpos hfin ρ shift hshift R hrooted hac hdom recenter hrec Q hcomp heq hfixed

end HarmonicBalls

#print axioms HarmonicBalls.ae_ae_pinch_block_density_of_origin_law
