import HarmonicBalls.Proofs.Sec8.CenteredCircleLocal
import HarmonicBalls.Proofs.Sec8.ContinuityExhaustion
import HarmonicBalls.Proofs.Sec8.PhaseLocalizedFrequency

/-! # Buffered local normalized LQG restrictions

The imported Section 8 path argument uses Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization of the ergodic theorem.
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal

namespace HarmonicBalls

/-- The normalized LQG measure on a sufficiently small ball has a version
measurable in the field modulo constants on any prescribed larger ball. -/
theorem IsWholePlaneGFF.exists_buffered_normalizedRestriction
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hpositive : ∀ᵐ ω ∂P, ∀ r : ℝ, 0 < r →
      μ ω (ball 0 r) ≠ 0 ∧ μ ω (ball 0 r) ≠ ∞) :
    ∀ ε, 0 < ε → ∃ r ∈ Ioo (0 : ℝ) ε, ∃ ν : Ω → Measure ℂ,
      @Measurable Ω (Measure ℂ)
        (Section6.fieldSigmaAlgebraModConst α hC (ball 0 ε)) _ ν ∧
      ∀ᵐ ω ∂P, ν ω = normalizedRestriction (μ ω) (ball 0 r) := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  intro ε hε
  let m := Section6.fieldSigmaAlgebraModConst α hC (ball 0 ε)
  let : MeasurableSpace Ω := mΩ
  have hm : m ≤ mΩ := (Section6.fieldSigmaAlgebraModConst_le α hC _).trans
    (hGFF.fieldSigmaAlgebra_le α _)
  obtain ⟨R, E, hR, _, hbuffer, hversion⟩ :=
    hGFF.exists_normalizedRestriction_of_centered_versions P m hm hμ hpositive hε
  have hc : ∀ n, ∃ d : Ω → ℂ → ℝ,
      @Measurable (Ω × ℂ) ℝ (m.prod inferInstance) _ (Function.uncurry d) ∧
      ∀ᵐ ω ∂P, ∀ z, closedBall z (dyadicScale n) ⊆ ball 0 ε →
        d ω z = fieldCircleAverage α (hcirc ω) (dyadicScale n) z -
          fieldCircleAverage α (hcirc ω) (dyadicScale n) 0 := by
    intro n
    exact hGFF.exists_joint_centered_circle_version (α₀ := α) (ε := ε) (dyadicScale_pos n)
  choose d hdm hdeq using hc
  refine ⟨R, hR, ?_⟩
  apply hversion d hdm
  intro n
  filter_upwards [hdeq n] with ω hω z hz
  exact hω z (hbuffer n z hz)

universe u

/-- Full support and local finiteness supply the positive finite masses needed
for buffered normalized LQG restrictions. -/
theorem IsWholePlaneGFF.exists_buffered_normalizedRestriction_of_fullSupport
    (hfull : LQGMeasureFullSupportStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ) :
    ∀ ε, 0 < ε → ∃ r ∈ Ioo (0 : ℝ) ε, ∃ ν : Ω → Measure ℂ,
      @Measurable Ω (Measure ℂ)
        (Section6.fieldSigmaAlgebraModConst α hC (ball 0 ε)) _ ν ∧
      ∀ᵐ ω ∂P, ν ω = normalizedRestriction (μ ω) (ball 0 r) := by
  apply hGFF.exists_buffered_normalizedRestriction hμ
  exact ae_referenceBall_pos_finite P μ
    (hfull γ α hγ hγ2 hα Ω P hC hcirc μ hGFF hμ)
    (hμ.mono (fun _ h => h.isLocallyFiniteMeasure))

/-- The normalized dyadic LQG path is ergodic under the stated affine and
coordinate-change hypotheses. -/
theorem IsWholePlaneGFF.ergodic_localizedDyadicMeasure_shift_of_locality
    (hfull : LQGMeasureFullSupportStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α hC hcirc) (R : ℝ) (hR : 0 < R) :
    Ergodic (fun x : ℕ → Measure ℂ => fun n => x (n + 1))
      (P.map (fun ω n => localizedDyadicMeasure (ball 0 R) (μ ω) n)) := by
  exact hGFF.ergodic_localizedDyadicMeasure_shift_of_fullSupport hfull hγ hγ2 hα
    hμ hAff hCC R hR
    (hGFF.exists_buffered_normalizedRestriction_of_fullSupport hfull hγ hγ2 hα hμ)

open Classical in
/-- Uniform one-scale estimates yield phase block frequency; the buffered
local normalized restrictions follow from the field and LQG measure. -/
theorem IsWholePlaneGFF.exists_ae_phaseVeryGoodComparable_blockFrequency_of_locality
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ β : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hβ : (2 + γ) ^ 2 / 2 < β)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {a b c : ℝ} (hc : 0 < c)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hprev : PolyHighProb P fun ε => {ω | ∀ z ∈ Section6.prevalenceGrid ε,
      c * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus (μ ω) r z a b}.ncard : ℝ)})
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b})
    {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ C₁m C₁p C₂m C₂p : ℝ,
      0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
      ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∃ m ∈ Ioo (0 : ℝ) 1,
      ∀ N : ℕ, N₀ ≤ N →
      ∀ᵐ p ∂(((volume : Measure PhaseCircle).prod volume).prod P),
        ∀ᶠ K : ℕ in atTop, (1 - ζ) * (K : ℝ) ≤
          ({n : ℕ | n ∈ Icc (K + 1) (2 * K) ∧
            PhaseVeryGoodAnnulus (μ p.2) β (dyadicScale n) 0 N
              a b C₁m C₁p C₂m C₂p c (torusPhase p.1) ∧
            AnnulusBallComparison (μ p.2) n 0 m}.ncard : ℝ) := by
  exact hGFF.exists_ae_phaseVeryGoodComparable_blockFrequency hgrowth hfull
    hγ hγ2 hβ hc hμ hAff hCC
    (hGFF.exists_buffered_normalizedRestriction_of_fullSupport hfull hγ hγ2
      (by unfold lqgQ; positivity) hμ) hprev hunit hζ

end HarmonicBalls
