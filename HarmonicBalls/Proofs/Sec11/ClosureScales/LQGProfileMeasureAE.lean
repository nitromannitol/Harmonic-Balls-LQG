import HarmonicBalls.Proofs.Sec11.ClosureScales.LQGProfileMeasurable

/-!
# Lemma l:r6-transfer, step 3e: the LQG measure is the Borel map of the canonical profile almost surely

Source: `notes/sec11-proof/sec11-proof-r7.tex`, Lemma `l:r6-transfer`, measure part (lines 560-600), the identity
`μ(ω) = m_{γ,α}(c(ω))` (eq:r6-area). Let `μ` be the LQG measure of a whole-plane GFF (`IsLQGMeasureOfField`), and let `c`
be a canonical profile agreeing with the circle averages on `J` almost surely. Then `c ω` is a good profile for almost every
`ω`, and the Riesz measure `profileMeasure γ α₀ (c ω)` equals `μ ω`: both are Radon measures with the same vague limit
along the dyadic scales (`IsLQGLimit.unique`).
-/

namespace HarmonicBalls

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

/-- A canonical profile whose field is the circle averages of a vague limit is good. -/
theorem good_of_isLQGLimit {γ α₀ : ℝ} {hcirc : ℝ → ℂ → ℝ} {μ : Measure ℂ} {f : CanonicalProfile}
    (hL : IsLQGLimit γ (fun r z => fieldCircleAverage α₀ hcirc r z) μ)
    (hf : ∀ p ∈ circleIndexSet, f.1 p = hcirc p.1 p.2) : f ∈ goodProfiles γ α₀ := by
  simp only [goodProfiles, Set.mem_ofPred_eq]
  refine ⟨fun R => ?_, fun g hg => ?_⟩
  · have hT := tendsto_profileApprox_of_isLQGLimit hL hf (cutoffBallC (R + 1)).continuous
      (cutoffBallC (R + 1)).hasCompactSupport
    obtain ⟨M, hM⟩ := hT.bddAbove_range
    have hbound : ∀ n : ℕ, profileApprox γ α₀ n f (closedBall (0 : ℂ) ((R : ℝ) + 1)) ≤
        ENNReal.ofReal (∫ z, (cutoffBallC (R + 1)) z ∂(profileApprox γ α₀ n f)) := by
      intro n
      have := isLocallyFiniteMeasure_profileApprox γ α₀ n f
      have hint : Integrable ⇑(cutoffBallC (R + 1)) (profileApprox γ α₀ n f) :=
        (cutoffBallC (R + 1)).continuous.integrable_of_hasCompactSupport
          (cutoffBallC (R + 1)).hasCompactSupport
      have hnn : 0 ≤ᵐ[profileApprox γ α₀ n f] ⇑(cutoffBallC (R + 1)) :=
        Filter.Eventually.of_forall fun z => cutoffBall_nonneg (R + 1) z
      rw [ofReal_integral_eq_lintegral_ofReal hint hnn, ← lintegral_indicator_one measurableSet_closedBall]
      apply lintegral_mono
      intro z
      by_cases hz : z ∈ closedBall (0 : ℂ) ((R : ℝ) + 1)
      · rw [indicator_of_mem hz, Pi.one_apply]
        have hz' : ‖z‖ ≤ ((R + 1 : ℕ) : ℝ) := by
          push_cast
          exact mem_closedBall_zero_iff.mp hz
        show (1 : ENNReal) ≤ ENNReal.ofReal (cutoffBall (R + 1) z)
        rw [cutoffBall_eq_one hz', ENNReal.ofReal_one]
      · rw [indicator_of_notMem hz]
        exact zero_le
    calc ⨆ n : ℕ, profileApprox γ α₀ n f (closedBall (0 : ℂ) ((R : ℝ) + 1))
        ≤ ⨆ n : ℕ, ENNReal.ofReal (∫ z, (cutoffBallC (R + 1)) z ∂(profileApprox γ α₀ n f)) :=
          iSup_mono hbound
      _ ≤ ENNReal.ofReal M := iSup_le fun n => ENNReal.ofReal_le_ofReal (hM (Set.mem_range_self n))
      _ < ⊤ := ENNReal.ofReal_lt_top
  · exact (tendsto_profileApprox_of_isLQGLimit hL hf (testFamily_spec g hg).1
      (testFamily_spec g hg).2).cauchySeq

/-- **The LQG measure is the Borel map of the canonical profile almost surely** (eq:r6-area of Lemma l:r6-transfer): for a
whole-plane GFF with LQG measure `μ`, `μ ω = profileMeasure γ α₀ (c ω)` for almost every `ω`. -/
theorem profileMeasure_ae_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {c : Ω → CanonicalProfile} (hcJ : ∀ᵐ ω ∂P, ∀ p ∈ circleIndexSet, (c ω).1 p = hcirc ω p.1 p.2) :
    ∀ᵐ ω ∂P, μ ω = profileMeasure γ α₀ (c ω) := by
  have hμ' : ∀ᵐ ω ∂P, IsLQGLimit γ (fun r z => fieldCircleAverage α₀ (hcirc ω) r z) (μ ω) := hμ
  filter_upwards [hμ', hcJ] with ω hL hωc
  have hgood : c ω ∈ goodProfiles γ α₀ := good_of_isLQGLimit hL hωc
  have hrad : ∀ (k : ℕ) (z : ℂ), fieldCircleAverage α₀ (profileField (c ω)) (dyadicScale k) z =
      fieldCircleAverage α₀ (hcirc ω) (dyadicScale k) z := by
    intro k z
    have hp : (dyadicScale k, z) ∈ circleIndexSet :=
      Set.mk_mem_prod (dyadicScale_pos k) (Set.mem_univ z)
    simp only [fieldCircleAverage, profileField, hωc (dyadicScale k, z) hp]
  have hprof : IsLQGLimit γ (fun r z => fieldCircleAverage α₀ (profileField (c ω)) r z)
      (profileMeasure γ α₀ (c ω)) := by
    refine ⟨inferInstance, fun ψ hψ hcs => ?_⟩
    have hT := exists_profileLimit_tendsto hgood (⟨⟨ψ, hψ⟩, hcs⟩ : CompactlySupportedContinuousMap ℂ ℝ)
    have hint : ∫ z, ψ z ∂(profileMeasure γ α₀ (c ω)) =
        profileLimit γ α₀ (c ω) (⟨⟨ψ, hψ⟩, hcs⟩ : CompactlySupportedContinuousMap ℂ ℝ) :=
      integral_profileMeasure γ α₀ (c ω) ⟨⟨ψ, hψ⟩, hcs⟩
    rw [hint]
    simp only [← profileApprox_eq_lqgApprox]
    exact hT
  have hprof' : IsLQGLimit γ (fun r z => fieldCircleAverage α₀ (hcirc ω) r z)
      (profileMeasure γ α₀ (c ω)) :=
    isLQGLimit_of_radius_eq (fun k z => hrad k z) hprof
  exact (IsLQGLimit.unique hprof' hL).symm

end HarmonicBalls
