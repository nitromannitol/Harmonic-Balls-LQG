import HarmonicBalls.Proofs.Sec8.LocalCircleDecoder
import HarmonicBalls.Proofs.Sec8.VagueMassConvergence
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Local normalized mass approximations

The imported Section 8 argument uses Leonardo Bonanno's LatticeProb
formalization of the ergodic theorem.
-/

open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

namespace HarmonicBalls

/-- Under the continuity-set hypotheses for an exhaustion, normalized mass
approximations are measurable functions of local mean-zero field pairings and
converge in probability to the corresponding normalized LQG masses. -/
theorem IsWholePlaneGFF.exists_localPairing_normalizedMass_approximations
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ ε : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (E : ℕ → Set ℂ) (hEm : ∀ n, MeasurableSet (E n)) (hmono : Monotone E)
    (hbounded : Bornology.IsBounded (⋃ n, E n))
    (hbuffer : ∀ n z, z ∈ E n → closedBall z (dyadicScale n) ⊆ ball 0 ε)
    (hunion : (⋃ n, E n) = ball 0 ε)
    (S : Set (Set ℂ)) (hsets : ∀ A ∈ S, MeasurableSet A)
    (hfront : ∀ A ∈ S, ∀ᵐ ω ∂P, (∀ n, μ ω (frontier (E n)) = 0 ∧
        μ ω (frontier (A ∩ E n)) = 0) ∧
      μ ω (frontier (⋃ n, E n)) = 0 ∧ μ ω (frontier (A ∩ ⋃ n, E n)) = 0)
    (hpositive : ∀ᵐ ω ∂P, μ ω (⋃ n, E n) ≠ 0 ∧ μ ω (⋃ n, E n) ≠ ∞) :
    ∃ f : S → ℕ → (Section6.LocalTest (ball 0 ε) → ℝ) → ℝ,
      (∀ A n, Measurable (f A n)) ∧ ∀ A,
        TendstoInMeasure P (fun n ω => f A n (Section6.localPairingProc (ball 0 ε) hC ω))
          atTop (fun ω => (normalizedRestriction (μ ω) (ball 0 ε) A.val).toReal) := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  have hX : Measurable (Section6.localPairingProc (ball 0 ε) hC) :=
    measurable_pi_iff.2 fun φ => hGFF.measurable_pairing φ.1.1 (Section6.isTestFunction_of_testC φ.1.1)
  obtain ⟨F, hFm, hFeq⟩ := hGFF.exists_localPairing_normalizedLQGApprox
    (γ := γ) (α₀ := α₀) E hEm hbuffer
  refine ⟨fun A n x => (F n x A.val).toReal, ?_, ?_⟩
  · intro A n
    exact ENNReal.measurable_toReal.comp ((Measure.measurable_coe (hsets A A.property)).comp (hFm n))
  · intro A
    apply tendstoInMeasure_of_tendsto_ae
      (fun n => (ENNReal.measurable_toReal.comp
        (((Measure.measurable_coe (hsets A A.property)).comp (hFm n)).comp hX)).aestronglyMeasurable)
    have hc := ae_all_iff.mpr fun n => hGFF.ae_continuous_fieldCircleAverage α₀ (dyadicScale_pos n)
    filter_upwards [hμ, hc, hfront A A.property, hpositive, hFeq] with ω hω hcω hfrontω hpω heqω
    have hlim := hω.tendsto_normalizedRestriction_exhaustion hcω E hmono hbounded A.val
      (hsets A A.property) hfrontω.1 hfrontω.2 hpω.1 hpω.2
    have ht : μ ω (A.val ∩ ⋃ n, E n) / μ ω (⋃ n, E n) =
        normalizedRestriction (μ ω) (ball 0 ε) A.val := by
      simp only [normalizedRestriction, Measure.smul_apply, smul_eq_mul,
        Measure.restrict_apply (hsets A A.property), ENNReal.div_eq_inv_mul, hunion]
    rw [ht] at hlim
    have hlim' := (ENNReal.tendsto_toReal (measure_ne_top
      (normalizedRestriction (μ ω) (ball 0 ε)) A.val)).comp hlim
    change Tendsto (fun n => (F n (Section6.localPairingProc (ball 0 ε) hC ω) A.val).toReal)
      atTop (𝓝 ((normalizedRestriction (μ ω) (ball 0 ε) A.val).toReal))
    simp_rw [heqω]
    exact hlim'

end HarmonicBalls
