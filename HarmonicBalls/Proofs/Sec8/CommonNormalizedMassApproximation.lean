import HarmonicBalls.Proofs.Sec8.CommonCircleApproximation
import HarmonicBalls.Proofs.Sec8.LocalNormalizedMassApproximation

/-! # Common normalized mass approximations

The imported Section 8 argument uses Leonardo Bonanno's LatticeProb
formalization of the ergodic theorem.
-/

open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

namespace HarmonicBalls

/-- A measurable local approximation representing the normalized LQG
approximants converges to normalized LQG masses on continuity sets. -/
theorem IsWholePlaneGFF.tendstoInMeasure_normalizedMass_of_approximation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ ε : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (E : ℕ → Set ℂ) (hmono : Monotone E)
    (hbounded : Bornology.IsBounded (⋃ n, E n)) (hunion : (⋃ n, E n) = ball 0 ε)
    (A : Set ℂ) (hA : MeasurableSet A)
    (hfront : ∀ᵐ ω ∂P, (∀ n, μ ω (frontier (E n)) = 0 ∧
        μ ω (frontier (A ∩ E n)) = 0) ∧
      μ ω (frontier (⋃ n, E n)) = 0 ∧ μ ω (frontier (A ∩ ⋃ n, E n)) = 0)
    (hpositive : ∀ᵐ ω ∂P, μ ω (⋃ n, E n) ≠ 0 ∧ μ ω (⋃ n, E n) ≠ ∞)
    (F : ℕ → (Section6.LocalTest (ball 0 ε) → ℝ) → Measure ℂ)
    (hFm : ∀ n, Measurable (F n))
    (hFeq : ∀ᵐ ω ∂P, ∀ n, F n (Section6.localPairingProc (ball 0 ε) hC ω) =
      normalizedRestriction (lqgApprox γ (fieldCircleAverage α₀ (hcirc ω))
        (dyadicScale n)) (E n)) :
    TendstoInMeasure P
      (fun n ω => (F n (Section6.localPairingProc (ball 0 ε) hC ω) A).toReal)
      atTop (fun ω => (normalizedRestriction (μ ω) (ball 0 ε) A).toReal) := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  have hX : Measurable (Section6.localPairingProc (ball 0 ε) hC) :=
    measurable_pi_iff.2 fun φ => hGFF.measurable_pairing φ.1.1 (Section6.isTestFunction_of_testC φ.1.1)
  apply tendstoInMeasure_of_tendsto_ae
    (fun n => (ENNReal.measurable_toReal.comp
      (((Measure.measurable_coe hA).comp (hFm n)).comp hX)).aestronglyMeasurable)
  have hc := ae_all_iff.mpr fun n => hGFF.ae_continuous_fieldCircleAverage α₀ (dyadicScale_pos n)
  filter_upwards [hμ, hc, hfront, hpositive, hFeq] with ω hω hcω hfrontω hpω heqω
  have hlim := hω.tendsto_normalizedRestriction_exhaustion hcω E hmono hbounded A
    hA hfrontω.1 hfrontω.2 hpω.1 hpω.2
  have ht : μ ω (A ∩ ⋃ n, E n) / μ ω (⋃ n, E n) =
      normalizedRestriction (μ ω) (ball 0 ε) A := by
    simp only [normalizedRestriction, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply hA, ENNReal.div_eq_inv_mul, hunion]
  rw [ht] at hlim
  have hlim' := (ENNReal.tendsto_toReal (measure_ne_top
    (normalizedRestriction (μ ω) (ball 0 ε)) A)).comp hlim
  change Tendsto (fun n => (F n (Section6.localPairingProc (ball 0 ε) hC ω) A).toReal)
    atTop (𝓝 ((normalizedRestriction (μ ω) (ball 0 ε) A).toReal))
  simp_rw [heqω]
  exact hlim'

/-- Two whole-plane GFF realizations with the same logarithmic singularity
have one sequence of local measurable mass approximations converging under
both laws, on common continuity sets. -/
theorem IsWholePlaneGFF.exists_common_normalizedMass_approximations
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} {Q : Measure Ξ} {γ α₀ ε : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {gC : Ξ → (ℂ → ℝ) → ℝ} {gcirc : Ξ → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {ν : Ξ → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (gGFF : IsWholePlaneGFF Q gC gcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hν : IsLQGMeasureOfField Q γ α₀ gcirc ν)
    (E : ℕ → Set ℂ) (hEm : ∀ n, MeasurableSet (E n)) (hmono : Monotone E)
    (hbounded : Bornology.IsBounded (⋃ n, E n))
    (hbuffer : ∀ n z, z ∈ E n → closedBall z (dyadicScale n) ⊆ ball 0 ε)
    (hunion : (⋃ n, E n) = ball 0 ε)
    (S : Set (Set ℂ)) (hsets : ∀ A ∈ S, MeasurableSet A)
    (hfrontμ : ∀ A ∈ S, ∀ᵐ ω ∂P, (∀ n, μ ω (frontier (E n)) = 0 ∧
        μ ω (frontier (A ∩ E n)) = 0) ∧
      μ ω (frontier (⋃ n, E n)) = 0 ∧ μ ω (frontier (A ∩ ⋃ n, E n)) = 0)
    (hfrontν : ∀ A ∈ S, ∀ᵐ ω ∂Q, (∀ n, ν ω (frontier (E n)) = 0 ∧
        ν ω (frontier (A ∩ E n)) = 0) ∧
      ν ω (frontier (⋃ n, E n)) = 0 ∧ ν ω (frontier (A ∩ ⋃ n, E n)) = 0)
    (hpositiveμ : ∀ᵐ ω ∂P, μ ω (⋃ n, E n) ≠ 0 ∧ μ ω (⋃ n, E n) ≠ ∞)
    (hpositiveν : ∀ᵐ ω ∂Q, ν ω (⋃ n, E n) ≠ 0 ∧ ν ω (⋃ n, E n) ≠ ∞) :
    ∃ f : S → ℕ → (Section6.LocalTest (ball 0 ε) → ℝ) → ℝ,
      (∀ A n, Measurable (f A n)) ∧ (∀ A,
        TendstoInMeasure P (fun n ω => f A n (Section6.localPairingProc (ball 0 ε) hC ω))
          atTop (fun ω => (normalizedRestriction (μ ω) (ball 0 ε) A.val).toReal)) ∧ ∀ A,
        TendstoInMeasure Q (fun n ω => f A n (Section6.localPairingProc (ball 0 ε) gC ω))
          atTop (fun ω => (normalizedRestriction (ν ω) (ball 0 ε) A.val).toReal) := by
  obtain ⟨F, hFm, hFP, hFQ⟩ :=
    hGFF.exists_common_normalizedLQGApprox (γ := γ) (α₀ := α₀) gGFF E hEm hbuffer
  refine ⟨fun A n x => (F n x A.val).toReal, ?_, ?_, ?_⟩
  · intro A n
    exact ENNReal.measurable_toReal.comp ((Measure.measurable_coe (hsets A A.property)).comp (hFm n))
  · intro A
    exact hGFF.tendstoInMeasure_normalizedMass_of_approximation hμ E hmono hbounded hunion
      A.val (hsets A A.property) (hfrontμ A A.property) hpositiveμ F hFm hFP
  · intro A
    exact gGFF.tendstoInMeasure_normalizedMass_of_approximation hν E hmono hbounded hunion
      A.val (hsets A A.property) (hfrontν A A.property) hpositiveν F hFm hFQ

/-- The law of all local test-function pairings is independent of the
realization of the whole-plane GFF. -/
theorem IsWholePlaneGFF.map_localPairingProc_eq
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} {Q : Measure Ξ} {ε : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {gC : Ξ → (ℂ → ℝ) → ℝ} {gcirc : Ξ → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (gGFF : IsWholePlaneGFF Q gC gcirc) :
    P.map (Section6.localPairingProc (ball 0 ε) hC) =
      Q.map (Section6.localPairingProc (ball 0 ε) gC) := by
  let L : (GFFObservable.Admissible → ℝ) → Section6.LocalTest (ball 0 ε) → ℝ :=
    fun x φ => x ⟨.pairing φ.1.1, Section6.isTestFunction_of_testC φ.1.1⟩
  have hL : Measurable L := measurable_pi_iff.mpr fun φ => measurable_pi_apply _
  have hh := congrArg (fun m : Measure (GFFObservable.Admissible → ℝ) => m.map L)
    (hGFF.map_wholePlaneObservableProc_eq gGFF)
  rw [Measure.map_map hL hGFF.measurable_wholePlaneObservableProc,
    Measure.map_map hL gGFF.measurable_wholePlaneObservableProc] at hh
  exact hh

#print axioms IsWholePlaneGFF.map_localPairingProc_eq
#print axioms IsWholePlaneGFF.tendstoInMeasure_normalizedMass_of_approximation
#print axioms IsWholePlaneGFF.exists_common_normalizedMass_approximations

end HarmonicBalls
