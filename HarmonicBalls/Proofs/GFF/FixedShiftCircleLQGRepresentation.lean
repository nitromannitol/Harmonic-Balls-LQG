import HarmonicBalls.Proofs.Sec8.LocalCirclePairingApproximation
import HarmonicBalls.Proofs.Sec8.LocalNormalizedMassApproximation
import HarmonicBalls.Proofs.Sec8.CommonApproximationLaw

/-! # Deterministic shifts of local circle approximations

The imported Section 8 development uses Leonardo Bonanno's LatticeProb
formalization.  The first result identifies the deterministic correction to
the actual signed annular tests used to construct the circle decoder.
-/

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal Topology

namespace HarmonicBalls

/-- Pairing a continuous deterministic shift with the signed annular tests
converges to the difference of its two circle averages. -/
theorem circleDensityDifference_shift_tendsto {r η : ℝ}
    (hr : 0 < r) (hη : 0 < η) (z : ℂ) {g : ℂ → ℝ} (hg : Continuous g) :
    Tendsto (fun n => ∫ x, circleDensityDifference r η hr hη z n x * g x)
      atTop (𝓝 (Real.circleAverage g z r - Real.circleAverage g 0 r)) := by
  have ht := (circleDensity_integral_tendsto_circleAverage hr hη z hg).sub
    (circleDensity_integral_tendsto_circleAverage hr hη 0 hg)
  apply ht.congr'
  filter_upwards with n
  let δ := circleDensityWidth r η n
  let hδ := circleDensityWidth_pos hr hη n
  let m : ℝ := (∫ y, circleDensity r δ hδ 0 y)⁻¹
  have hi (v : ℂ) : Integrable (fun x => m * circleDensity r δ hδ v x * g x) := by
    apply ((continuous_const.mul (circleDensity_contDiff r δ hδ v).continuous).mul hg).integrable_of_hasCompactSupport
    exact (circleDensity_hasCompactSupport hr.le hδ v).mul_left.mul_right
  symm
  change (∫ x, (m * circleDensity r δ hδ z x - m * circleDensity r δ hδ 0 x) * g x) = _
  simp_rw [sub_mul]
  exact integral_sub (hi z) (hi 0)

/-- The same local annular tests approximate the GFF's centered circle in
probability and the deterministic shift's centered circle in the ordinary
sense. The test sequence is fixed before the shift is chosen. -/
theorem IsWholePlaneGFF.exists_localPairing_tests_with_shift_limit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ε r : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hr : 0 < r) (z : ℂ)
    (hz : closedBall z r ⊆ ball 0 ε) :
    ∃ φ : ℕ → Section6.LocalTest (ball 0 ε),
      TendstoInMeasure P (fun n ω => hC ω (φ n).1.1) atTop
        (fun ω => hcirc ω r z - hcirc ω r 0) ∧
      ∀ g : ℂ → ℝ, Continuous g →
        Tendsto (fun n => ∫ x, (φ n).1.1 x * g x) atTop
          (𝓝 (Real.circleAverage g z r - Real.circleAverage g 0 r)) := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  obtain ⟨η, hη, _, htests, _, _⟩ := exists_local_circleDensity_tests hr z hz
  let ψ := circleDensityDifference r η hr hη z
  have htest (n : ℕ) : IsTestFunction (ball 0 ε) (ψ n) ∧ ∫ x, ψ n x = 0 := htests n
  have htestU (n : ℕ) : IsTestFunction univ (ψ n) :=
    ⟨(htest n).1.1, (htest n).1.2.1, subset_univ _⟩
  let φ : ℕ → Section6.LocalTest (ball 0 ε) := fun n =>
    ⟨⟨⟨ψ n, (htest n).1.1, (htest n).1.2.1, subset_univ _⟩, (htest n).2⟩,
      (htest n).1.2.2⟩
  refine ⟨φ, ?_, ?_⟩
  · have hp (n : ℕ) : MemLp (fun ω => hC ω (ψ n)) 2 P :=
      (hGFF.isGaussianProcess.hasGaussianLaw_eval
        (⟨.pairing (ψ n), htestU n⟩ : GFFObservable.Admissible)).memLp (by simp)
    have hzLp : MemLp (fun ω => hcirc ω r z) 2 P :=
      (hGFF.hasGaussianLaw_circle hr z).memLp (by simp)
    have h0Lp : MemLp (fun ω => hcirc ω r 0) 2 P :=
      (hGFF.hasGaussianLaw_circle hr 0).memLp (by simp)
    have hm : ∀ n, ∫ ω, (hC ω (ψ n) - (hcirc ω r z - hcirc ω r 0)) ∂P = 0 := by
      intro n
      have hp0 := hGFF.integral_eq_zero (.pairing (ψ n)) (htestU n)
      have hz0 := hGFF.integral_eq_zero (.circle r z) hr
      have h00 := hGFF.integral_eq_zero (.circle r 0) hr
      simp only [GFFObservable.eval] at hp0 hz0 h00
      have hxy : Integrable (fun ω => hcirc ω r z - hcirc ω r 0) P :=
        (hzLp.sub h0Lp).integrable (by simp)
      rw [integral_sub ((hp n).integrable (by simp)) hxy,
        integral_sub (hzLp.integrable (by simp)) (h0Lp.integrable (by simp)), hp0, hz0, h00]
      ring
    have hkernel := hGFF.circleDensityDifference_error_tendsto_of_self hr hη z
      (hGFF.circleDensityDifference_self_covariance_tendsto hr hη z)
    have hvar : Tendsto (fun n => ProbabilityTheory.variance
        (fun ω => hC ω (ψ n) - (hcirc ω r z - hcirc ω r 0)) P) atTop (𝓝 0) := by
      convert hkernel using 1
      funext n
      exact hGFF.variance_pairing_sub_circle_difference hr z (ψ n) (htestU n)
    exact tendstoInMeasure_of_centered_variance_tendsto_zero P _ _
      (fun n => (hp n).sub (hzLp.sub h0Lp)) hm hvar
  · intro g hg
    exact circleDensityDifference_shift_tendsto hr hη z hg

/-- An actual LQG limit and continuity-set exhaustion turn a measurable
finite-scale decoder into convergence in probability of normalized masses.
This applies equally to a smooth-shifted circle process. -/
theorem tendstoInMeasure_normalizedMass_of_fixedShift_approximation
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] {γ : ℝ}
    (h : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hμ : IsLQGMeasure P γ h μ)
    (hc : ∀ᵐ ω ∂P, ∀ n, Continuous (h ω (dyadicScale n)))
    (U : Set ℂ) (V : ℕ → Set ℂ) (hmono : Monotone V)
    (hbounded : Bornology.IsBounded (⋃ n, V n)) (hunion : (⋃ n, V n) = U)
    (A : Set ℂ) (hA : MeasurableSet A)
    (hfront : ∀ᵐ ω ∂P, (∀ n, μ ω (frontier (V n)) = 0 ∧
      μ ω (frontier (A ∩ V n)) = 0) ∧
      μ ω (frontier (⋃ n, V n)) = 0 ∧ μ ω (frontier (A ∩ ⋃ n, V n)) = 0)
    (hpos : ∀ᵐ ω ∂P, μ ω (⋃ n, V n) ≠ 0 ∧ μ ω (⋃ n, V n) ≠ ∞)
    (X : Ω → E) (hX : Measurable X) (F : ℕ → E → Measure ℂ)
    (hF : ∀ n, Measurable (F n))
    (heq : ∀ᵐ ω ∂P, ∀ n, F n (X ω) =
      normalizedRestriction (lqgApprox γ (h ω) (dyadicScale n)) (V n)) :
    TendstoInMeasure P (fun n ω => (F n (X ω) A).toReal) atTop
      (fun ω => (normalizedRestriction (μ ω) U A).toReal) := by
  apply tendstoInMeasure_of_tendsto_ae
    (fun n => (ENNReal.measurable_toReal.comp
      (((Measure.measurable_coe hA).comp (hF n)).comp hX)).aestronglyMeasurable)
  filter_upwards [hμ, hc, hfront, hpos, heq] with ω hω hcω hfω hpω heqω
  have hlim := hω.tendsto_normalizedRestriction_exhaustion hcω V hmono hbounded A hA
    hfω.1 hfω.2 hpω.1 hpω.2
  have ht : μ ω (A ∩ ⋃ n, V n) / μ ω (⋃ n, V n) =
      normalizedRestriction (μ ω) U A := by
    simp only [normalizedRestriction, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply hA, ENNReal.div_eq_inv_mul, hunion]
  rw [ht] at hlim
  have hlim' := (ENNReal.tendsto_toReal (measure_ne_top
    (normalizedRestriction (μ ω) U) A)).comp hlim
  change Tendsto (fun n => (F n (X ω) A).toReal) atTop
    (𝓝 ((normalizedRestriction (μ ω) U A).toReal))
  simp_rw [heqω]
  exact hlim'

/-- Common measurable normalized approximations have one measurable final
decoder on any countable family of mass observables. The two convergence
premises are deliberately explicit: equality of the finite-scale decoders
alone does not establish convergence to a shifted LQG measure. -/
theorem exists_fixedShift_normalizedMass_decoder_of_common_limits
    {Ω Ξ E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    [MeasurableSpace E] [Countable ι] (P : Measure Ω) (Q : Measure Ξ)
    (X : Ω → E) (Y : Ξ → E) (f : ι → ℕ → E → ℝ)
    (hf : ∀ i n, Measurable (f i n))
    (μ : Ω → Measure ℂ) (ν : Ξ → Measure ℂ) (U : Set ℂ) (A : ι → Set ℂ)
    (hμ : ∀ i, TendstoInMeasure P (fun n ω => f i n (X ω)) atTop
      (fun ω => (normalizedRestriction (μ ω) U (A i)).toReal))
    (hν : ∀ i, TendstoInMeasure Q (fun n ω => f i n (Y ω)) atTop
      (fun ω => (normalizedRestriction (ν ω) U (A i)).toReal)) :
    ∃ D : E → ι → ℝ, Measurable D ∧
      (∀ᵐ ω ∂P, ∀ i, D (X ω) i = (normalizedRestriction (μ ω) U (A i)).toReal) ∧
      ∀ᵐ ω ∂Q, ∀ i, D (Y ω) i = (normalizedRestriction (ν ω) U (A i)).toReal := by
  obtain ⟨F, hF, hFP, hFQ⟩ :=
    exists_common_countable_limits_of_tendstoInMeasure P Q X Y f hf
      (fun i ω => (normalizedRestriction (μ ω) U (A i)).toReal)
      (fun i ω => (normalizedRestriction (ν ω) U (A i)).toReal) hμ hν
  exact ⟨fun x i => F i x, Measurable.of_eval hF, hFP, hFQ⟩

/-- A measurable event in countably many decoded normalized masses has the
two almost-sure local pairing representations needed for event transfer. -/
theorem fixedShift_event_representation_of_mass_decoder
    {Ω Ξ E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    [MeasurableSpace E] (P : Measure Ω) (Q : Measure Ξ)
    (X : Ω → E) (Y : Ξ → E) (D : E → ι → ℝ) (hD : Measurable D)
    (u : Ω → ι → ℝ) (v : Ξ → ι → ℝ)
    (hu : ∀ᵐ ω ∂P, D (X ω) = u ω) (hv : ∀ᵐ ω ∂Q, D (Y ω) = v ω)
    (C : Set (ι → ℝ)) (hC : MeasurableSet C) :
    ∃ B : Set E, MeasurableSet B ∧
      (∀ᵐ ω ∂P, (u ω ∈ C ↔ X ω ∈ B)) ∧
      ∀ᵐ ω ∂Q, (v ω ∈ C ↔ Y ω ∈ B) := by
  refine ⟨D ⁻¹' C, hD hC, ?_, ?_⟩
  · filter_upwards [hu] with ω hω
    simp only [Set.mem_preimage, hω]
  · filter_upwards [hv] with ω hω
    simp only [Set.mem_preimage, hω]

#print axioms circleDensityDifference_shift_tendsto
#print axioms IsWholePlaneGFF.exists_localPairing_tests_with_shift_limit
#print axioms tendstoInMeasure_normalizedMass_of_fixedShift_approximation
#print axioms exists_fixedShift_normalizedMass_decoder_of_common_limits
#print axioms fixedShift_event_representation_of_mass_decoder

end HarmonicBalls
