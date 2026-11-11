import HarmonicBalls.Proofs.Sec8.LocalCircleDecoder
import HarmonicBalls.Proofs.Sec8.MeanZeroTestEquivalence
import HarmonicBalls.Proofs.Sec8.RootedMassApproximation
import HarmonicBalls.Proofs.Sec8.UnitBallObservedFrequency
import HarmonicBalls.Proofs.Sec8.RootedContinuitySets

/-! # Rooted approximations from mean-zero field pairings

A centered circle-average decoder on a sufficiently large ball yields the
normalized translated approximations jointly from the raw field and root.
The imported Section 8 development uses Leonardo Bonanno's LatticeProb
formalization of the ergodic theorem.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal Topology

/-- On buffered sets, normalized translated circle-average approximations are
jointly measurable functions of the raw mean-zero field and the root. -/
theorem IsWholePlaneGFF.exists_raw_rooted_normalizedLQGApprox
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ R : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (B : Set ℂ) (E : ℕ → Set ℂ)
    (hEm : ∀ n, MeasurableSet (E n))
    (hbuffer : ∀ n z, z ∈ B →
      closedBall z (dyadicScale n) ⊆ ball 0 R ∧
      ∀ x ∈ E n, closedBall (x + z) (dyadicScale n) ⊆ ball 0 R) :
    ∃ F : ℕ → ((RawMeanZeroTest → ℝ) × ℂ) → Measure ℂ,
      (∀ n, Measurable (F n)) ∧ ∀ᵐ ω ∂P, ∀ z ∈ B, ∀ n,
        F n ((fun φ : RawMeanZeroTest => hC ω φ.1), z) =
          normalizedRestriction (lqgApprox γ (fun r x => hcirc ω r (x + z))
            (dyadicScale n)) (E n) := by
  let L : (RawMeanZeroTest → ℝ) → Section6.LocalTest (ball 0 R) → ℝ :=
    fun f φ => f (meanZeroTestEquiv φ.1)
  have hLm : Measurable L := by
    apply measurable_pi_iff.mpr
    intro φ
    exact measurable_pi_apply (meanZeroTestEquiv φ.1)
  choose D hDm hDeq using fun n =>
    hh.exists_localPairing_centeredCircle_decoder (α₀ := 0) (ε := R) (dyadicScale_pos n)
  let d : ℕ → ((RawMeanZeroTest → ℝ) × ℂ) → ℂ → ℝ :=
    fun n p x => D n (L p.1) (x + p.2) - D n (L p.1) p.2
  have hdm : ∀ n, Measurable (Function.uncurry (d n)) := by
    intro n
    apply Measurable.sub
    · exact (hDm n).comp ((hLm.comp (measurable_fst.comp measurable_fst)).prodMk
        (measurable_snd.add (measurable_snd.comp measurable_fst)))
    · exact (hDm n).comp ((hLm.comp (measurable_fst.comp measurable_fst)).prodMk
        (measurable_snd.comp measurable_fst))
  refine ⟨fun n p => normalizedRestriction
    (volume.withDensity fun x => ENNReal.ofReal (Real.exp (γ * d n p x))) (E n), ?_, ?_⟩
  · exact fun n => measurable_normalized_centeredLQGApprox γ (d n) (hdm n) (E n) (hEm n)
  · filter_upwards [ae_all_iff.mpr hDeq] with ω hω z hz n
    apply (normalizedRestriction_lqgApprox_eq_of_centered_on γ
      (fun r x => hcirc ω r (x + z)) (dyadicScale_pos n) 0 (hEm n) _ ?_).symm
    intro x hx
    have h₁ := hω n (x + z) ((hbuffer n z hz).2 x hx)
    have h₂ := hω n z ((hbuffer n z hz).1)
    change D n (L (fun φ : RawMeanZeroTest => hC ω φ.1)) (x + z) -
      D n (L (fun φ : RawMeanZeroTest => hC ω φ.1)) z = _
    change D n (Section6.localPairingProc (ball 0 R) hC ω) (x + z) -
      D n (Section6.localPairingProc (ball 0 R) hC ω) z = _
    simp only [fieldCircleAverage, zero_mul, sub_zero] at h₁ h₂
    rw [h₁, h₂]
    simp only [zero_add]
    ring

/-- The translated dyadic circles around unit-ball roots fit in one fixed
larger ball whenever the original sets lie in a bounded ball. -/
theorem unitBall_rooted_dyadic_buffer {ε : ℝ} (hε : 0 < ε)
    (E : ℕ → Set ℂ) (hE : ∀ n, E n ⊆ ball 0 ε) :
    ∀ n z, z ∈ ball (0 : ℂ) 1 →
      closedBall z (dyadicScale n) ⊆ ball 0 (ε + 3) ∧
      ∀ x ∈ E n, closedBall (x + z) (dyadicScale n) ⊆ ball 0 (ε + 3) := by
  have hscale (n : ℕ) : dyadicScale n ≤ 1 := by
    unfold dyadicScale
    exact pow_le_one₀ (by norm_num) (by norm_num)
  intro n z hz
  have hz' : dist z 0 < 1 := mem_ball.mp hz
  constructor
  · intro y hy
    have hy' : dist y z ≤ dyadicScale n := mem_closedBall.mp hy
    have ht := dist_triangle y z (0 : ℂ)
    rw [mem_ball]
    linarith [hscale n]
  · intro x hx y hy
    have hx' : dist x 0 < ε := mem_ball.mp (hE n hx)
    have hy' : dist y (x + z) ≤ dyadicScale n := mem_closedBall.mp hy
    have ht := dist_triangle y (x + z) (0 : ℂ)
    have hzsum : dist (x + z) 0 ≤ dist x 0 + dist z 0 := by
      simpa only [dist_zero_right] using norm_add_le x z
    rw [mem_ball]
    linarith [hscale n]

/-- A normalized weighted root lies in the sampling set almost surely. -/
theorem ae_mem_weightedRestriction_compProd
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (μ : Ω → Measure ℂ) (hm : AEMeasurable μ P)
    (B : Set ℂ) (hB : MeasurableSet B) (w : ℂ → ℝ≥0∞) (hw : Measurable w) :
    ∀ᵐ x ∂(P ⊗ₘ weightedRestrictionKernel P μ hm B hB w hw), x.2 ∈ B := by
  apply Measure.ae_compProd_of_ae_ae (hB.preimage measurable_snd)
  filter_upwards [ae_weightedRestrictionKernel_eq P μ hm B hB w hw] with ω hω
  rw [hω, normalizedRestriction]
  exact Measure.ae_smul_measure (ae_restrict_mem hB) _

/-- On rooted continuity sets, the normalized masses are limits in measure
of jointly measurable functions of the raw mean-zero field and the root. -/
theorem IsWholePlaneGFF.exists_unitBall_rooted_mass_approximations
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ ε : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {ν : Ω → Measure ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hν : IsLQGMeasureOfField P γ 0 hcirc ν)
    (hmass : ∀ᵐ ω ∂P, ν ω (ball 0 1) ≠ 0) (hε : 0 < ε)
    (E : ℕ → Set ℂ) (hEm : ∀ n, MeasurableSet (E n)) (hmono : Monotone E)
    (hunion : (⋃ n, E n) = ball 0 ε)
    (S : Set (Set ℂ)) (hsets : ∀ A ∈ S, MeasurableSet A)
    (hfront : ∀ A ∈ S, ∀ᵐ x ∂(P ⊗ₘ weightedRestrictionKernel P ν
      (hh.aemeasurable_lqgMeasure hν) (ball 0 1) measurableSet_ball
      (fun _ => 1) measurable_const),
      let η := (ν x.1).map (fun v : ℂ => v - x.2)
      (∀ n, η (frontier (E n)) = 0 ∧ η (frontier (A ∩ E n)) = 0) ∧
        η (frontier (⋃ n, E n)) = 0 ∧ η (frontier (A ∩ ⋃ n, E n)) = 0) :
    ∃ f : S → ℕ → (RawMeanZeroTest → ℝ) × ℂ → ℝ,
      (∀ A n, Measurable (f A n)) ∧ ∀ A, TendstoInMeasure
        (P ⊗ₘ weightedRestrictionKernel P ν (hh.aemeasurable_lqgMeasure hν)
          (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const)
        (fun n x => f A n ((fun φ : RawMeanZeroTest => hC x.1 φ.1), x.2)) atTop
        (fun x => (normalizedRestriction
          ((ν x.1).map (fun v : ℂ => v - x.2)) (ball 0 ε) A.val).toReal) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let hm := hh.aemeasurable_lqgMeasure hν
  let K := weightedRestrictionKernel P ν hm (ball 0 1) measurableSet_ball
    (fun _ => 1) measurable_const
  have hsub : ∀ n, E n ⊆ ball 0 ε := by
    intro n
    rw [← hunion]
    exact subset_iUnion E n
  obtain ⟨F, hFm, hFeq⟩ := hh.exists_raw_rooted_normalizedLQGApprox (γ := γ)
    (ball 0 1) E hEm (unitBall_rooted_dyadic_buffer hε E hsub)
  have hFeq' : ∀ᵐ x ∂(P ⊗ₘ K), ∀ n,
      F n ((fun φ : RawMeanZeroTest => hC x.1 φ.1), x.2) =
        normalizedRestriction (lqgApprox γ (fun r z => hcirc x.1 r (z + x.2))
          (dyadicScale n)) (E n) := by
    filter_upwards [ae_fst_of_ae_compProd P K hFeq,
      ae_mem_weightedRestriction_compProd P ν hm (ball 0 1) measurableSet_ball
        (fun _ => 1) measurable_const] with x hx hz
    exact hx x.2 hz
  have hX : Measurable (fun x : Ω × ℂ =>
      ((fun φ : RawMeanZeroTest => hC x.1 φ.1), x.2)) := by
    apply Measurable.prodMk
    · apply measurable_pi_iff.mpr
      intro φ
      exact (hh.measurable_pairing φ.1 φ.2.1).comp measurable_fst
    · exact measurable_snd
  have hmass' : ∀ᵐ ω ∂P, ((ν ω).withDensity (fun _ => 1)) (ball 0 1) ≠ 0 ∧
      ((ν ω).withDensity (fun _ => 1)) (ball 0 1) ≠ ∞ := by
    filter_upwards [hmass, hν] with ω hω hνω
    let : IsLocallyFiniteMeasure (ν ω) := hνω.isLocallyFiniteMeasure
    simp only [withDensity_const, one_smul]
    exact ⟨hω, measure_ball_ne_top⟩
  have hc : ∀ᵐ ω ∂P, ∀ n, Continuous (hcirc ω (dyadicScale n)) := by
    have h := ae_all_iff.mpr fun n => hh.ae_continuous_fieldCircleAverage 0 (dyadicScale_pos n)
    simpa only [fieldCircleAverage, zero_mul, sub_zero] using h
  have hν' : IsLQGMeasure P γ hcirc ν := by
    have heq : (fun ω => fieldCircleAverage 0 (hcirc ω)) = hcirc := by
      funext ω r z
      simp [fieldCircleAverage]
    change IsLQGMeasure P γ (fun ω => fieldCircleAverage 0 (hcirc ω)) ν at hν
    rw [heq] at hν
    exact hν
  refine ⟨fun A n p => (F n p A.val).toReal, ?_, ?_⟩
  · intro A n
    exact ENNReal.measurable_toReal.comp ((Measure.measurable_coe (hsets A A.property)).comp (hFm n))
  · exact tendstoInMeasure_rooted_normalizedMass_of_approximation P hcirc ν hm hν' hc
      (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const hmass' hε E hmono hunion
      S hsets hfront _ hX F hFm hFeq'

/-- A measurable unit-ball frequency certificate exists without assuming a
rooted mass decoder. Its radius can be chosen below any positive bound. -/
theorem IsWholePlaneGFF.exists_unitBall_frequency_certificate
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ β : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {ν : Ω → Measure ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hν : IsLQGMeasureOfField P γ 0 hcirc ν)
    (hmass : ∀ᵐ ω ∂P, ν ω (ball 0 1) ≠ 0) {R : ℝ} (hR : 0 < R)
    (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ) (ha : 0 < a) :
    ∃ ε ∈ Ioo (0 : ℝ) R, ∃ E : Set ((RawMeanZeroTest → ℝ) × ℂ),
      MeasurableSet E ∧ ∀ᵐ ω ∂P, ∀ᵐ z ∂ν ω, z ∈ ball 0 1 →
        (((fun φ : RawMeanZeroTest => hC ω φ.1), z) ∈ E ↔
          ∀ᶠ K : ℕ in atTop, (1 - ζ) * (K : ℝ) ≤
            (veryGoodComparableScaleCount (ν ω) β z N₀ a b C₁m C₁p C₂m C₂p C₃ m K : ℝ)) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let hm := hh.aemeasurable_lqgMeasure hν
  let K := weightedRestrictionKernel P ν hm (ball 0 1) measurableSet_ball
    (fun _ => 1) measurable_const
  have hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (ν ω) :=
    hν.mono fun _ h => h.isLocallyFiniteMeasure
  have hmass' : ∀ᵐ ω ∂P, ((ν ω).withDensity (fun _ => 1)) (ball 0 1) ≠ 0 ∧
      ((ν ω).withDensity (fun _ => 1)) (ball 0 1) ≠ ∞ := by
    filter_upwards [hmass, hloc] with ω hω hνω
    let : IsLocallyFiniteMeasure (ν ω) := hνω
    simp only [withDensity_const, one_smul]
    exact ⟨hω, measure_ball_ne_top⟩
  let : IsProbabilityMeasure (P ⊗ₘ K) :=
    isProbabilityMeasure_weightedRestriction_compProd P ν hm (ball 0 1)
      measurableSet_ball (fun _ => 1) measurable_const hmass'
  let η : Ω × ℂ → Measure ℂ := fun x => (ν x.1).map (fun v : ℂ => v - x.2)
  have hη := aemeasurable_recentered_of_weightedRestriction_compProd P ν hm hloc
    (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const
  obtain ⟨ε, hε, S, hcount, hpi, _, hopen, hgen, U, hUm, hmono, hunion, _, hfront⟩ :=
    exists_recentered_continuity_system (P ⊗ₘ K) η hη.1 hη.2 (fun _ => 0)
      measurable_const hR
  have hsets : ∀ A ∈ S, MeasurableSet A := fun A hA => (hopen A hA).measurableSet
  have hfront' : ∀ A ∈ S, ∀ᵐ x ∂(P ⊗ₘ K),
      (∀ n, η x (frontier (U n)) = 0 ∧ η x (frontier (A ∩ U n)) = 0) ∧
        η x (frontier (⋃ n, U n)) = 0 ∧ η x (frontier (A ∩ ⋃ n, U n)) = 0 := by
    intro A hA
    filter_upwards [hfront] with x hx
    have hid : (fun v : ℂ => v - 0) = id := by funext v; simp
    simpa only [hid, Measure.map_id] using hx A hA
  obtain ⟨f, hf, hlim⟩ := hh.exists_unitBall_rooted_mass_approximations hν hmass
    hε.1 U hUm hmono hunion S hsets hfront'
  obtain ⟨E, hE, hEae⟩ := hh.exists_unitBall_observed_frequency_certificate hν hmass
    ε hε.1 S hcount hgen hpi hsets f hf hlim N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ ha
  exact ⟨ε, hε, E, hE, hEae⟩

end HarmonicBalls
