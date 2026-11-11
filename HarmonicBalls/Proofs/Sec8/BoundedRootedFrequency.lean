import HarmonicBalls.Proofs.Sec8.RawRootedApproximation

/-! # Bounded-root frequency certificates

The field/root certificate applies to arbitrary origin-centered sampling balls.
The imported Section 8 development uses Leonardo Bonanno's LatticeProb
formalization of the ergodic theorem.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal Topology

/-- Circles around roots in a bounded sampling ball have a common buffer. -/
theorem ball_rooted_dyadic_buffer {ε s : ℝ}
    (hε : 0 < ε) (E : ℕ → Set ℂ) (hE : ∀ n, E n ⊆ ball 0 ε) :
    ∀ n z, z ∈ ball (0 : ℂ) s →
      closedBall z (dyadicScale n) ⊆ ball 0 (ε + s + 2) ∧
      ∀ x ∈ E n, closedBall (x + z) (dyadicScale n) ⊆ ball 0 (ε + s + 2) := by
  have hscale (n : ℕ) : dyadicScale n ≤ 1 := by
    unfold dyadicScale
    exact pow_le_one₀ (by norm_num) (by norm_num)
  intro n z hz
  have hz' : dist z 0 < s := mem_ball.mp hz
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

/-- On rooted continuity sets, the normalized masses are limits in measure
of jointly measurable functions of the raw mean-zero field and the root. -/
theorem IsWholePlaneGFF.exists_ball_rooted_mass_approximations
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ ε : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {ν : Ω → Measure ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hν : IsLQGMeasureOfField P γ 0 hcirc ν)
    (s : ℝ) (hmass : ∀ᵐ ω ∂P, ν ω (ball 0 s) ≠ 0) (hε : 0 < ε)
    (E : ℕ → Set ℂ) (hEm : ∀ n, MeasurableSet (E n)) (hmono : Monotone E)
    (hunion : (⋃ n, E n) = ball 0 ε)
    (S : Set (Set ℂ)) (hsets : ∀ A ∈ S, MeasurableSet A)
    (hfront : ∀ A ∈ S, ∀ᵐ x ∂(P ⊗ₘ weightedRestrictionKernel P ν
      (hh.aemeasurable_lqgMeasure hν) (ball 0 s) measurableSet_ball
      (fun _ => 1) measurable_const),
      let η := (ν x.1).map (fun v : ℂ => v - x.2)
      (∀ n, η (frontier (E n)) = 0 ∧ η (frontier (A ∩ E n)) = 0) ∧
        η (frontier (⋃ n, E n)) = 0 ∧ η (frontier (A ∩ ⋃ n, E n)) = 0) :
    ∃ f : S → ℕ → (RawMeanZeroTest → ℝ) × ℂ → ℝ,
      (∀ A n, Measurable (f A n)) ∧ ∀ A, TendstoInMeasure
        (P ⊗ₘ weightedRestrictionKernel P ν (hh.aemeasurable_lqgMeasure hν)
          (ball 0 s) measurableSet_ball (fun _ => 1) measurable_const)
        (fun n x => f A n ((fun φ : RawMeanZeroTest => hC x.1 φ.1), x.2)) atTop
        (fun x => (normalizedRestriction
          ((ν x.1).map (fun v : ℂ => v - x.2)) (ball 0 ε) A.val).toReal) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let hm := hh.aemeasurable_lqgMeasure hν
  let K := weightedRestrictionKernel P ν hm (ball 0 s) measurableSet_ball
    (fun _ => 1) measurable_const
  have hsub : ∀ n, E n ⊆ ball 0 ε := by
    intro n
    rw [← hunion]
    exact subset_iUnion E n
  obtain ⟨F, hFm, hFeq⟩ := hh.exists_raw_rooted_normalizedLQGApprox (γ := γ)
    (ball 0 s) E hEm (ball_rooted_dyadic_buffer hε E hsub)
  have hFeq' : ∀ᵐ x ∂(P ⊗ₘ K), ∀ n,
      F n ((fun φ : RawMeanZeroTest => hC x.1 φ.1), x.2) =
        normalizedRestriction (lqgApprox γ (fun r z => hcirc x.1 r (z + x.2))
          (dyadicScale n)) (E n) := by
    filter_upwards [ae_fst_of_ae_compProd P K hFeq,
      ae_mem_weightedRestriction_compProd P ν hm (ball 0 s) measurableSet_ball
        (fun _ => 1) measurable_const] with x hx hz
    exact hx x.2 hz
  have hX : Measurable (fun x : Ω × ℂ =>
      ((fun φ : RawMeanZeroTest => hC x.1 φ.1), x.2)) := by
    apply Measurable.prodMk
    · apply measurable_pi_iff.mpr
      intro φ
      exact (hh.measurable_pairing φ.1 φ.2.1).comp measurable_fst
    · exact measurable_snd
  have hmass' : ∀ᵐ ω ∂P, ((ν ω).withDensity (fun _ => 1)) (ball 0 s) ≠ 0 ∧
      ((ν ω).withDensity (fun _ => 1)) (ball 0 s) ≠ ∞ := by
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
      (ball 0 s) measurableSet_ball (fun _ => 1) measurable_const hmass' hε E hmono hunion
      S hsets hfront _ hX F hFm hFeq'

/-- Convergent observed normalized-mass approximations give a measurable
ball frequency certificate. The convergence premise remains explicit. -/
theorem IsWholePlaneGFF.exists_ball_observed_frequency_certificate
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ β : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {ν : Ω → Measure ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hν : IsLQGMeasureOfField P γ 0 hcirc ν)
    (s : ℝ) (hmass : ∀ᵐ ω ∂P, ν ω (ball 0 s) ≠ 0)
    (ε : ℝ) (hε : 0 < ε)
    (S : Set (Set ℂ)) (hcount : S.Countable)
    (hgen : (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom S)
    (hpi : IsPiSystem S) (hsets : ∀ V ∈ S, MeasurableSet V)
    (f : S → ℕ → (RawMeanZeroTest → ℝ) × ℂ → ℝ) (hf : ∀ V n, Measurable (f V n))
    (hlim : ∀ V, TendstoInMeasure
      (P ⊗ₘ weightedRestrictionKernel P ν (hh.aemeasurable_lqgMeasure hν)
        (ball 0 s) measurableSet_ball (fun _ => 1) measurable_const)
      (fun n x => f V n ((fun φ : RawMeanZeroTest => hC x.1 φ.1), x.2)) atTop
      (fun x => (normalizedRestriction
        ((ν x.1).map (fun v : ℂ => v - x.2)) (ball 0 ε) V.val).toReal))
    (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ) (ha : 0 < a) :
    ∃ E : Set ((RawMeanZeroTest → ℝ) × ℂ), MeasurableSet E ∧
      ∀ᵐ ω ∂P, ∀ᵐ z ∂ν ω, z ∈ ball 0 s →
        (((fun φ : RawMeanZeroTest => hC ω φ.1), z) ∈ E ↔
          ∀ᶠ K : ℕ in atTop, (1 - ζ) * (K : ℝ) ≤
            (veryGoodComparableScaleCount (ν ω) β z N₀ a b C₁m C₁p C₂m C₂p C₃ m K : ℝ)) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let X : Ω → RawMeanZeroTest → ℝ := fun ω φ => hC ω φ.1
  have hX : Measurable X := by
    apply measurable_pi_iff.mpr
    intro φ
    exact hh.measurable_pairing φ.1 φ.2.1
  have hνmeas := hh.aemeasurable_lqgMeasure hν
  have hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (ν ω) :=
    hν.mono fun _ h => h.isLocallyFiniteMeasure
  have hfin : ∀ᵐ ω ∂P, ((ν ω).withDensity (fun _ => 1)) (ball 0 s) ≠ ∞ := by
    filter_upwards [hloc] with ω hω
    let : IsLocallyFiniteMeasure (ν ω) := hω
    simpa only [withDensity_const, one_smul] using
      (measure_ball_ne_top : ν ω (ball (0 : ℂ) s) ≠ ∞)
  have hmass' : ∀ᵐ ω ∂P, ((ν ω).withDensity (fun _ => 1)) (ball 0 s) ≠ 0 ∧
      ((ν ω).withDensity (fun _ => 1)) (ball 0 s) ≠ ∞ := by
    filter_upwards [hmass, hfin] with ω hω hfω
    exact ⟨by simpa only [withDensity_const, one_smul] using hω, hfω⟩
  obtain ⟨E, hE, hEae⟩ := exists_observed_frequency_event_weightedRestriction_compProd
    P ν hνmeas hloc (ball 0 s) measurableSet_ball (fun _ => 1) measurable_const hmass'
    X hX ε hε S hcount hgen hpi hsets f hf hlim β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ
    (measurableSet_isGoodAnnulus_of_pos 1 (by norm_num) 0 a b ha)
  refine ⟨E, hE, ?_⟩
  apply ae_ae_of_rooted_weighted_restriction P ν
    (weightedRestrictionKernel P ν hνmeas (ball 0 s) measurableSet_ball
      (fun _ => 1) measurable_const) (ball 0 s) measurableSet_ball
    (fun _ => 1) measurable_const ?_ hfin
    (ae_weightedRestrictionKernel_eq P ν hνmeas (ball 0 s) measurableSet_ball
      (fun _ => 1) measurable_const) _ Measure.AbsolutelyContinuous.rfl hEae
  filter_upwards with ω
  filter_upwards with z
  exact one_ne_zero

/-- A measurable ball frequency certificate exists without assuming a
rooted mass decoder. Its radius can be chosen below any positive bound. -/
theorem IsWholePlaneGFF.exists_ball_frequency_certificate
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ β : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {ν : Ω → Measure ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hν : IsLQGMeasureOfField P γ 0 hcirc ν)
    (s : ℝ) (hmass : ∀ᵐ ω ∂P, ν ω (ball 0 s) ≠ 0) {R : ℝ} (hR : 0 < R)
    (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ) (ha : 0 < a) :
    ∃ ε ∈ Ioo (0 : ℝ) R, ∃ E : Set ((RawMeanZeroTest → ℝ) × ℂ),
      MeasurableSet E ∧ ∀ᵐ ω ∂P, ∀ᵐ z ∂ν ω, z ∈ ball 0 s →
        (((fun φ : RawMeanZeroTest => hC ω φ.1), z) ∈ E ↔
          ∀ᶠ K : ℕ in atTop, (1 - ζ) * (K : ℝ) ≤
            (veryGoodComparableScaleCount (ν ω) β z N₀ a b C₁m C₁p C₂m C₂p C₃ m K : ℝ)) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let hm := hh.aemeasurable_lqgMeasure hν
  let K := weightedRestrictionKernel P ν hm (ball 0 s) measurableSet_ball
    (fun _ => 1) measurable_const
  have hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (ν ω) :=
    hν.mono fun _ h => h.isLocallyFiniteMeasure
  have hmass' : ∀ᵐ ω ∂P, ((ν ω).withDensity (fun _ => 1)) (ball 0 s) ≠ 0 ∧
      ((ν ω).withDensity (fun _ => 1)) (ball 0 s) ≠ ∞ := by
    filter_upwards [hmass, hloc] with ω hω hνω
    let : IsLocallyFiniteMeasure (ν ω) := hνω
    simp only [withDensity_const, one_smul]
    exact ⟨hω, measure_ball_ne_top⟩
  let : IsProbabilityMeasure (P ⊗ₘ K) :=
    isProbabilityMeasure_weightedRestriction_compProd P ν hm (ball 0 s)
      measurableSet_ball (fun _ => 1) measurable_const hmass'
  let η : Ω × ℂ → Measure ℂ := fun x => (ν x.1).map (fun v : ℂ => v - x.2)
  have hη := aemeasurable_recentered_of_weightedRestriction_compProd P ν hm hloc
    (ball 0 s) measurableSet_ball (fun _ => 1) measurable_const
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
  obtain ⟨f, hf, hlim⟩ := hh.exists_ball_rooted_mass_approximations hν s hmass
    hε.1 U hUm hmono hunion S hsets hfront'
  obtain ⟨E, hE, hEae⟩ := hh.exists_ball_observed_frequency_certificate hν s hmass
    ε hε.1 S hcount hgen hpi hsets f hf hlim N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ ha
  exact ⟨ε, hε, E, hE, hEae⟩


/-- A single measurable field/root event represents the frequency at almost
every point of the regular LQG measure over the entire plane. Positive mass
in the unit ball supplies positive mass in each ball of the covering. -/
theorem IsWholePlaneGFF.exists_global_frequency_certificate
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ β : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {ν : Ω → Measure ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hν : IsLQGMeasureOfField P γ 0 hcirc ν)
    (hmass : ∀ᵐ ω ∂P, ν ω (ball 0 1) ≠ 0)
    (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ) (ha : 0 < a) :
    ∃ E : Set ((RawMeanZeroTest → ℝ) × ℂ), MeasurableSet E ∧
      ∀ᵐ ω ∂P, ∀ᵐ z ∂ν ω,
        (((fun φ : RawMeanZeroTest => hC ω φ.1), z) ∈ E ↔
          ∀ᶠ K : ℕ in atTop, (1 - ζ) * (K : ℝ) ≤
            (veryGoodComparableScaleCount (ν ω) β z N₀ a b C₁m C₁p C₂m C₂p C₃ m K : ℝ)) := by
  have hex (n : ℕ) : ∃ E : Set ((RawMeanZeroTest → ℝ) × ℂ), MeasurableSet E ∧
      ∀ᵐ ω ∂P, ∀ᵐ z ∂ν ω, z ∈ ball 0 ((n : ℝ) + 1) →
        (((fun φ : RawMeanZeroTest => hC ω φ.1), z) ∈ E ↔
          ∀ᶠ K : ℕ in atTop, (1 - ζ) * (K : ℝ) ≤
            (veryGoodComparableScaleCount (ν ω) β z N₀ a b C₁m C₁p C₂m C₂p C₃ m K : ℝ)) := by
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have hx : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hmassn : ∀ᵐ ω ∂P, ν ω (ball 0 ((n : ℝ) + 1)) ≠ 0 := by
      filter_upwards [hmass] with ω hω hzero
      exact hω (measure_mono_null (ball_subset_ball hn) hzero)
    obtain ⟨_, _, E, hE, hEq⟩ := hh.exists_ball_frequency_certificate hν
      ((n : ℝ) + 1) hmassn (by norm_num : (0 : ℝ) < 1)
      N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ ha
    exact ⟨E, hE, hEq⟩
  choose E hEm hEq using hex
  refine ⟨⋃ n, E n ∩ {p : (RawMeanZeroTest → ℝ) × ℂ | p.2 ∈ ball 0 ((n : ℝ) + 1)}, ?_, ?_⟩
  · exact MeasurableSet.iUnion fun n => (hEm n).inter (measurableSet_ball.preimage measurable_snd)
  · filter_upwards [ae_all_iff.mpr hEq] with ω hω
    filter_upwards [ae_all_iff.mpr hω] with z hz
    constructor
    · intro h
      obtain ⟨n, hE, hball⟩ := mem_iUnion.mp h
      exact (hz n hball).mp hE
    · intro h
      obtain ⟨n, hn⟩ := exists_nat_gt (dist z (0 : ℂ))
      have hball : z ∈ ball (0 : ℂ) ((n : ℝ) + 1) := by
        rw [mem_ball]
        linarith
      exact mem_iUnion.mpr ⟨n, (hz n hball).mpr h, hball⟩

/-- For any observed rooted-law comparisons on the expanding balls, a
fixed-root estimate for the constructed certificate implies the global
regular-measure frequency estimate. -/
theorem IsWholePlaneGFF.exists_global_frequency_certificate_of_root_reference
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} {γ β : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {ν : Ω → Measure ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hν : IsLQGMeasureOfField P γ 0 hcirc ν)
    (hmass : ∀ᵐ ω ∂P, ν ω (ball 0 1) ≠ 0)
    (ρ : ℕ → Measure ℂ) (Q : Measure Ξ) [SFinite Q]
    (shift : ℕ → ℂ × Ξ → RawMeanZeroTest → ℝ) (hshift : ∀ n, Measurable (shift n))
    (R : ℕ → ℂ → Measure (RawMeanZeroTest → ℝ))
    (hrooted : ∀ n : ℕ, (P.bind fun ω => ((ν ω).restrict (ball 0 ((n : ℝ) + 1))).map
      (fun z => ((fun φ : RawMeanZeroTest => hC ω φ.1), z))) ≪
        shiftedRootReferenceLaw (ρ n) Q (shift n))
    (hac : ∀ n, ∀ᵐ z ∂ρ n, Q.map (fun ω => shift n (z, ω)) ≪ R n z)
    (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ) (ha : 0 < a) :
    ∃ E : Set ((RawMeanZeroTest → ℝ) × ℂ), MeasurableSet E ∧
      ((∀ n, ∀ᵐ z ∂ρ n, ∀ᵐ f ∂(R n z), (f, z) ∈ E) →
        ∀ᵐ ω ∂P, ∀ᵐ z ∂ν ω, ∀ᶠ K : ℕ in atTop,
          (1 - ζ) * (K : ℝ) ≤
            (veryGoodComparableScaleCount (ν ω) β z N₀ a b C₁m C₁p C₂m C₂p C₃ m K : ℝ)) := by
  let X : Ω → RawMeanZeroTest → ℝ := fun ω φ => hC ω φ.1
  have hX : Measurable X := by
    apply measurable_pi_iff.mpr
    intro φ
    exact hh.measurable_pairing φ.1 φ.2.1
  have hfin : ∀ n : ℕ, ∀ᵐ ω ∂P, ν ω (ball 0 ((n : ℝ) + 1)) ≠ ∞ := by
    intro n
    filter_upwards [hν] with ω hω
    let : IsLocallyFiniteMeasure (ν ω) := hω.isLocallyFiniteMeasure
    exact measure_ball_ne_top
  have hcover : ∀ z : ℂ, ∃ n : ℕ, z ∈ ball 0 ((n : ℝ) + 1) := by
    intro z
    obtain ⟨n, hn⟩ := exists_nat_gt (dist z (0 : ℂ))
    exact ⟨n, mem_ball.mpr (by linarith)⟩
  obtain ⟨E, hE, hcert⟩ := hh.exists_global_frequency_certificate hν hmass
    N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ ha
  refine ⟨E, hE, fun hfixed => ?_⟩
  have ht := ae_ae_of_observed_root_reference_cover P ν (hh.aemeasurable_lqgMeasure hν)
    X hX (fun n => ball 0 ((n : ℝ) + 1)) (fun _ => measurableSet_ball) hcover hfin
    ρ Q shift hshift R (p := fun x => x ∈ E) hE hrooted hac hfixed
  filter_upwards [ht, hcert] with ω hω hc
  filter_upwards [hω, hc] with z hz hcz
  exact hcz.mp hz

end HarmonicBalls
