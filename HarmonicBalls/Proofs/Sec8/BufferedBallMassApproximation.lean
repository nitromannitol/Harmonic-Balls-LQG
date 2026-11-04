import HarmonicBalls.Proofs.Sec8.LocalNormalizedMassApproximation
import HarmonicBalls.Proofs.Sec8.ContinuityExhaustion
import HarmonicBalls.Proofs.Sec8.OpenBallDensity
import HarmonicBalls.Proofs.Sec6.BufferedExhaustion

/-! # Buffered mass approximations on a continuity ball

The imported Section 8 argument uses Leonardo Bonanno's LatticeProb
formalization of the ergodic theorem.
-/

open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

namespace HarmonicBalls

/-- A ball with almost surely null LQG boundary admits an exhaustion by
continuity sets buffered at the dyadic circle-average scales. -/
theorem IsWholePlaneGFF.exists_buffered_lqg_ball_exhaustion
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ ε : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) (hε : 0 < ε)
    (hfront : ∀ᵐ ω ∂P, μ ω (frontier (ball (0 : ℂ) ε)) = 0) :
    ∃ E : ℕ → Set ℂ, (∀ n, MeasurableSet (E n)) ∧ Monotone E ∧
      (⋃ n, E n) = ball 0 ε ∧
      (∀ n z, z ∈ E n → closedBall z (dyadicScale n) ⊆ ball 0 ε) ∧
      ∀ᵐ ω ∂P, (∀ n, μ ω (frontier (E n)) = 0) ∧
        μ ω (frontier (⋃ n, E n)) = 0 := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  obtain ⟨s, hsmono, hsrange, hslim⟩ := exists_seq_strictMono_tendsto' hε
  obtain ⟨r, hr, hnull⟩ := hGFF.exists_ae_lqg_null_frontier_balls_unbounded P hμ
    (fun _ => 0) s (fun n => s (n + 1)) (fun n => hsmono (Nat.lt_succ_self n))
  have hrmono : Monotone r := by
    apply StrictMono.monotone
    intro i j hij
    exact lt_trans (hr i).2 (lt_of_le_of_lt (hsmono.monotone (Nat.succ_le_of_lt hij)) (hr j).1)
  have hrlt (n : ℕ) : r n < ε := lt_trans (hr n).2 (hsrange (n + 1)).2
  have hrlim : Tendsto r atTop (𝓝 ε) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hslim tendsto_const_nhds
      (fun n => (hr n).1.le) (fun n => (hrlt n).le)
  let B : ℕ → Set ℂ := fun n => ball 0 (r n)
  have hBmono : Monotone B := fun _ _ hij => ball_subset_ball (hrmono hij)
  have hBunion : (⋃ n, B n) = ball 0 ε :=
    iUnion_ball_of_tendsto_radius 0 r ε (fun n => (hrlt n).le) hrlim
  have hBbuffer : ∀ k, ∃ δ : ℝ, 0 < δ ∧
      ∀ z ∈ B k, closedBall z δ ⊆ ball 0 ε := by
    intro k
    refine ⟨(ε - r k) / 2, by linarith [hrlt k], ?_⟩
    intro z hz w hw
    have hz' : dist z 0 < r k := mem_ball.mp hz
    have hw' : dist w z ≤ (ε - r k) / 2 := mem_closedBall.mp hw
    have ht := dist_triangle w z (0 : ℂ)
    rw [mem_ball]
    linarith [hrlt k]
  have hlim : Tendsto dyadicScale atTop (𝓝 0) :=
    tendsto_dyadicScale_nhdsGT.mono_right nhdsWithin_le_nhds
  obtain ⟨E, hmono, hunion, hchoice, hbuffer⟩ :=
    Section6.exists_buffered_exhaustion B (ball 0 ε) hBmono hBbuffer dyadicScale hlim
  refine ⟨E, ?_, hmono, hunion.trans hBunion, hbuffer, ?_⟩
  · intro n
    rcases hchoice n with h | ⟨k, h⟩
    · rw [h]; exact MeasurableSet.empty
    · rw [h]; exact isOpen_ball.measurableSet
  · filter_upwards [hnull, hfront] with ω hnullω hfrontω
    refine ⟨?_, ?_⟩
    · intro n
      rcases hchoice n with h | ⟨k, h⟩
      · simp [h, frontier_empty]
      · simpa only [h] using hnullω k
    · simpa only [hunion, hBunion] using hfrontω

/-- On a positive-mass LQG continuity ball, one may choose a countable
continuity π-system and measurable local-field approximants for all its
normalized masses. -/
theorem IsWholePlaneGFF.exists_localPairing_normalizedMass_continuity_system
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ ε : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) (hε : 0 < ε)
    (hfront : ∀ᵐ ω ∂P, μ ω (frontier (ball (0 : ℂ) ε)) = 0)
    (hpos : ∀ᵐ ω ∂P, μ ω (ball (0 : ℂ) ε) ≠ 0) :
    ∃ S : Set (Set ℂ), S.Countable ∧
      (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom S ∧
      IsPiSystem S ∧ (∀ A ∈ S, MeasurableSet A) ∧ univ ∈ S ∧
      ∃ f : S → ℕ → (Section6.LocalTest (ball 0 ε) → ℝ) → ℝ,
        (∀ A n, Measurable (f A n)) ∧ ∀ A,
          TendstoInMeasure P (fun n ω => f A n (Section6.localPairingProc (ball 0 ε) hC ω))
            atTop (fun ω => (normalizedRestriction (μ ω) (ball 0 ε) A.val).toReal) := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  obtain ⟨E, hEm, hmono, hunion, hbuffer, hEfront⟩ :=
    hGFF.exists_buffered_lqg_ball_exhaustion hμ hε hfront
  obtain ⟨S, hcount, hpi, huniv, hopen, hgen, hSfront⟩ :=
    hGFF.exists_ae_lqg_continuity_piSystem P hμ
  have hfronts := ae_frontiers_intersections_of_common_continuity P μ E S hEfront hSfront
  have hbounded : Bornology.IsBounded (⋃ n, E n) := by
    rw [hunion]
    exact isBounded_ball
  have hpositive : ∀ᵐ ω ∂P, μ ω (⋃ n, E n) ≠ 0 ∧ μ ω (⋃ n, E n) ≠ ∞ := by
    filter_upwards [hμ, hpos] with ω hω hp
    let : IsLocallyFiniteMeasure (μ ω) := hω.isLocallyFiniteMeasure
    rw [hunion]
    exact ⟨hp, measure_ball_lt_top.ne⟩
  refine ⟨S, hcount, hgen, hpi, fun A hA => (hopen A hA).measurableSet, huniv, ?_⟩
  apply hGFF.exists_localPairing_normalizedMass_approximations hμ E hEm hmono hbounded
    hbuffer hunion S (fun A hA => (hopen A hA).measurableSet) ?_ hpositive
  intro A hA
  filter_upwards [hfronts] with ω hω
  exact hω A hA

/-- Every neighborhood contains a continuity ball for which the local
pairing process supplies normalized mass approximants. -/
theorem IsWholePlaneGFF.exists_localPairing_normalizedMass_continuity_system_inside
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ R : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) (hR : 0 < R)
    (hpos : ∀ᵐ ω ∂P, ∀ r : ℝ, 0 < r → μ ω (ball (0 : ℂ) r) ≠ 0) :
    ∃ ε ∈ Ioo (0 : ℝ) R, ∃ S : Set (Set ℂ), S.Countable ∧
      (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom S ∧
      IsPiSystem S ∧ (∀ A ∈ S, MeasurableSet A) ∧ univ ∈ S ∧
      ∃ f : S → ℕ → (Section6.LocalTest (ball 0 ε) → ℝ) → ℝ,
        (∀ A n, Measurable (f A n)) ∧ ∀ A,
          TendstoInMeasure P (fun n ω => f A n (Section6.localPairingProc (ball 0 ε) hC ω))
            atTop (fun ω => (normalizedRestriction (μ ω) (ball 0 ε) A.val).toReal) := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  obtain ⟨r, hr, hfront⟩ := hGFF.exists_ae_lqg_null_frontier_balls_unbounded P hμ
    (fun _ => 0) (fun _ => 0) (fun _ => R) (fun _ => hR)
  have hpos' : ∀ᵐ ω ∂P, μ ω (ball (0 : ℂ) (r 0)) ≠ 0 := by
    filter_upwards [hpos] with ω hω
    exact hω (r 0) (hr 0).1
  have hfront' : ∀ᵐ ω ∂P, μ ω (frontier (ball (0 : ℂ) (r 0))) = 0 := by
    filter_upwards [hfront] with ω hω
    exact hω 0
  exact ⟨r 0, hr 0,
    hGFF.exists_localPairing_normalizedMass_continuity_system hμ (hr 0).1 hfront' hpos'⟩

#print axioms IsWholePlaneGFF.exists_buffered_lqg_ball_exhaustion
#print axioms IsWholePlaneGFF.exists_localPairing_normalizedMass_continuity_system
#print axioms IsWholePlaneGFF.exists_localPairing_normalizedMass_continuity_system_inside

end HarmonicBalls
