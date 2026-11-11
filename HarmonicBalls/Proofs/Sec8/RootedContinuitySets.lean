import HarmonicBalls.Proofs.Sec8.RandomMeasureContinuitySets
import HarmonicBalls.Proofs.Sec8.ObservedFrequencyEvent
import HarmonicBalls.Proofs.Sec8.CenteredMeasureLaw
import HarmonicBalls.Proofs.Sec8.BufferedBallMassApproximation

/-! # Continuity sets for recentered random measures

The phase-frequency argument uses Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization. The results here apply to any
probability law on a random measure and its root.
-/

open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

namespace HarmonicBalls

/-- Countably many balls can be chosen with almost surely null frontiers for
any locally finite random measure. -/
theorem exists_ae_null_frontier_balls_of_ae_locallyFinite
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (x : ℕ → ℂ) (a b : ℕ → ℝ) (hab : ∀ n, a n < b n) :
    ∃ r : ℕ → ℝ, (∀ n, r n ∈ Ioo (a n) (b n)) ∧
      ∀ᵐ ω ∂P, ∀ n, μ ω (frontier (ball (x n) (r n))) = 0 := by
  apply exists_ae_null_frontier_balls_of_localizations P μ hμ
    (fun n => ball 0 (dist (x n) 0 + max (b n) 0 + 1))
    (fun _ => measurableSet_ball) ?_ x a b hab
  · intro n r hr z hz
    have hs := frontier_ball_subset_sphere hz
    rw [mem_sphere] at hs
    rw [mem_ball]
    have ht := dist_triangle z (x n) 0
    have hb := le_max_left (b n) (0 : ℝ)
    linarith [hr.2]
  · intro n
    filter_upwards [hloc] with ω hω
    let : IsLocallyFiniteMeasure (μ ω) := hω
    exact measure_ball_lt_top.ne

/-- A locally finite random measure admits a deterministic countable open
generating π-system consisting of almost sure continuity sets. -/
theorem exists_ae_continuity_piSystem_of_ae_locallyFinite
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω)) :
    ∃ T : Set (Set ℂ), T.Countable ∧ IsPiSystem T ∧ univ ∈ T ∧
      (∀ A ∈ T, IsOpen A) ∧
      (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom T ∧
      ∀ᵐ ω ∂P, ∀ A ∈ T, μ ω (frontier A) = 0 := by
  obtain ⟨c, hc⟩ := TopologicalSpace.exists_dense_seq ℂ
  let x : ℕ → ℂ := fun n => c (Nat.unpair n).1
  let a : ℕ → ℝ := fun n => 1 / (2 * ((Nat.unpair n).2 + 1 : ℝ))
  let b : ℕ → ℝ := fun n => 1 / ((Nat.unpair n).2 + 1 : ℝ)
  have hab (n : ℕ) : a n < b n := by
    dsimp [a, b]
    have hp : (0 : ℝ) < ((Nat.unpair n).2 : ℝ) + 1 := by positivity
    apply div_lt_div_of_pos_left (by norm_num) (by positivity)
    linarith
  obtain ⟨r, hr, hz⟩ := exists_ae_null_frontier_balls_of_ae_locallyFinite P μ hμ hloc x a b hab
  let S : ℕ → Set ℂ := fun n => ball (x n) (r n)
  have hbasis : TopologicalSpace.IsTopologicalBasis (range S) :=
    isTopologicalBasis_selected_balls c hc r hr
  obtain ⟨T, hcount, hpi, huniv, hopen, hgen, hnull⟩ :=
    exists_common_continuity_piSystem P μ S (fun _ => isOpen_ball) hz
  refine ⟨T, hcount, hpi, huniv, hopen, ?_, hnull⟩
  calc
    (inferInstance : MeasurableSpace ℂ) = borel ℂ := BorelSpace.measurable_eq
    _ = MeasurableSpace.generateFrom (range S) := hbasis.borel_eq_generateFrom
    _ = MeasurableSpace.generateFrom T := hgen.symm

/-- A continuity ball has a dyadically buffered exhaustion by continuity
sets for any locally finite random measure. -/
theorem exists_buffered_ball_exhaustion_of_ae_locallyFinite
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω)) {ε : ℝ} (hε : 0 < ε)
    (hfront : ∀ᵐ ω ∂P, μ ω (frontier (ball (0 : ℂ) ε)) = 0) :
    ∃ E : ℕ → Set ℂ, (∀ n, MeasurableSet (E n)) ∧ Monotone E ∧
      (⋃ n, E n) = ball 0 ε ∧
      (∀ n z, z ∈ E n → closedBall z (dyadicScale n) ⊆ ball 0 ε) ∧
      ∀ᵐ ω ∂P, (∀ n, μ ω (frontier (E n)) = 0) ∧
        μ ω (frontier (⋃ n, E n)) = 0 := by
  obtain ⟨s, hsmono, hsrange, hslim⟩ := exists_seq_strictMono_tendsto' hε
  obtain ⟨r, hr, hnull⟩ := exists_ae_null_frontier_balls_of_ae_locallyFinite P μ hμ hloc
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

/-- Recentered measures under an arbitrary probability law have a common
continuity ball, a countable generating π-system, and a buffered exhaustion
whose intersections with the π-system are continuity sets. -/
theorem exists_recentered_continuity_system
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    (μ : A → Measure ℂ) (hμ : AEMeasurable μ P)
    (hloc : ∀ᵐ x ∂P, IsLocallyFiniteMeasure (μ x))
    (z : A → ℂ) (hz : Measurable z) {R : ℝ} (hR : 0 < R) :
    ∃ ε ∈ Ioo (0 : ℝ) R, ∃ T : Set (Set ℂ),
      T.Countable ∧ IsPiSystem T ∧ univ ∈ T ∧ (∀ V ∈ T, IsOpen V) ∧
      (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom T ∧
      ∃ E : ℕ → Set ℂ, (∀ n, MeasurableSet (E n)) ∧ Monotone E ∧
        (⋃ n, E n) = ball 0 ε ∧
        (∀ n w, w ∈ E n → closedBall w (dyadicScale n) ⊆ ball 0 ε) ∧
        ∀ᵐ x ∂P, let ν := (μ x).map (fun v : ℂ => v - z x)
          ∀ V ∈ T, (∀ n, ν (frontier (E n)) = 0 ∧
            ν (frontier (V ∩ E n)) = 0) ∧
            ν (frontier (⋃ n, E n)) = 0 ∧ ν (frontier (V ∩ ⋃ n, E n)) = 0 := by
  let ν : A → Measure ℂ := fun x => (μ x).map (fun v : ℂ => v - z x)
  obtain ⟨μ', hμm, hμloc, hμeq⟩ := Section6.exists_measurable_locallyFinite_rep hμ hloc
  have hmap : Measurable (fun x : A => (μ' x).map (fun v : ℂ => v - z x)) :=
    Section6.measurable_map_of_locallyFinite hμm hμloc (measurable_snd.sub (hz.comp measurable_fst))
  have hν : AEMeasurable ν P := by
    apply hmap.aemeasurable.congr
    filter_upwards [hμeq] with x hx
    exact congrArg (fun η : Measure ℂ => η.map (fun v : ℂ => v - z x)) hx.symm
  have hνloc : ∀ᵐ x ∂P, IsLocallyFiniteMeasure (ν x) := by
    filter_upwards [hloc] with x hx
    exact Section6.isLocallyFiniteMeasure_map_sub_right hx (z x)
  obtain ⟨r, hr, hnull⟩ := exists_ae_null_frontier_balls_of_ae_locallyFinite P ν hν hνloc
    (fun _ => 0) (fun _ => 0) (fun _ => R) (fun _ => hR)
  obtain ⟨T, hc, hp, hu, ho, hg, hT⟩ :=
    exists_ae_continuity_piSystem_of_ae_locallyFinite P ν hν hνloc
  have hfront : ∀ᵐ x ∂P, ν x (frontier (ball (0 : ℂ) (r 0))) = 0 :=
    hnull.mono fun _ hx => hx 0
  obtain ⟨E, hEm, hmono, hunion, hbuffer, hE⟩ :=
    exists_buffered_ball_exhaustion_of_ae_locallyFinite P ν hν hνloc (hr 0).1 hfront
  exact ⟨r 0, hr 0, T, hc, hp, hu, ho, hg, E, hEm, hmono, hunion, hbuffer,
    ae_frontiers_intersections_of_common_continuity P ν E T hE hT⟩

end HarmonicBalls
