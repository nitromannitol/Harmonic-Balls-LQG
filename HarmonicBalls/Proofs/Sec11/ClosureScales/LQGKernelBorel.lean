import Mathlib
import HarmonicBalls.Proofs.Sec11.ClosureScales.LQGKernelMeasurable

/-! # Route (A), Step M: the LQG measure as a random measure (open and Borel sets)

For `G` as in `exists_lqg_good_set`, `ω ↦ μ ω U` is measurable on `G` for every open `U ≠ ℂ` (`measurable_lqg_open`),
through increasing cutoff approximations `openApprox U m` of `1_U`, each in `C_c` (`measurable_integral_lqg_test`).
Borel sets follow by induction from open sets (`measurable_lqg_borel_ball`); the complement step uses that
`μ ω (ball 0 1) < ∞` (local finiteness of the LQG measure). The kernel `ω ↦ (μ ω).restrict (ball 0 1)` is then a
measurable `Measure ℂ`-valued map on `G` (`measurable_lqg_kernel`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Filter Topology
open scoped ENNReal NNReal

namespace HarmonicBalls

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Cutoff approximations of the indicator of an open set `U ⊆ ℂ` with `Uᶜ` nonempty: continuous, nonnegative,
supported in `closedBall 0 m`, increasing in `m`, and increasing to `1_U`. -/
def openApprox (U : Set ℂ) (m : ℕ) (z : ℂ) : ℝ :=
  min 1 ((m : ℝ) * Metric.infDist z Uᶜ) * max 0 (min 1 ((m : ℝ) - ‖z‖))

theorem openApprox_nonneg (U : Set ℂ) (m : ℕ) (z : ℂ) : 0 ≤ openApprox U m z :=
  mul_nonneg (le_min zero_le_one (mul_nonneg (Nat.cast_nonneg m) Metric.infDist_nonneg)) (le_max_left _ _)

theorem openApprox_le_one (U : Set ℂ) (m : ℕ) (z : ℂ) : openApprox U m z ≤ 1 := by
  unfold openApprox
  have h1 : min 1 ((m : ℝ) * Metric.infDist z Uᶜ) ≤ 1 := min_le_left _ _
  have h2 : max 0 (min 1 ((m : ℝ) - ‖z‖)) ≤ 1 := max_le zero_le_one (min_le_left _ _)
  calc min 1 ((m : ℝ) * Metric.infDist z Uᶜ) * max 0 (min 1 ((m : ℝ) - ‖z‖)) ≤ 1 * 1 :=
        mul_le_mul h1 h2 (le_max_left _ _) zero_le_one
    _ = 1 := one_mul 1

theorem openApprox_mono (U : Set ℂ) (z : ℂ) : Monotone fun m : ℕ => openApprox U m z := by
  intro m m' hmm
  unfold openApprox
  have hm : (m : ℝ) ≤ (m' : ℝ) := Nat.cast_le.2 hmm
  apply mul_le_mul
  · exact min_le_min le_rfl (mul_le_mul_of_nonneg_right hm Metric.infDist_nonneg)
  · exact max_le_max le_rfl (min_le_min le_rfl (sub_le_sub_right hm _))
  · exact le_max_left _ _
  · exact le_min zero_le_one (mul_nonneg (Nat.cast_nonneg m') Metric.infDist_nonneg)

theorem openApprox_continuous (U : Set ℂ) (m : ℕ) : Continuous (openApprox U m) := by
  unfold openApprox
  have h1 : Continuous fun z : ℂ => Metric.infDist z Uᶜ := Metric.continuous_infDist_pt (s := Uᶜ)
  exact (continuous_const.min (continuous_const.mul h1)).mul
    (continuous_const.max (continuous_const.min (continuous_const.sub continuous_norm)))

theorem openApprox_hasCompactSupport (U : Set ℂ) (m : ℕ) : HasCompactSupport (openApprox U m) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) m) fun z hz => ?_
  have hz' : (m : ℝ) < ‖z‖ := by
    simp only [mem_closedBall, dist_zero_right, not_le] at hz
    exact hz
  have h2 : max 0 (min 1 ((m : ℝ) - ‖z‖)) = 0 :=
    max_eq_left ((min_le_right _ _).trans (sub_nonpos.2 hz'.le))
  unfold openApprox
  rw [h2, mul_zero]

/-- The cutoff approximations increase to the indicator of an open set `U` with `Uᶜ` nonempty. -/
theorem openApprox_iSup {U : Set ℂ} (hU : IsOpen U) (hUc : Uᶜ.Nonempty) (z : ℂ) :
    U.indicator (1 : ℂ → ℝ≥0∞) z = ⨆ m : ℕ, ENNReal.ofReal (openApprox U m z) := by
  by_cases hz : z ∈ U
  · have hcl : IsClosed Uᶜ := hU.isClosed_compl
    have hd : 0 < Metric.infDist z Uᶜ := (IsClosed.notMem_iff_infDist_pos hcl hUc).1 (fun h => h hz)
    obtain ⟨m, hm⟩ := exists_nat_gt (max (1 / Metric.infDist z Uᶜ) (‖z‖ + 1))
    have hm1 : 1 / Metric.infDist z Uᶜ < (m : ℝ) := lt_of_le_of_lt (le_max_left _ _) hm
    have hm2 : ‖z‖ + 1 < (m : ℝ) := lt_of_le_of_lt (le_max_right _ _) hm
    have h3 : 1 < (m : ℝ) * Metric.infDist z Uᶜ := by
      have := mul_lt_mul_of_pos_right hm1 hd
      rwa [one_div_mul_cancel hd.ne'] at this
    have hval : openApprox U m z = 1 := by
      unfold openApprox
      rw [min_eq_left h3.le, min_eq_left (show (1 : ℝ) ≤ (m : ℝ) - ‖z‖ by linarith),
        max_eq_right zero_le_one, mul_one]
    rw [Set.indicator_of_mem hz, Pi.one_apply]
    apply le_antisymm
    · have h1 : ENNReal.ofReal (openApprox U m z) = 1 := by rw [hval]; simp
      rw [← h1]
      exact le_iSup (fun m' : ℕ => ENNReal.ofReal (openApprox U m' z)) m
    · exact iSup_le fun m' => ENNReal.ofReal_le_one.2 (openApprox_le_one U m' z)
  · have hz0 : Metric.infDist z Uᶜ = 0 := Metric.infDist_zero_of_mem hz
    have hval : ∀ m : ℕ, openApprox U m z = 0 := by
      intro m
      unfold openApprox
      rw [hz0]
      simp
    rw [Set.indicator_of_notMem hz]
    simp [hval]

/-- For `ω` in the good set, `μ ω U` is the supremum of the integrals of the cutoff approximations (monotone
convergence), and each integral is a Bochner integral (the LQG measure is locally finite). -/
theorem measurable_lqg_open {γ : ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {G : Set Ω}
    (hGm : MeasurableSet G) {g : ℕ → Ω → ℂ → ℝ} (hgm : ∀ k, Measurable (fun p : Ω × ℂ => g k p.1 p.2))
    (hgN : ∀ k, ∀ ω ∈ G, ∀ z, g k ω z = hcirc ω (dyadicScale k) z)
    (hGgood : ∀ ω ∈ G, IsLQGLimit γ (hcirc ω) (μ ω))
    {U : Set ℂ} (hU : IsOpen U) (hUc : Uᶜ.Nonempty) :
    Measurable (G.indicator fun ω => μ ω U) := by
  have hΦ : ∀ m : ℕ, Measurable (G.indicator fun ω => ∫ z, openApprox U m z ∂(μ ω)) := fun m =>
    measurable_integral_lqg_test hGm hgm hgN hGgood (openApprox_continuous U m)
      (openApprox_hasCompactSupport U m)
  have hpt : ∀ ω, G.indicator (fun ω => μ ω U) ω =
      ⨆ m : ℕ, ENNReal.ofReal (G.indicator (fun ω => ∫ z, openApprox U m z ∂(μ ω)) ω) := by
    intro ω
    by_cases hω : ω ∈ G
    · have hloc : IsLocallyFiniteMeasure (μ ω) := (hGgood ω hω).isLocallyFiniteMeasure
      have hint : ∫⁻ a, U.indicator (1 : ℂ → ℝ≥0∞) a ∂(μ ω) =
          ∫⁻ a, ⨆ m : ℕ, ENNReal.ofReal (openApprox U m a) ∂(μ ω) :=
        lintegral_congr fun a => openApprox_iSup hU hUc a
      rw [Set.indicator_of_mem hω, ← lintegral_indicator_one hU.measurableSet, hint,
        lintegral_iSup (f := fun m a => ENNReal.ofReal (openApprox U m a))
          (fun m => ENNReal.measurable_ofReal.comp (openApprox_continuous U m).measurable)
          (fun m m' h z => ENNReal.ofReal_le_ofReal (openApprox_mono U z h))]
      congr 1
      funext m
      rw [Set.indicator_of_mem hω]
      exact (ofReal_integral_eq_lintegral_ofReal
        ((openApprox_continuous U m).integrable_of_hasCompactSupport (openApprox_hasCompactSupport U m))
        (ae_of_all _ fun z => openApprox_nonneg U m z)).symm
    · rw [Set.indicator_of_notMem hω]
      simp [Set.indicator_of_notMem hω]
  have hfun : (G.indicator fun ω => μ ω U) = fun ω =>
      ⨆ m : ℕ, ENNReal.ofReal (G.indicator (fun ω => ∫ z, openApprox U m z ∂(μ ω)) ω) :=
    funext hpt
  rw [hfun]
  exact Measurable.iSup fun m => ENNReal.measurable_ofReal.comp (hΦ m)

/-- The complement of the unit ball in `ℂ` is nonempty. -/
theorem compl_ball_zero_one_nonempty : (ball (0 : ℂ) 1)ᶜ.Nonempty :=
  ⟨2, by simp [Metric.mem_ball]⟩

/-- The complement of `s ∩ ball 0 1` is nonempty (it contains the complement of the ball). -/
theorem compl_inter_ball_nonempty (s : Set ℂ) : (s ∩ ball (0 : ℂ) 1)ᶜ.Nonempty := by
  refine Set.Nonempty.mono ?_ compl_ball_zero_one_nonempty
  intro x hx hU
  exact hx hU.2

/-- Borel sets: `ω ↦ μ ω (B ∩ ball 0 1)` is measurable on the good set for every measurable `B` (induction from
open sets, the complement step using local finiteness of `μ ω` on `ball 0 1`). -/
theorem measurable_lqg_borel_ball {γ : ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {G : Set Ω}
    (hGm : MeasurableSet G) {g : ℕ → Ω → ℂ → ℝ} (hgm : ∀ k, Measurable (fun p : Ω × ℂ => g k p.1 p.2))
    (hgN : ∀ k, ∀ ω ∈ G, ∀ z, g k ω z = hcirc ω (dyadicScale k) z)
    (hGgood : ∀ ω ∈ G, IsLQGLimit γ (hcirc ω) (μ ω)) (B : Set ℂ) (hB : MeasurableSet B) :
    Measurable (G.indicator fun ω => μ ω (B ∩ ball (0 : ℂ) 1)) := by
  have hball : Measurable (G.indicator fun ω => μ ω (ball (0 : ℂ) 1)) := by
    simpa using measurable_lqg_open hGm hgm hgN hGgood isOpen_ball compl_ball_zero_one_nonempty
  have key : ∀ t : Set ℂ, MeasurableSet t →
      Measurable (G.indicator fun ω => μ ω (t ∩ ball (0 : ℂ) 1)) := by
    intro t ht
    refine MeasurableSpace.induction_on_inter
      (C := fun t _ => Measurable (G.indicator fun ω => μ ω (t ∩ ball (0 : ℂ) 1)))
      (s := {t : Set ℂ | IsOpen t}) (BorelSpace.measurable_eq.trans rfl)
      (fun s hs t ht _ => by
        have hs' : IsOpen s := hs
        have ht' : IsOpen t := ht
        exact (IsOpen.inter hs' ht' : IsOpen (s ∩ t))) ?_ ?_ ?_ ?_ t ht
    · simp
    · intro s hs
      have hs' : IsOpen s := hs
      exact measurable_lqg_open hGm hgm hgN hGgood (IsOpen.inter hs' isOpen_ball)
        (compl_inter_ball_nonempty s)
    · intro s hsm ih
      have hset : sᶜ ∩ ball (0 : ℂ) 1 = ball (0 : ℂ) 1 \ (s ∩ ball (0 : ℂ) 1) := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff]
        tauto
      have hpt : G.indicator (fun ω => μ ω (sᶜ ∩ ball (0 : ℂ) 1)) = fun ω =>
          G.indicator (fun ω => μ ω (ball (0 : ℂ) 1)) ω -
            G.indicator (fun ω => μ ω (s ∩ ball (0 : ℂ) 1)) ω := by
        funext ω
        by_cases hω : ω ∈ G
        · have hloc : IsLocallyFiniteMeasure (μ ω) := (hGgood ω hω).isLocallyFiniteMeasure
          have hfin : μ ω (s ∩ ball (0 : ℂ) 1) ≠ ∞ :=
            ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono Set.inter_subset_right)
          simp only [Set.indicator_of_mem hω]
          rw [hset, measure_sdiff Set.inter_subset_right
            ((hsm.inter measurableSet_ball).nullMeasurableSet) hfin]
        · simp [Set.indicator_of_notMem hω]
      rw [hpt]
      exact hball.sub ih
    · intro f hdisj hfm ih
      have hpt : G.indicator (fun ω => μ ω ((⋃ i, f i) ∩ ball (0 : ℂ) 1)) = fun ω =>
          ∑' i, G.indicator (fun ω => μ ω (f i ∩ ball (0 : ℂ) 1)) ω := by
        funext ω
        by_cases hω : ω ∈ G
        · have hloc : IsLocallyFiniteMeasure (μ ω) := (hGgood ω hω).isLocallyFiniteMeasure
          simp only [Set.indicator_of_mem hω, Set.iUnion_inter]
          exact measure_iUnion (fun i j hij => (hdisj hij).mono Set.inter_subset_left Set.inter_subset_left)
            fun i => (hfm i).inter measurableSet_ball
        · simp [Set.indicator_of_notMem hω]
      rw [hpt]
      exact Measurable.tsum fun i => ih i
  exact key B hB

/-- The kernel `ω ↦ (μ ω).restrict (ball 0 1)` on the good set (zero outside) is a measurable `Measure ℂ`-valued
map: its evaluations at measurable sets are the measurable Borel functions `ω ↦ μ ω (s ∩ ball 0 1)`. -/
theorem measurable_lqg_kernel {γ : ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {G : Set Ω}
    (hGm : MeasurableSet G) {g : ℕ → Ω → ℂ → ℝ} (hgm : ∀ k, Measurable (fun p : Ω × ℂ => g k p.1 p.2))
    (hgN : ∀ k, ∀ ω ∈ G, ∀ z, g k ω z = hcirc ω (dyadicScale k) z)
    (hGgood : ∀ ω ∈ G, IsLQGLimit γ (hcirc ω) (μ ω)) :
    Measurable (G.indicator fun ω => (μ ω).restrict (ball (0 : ℂ) 1)) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have heq : (fun ω => (G.indicator (fun ω => (μ ω).restrict (ball (0 : ℂ) 1)) ω) s) =
      G.indicator (fun ω => μ ω (s ∩ ball (0 : ℂ) 1)) := by
    funext ω
    by_cases hω : ω ∈ G
    · simp [hω, Measure.restrict_apply hs]
    · simp [hω]
  rw [heq]
  exact measurable_lqg_borel_ball hGm hgm hgN hGgood s hs

end HarmonicBalls

end
