import HarmonicBalls.Proofs.Potential.LQGClockAllStarts
import HarmonicBalls.Proofs.Potential.LBMClauseSubcritical
import HarmonicBalls.Proofs.Potential.LQGClockInsertedExistence
import HarmonicBalls.Proofs.Potential.LQGClockZeroInsertionConvergence

/-!
# The LBM clause of Proposition 2.5 with a clock from every start

The LBM clause of `GreenPotentialLiouvilleHolderStmt` is stated for every family `F` of LQG clocks
such that, almost surely, `F ω x` is an LQG clock from every start `x`. This file proves that
such a family exists and so that the clause applies:

* `exists_ae_forall_isLQGClock_zero`: without insertion (`α₀ = 0`), for every `0 < γ < 2`, from the
  almost sure locally uniform convergence of the approximate clocks from one start
  (`ae_exists_locally_uniform_limit_clock_zero`);
* `exists_ae_forall_isLQGClock_of_sq_lt_two`: for every insertion `α₀ < Q` when `γ² < 2`, from the
  LQG clock from one start (`exists_ae_isLQGClock_fieldCircleAverage`, sample spaces in `Type`).

Both go through `ae_forall_exists_isLQGClock_of_cauchy` (`LQGClockAllStarts.lean`). The theorems
`exists_lbmClause_zero` and `exists_lbmClause_of_sq_lt_two` then give the LBM clause of
Proposition 2.5 for a family of clocks that exists: almost surely, for every smooth bounded `O`,
the expected exit time of Liouville Brownian motion from `O` is finite and Hölder continuous in the
start. For `2 ≤ γ² < 4` with an insertion `α₀ ≠ 0`, an LQG clock from one start is not proved here.
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology Set Metric MarkovProcess
open scoped ENNReal NNReal

/-- Almost sure locally uniform convergence of the approximate clocks along `ε = 2^{-(n+1)}` makes
them Cauchy in probability uniformly on bounded time sets. -/
theorem cauchy_of_ae_exists_locally_uniform {γ : ℝ} {hε : ℝ → ℂ → ℝ}
    (hc : ∀ k, Continuous (hε (dyadicScale k))) {x : ℂ}
    (hlim : ∀ᵐ b ∂(planarBrownianMotion x), ∃ F : ℝ≥0 → ℝ, ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η →
      ∀ᶠ n in atTop, ∀ t : ℝ≥0, t ≤ T →
        |lqgClockApprox γ hε (dyadicScale (n + 1)) b t - F t| < η)
    (T : ℝ≥0) {η : ℝ} (hη : 0 < η) {θ : ℝ} (hθ : 0 < θ) :
    ∃ N : ℕ, ∀ j, N ≤ j → ∀ k, N ≤ k → planarBrownianMotion x
      {b | ∃ t ≤ T, η ≤ |lqgClockApprox γ hε (dyadicScale j) b t -
        lqgClockApprox γ hε (dyadicScale k) b t|} ≤ ENNReal.ofReal θ := by
  choose M hMm hBM hMB using fun j k =>
    exists_measurableSet_sup_diff_between (γ := γ) (hc j) (hc k) T (ζ := η / 2) (by positivity)
  set G : ℕ → Set (ContinuousPath ℂ) := fun N => ⋃ j, ⋃ (_ : N ≤ j), ⋃ k, ⋃ (_ : N ≤ k), M j k
    with hG
  have hGm : ∀ N, MeasurableSet (G N) := fun N =>
    MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ =>
      MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ => hMm j k
  have hGanti : Antitone G := by
    intro N N' hNN' b hb
    simp only [hG, mem_iUnion] at hb ⊢
    obtain ⟨j, hj, k, hk, h⟩ := hb
    exact ⟨j, hNN'.trans hj, k, hNN'.trans hk, h⟩
  have hlimG := tendsto_measure_iInter_atTop (μ := planarBrownianMotion x)
    (fun N => (hGm N).nullMeasurableSet) hGanti ⟨0, measure_ne_top _ _⟩
  have hzero : planarBrownianMotion x (⋂ N, G N) = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 hlim)
    intro b hb hgood
    obtain ⟨F, hF⟩ := hgood
    obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 (hF T (η / 4) (by positivity))
    have hbG := mem_iInter.1 hb (N₀ + 1)
    simp only [hG, mem_iUnion] at hbG
    obtain ⟨j, hj, k, hk, hjk⟩ := hbG
    obtain ⟨t, htT, ht⟩ := hMB j k hjk
    have h1 := hN₀ (j - 1) (by omega) t htT
    have h2 := hN₀ (k - 1) (by omega) t htT
    rw [show j - 1 + 1 = j by omega] at h1
    rw [show k - 1 + 1 = k by omega] at h2
    have h3 : |lqgClockApprox γ hε (dyadicScale j) b t - lqgClockApprox γ hε (dyadicScale k) b t| ≤
        |lqgClockApprox γ hε (dyadicScale j) b t - F t| +
          |lqgClockApprox γ hε (dyadicScale k) b t - F t| := by
      rw [show lqgClockApprox γ hε (dyadicScale j) b t - lqgClockApprox γ hε (dyadicScale k) b t =
        (lqgClockApprox γ hε (dyadicScale j) b t - F t) -
          (lqgClockApprox γ hε (dyadicScale k) b t - F t) by ring]
      exact abs_sub _ _
    linarith
  rw [Function.comp_def, hzero] at hlimG
  obtain ⟨N, hN⟩ := ENNReal.tendsto_atTop_zero.1 hlimG (ENNReal.ofReal θ) (by simp; positivity)
  refine ⟨N, fun j hj k hk => (measure_mono fun b hb => ?_).trans (hN N le_rfl)⟩
  simp only [hG, mem_iUnion]
  obtain ⟨t, ht, h⟩ := hb
  exact ⟨j, hj, k, hk, hBM j k ⟨t, ht, by linarith⟩⟩

/-- **An LQG clock from every start, without insertion**: for a whole-plane GFF and every
`0 < γ < 2`, there is a family `F` such that, for almost every field, `F ω x` is an LQG clock of
planar Brownian motion from `x` for every start `x`. -/
theorem exists_ae_forall_isLQGClock_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ F : Ω → ℂ → ContinuousPath ℂ → ℝ≥0 → ℝ, ∀ᵐ ω ∂P, ∀ x : ℂ,
      IsLQGClock planarBrownianMotion γ (fieldCircleAverage 0 (hcirc ω)) x (F ω x) := by
  have hLP := (LPBridge.isWholePlaneGFF_iff P hC hcirc).mp hh
  have : IsProbabilityMeasure P := hh.isProbabilityMeasure
  have hloc := Measure.ae_ae_of_ae_prod (ae_exists_locally_uniform_limit_clock_zero hLP hγ hγ2 0)
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  have hall := ae_forall_exists_isLQGClock_of_cauchy hh hγ hγ2 hQ (x₀ := 0) (by
    filter_upwards [hloc, ae_continuous_fieldCircleAverage hLP 0] with ω hω hc T η hη θ hθ
    exact cauchy_of_ae_exists_locally_uniform (fun k => hc _ (dyadicScale_pos k))
      (hω.mono fun b hb => by
        obtain ⟨F, -, -, -, hF⟩ := hb
        exact ⟨F, hF⟩) T hη hθ)
  exact ⟨fun ω x => Classical.epsilon fun F => IsLQGClock planarBrownianMotion γ
    (fieldCircleAverage 0 (hcirc ω)) x F, hall.mono fun ω hω x => Classical.epsilon_spec (hω x)⟩

/-- **An LQG clock from every start for every insertion, `γ² < 2`**: for a whole-plane GFF on a
sample space in `Type`, `0 < γ` with `γ² < 2` and `α < Q`, there is a family `F` such that, for
almost every field, `F ω x` is an LQG clock of the inserted field from every start `x`. -/
theorem exists_ae_forall_isLQGClock_of_sq_lt_two {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ ^ 2 < 2) (hα : α < lqgQ γ) :
    ∃ F : Ω → ℂ → ContinuousPath ℂ → ℝ≥0 → ℝ, ∀ᵐ ω ∂P, ∀ x : ℂ,
      IsLQGClock planarBrownianMotion γ (fieldCircleAverage α (hcirc ω)) x (F ω x) := by
  obtain ⟨F₀, hF₀⟩ := exists_ae_isLQGClock_fieldCircleAverage
    ((LPBridge.isWholePlaneGFF_iff P hC hcirc).mp hh) 0 hγ hγ2 hα
  exact exists_ae_forall_isLQGClock_of_one_start hh hγ (by nlinarith) hα hF₀

/-- **Proposition 2.5, LBM clause, without insertion**: for every `0 < γ < 2` there is a family of
LQG clocks from every start, and for it, almost surely, the expected exit time of Liouville
Brownian motion from every smooth bounded open set is finite and Hölder continuous. -/
theorem exists_lbmClause_zero {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ) :
    ∃ F : Ω → ℂ → ContinuousPath ℂ → ℝ≥0 → ℝ,
      (∀ᵐ ω ∂P, ∀ x : ℂ, IsLQGClock planarBrownianMotion γ (fieldCircleAverage 0 (hcirc ω)) x (F ω x)) ∧
      ∀ᵐ ω ∂P, ∀ O : Set ℂ, IsSmoothBoundedOpen O →
        (∀ x ∈ O, expectedLBMExitTime (F ω x) O x < ⊤) ∧
          ∃ C r : ℝ≥0, 0 < r ∧
            HolderOnWith C r (fun x => (expectedLBMExitTime (F ω x) O x).toReal) O := by
  obtain ⟨F, hF⟩ := exists_ae_forall_isLQGClock_zero hh hγ hγ2
  exact ⟨F, hF, greenPotentialLiouvilleHolder_lbmClause_of_lt_two hγ hγ2
    (by unfold lqgQ; positivity) hh hμ F hF⟩

/-- **Proposition 2.5, LBM clause, `γ² < 2`, every insertion**: on a sample space in `Type`, for
`0 < γ` with `γ² < 2` and `α₀ < Q` there is a family of LQG clocks from every start, and for it,
almost surely, the expected exit time of Liouville Brownian motion from every smooth bounded open
set is finite and Hölder continuous. -/
theorem exists_lbmClause_of_sq_lt_two {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ ^ 2 < 2) (hα : α₀ < lqgQ γ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∃ F : Ω → ℂ → ContinuousPath ℂ → ℝ≥0 → ℝ,
      (∀ᵐ ω ∂P, ∀ x : ℂ, IsLQGClock planarBrownianMotion γ (fieldCircleAverage α₀ (hcirc ω)) x (F ω x)) ∧
      ∀ᵐ ω ∂P, ∀ O : Set ℂ, IsSmoothBoundedOpen O →
        (∀ x ∈ O, expectedLBMExitTime (F ω x) O x < ⊤) ∧
          ∃ C r : ℝ≥0, 0 < r ∧
            HolderOnWith C r (fun x => (expectedLBMExitTime (F ω x) O x).toReal) O := by
  obtain ⟨F, hF⟩ := exists_ae_forall_isLQGClock_of_sq_lt_two hh hγ hγ2 hα
  exact ⟨F, hF, greenPotentialLiouvilleHolder_lbmClause_of_lt_two hγ (by nlinarith) hα hh hμ F hF⟩

end HarmonicBalls
