import HarmonicBalls.Defs.LBM
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Clock construction from summable increments

Summable uniform bounds on dyadic increments give a locally uniform clock limit.
-/

namespace HarmonicBalls

open MeasureTheory MarkovProcess Filter Topology Set
open scoped ENNReal NNReal

/-- Summable uniform increment bounds construct a clock as the pointwise limit of the
    dyadic approximations, with almost sure locally uniform convergence. -/
theorem exists_lqgClock_of_summable_uniform_increments
    {γ : ℝ} {hε : ℝ → ℂ → ℝ} {x : ℂ}
    (a : ℕ → ℕ → ContinuousPath ℂ → ℝ)
    (ha : ∀ N k, Measurable (a N k))
    (hbound : ∀ᵐ b ∂(planarBrownianMotion x), ∀ N,
      Summable (fun k => a N k b) ∧ ∀ k t, t ≤ (N : ℝ≥0) →
        |lqgClockApprox γ hε (dyadicScale (k + 1)) b t -
          lqgClockApprox γ hε (dyadicScale k) b t| ≤ a N k b) :
    ∃ F : ContinuousPath ℂ → ℝ≥0 → ℝ,
      IsLQGClock planarBrownianMotion γ hε x F ∧
      ∀ᵐ b ∂(planarBrownianMotion x), ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η →
        ∀ᶠ k in atTop, ∀ t ≤ T,
          |lqgClockApprox γ hε (dyadicScale k) b t - F b t| < η := by
  classical
  let A (k : ℕ) (b : ContinuousPath ℂ) (t : ℝ≥0) :=
    lqgClockApprox γ hε (dyadicScale k) b t
  let P (b : ContinuousPath ℂ) := ∀ N,
    Summable (fun k => a N k b) ∧ ∀ k t, t ≤ (N : ℝ≥0) →
      |A (k + 1) b t - A k b t| ≤ a N k b
  have hP : ∀ᵐ b ∂(planarBrownianMotion x), P b := hbound
  let F (b : ContinuousPath ℂ) (t : ℝ≥0) :=
    if P b then atTop.limUnder (fun k => A k b t) else 0
  have hlim (b : ContinuousPath ℂ) (hb : P b) (t : ℝ≥0) :
      Tendsto (fun k => A k b t) atTop (𝓝 (F b t)) := by
    obtain ⟨N, hN⟩ := exists_nat_ge (t : ℝ)
    have ht : t ≤ (N : ℝ≥0) := by exact_mod_cast hN
    have hc : CauchySeq (fun k => A k b t) := by
      apply cauchySeq_of_dist_le_of_summable (fun k => a N k b) _ (hb N).1
      intro k
      rw [Real.dist_eq, abs_sub_comm]
      exact (hb N).2 k t ht
    simpa only [F, hb, ↓reduceIte] using hc.tendsto_limUnder
  have htail (b : ContinuousPath ℂ) (hb : P b) (N k : ℕ) (t : ℝ≥0)
      (ht : t ≤ (N : ℝ≥0)) :
      |A k b t - F b t| ≤ ∑' j, a N (k + j) b := by
    have hd : ∀ j, dist (A j b t) (A (j + 1) b t) ≤ a N j b := by
      intro j
      rw [Real.dist_eq, abs_sub_comm]
      exact (hb N).2 j t ht
    simpa only [Real.dist_eq] using
      dist_le_tsum_of_dist_le_of_tendsto (fun j => a N j b) hd (hb N).1 (hlim b hb t) k
  refine ⟨F, ?_, ?_⟩
  · intro T η hη
    obtain ⟨N, hN⟩ := exists_nat_ge (T : ℝ)
    have hTN : T ≤ (N : ℝ≥0) := by exact_mod_cast hN
    let tail (k : ℕ) (b : ContinuousPath ℂ) := ∑' j, a N (k + j) b
    have hm : ∀ k, Measurable (tail k) := by
      intro k
      exact Measurable.tsum (fun j => ha N (k + j))
    have hc : TendstoInMeasure (planarBrownianMotion x) tail atTop (fun _ => 0) := by
      apply tendstoInMeasure_of_tendsto_ae_of_measurable_edist
      · intro k
        exact (hm k).edist measurable_const
      · exact ae_of_all _ (fun b => by simpa only [tail, Nat.add_comm] using tendsto_sum_nat_add (fun j => a N j b))
    have hprob := (tendstoInMeasure_iff_norm.mp hc) η hη
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hprob
    · intro k; exact zero_le
    · intro k
      apply measure_mono_ae
      filter_upwards [hP] with b hb
      intro h
      obtain ⟨t, ht, he⟩ := h
      have hle := htail b hb N k t (ht.trans hTN)
      change η ≤ ‖tail k b - 0‖
      rw [sub_zero, Real.norm_eq_abs]
      exact he.trans (hle.trans (le_abs_self _))
  · filter_upwards [hP] with b hb
    intro T η hη
    obtain ⟨N, hN⟩ := exists_nat_ge (T : ℝ)
    have hTN : T ≤ (N : ℝ≥0) := by exact_mod_cast hN
    have htend : Tendsto (fun k => ∑' j, a N (k + j) b) atTop (𝓝 0) := by
      simpa only [Nat.add_comm] using tendsto_sum_nat_add (fun j => a N j b)
    filter_upwards [htend.eventually (Iio_mem_nhds hη)] with k hk t ht
    exact (htail b hb N k t (ht.trans hTN)).trans_lt hk

end HarmonicBalls
