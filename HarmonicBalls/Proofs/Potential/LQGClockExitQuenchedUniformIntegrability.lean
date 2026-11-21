import HarmonicBalls.Proofs.Potential.LQGClockExitIncrementUniformIntegrability

/-! # Uniform integrability of exit-time clocks from summable expected increments

For a field whose circle averages are continuous at every dyadic scale, if the expected sum of
the absolute dyadic increments of the clock approximations read at the exit time from a bounded
open domain is finite, then the exit-time clock approximations are dominated by one integrable
function: the first two approximations are bounded by a multiple of the exit time, and the
later ones by the first plus the sum of the increments. They are therefore uniformly
integrable.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal
namespace HarmonicBalls

/-- If the expected sum of the absolute dyadic increments of the clock approximations at the
exit time from a bounded open domain is finite, the exit-time clock approximations are
uniformly integrable. -/
theorem uniformIntegrable_exit_clockApprox_of_lintegral_tsum_ne_top {γ : ℝ}
    {hε : ℝ → ℂ → ℝ} (hεc : ∀ k : ℕ, Continuous (hε (dyadicScale k)))
    {D : Set ℂ} (hD : IsOpen D) (hDb : Bornology.IsBounded D) (x : ℂ)
    (hsum : (∫⁻ b, ∑' k, ENNReal.ofReal
      |lqgClockApprox γ hε (dyadicScale (k+2)) b (ContinuousPath.exitTime D b).toNNReal -
        lqgClockApprox γ hε (dyadicScale (k+1)) b (ContinuousPath.exitTime D b).toNNReal|
      ∂(planarBrownianMotion x)) ≠ ⊤) :
    UniformIntegrable (fun k : ℕ => fun b =>
      lqgClockApprox γ hε (dyadicScale k) b (ContinuousPath.exitTime D b).toNNReal) 1
      (planarBrownianMotion x) := by
  let μ := planarBrownianMotion x
  let τ : ContinuousPath ℂ → ℝ≥0∞ := ContinuousPath.exitTime D
  have hτm : Measurable τ := ContinuousPath.measurable_exitTime D hD
  have hEτ : (∫⁻ b, τ b ∂μ) ≠ ⊤ :=
    (GreenOccupation.lintegral_exitTime_planarBrownianMotion_lt_top hD hDb x).ne
  have hfin : ∀ᵐ b ∂μ, τ b ≠ ⊤ := (ae_lt_top hτm hEτ).mono fun _ h => h.ne
  let f : ℕ → ℂ → ℝ := fun k z =>
    dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * hε (dyadicScale k) z)
  have hfc (k : ℕ) : Continuous (f k) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul (hεc k)))
  have happrox (k : ℕ) (b : ContinuousPath ℂ) (u : ℝ) (hu : 0 ≤ u) :
      lqgClockApprox γ hε (dyadicScale k) b u.toNNReal =
        ∫ s in (0 : ℝ)..u, f k (b s.toNNReal) := by
    simp only [lqgClockApprox, Real.coe_toNNReal _ hu, f]
  let A : ℕ → ContinuousPath ℂ → ℝ := fun k b =>
    lqgClockApprox γ hε (dyadicScale k) b (τ b).toNNReal
  have hAm (k : ℕ) : Measurable (A k) := measurable_lqgClockApprox_exit hD k (hεc k)
  let Δ : ℕ → ContinuousPath ℂ → ℝ≥0∞ := fun k b => ENNReal.ofReal |A (k+2) b - A (k+1) b|
  have hΔm (k : ℕ) : Measurable (Δ k) :=
    (((hAm (k+2)).sub (hAm (k+1))).abs).ennreal_ofReal
  have hbd (j : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ closure D, ‖f j z‖ ≤ M := by
    obtain ⟨M₁, hM₁⟩ := (hDb.isCompact_closure).exists_bound_of_continuousOn
      (hfc j).continuousOn
    exact ⟨max M₁ 0, le_max_right _ _, fun z hz => (hM₁ z hz).trans (le_max_left _ _)⟩
  choose M hM0 hM using hbd
  have hAj (j : ℕ) (b : ContinuousPath ℂ) (hb : τ b ≠ ⊤) : ‖A j b‖ ≤ M j * (τ b).toReal := by
    have hrepr : A j b = ∫ s in (0 : ℝ)..(τ b).toReal, f j (b s.toNNReal) := by
      have hconv : ((τ b).toReal).toNNReal = (τ b).toNNReal := Real.toNNReal_coe
      have h := happrox j b _ (ENNReal.toReal_nonneg (a := τ b))
      rw [hconv] at h
      exact h
    rw [hrepr]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const_ae
      (a := 0) (b := (τ b).toReal) (C := M j) (f := fun s => f j (b s.toNNReal)) ?_
    · rwa [sub_zero, abs_of_nonneg ENNReal.toReal_nonneg] at h
    · filter_upwards [(volume : Measure ℝ).ae_ne (τ b).toReal] with s hs hsI
      rw [uIoc_of_le ENNReal.toReal_nonneg] at hsI
      have hlt : s < (τ b).toReal := lt_of_le_of_ne hsI.2 hs
      have hmem : b s.toNNReal ∈ D := by
        apply ContinuousPath.mem_of_lt_exitTime D b
        have h' : ENNReal.ofReal s < ENNReal.ofReal (τ b).toReal :=
          (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hsI.1.le).mpr hlt
        rw [ENNReal.ofReal_toReal hb] at h'
        exact h'
      exact hM j _ (subset_closure hmem)
  let Y : ContinuousPath ℂ → ℝ≥0∞ := fun b =>
    ENNReal.ofReal (M 0 * (τ b).toReal) + ENNReal.ofReal (M 1 * (τ b).toReal) +
      ∑' k, Δ k b
  have hS : Measurable (fun b => ∑' k, Δ k b) := Measurable.tsum hΔm
  have hTj (j : ℕ) : Measurable (fun b => ENNReal.ofReal (M j * (τ b).toReal)) :=
    (measurable_const.mul hτm.ennreal_toReal).ennreal_ofReal
  have hYm : Measurable Y := ((hTj 0).add (hTj 1)).add hS
  have hTi (j : ℕ) : (∫⁻ b, ENNReal.ofReal (M j * (τ b).toReal) ∂μ) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := M j)) hEτ) ?_
    rw [← lintegral_const_mul _ hτm]
    apply lintegral_mono
    intro b
    simp only
    rw [ENNReal.ofReal_mul (hM0 j)]
    exact mul_le_mul_of_nonneg_left ENNReal.ofReal_toReal_le zero_le
  have hYi : (∫⁻ b, Y b ∂μ) ≠ ⊤ := by
    rw [lintegral_add_right' _ hS.aemeasurable, lintegral_add_right' _ (hTj 1).aemeasurable]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hTi 0, hTi 1⟩, hsum⟩
  have hdom (k : ℕ) : ∀ᵐ b ∂μ, ENNReal.ofReal ‖A k b‖ ≤ Y b := by
    filter_upwards [hfin] with b hb
    rcases k with _ | m
    · calc
        ENNReal.ofReal ‖A 0 b‖ ≤ ENNReal.ofReal (M 0 * (τ b).toReal) :=
          ENNReal.ofReal_le_ofReal (hAj 0 b hb)
        _ ≤ Y b := le_self_add.trans le_self_add
    · have htel : A (m+1) b = A 1 b + ∑ j ∈ Finset.range m, (A (j+2) b - A (j+1) b) := by
        rw [Finset.sum_range_sub (fun j => A (j+1) b)]
        ring
      calc
        ENNReal.ofReal ‖A (m+1) b‖ ≤ ENNReal.ofReal (‖A 1 b‖ +
            ∑ j ∈ Finset.range m, |A (j+2) b - A (j+1) b|) := by
          apply ENNReal.ofReal_le_ofReal
          rw [htel, Real.norm_eq_abs, Real.norm_eq_abs]
          exact (abs_add_le _ _).trans (add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _))
        _ = ENNReal.ofReal ‖A 1 b‖ +
            ∑ j ∈ Finset.range m, ENNReal.ofReal |A (j+2) b - A (j+1) b| := by
          rw [ENNReal.ofReal_add (norm_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _),
            ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _)]
        _ ≤ ENNReal.ofReal (M 1 * (τ b).toReal) + ∑' j, Δ j b := by
          apply add_le_add (ENNReal.ofReal_le_ofReal (hAj 1 b hb))
          exact ENNReal.sum_le_tsum _
        _ ≤ Y b := by
          simp only [Y]
          rw [add_assoc]
          exact le_add_self
  let Yr : ContinuousPath ℂ → ℝ := fun b => (Y b).toReal
  have hYr : MemLp Yr 1 μ := by
    rw [memLp_one_iff_integrable]
    exact integrable_toReal_of_lintegral_ne_top hYm.aemeasurable hYi
  have hYfin : ∀ᵐ b ∂μ, Y b ≠ ⊤ := (ae_lt_top hYm hYi).mono fun _ h => h.ne
  have hdomr (k : ℕ) : ∀ᵐ b ∂μ, ‖A k b‖ ≤ ‖Yr b‖ := by
    filter_upwards [hdom k, hYfin] with b hb hbf
    rw [Real.norm_eq_abs (Yr b), abs_of_nonneg ENNReal.toReal_nonneg]
    have := ENNReal.toReal_mono hbf hb
    rwa [ENNReal.toReal_ofReal (norm_nonneg _)] at this
  refine ⟨?_, ?_⟩
  · refine (unifIntegrable_const le_rfl ENNReal.one_ne_top hYr (ι := ℕ)).ae_mono
      (fun k => (hAm k).aestronglyMeasurable) (fun k => ?_)
    filter_upwards [hdomr k] with b hb
    exact enorm_le_iff_norm_le.mpr hb
  · refine ⟨(eLpNorm Yr 1 μ).toNNReal, fun k => ?_⟩
    rw [ENNReal.coe_toNNReal hYr.eLpNorm_lt_top.ne]
    exact eLpNorm_mono_ae (hAm k).aestronglyMeasurable (hdomr k)

end HarmonicBalls
