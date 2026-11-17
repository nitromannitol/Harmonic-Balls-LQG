import HarmonicBalls.Proofs.Potential.LQGClockFineInnerUniformTime
import HarmonicBalls.Proofs.Potential.LQGClockCoarseInnerExpectation

/-! # Expected inner occupations over all dyadic scales

Coarse and fine smoothing estimates control the expected supremum of inner
occupations uniformly over unit time.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal
namespace HarmonicBalls

/-- The product-law expected supremum of actual inner occupations over all
unit times and dyadic smoothing scales tends to zero. -/
theorem tendsto_lintegral_iSup_time_inner_inserted_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hq0 : 0 < γ*α) (hq1 : γ*α < 1) (hγ : 0 < γ)
    (hsub : γ^2/2 < 2*(1-γ*α)) :
    Tendsto (fun n : ℕ => ∫⁻ q : Ω × ContinuousPath ℂ,
      (⨆ i : ℕ, ⨆ t : Icc (0 : ℝ) 1,
        let ε : ℝ := (2 : ℝ)⁻¹ ^ (i+1)
        ∫⁻ s in Ioc (0 : ℝ) t.1, ENNReal.ofReal
          ({z : ℂ | ‖z‖ < (2 : ℝ)⁻¹ ^ (n+2) ∧ ‖z‖ ≤ 1/2}.indicator
            (fun z => ε^(γ^2/2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) ε z)) (q.2 s.toNNReal)))
        ∂(P.prod (planarBrownianMotion x))) atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let d : ℕ → ℝ := fun i => (2 : ℝ)⁻¹ ^ (i+1)
  have hd (i : ℕ) : 0 < d i := by dsimp [d]; positivity
  have hdlt (i : ℕ) : d (i+1) < d i := by
    dsimp [d]
    rw [show i+1+1 = (i+1)+1 by omega, pow_succ]
    have h : 0 < (2 : ℝ)⁻¹ ^ (i+1) := by positivity
    nlinarith
  let F (q : Ω × ContinuousPath ℂ) (i : ℕ) (z : ℂ) := (d i)^(γ^2/2) * Real.exp (γ *
    LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (d i) z)
  let C (n : ℕ) (q : Ω × ContinuousPath ℂ) :=
    ∑ i ∈ Finset.range (n+1), ∫⁻ s in Ioc (0 : ℝ) 1,
      ENNReal.ofReal ({z : ℂ | ‖z‖ < d n}.indicator (F q i) (q.2 s.toNNReal))
  let J (n : ℕ) (q : Ω × ContinuousPath ℂ) := ⨆ i : ℕ, ENNReal.ofReal |∫ z,
    {z : ℂ | ‖z‖ ≤ d (n+1) ∧ ‖z‖ ≤ 1/2}.indicator (F q (n+i)) z
      ∂(Measure.map (fun t => q.2 t) (Measure.map Real.toNNReal
        (volume.restrict (Icc (0 : ℝ) 1))))|
  have hCmeas (n : ℕ) : AEMeasurable (C n) (P.prod (planarBrownianMotion x)) := by
    apply Finset.aemeasurable_fun_sum
    intro i hi
    exact aemeasurable_inner_inserted_clock_cell hh (planarBrownianMotion x) (hd i) γ α (d n) 0 1
  let p : ℝ := (2+γ*α)/2
  have hqp : γ*α < p := by dsimp [p]; linarith
  have hp : p < 2 := by dsimp [p]; linarith
  have hC : Tendsto (fun n => ∫⁻ q, C n q ∂(P.prod (planarBrownianMotion x))) atTop (𝓝 0) := by
    simpa only [C, F, d] using
      tendsto_lintegral_sum_inner_inserted_coarse_dyadic_zero hh x γ α p hq0 hqp hp
  have hJ : Tendsto (fun n => ∫⁻ q, J n q ∂(P.prod (planarBrownianMotion x))) atTop (𝓝 0) := by
    have heq (n : ℕ) : (∫⁻ q, J n q ∂(P.prod (planarBrownianMotion x))) =
        ∫⁻ q : ContinuousPath ℂ × Ω, J n q.swap ∂((planarBrownianMotion x).prod P) := by
      symm
      exact lintegral_prod_swap (J n)
    simp_rw [heq]
    simpa only [J, F, d, Nat.add_assoc, Nat.reduceAdd, Prod.swap] using
      tendsto_lintegral_iSup_inserted_inner_closed_occupation_zero hh x hq0 hq1 hγ hsub
  have hsum : Tendsto (fun n => (∫⁻ q, C n q ∂(P.prod (planarBrownianMotion x))) +
      (∫⁻ q, J n q ∂(P.prod (planarBrownianMotion x)))) atTop (𝓝 0) := by
    simpa only [add_zero] using hC.add hJ
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hcont : ∀ᵐ ω ∂P, ∀ r, 0 < r → Continuous (hcirc ω r) := by
    filter_upwards [hHae] with ω hω r hr
    rw [← funext (hω r)]
    exact hHc ω r hr
  have hbound (n : ℕ) : ∀ᵐ q : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      (⨆ i : ℕ, ⨆ t : Icc (0 : ℝ) 1, ∫⁻ s in Ioc (0 : ℝ) t.1, ENNReal.ofReal
        ({z : ℂ | ‖z‖ < d (n+1) ∧ ‖z‖ ≤ 1/2}.indicator (F q i) (q.2 s.toNNReal))) ≤ C n q + J n q := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)).ae hcont,
      (Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)).ae
        (ae_recentered_inserted_circle_average hh α)] with q hc hr
    have hF (i : ℕ) : Continuous (F q i) := by
      have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (d i) z) =
          fun z => hcirc q.1 (d i) z - hcirc q.1 1 0 - α * Real.log (max (d i) ‖z‖) := by
        funext z
        exact (hr (d i) z (hd i)).symm
      have hi : Continuous (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (d i) z) := by
        rw [heq]
        exact ((hc _ (hd i)).sub continuous_const).sub (continuous_const.mul
          ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left (hd i)).ne')))
      exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hi))
    have hF0 (i : ℕ) (z : ℂ) : 0 ≤ F q i z :=
      mul_nonneg (Real.rpow_nonneg (hd i).le _) (Real.exp_pos _).le
    apply iSup_le
    intro i
    apply iSup_le
    intro t
    by_cases hi : i < n+1
    · calc
        _ ≤ ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
            ({z : ℂ | ‖z‖ < d n}.indicator (F q i) (q.2 s.toNNReal)) := by
          calc
            _ ≤ ∫⁻ s in Ioc (0 : ℝ) t.1, ENNReal.ofReal
                ({z : ℂ | ‖z‖ < d n}.indicator (F q i) (q.2 s.toNNReal)) := by
              apply lintegral_mono
              intro s
              apply ENNReal.ofReal_le_ofReal
              apply Set.indicator_le_indicator_of_subset _ (hF0 i)
              intro z hz
              exact lt_trans hz.1 (hdlt n)
            _ ≤ _ := lintegral_mono_set (Ioc_subset_Ioc le_rfl t.2.2)
        _ ≤ C n q := by
          dsimp only [C]
          exact Finset.single_le_sum (f := fun j : ℕ => ∫⁻ s in Ioc (0 : ℝ) 1,
            ENNReal.ofReal ({z : ℂ | ‖z‖ < d n}.indicator (F q j) (q.2 s.toNNReal)))
            (fun _ _ => zero_le) (Finset.mem_range.mpr hi)
        _ ≤ C n q + J n q := le_add_right le_rfl
    · have hni : n ≤ i := by omega
      calc
        _ ≤ ENNReal.ofReal (∫ z, {z : ℂ | ‖z‖ ≤ d (n+1) ∧ ‖z‖ ≤ 1/2}.indicator
            (F q i) z ∂(Measure.map (fun u => q.2 u) (Measure.map Real.toNNReal
              (volume.restrict (Icc (0 : ℝ) 1))))) :=
          lintegral_inner_time_le_closed_unit_occupation q.2 (F q i) (hF i) (hF0 i)
            (d (n+1)) t.1 t.2.2
        _ ≤ ENNReal.ofReal |∫ z, {z : ℂ | ‖z‖ ≤ d (n+1) ∧ ‖z‖ ≤ 1/2}.indicator
            (F q i) z ∂(Measure.map (fun u => q.2 u) (Measure.map Real.toNNReal
              (volume.restrict (Icc (0 : ℝ) 1))))| := ENNReal.ofReal_le_ofReal (le_abs_self _)
        _ ≤ J n q := by
          simpa only [J, Nat.add_sub_of_le hni] using
            le_iSup (fun j : ℕ => ENNReal.ofReal |∫ z,
              {z : ℂ | ‖z‖ ≤ d (n+1) ∧ ‖z‖ ≤ 1/2}.indicator (F q (n+j)) z
                ∂(Measure.map (fun u => q.2 u) (Measure.map Real.toNNReal
                  (volume.restrict (Icc (0 : ℝ) 1))))|) (i-n)
        _ ≤ C n q + J n q := le_add_left le_rfl
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
  · intro n
    exact zero_le
  · intro n
    calc
      _ ≤ ∫⁻ q, C n q + J n q ∂(P.prod (planarBrownianMotion x)) := by
        apply lintegral_mono_ae
        simpa only [F, d, Nat.add_assoc, Nat.reduceAdd] using hbound n
      _ = _ := lintegral_add_left' (hCmeas n) (J n)

end HarmonicBalls
