import HarmonicBalls.Proofs.Potential.LQGClockFineInnerPathwise
import HarmonicBalls.Proofs.Potential.LQGClockInnerUniformTime

/-! # Uniform inner occupation over time and smoothing

Coarse- and fine-scale estimates control inner occupations uniformly in time.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal
namespace HarmonicBalls

/-- For almost every field and Brownian path, actual inner occupations vanish
uniformly over unit times and all dyadic smoothing scales. -/
theorem ae_ae_tendsto_iSup_time_inner_inserted_zero_of_fine_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hq0 : 0 < γ * α) (hq1 : γ * α < 1) (hγ : 0 < γ)
    (hsub : γ^2/2 < 2*(1-γ*α)) :
    ∀ᵐ ω ∂P, ∀ᵐ b ∂planarBrownianMotion x,
      Tendsto (fun n : ℕ => ⨆ i : ℕ, ⨆ t : Icc (0 : ℝ) 1,
        let ε : ℝ := (2 : ℝ)⁻¹ ^ (i+1)
        ∫⁻ s in Ioc (0 : ℝ) t.1, ENNReal.ofReal
          ({z : ℂ | ‖z‖ < (2 : ℝ)⁻¹ ^ (n+2) ∧ ‖z‖ ≤ 1/2}.indicator
            (fun z => ε^(γ^2/2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) (b s.toNNReal)))
        atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let p : ℝ := (2 + γ*α)/2
  have hqp : γ*α < p := by dsimp [p]; linarith
  have hp : p < 2 := by dsimp [p]; linarith
  have hcoarse := ae_ae_tendsto_inner_inserted_coarse_dyadic_zero hh x γ α p hq0 hqp hp
  have hfine := ae_tendsto_iSup_inserted_fine_inner_occupation_zero hh x hq0 hq1 hγ hsub
  have hfineswap := (Measure.measurePreserving_swap (μ := P) (ν := planarBrownianMotion x)).quasiMeasurePreserving.ae hfine
  have hfine' := Measure.ae_ae_of_ae_prod hfineswap
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hcont : ∀ᵐ ω ∂P, ∀ r, 0 < r → Continuous (hcirc ω r) := by
    filter_upwards [hHae] with ω hω r hr
    rw [← funext (hω r)]
    exact hHc ω r hr
  filter_upwards [hcoarse, hfine', hcont, ae_recentered_inserted_circle_average hh α] with ω hcoarse hfine hc hr
  filter_upwards [hcoarse, hfine] with b hcoarse hfine
  let d : ℕ → ℝ := fun i => (2 : ℝ)⁻¹ ^ (i+1)
  have hd (i : ℕ) : 0 < d i := by dsimp [d]; positivity
  have hdlt (i : ℕ) : d (i+1) < d i := by
    dsimp [d]
    rw [show i+1+1 = (i+1)+1 by omega, pow_succ]
    have h : 0 < (2 : ℝ)⁻¹ ^ (i+1) := by positivity
    nlinarith
  let F (i : ℕ) (z : ℂ) := (d i)^(γ^2/2) * Real.exp (γ *
    LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (d i) z)
  have hF (i : ℕ) : Continuous (F i) := by
    have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (d i) z) =
        fun z => hcirc ω (d i) z - hcirc ω 1 0 - α * Real.log (max (d i) ‖z‖) := by
      funext z
      exact (hr (d i) z (hd i)).symm
    have hi : Continuous (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (d i) z) := by
      rw [heq]
      exact ((hc _ (hd i)).sub continuous_const).sub (continuous_const.mul
        ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left (hd i)).ne')))
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hi))
  have hF0 (i : ℕ) (z : ℂ) : 0 ≤ F i z :=
    mul_nonneg (Real.rpow_nonneg (hd i).le _) (Real.exp_pos _).le
  let C (n : ℕ) := ∑ i ∈ Finset.range (n+1), ∫⁻ s in Ioc (0 : ℝ) 1,
    ENNReal.ofReal ({z : ℂ | ‖z‖ < d n}.indicator (F i) (b s.toNNReal))
  let J (n : ℕ) := ⨆ i : ℕ, ENNReal.ofReal |∫ z,
    {z : ℂ | ‖z‖ ≤ d (n+1) ∧ ‖z‖ ≤ 1/2}.indicator (F (n+i)) z
      ∂(Measure.map (fun t => b t) (Measure.map Real.toNNReal
        (volume.restrict (Icc (0 : ℝ) 1))))|
  have hC : Tendsto C atTop (𝓝 0) := by simpa only [C, F, d] using hcoarse
  have hJ : Tendsto J atTop (𝓝 0) := by simpa only [J, F, d, Nat.add_assoc, Nat.reduceAdd, Prod.swap_prod_mk] using hfine
  have hsum : Tendsto (fun n => C n + J n) atTop (𝓝 0) := by
    simpa only [add_zero] using hC.add hJ
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
  · intro n
    exact zero_le
  · intro n
    apply iSup_le
    intro i
    apply iSup_le
    intro t
    by_cases hi : i < n+1
    · calc
        _ ≤ ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
            ({z : ℂ | ‖z‖ < d n}.indicator (F i) (b s.toNNReal)) := by
          calc
            _ ≤ ∫⁻ s in Ioc (0 : ℝ) t.1, ENNReal.ofReal
                ({z : ℂ | ‖z‖ < d n}.indicator (F i) (b s.toNNReal)) := by
              apply lintegral_mono
              intro s
              apply ENNReal.ofReal_le_ofReal
              apply Set.indicator_le_indicator_of_subset _ (hF0 i)
              intro z hz
              exact lt_trans hz.1 (hdlt n)
            _ ≤ _ := lintegral_mono_set (Ioc_subset_Ioc le_rfl t.2.2)
        _ ≤ C n := by
          dsimp only [C]
          exact Finset.single_le_sum (f := fun j : ℕ => ∫⁻ s in Ioc (0 : ℝ) 1,
            ENNReal.ofReal ({z : ℂ | ‖z‖ < d n}.indicator (F j) (b s.toNNReal)))
            (fun _ _ => zero_le) (Finset.mem_range.mpr hi)
        _ ≤ C n + J n := le_add_right le_rfl
    · have hni : n ≤ i := by omega
      calc
        _ ≤ ENNReal.ofReal (∫ z, {z : ℂ | ‖z‖ ≤ d (n+1) ∧ ‖z‖ ≤ 1/2}.indicator
            (F i) z ∂(Measure.map (fun u => b u) (Measure.map Real.toNNReal
              (volume.restrict (Icc (0 : ℝ) 1))))) :=
          lintegral_inner_time_le_closed_unit_occupation b (F i) (hF i) (hF0 i)
            (d (n+1)) t.1 t.2.2
        _ ≤ ENNReal.ofReal |∫ z, {z : ℂ | ‖z‖ ≤ d (n+1) ∧ ‖z‖ ≤ 1/2}.indicator
            (F i) z ∂(Measure.map (fun u => b u) (Measure.map Real.toNNReal
              (volume.restrict (Icc (0 : ℝ) 1))))| := ENNReal.ofReal_le_ofReal (le_abs_self _)
        _ ≤ J n := by
          simpa only [J, Nat.add_sub_of_le hni] using
            le_iSup (fun j : ℕ => ENNReal.ofReal |∫ z,
              {z : ℂ | ‖z‖ ≤ d (n+1) ∧ ‖z‖ ≤ 1/2}.indicator (F (n+j)) z
                ∂(Measure.map (fun u => b u) (Measure.map Real.toNNReal
                  (volume.restrict (Icc (0 : ℝ) 1))))|) (i-n)
        _ ≤ C n + J n := le_add_left le_rfl

end HarmonicBalls
