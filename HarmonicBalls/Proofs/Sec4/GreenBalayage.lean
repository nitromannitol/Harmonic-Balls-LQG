import HarmonicBalls.Proofs.Sec4.Sweep
import HarmonicBalls.Proofs.Potential.GreenBall
import HarmonicBalls.Steps.Sec4.ClusterSubharmonicBall

/-!
# Lemma 4.3, Step 2: the harmonic correction of the Green function of an open set

`greenHarmonicCorrectionBalayageStep_holds : GreenHarmonicCorrectionBalayageStep`.

Let `O` be open, `L ⊆ O` compact with `cthickening (3ε) L ⊆ O`, `z ∈ L` and `m` a finite measure on `L` whose
regularized Newtonian potential `S = ∫ N_ε(x,·) m(dx)` equals `t N_ε(z,·)` at distance `> ε` from `L`.

* `N_ε(x,·) = -(2π)⁻¹ log max(|x - ·|, ε)` is continuous with the local super-mean-value property, and has the same
  harmonic minorants on `O` as `N(x,·)` (maximum principle on `B_ε(x)`), so `I_O[N(x,·)] = I_O[N_ε(x,·)]`.
* Greenian `O`: sweeping (Proofs/Sec4/Sweep.lean) gives `I_O[N_ε(x,·)] = lim_k sweep N_ε(x,·)`, harmonic;
  sweeping commutes with `∫ · m(dx)`. The swept function `g = t N_ε(z,·) - S` is continuous with support in
  `cthickening ε L`, hence `|g| ≤ C Σ_p (N_ε(p,·) - I_O[N_ε(p,·)])` over finitely many `p` (each term is `≥ 0` on
  `O` and `≥ (2π)⁻¹ log (3/2)` on `B_ε(p)`), whose sweeps tend to `0`. So `t H(z,·) - ∫ H(x,·) m(dx) = 0`.
* Non-Greenian `O`: no `N(x,·)`, `x ∈ L`, has a harmonic minorant (pole shift), and `H = 0`.
-/

namespace HarmonicBalls

open Complex Metric Real Filter Topology Set MeasureTheory InnerProductSpace Function

section RegularizedKernel

variable {ε : ℝ}

theorem regularizedNewtonKernel_le (hε : 0 < ε) (x y : ℂ) :
    regularizedNewtonKernel ε x y ≤ -(2 * π)⁻¹ * Real.log ε := by
  unfold regularizedNewtonKernel
  have h := Real.log_le_log hε (le_max_right ‖x - y‖ ε)
  have hπ : 0 ≤ (2 * π)⁻¹ := by positivity
  rw [neg_mul, neg_mul, neg_le_neg_iff]
  exact mul_le_mul_of_nonneg_left h hπ

theorem regularizedNewtonKernel_of_le_norm {x y : ℂ} (h : ε ≤ ‖x - y‖) :
    regularizedNewtonKernel ε x y = newtonKernel x y := by
  rw [regularizedNewtonKernel, newtonKernel, max_eq_left h]

theorem regularizedNewtonKernel_of_norm_le {x y : ℂ} (h : ‖x - y‖ ≤ ε) :
    regularizedNewtonKernel ε x y = -(2 * π)⁻¹ * Real.log ε := by
  rw [regularizedNewtonKernel, max_eq_right h]

theorem continuous_regularizedNewtonKernel (hε : 0 < ε) : Continuous (uncurry (regularizedNewtonKernel ε)) := by
  have e : uncurry (regularizedNewtonKernel ε) = fun p : ℂ × ℂ => -(2 * π)⁻¹ * Real.log (max ‖p.1 - p.2‖ ε) :=
    rfl
  rw [e]
  refine continuous_const.mul (Continuous.log ?_ fun p => ?_)
  · exact (continuous_fst.sub continuous_snd).norm.max continuous_const
  · exact (lt_of_lt_of_le hε (le_max_right _ _)).ne'

theorem continuous_regularizedNewtonKernel_right (hε : 0 < ε) (x : ℂ) :
    Continuous (regularizedNewtonKernel ε x) :=
  (continuous_regularizedNewtonKernel hε).comp (continuous_const.prodMk continuous_id)

theorem hasLocalSuperMean_regularizedNewtonKernel (hε : 0 < ε) (x : ℂ) (U : Set ℂ) :
    HasLocalSuperMean U (regularizedNewtonKernel ε x) := by
  have hc := continuous_regularizedNewtonKernel_right hε x
  intro y _
  rcases lt_trichotomy ‖x - y‖ ε with h | h | h
  · refine ⟨ε - ‖x - y‖, sub_pos.2 h, fun r hr => ⟨hc.continuousOn.circleIntegrable', le_of_eq ?_⟩⟩
    rw [regularizedNewtonKernel_of_norm_le h.le]
    have e : Real.circleAverage (regularizedNewtonKernel ε x) y r =
        Real.circleAverage (fun _ => -(2 * π)⁻¹ * Real.log ε) y r := by
      refine Real.circleAverage_congr_sphere fun w hw => regularizedNewtonKernel_of_norm_le ?_
      rw [mem_sphere, dist_eq_norm, abs_of_pos hr.1] at hw
      calc ‖x - w‖ = ‖(x - y) + (y - w)‖ := by ring_nf
        _ ≤ ‖x - y‖ + ‖y - w‖ := norm_add_le _ _
        _ ≤ ε := by rw [norm_sub_rev y w, hw]; linarith [hr.2]
    rw [e, Real.circleAverage_const]
  · refine ⟨1, one_pos, fun r _ => ⟨hc.continuousOn.circleIntegrable', ?_⟩⟩
    rw [regularizedNewtonKernel_of_norm_le h.le]
    exact Real.circleAverage_mono_on_of_le_circle hc.continuousOn.circleIntegrable'
      fun w _ => regularizedNewtonKernel_le hε x w
  · refine ⟨‖x - y‖ - ε, sub_pos.2 h, fun r hr => ⟨hc.continuousOn.circleIntegrable', le_of_eq ?_⟩⟩
    refine InnerProductSpace.HarmonicOnNhd.circleAverage_eq fun w hw => ?_
    rw [mem_closedBall, dist_eq_norm, abs_of_pos hr.1] at hw
    have hw' : ε < ‖x - w‖ := by
      have : ‖x - y‖ ≤ ‖x - w‖ + ‖w - y‖ := by
        calc ‖x - y‖ = ‖(x - w) + (w - y)‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      linarith [hr.2]
    have hev : regularizedNewtonKernel ε x =ᶠ[𝓝 w] newtonKernel x := by
      have ho : IsOpen {v : ℂ | ε < ‖x - v‖} := isOpen_lt continuous_const (continuous_const.sub continuous_id).norm
      filter_upwards [ho.mem_nhds hw'] with v hv using regularizedNewtonKernel_of_le_norm (le_of_lt hv)
    refine (harmonicAt_congr_nhds hev).2 (harmonicAt_newtonKernel fun hwx => ?_)
    rw [hwx, sub_self, norm_zero] at hw'
    linarith

/-- `N(x,·)` and `N_ε(x,·)` have the same harmonic minorants on `O ⊇ closedBall x (2ε)`. -/
theorem isHarmonicMinorant_regularized_iff (hε : 0 < ε) {O : Set ℂ} {x : ℂ} (hxO : closedBall x (2 * ε) ⊆ O)
    {h : ℂ → ℝ} : IsHarmonicMinorant O (newtonKernelEReal x) h ↔
      IsHarmonicMinorant O (fun w => (regularizedNewtonKernel ε x w : EReal)) h := by
  constructor
  · intro hh
    refine ⟨hh.1, fun w hw => ?_⟩
    show (h w : EReal) ≤ (regularizedNewtonKernel ε x w : EReal)
    by_cases hw' : ε ≤ ‖x - w‖
    · have hwx : w ≠ x := fun e => by rw [e, sub_self, norm_zero] at hw'; linarith
      rw [regularizedNewtonKernel_of_le_norm hw']
      simpa [newtonKernelEReal, hwx] using hh.2 w hw
    · rw [not_le] at hw'
      rw [regularizedNewtonKernel_of_norm_le hw'.le, EReal.coe_le_coe_iff]
      have hharm : HarmonicOnNhd h (ball x (2 * ε)) :=
        fun v hv => hh.1 v (hxO (ball_subset_closedBall hv))
      refine le_of_forall_mem_sphere_le_of_harmonicOnNhd hharm hε (by linarith) (fun v hv => ?_) ?_
      · have hvx : ‖x - v‖ = ε := by rw [mem_sphere, dist_eq_norm, norm_sub_rev] at hv; exact hv
        have hvne : v ≠ x := fun e => by rw [e, sub_self, norm_zero] at hvx; linarith
        have hv2 : v ∈ O := hxO (sphere_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)) hv)
        have := hh.2 v hv2
        simp only [newtonKernelEReal, hvne, ite_false, EReal.coe_le_coe_iff] at this
        rwa [newtonKernel, hvx] at this
      · rw [mem_closedBall, dist_eq_norm, norm_sub_rev]
        exact hw'.le
  · intro hh
    refine ⟨hh.1, fun w hw => (hh.2 w hw).trans ?_⟩
    by_cases hwx : w = x
    · simp [newtonKernelEReal, hwx]
    · simp only [newtonKernelEReal, hwx, ite_false, EReal.coe_le_coe_iff]
      unfold regularizedNewtonKernel newtonKernel
      have hpos : 0 < ‖x - w‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hwx))
      have hlog := Real.log_le_log hpos (le_max_left ‖x - w‖ ε)
      have hπ : 0 ≤ (2 * π)⁻¹ := by positivity
      rw [neg_mul, neg_mul, neg_le_neg_iff]
      exact mul_le_mul_of_nonneg_left hlog hπ

theorem greatestHarmonicMinorant_regularized (hε : 0 < ε) {O : Set ℂ} {x : ℂ}
    (hxO : closedBall x (2 * ε) ⊆ O) :
    greatestHarmonicMinorant O (newtonKernelEReal x) =
      greatestHarmonicMinorant O (fun w => (regularizedNewtonKernel ε x w : EReal)) := by
  funext y
  apply le_antisymm
  · exact iSup₂_le fun h hh => ((isHarmonicMinorant_regularized_iff hε hxO).1 hh).le_greatestHarmonicMinorant y
  · exact iSup₂_le fun h hh => ((isHarmonicMinorant_regularized_iff hε hxO).2 hh).le_greatestHarmonicMinorant y

/-- **Pole shift**: `N_ε(x',·) - N_ε(x,·) ≤ (2π)⁻¹ log (1 + |x - x'| / ε)`. -/
theorem regularizedNewtonKernel_sub_le (hε : 0 < ε) (x x' w : ℂ) :
    regularizedNewtonKernel ε x' w - regularizedNewtonKernel ε x w ≤
      (2 * π)⁻¹ * Real.log (1 + ‖x - x'‖ / ε) := by
  have hb : ε ≤ max ‖x' - w‖ ε := le_max_right _ _
  have hbpos : 0 < max ‖x' - w‖ ε := hε.trans_le hb
  have hapos : 0 < max ‖x - w‖ ε := hε.trans_le (le_max_right _ _)
  have hd : 0 ≤ ‖x - x'‖ / ε := div_nonneg (norm_nonneg _) hε.le
  have h1 : ‖x - w‖ ≤ ‖x' - w‖ + ‖x - x'‖ := by
    calc ‖x - w‖ = ‖(x - x') + (x' - w)‖ := by ring_nf
      _ ≤ ‖x - x'‖ + ‖x' - w‖ := norm_add_le _ _
      _ = _ := add_comm _ _
  have h2 : max ‖x - w‖ ε ≤ max ‖x' - w‖ ε + ‖x - x'‖ :=
    max_le (h1.trans (by linarith [le_max_left ‖x' - w‖ ε])) (by linarith [norm_nonneg (x - x')])
  have h3 : ‖x - x'‖ ≤ max ‖x' - w‖ ε * (‖x - x'‖ / ε) := by
    calc ‖x - x'‖ = ε * (‖x - x'‖ / ε) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hb hd
  have h4 : max ‖x - w‖ ε ≤ max ‖x' - w‖ ε * (1 + ‖x - x'‖ / ε) := by nlinarith
  have h5 := Real.log_le_log hapos h4
  rw [Real.log_mul hbpos.ne' (by positivity)] at h5
  have hπ : 0 ≤ (2 * π)⁻¹ := by positivity
  unfold regularizedNewtonKernel
  have : -(2 * π)⁻¹ * Real.log (max ‖x' - w‖ ε) - -(2 * π)⁻¹ * Real.log (max ‖x - w‖ ε) =
      (2 * π)⁻¹ * (Real.log (max ‖x - w‖ ε) - Real.log (max ‖x' - w‖ ε)) := by ring
  rw [this]
  exact mul_le_mul_of_nonneg_left (by linarith) hπ

end RegularizedKernel

theorem sweep_finset_sum {O : Set ℂ} (hO : IsOpen O) {ι : Type*} (T : Finset ι) {f : ι → ℂ → ℝ}
    (hf : ∀ i ∈ T, ContinuousOn (f i) O) (k : ℕ) :
    sweep O (fun w => ∑ i ∈ T, f i w) k = fun w => ∑ i ∈ T, sweep O (f i) k w := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact sweep_harmonic (harmonicOnNhd_const 0) k
  | insert a T ha ih =>
    have hfa := hf a (Finset.mem_insert_self a T)
    have hfT : ∀ i ∈ T, ContinuousOn (f i) O := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have e : (fun w => ∑ i ∈ insert a T, f i w) = f a + fun w => ∑ i ∈ T, f i w := by
      funext w
      simp [Finset.sum_insert ha]
    rw [e, sweep_add hO hfa (continuousOn_finsetSum T hfT) k, ih hfT]
    funext w
    simp [Finset.sum_insert ha]

/-- **Lemma 4.3, Step 2: the harmonic correction of the Green function** (`GreenHarmonicCorrectionBalayageStep`). -/
theorem greenHarmonicCorrectionBalayageStep_holds : GreenHarmonicCorrectionBalayageStep := by
  intro O L m z t ε hO hL hm hmL hzL hε hLO hbal
  have hLε : L ⊆ cthickening ε L := self_subset_cthickening L
  have hball : ∀ p ∈ cthickening ε L, closedBall p (2 * ε) ⊆ O := by
    intro p hp
    refine (closedBall_subset_cthickening hp (2 * ε)).trans ?_
    refine (cthickening_cthickening_subset (by linarith) hε.le L).trans ?_
    rw [show 2 * ε + ε = 3 * ε by ring]
    exact hLO
  have hcN := continuous_regularizedNewtonKernel_right hε
  by_cases hG : ∃ h, IsHarmonicMinorant O (newtonKernelEReal z) h
  swap
  · -- non-Greenian `O`
    have hnone : ∀ x ∈ L, ∀ h, ¬IsHarmonicMinorant O (newtonKernelEReal x) h := by
      intro x hx h hh
      apply hG
      have h1 := (isHarmonicMinorant_regularized_iff hε (hball x (hLε hx))).1 hh
      refine ⟨fun w => h w - (2 * π)⁻¹ * Real.log (1 + ‖z - x‖ / ε),
        (isHarmonicMinorant_regularized_iff hε (hball z (hLε hzL))).2 ⟨fun w hw => (h1.1 w hw).sub
          (harmonicAt_const _), fun w hw => ?_⟩⟩
      have h2 := EReal.coe_le_coe_iff.1 (h1.2 w hw)
      have h3 := regularizedNewtonKernel_sub_le hε z x w
      exact EReal.coe_le_coe_iff.2 (by linarith)
    refine ⟨fun _ _ => 0, measurable_const, fun x hx y _ => ?_, fun K _ _ => ⟨0, by simp⟩, fun y _ => by simp⟩
    have hbot : greatestHarmonicMinorant O (newtonKernelEReal x) y = ⊥ := by
      simp [greatestHarmonicMinorant, hnone x hx]
    rw [hbot, EReal.toReal_bot]
  -- Greenian `O`
  obtain ⟨hz0, hhz0⟩ := hG
  have hhz := (isHarmonicMinorant_regularized_iff hε (hball z (hLε hzL))).1 hhz0
  obtain ⟨D, hD⟩ := (hL.cthickening (r := ε)).isBounded.subset_closedBall z
  have hDz : ∀ p ∈ cthickening ε L, ‖p - z‖ ≤ D := fun p hp => by
    have := hD hp
    rwa [mem_closedBall, dist_eq_norm] at this
  have hD0 : 0 ≤ D := by simpa using hDz z (hLε hzL)
  -- the shift constant and the harmonic lower bound
  have hC0 : 0 ≤ (2 * π)⁻¹ * Real.log (1 + D / ε) :=
    mul_nonneg (by positivity) (Real.log_nonneg (by linarith [div_nonneg hD0 hε.le]))
  have hshift : ∀ p ∈ cthickening ε L, ∀ w, regularizedNewtonKernel ε z w -
      (2 * π)⁻¹ * Real.log (1 + D / ε) ≤ regularizedNewtonKernel ε p w := by
    intro p hp w
    have h1 := regularizedNewtonKernel_sub_le hε p z w
    have h2 : Real.log (1 + ‖p - z‖ / ε) ≤ Real.log (1 + D / ε) :=
      Real.log_le_log (by positivity) (by
        have := div_le_div_of_nonneg_right (hDz p hp) hε.le
        linarith)
    have hπ : 0 ≤ (2 * π)⁻¹ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 hπ]
  classical
  set C₀ : ℝ := (2 * π)⁻¹ * Real.log (1 + D / ε) with hC₀
  let lo : ℂ → ℝ := O.piecewise (fun w => hz0 w - C₀) (fun w => regularizedNewtonKernel ε z w - C₀)
  have hlo1 : HarmonicOnNhd lo O := by
    intro w hw
    have hev : lo =ᶠ[𝓝 w] fun v => hz0 v - C₀ := by
      filter_upwards [hO.mem_nhds hw] with v hv using Set.piecewise_eq_of_mem _ _ _ hv
    exact (harmonicAt_congr_nhds hev).2 ((hhz.1 w hw).sub (harmonicAt_const _))
  have hlo2 : Measurable lo :=
    ContinuousOn.measurable_piecewise ((harmonicOnNhd_continuousOn hhz.1).sub continuousOn_const)
      ((hcN z).sub continuous_const).continuousOn hO.measurableSet
  have hlo3 : ∀ p ∈ cthickening ε L, ∀ w, lo w ≤ regularizedNewtonKernel ε p w := by
    intro p hp w
    by_cases hw : w ∈ O
    · have h1 : lo w = hz0 w - C₀ := Set.piecewise_eq_of_mem _ _ _ hw
      have h2 := EReal.coe_le_coe_iff.1 (hhz.2 w hw)
      rw [h1]
      linarith [hshift p hp w]
    · have h1 : lo w = regularizedNewtonKernel ε z w - C₀ := Set.piecewise_eq_of_notMem _ _ _ hw
      rw [h1]
      exact hshift p hp w
  have hlo4 : ∀ w, lo w ≤ -(2 * π)⁻¹ * Real.log ε :=
    fun w => (hlo3 z (hLε hzL) w).trans (regularizedNewtonKernel_le hε z w)
  -- the clipped family
  let F : ℂ → ℂ → ℝ := fun x w => max (regularizedNewtonKernel ε x w) (lo w)
  have hF1 : Measurable (uncurry F) :=
    (continuous_regularizedNewtonKernel hε).measurable.max (hlo2.comp measurable_snd)
  have hF2 : ∀ x, ContinuousOn (F x) O :=
    fun x => ContinuousOn.sup (hcN x).continuousOn (harmonicOnNhd_continuousOn hlo1)
  have hF3 : ∀ x, ∀ y ∈ O, lo y ≤ F x y ∧ F x y ≤ -(2 * π)⁻¹ * Real.log ε :=
    fun x y _ => ⟨le_max_right _ _, max_le (regularizedNewtonKernel_le hε x y) (hlo4 y)⟩
  have hF4 : ∀ p ∈ cthickening ε L, F p = regularizedNewtonKernel ε p :=
    fun p hp => funext fun w => max_eq_left (hlo3 p hp w)
  have hSI := fun k => sweep_integral (m := m) hO hF1 hF2 hlo1 hF3 k
  have hbk : ∀ k x, ∀ y ∈ O, lo y ≤ sweep O (F x) k y ∧ sweep O (F x) k y ≤ -(2 * π)⁻¹ * Real.log ε := by
    intro k x y hy
    have h1 := sweep_mono hO (harmonicOnNhd_continuousOn hlo1) (hF2 x) (fun w hw => (hF3 x w hw).1) k y hy
    have h2 := sweep_mono hO (hF2 x) continuousOn_const (fun w hw => (hF3 x w hw).2) k y hy
    rw [sweep_harmonic hlo1] at h1
    rw [sweep_harmonic (harmonicOnNhd_const _)] at h2
    exact ⟨h1, h2⟩
  -- sweep limits of the regularized kernels
  have hlim : ∀ p ∈ cthickening ε L, _ := fun p hp =>
    sweep_limit hO (hcN p).continuousOn (hasLocalSuperMean_regularizedNewtonKernel hε p O) hlo1
      (fun w _ => hlo3 p hp w)
  let H : ℂ → ℂ → ℝ := fun x y => ⨅ k, sweep O (F x) k y
  have hH1 : Measurable (uncurry H) := Measurable.iInf fun k => (hSI k).1
  have hHF : ∀ p ∈ cthickening ε L, ∀ y, H p y = ⨅ k, sweep O (regularizedNewtonKernel ε p) k y := by
    intro p hp y
    simp only [H, hF4 p hp]
  have hbdd : ∀ x, ∀ y ∈ O, BddBelow (range fun k => sweep O (F x) k y) :=
    fun x y hy => ⟨lo y, by rintro _ ⟨k, rfl⟩; exact (hbk k x y hy).1⟩
  have hHb : ∀ x, ∀ y ∈ O, lo y ≤ H x y ∧ H x y ≤ -(2 * π)⁻¹ * Real.log ε :=
    fun x y hy => ⟨le_ciInf fun k => (hbk k x y hy).1, (ciInf_le (hbdd x y hy) 0).trans (hbk 0 x y hy).2⟩
  refine ⟨H, hH1, fun x hx y hy => ?_, fun K hK hKO => ?_, fun y hy => ?_⟩
  · -- agreement with the greatest harmonic minorant
    rw [greatestHarmonicMinorant_regularized hε (hball x (hLε hx)),
      greatestHarmonicMinorant_eq_of_sweep_limit hO (hcN x).continuousOn
        (hasLocalSuperMean_regularizedNewtonKernel hε x O) hlo1 (fun w _ => hlo3 x (hLε hx) w) y hy,
      EReal.toReal_coe, hHF x (hLε hx)]
  · -- local bound
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn ((harmonicOnNhd_continuousOn hlo1).mono hKO)
    refine ⟨B + |-(2 * π)⁻¹ * Real.log ε|, fun x _ y hy => ?_⟩
    obtain ⟨h1, h2⟩ := hHb x y (hKO hy)
    have h3 := hB y hy
    rw [Real.norm_eq_abs, abs_le] at h3
    rw [abs_le]
    constructor <;> linarith [le_abs_self (-(2 * π)⁻¹ * Real.log ε), neg_abs_le (-(2 * π)⁻¹ * Real.log ε)]
  · -- the balayage identity
    have hae : ∀ᵐ x ∂m, x ∈ L := by
      rw [ae_iff]
      simpa [compl_def] using hmL
    let S : ℂ → ℝ := fun w => ∫ x, regularizedNewtonKernel ε x w ∂m
    have hmres : m.restrict L = m := Measure.restrict_eq_self_of_ae_mem hae
    have hS1 : Continuous S := by
      have h := continuous_parametric_integral_of_continuous (μ := m)
        (f := fun w x => regularizedNewtonKernel ε x w)
        ((continuous_regularizedNewtonKernel hε).comp continuous_swap) hL
      simpa only [S, hmres] using h
    have hS2 : (fun w => ∫ x, F x w ∂m) = S := by
      funext w
      refine integral_congr_ae ?_
      filter_upwards [hae] with x hx
      exact congrFun (hF4 x (hLε hx)) w
    have hS3 : ∀ k, sweep O S k y = ∫ x, sweep O (F x) k y ∂m := by
      intro k
      rw [← hS2]
      exact (hSI k).2 y
    have hS4 : Tendsto (fun k => ∫ x, sweep O (F x) k y ∂m) atTop (𝓝 (∫ x, H x y ∂m)) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => |lo y| + |-(2 * π)⁻¹ * Real.log ε|)
        (fun k => ((hSI k).1.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
        (integrable_const _) (fun k => Eventually.of_forall fun x => ?_) ?_
      · obtain ⟨h1, h2⟩ := hbk k x y hy
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith [le_abs_self (lo y), neg_abs_le (lo y),
          le_abs_self (-(2 * π)⁻¹ * Real.log ε), neg_abs_le (-(2 * π)⁻¹ * Real.log ε)]
      · filter_upwards [hae] with x hx
        have := ((hlim x (hLε hx)).2.2.1 y hy)
        rw [hF4 x (hLε hx)]
        simpa only [H, hF4 x (hLε hx)] using this
    have hS5 : Tendsto (fun k => sweep O (regularizedNewtonKernel ε z) k y) atTop (𝓝 (H z y)) := by
      rw [hHF z (hLε hzL)]
      exact (hlim z (hLε hzL)).2.2.1 y hy
    -- the swept difference
    let g : ℂ → ℝ := fun w => t * regularizedNewtonKernel ε z w - S w
    have hg : Continuous g := (continuous_const.mul (hcN z)).sub hS1
    have hgsweep : ∀ k, sweep O g k y = t * sweep O (regularizedNewtonKernel ε z) k y - sweep O S k y := by
      intro k
      have e : g = t • regularizedNewtonKernel ε z + (-1 : ℝ) • S := by
        funext w
        simp only [g, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [e, sweep_add hO ((hcN z).continuousOn.const_smul t) (hS1.continuousOn.const_smul _), sweep_smul,
        sweep_smul]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hlimg : Tendsto (fun k => sweep O g k y) atTop (𝓝 (t * H z y - ∫ x, H x y ∂m)) := by
      simp only [hgsweep, hS3]
      exact (hS5.const_mul t).sub hS4
    -- `g` vanishes away from `L`
    have hg0 : ∀ w ∉ cthickening ε L, g w = 0 := by
      intro w hw
      have hfar : ∀ x ∈ L, ε < ‖x - w‖ := by
        intro x hx
        by_contra hc
        rw [not_lt] at hc
        exact hw (mem_cthickening_of_dist_le w x ε L hx (by rw [dist_eq_norm, norm_sub_rev]; exact hc))
      simp only [g, S, hbal w hfar, sub_self]
    -- the comparison function
    have hLεc : IsCompact (cthickening ε L) := hL.cthickening
    obtain ⟨T, hTsub, hTcov⟩ := hLεc.elim_nhds_subcover (fun p => ball p ε) (fun p _ => ball_mem_nhds p hε)
    obtain ⟨Bg, hBg⟩ := hLεc.exists_bound_of_continuousOn hg.continuousOn
    let Gp : ℂ → ℂ → ℝ := fun p w => ⨅ k, sweep O (regularizedNewtonKernel ε p) k w
    let s : ℂ → ℝ := fun w => ∑ p ∈ T, (regularizedNewtonKernel ε p w - Gp p w)
    have hGpc : ∀ p ∈ T, ContinuousOn (Gp p) O :=
      fun p hp => harmonicOnNhd_continuousOn (hlim p (hTsub p hp)).1
    have hs0 : ∀ p ∈ T, ∀ w ∈ O, 0 ≤ regularizedNewtonKernel ε p w - Gp p w :=
      fun p hp w hw => sub_nonneg.2 ((hlim p (hTsub p hp)).2.1 w hw)
    have hκ : ∀ p ∈ T, ∀ w ∈ ball p ε, (2 * π)⁻¹ * Real.log (3 / 2) ≤
        regularizedNewtonKernel ε p w - Gp p w := by
      intro p hp w hw
      have hpL := hTsub p hp
      have hharm : HarmonicOnNhd (Gp p) (ball p (2 * ε)) :=
        fun v hv => (hlim p hpL).1 v (hball p hpL (ball_subset_closedBall hv))
      have hmax : Gp p w ≤ -(2 * π)⁻¹ * Real.log (3 / 2 * ε) := by
        refine le_of_forall_mem_sphere_le_of_harmonicOnNhd (ρ := 3 / 2 * ε) hharm (by positivity) (by linarith)
          (fun v hv => ?_) (ball_subset_closedBall (ball_subset_ball (by linarith) hw))
        have hvp : ‖p - v‖ = 3 / 2 * ε := by
          rw [mem_sphere, dist_eq_norm, norm_sub_rev] at hv
          exact hv
        have h1 := (hlim p hpL).2.1 v (hball p hpL (sphere_subset_closedBall.trans
          (closedBall_subset_closedBall (by linarith)) hv))
        rw [regularizedNewtonKernel_of_le_norm (by rw [hvp]; linarith), newtonKernel, hvp] at h1
        exact h1
      have hwp : ‖p - w‖ ≤ ε := by
        rw [mem_ball, dist_eq_norm, norm_sub_rev] at hw
        exact hw.le
      rw [regularizedNewtonKernel_of_norm_le hwp]
      have e : Real.log (3 / 2 * ε) = Real.log (3 / 2) + Real.log ε :=
        Real.log_mul (by norm_num) hε.ne'
      rw [e] at hmax
      nlinarith
    have hκpos : 0 < (2 * π)⁻¹ * Real.log (3 / 2) :=
      mul_pos (by positivity) (Real.log_pos (by norm_num))
    set κ := (2 * π)⁻¹ * Real.log (3 / 2) with hκdef
    set A : ℝ := max Bg 0 / κ with hA
    have hA0 : 0 ≤ A := div_nonneg (le_max_right _ _) hκpos.le
    have hsc : ContinuousOn s O :=
      continuousOn_finsetSum T fun p hp => (hcN p).continuousOn.sub (hGpc p hp)
    have hdom : ∀ w ∈ O, |g w| ≤ A * s w := by
      intro w hw
      have hsnn : 0 ≤ s w := Finset.sum_nonneg fun p hp => hs0 p hp w hw
      by_cases hwL : w ∈ cthickening ε L
      · obtain ⟨p, hp, hwp⟩ : ∃ p ∈ T, w ∈ ball p ε := by
          have := hTcov hwL
          simpa only [mem_iUnion, exists_prop] using this
        have h1 : κ ≤ s w :=
          (hκ p hp w hwp).trans (Finset.single_le_sum (fun q hq => hs0 q hq w hw) hp)
        have h2' : |g w| ≤ Bg := by simpa [Real.norm_eq_abs] using hBg w hwL
        have h2 : |g w| ≤ max Bg 0 := h2'.trans (le_max_left _ _)
        calc |g w| ≤ max Bg 0 := h2
          _ = A * κ := by rw [hA, div_mul_cancel₀ _ hκpos.ne']
          _ ≤ A * s w := mul_le_mul_of_nonneg_left h1 hA0
      · rw [hg0 w hwL, abs_zero]
        exact mul_nonneg hA0 hsnn
    have hssweep : ∀ k, sweep O s k y = ∑ p ∈ T, (sweep O (regularizedNewtonKernel ε p) k y - Gp p y) := by
      intro k
      have h := congrFun (sweep_finset_sum hO T (f := fun p w => regularizedNewtonKernel ε p w - Gp p w)
        (fun p hp => (hcN p).continuousOn.sub (hGpc p hp)) k) y
      simp only [s]
      rw [h]
      refine Finset.sum_congr rfl fun p hp => ?_
      have e : (fun w => regularizedNewtonKernel ε p w - Gp p w) =
          regularizedNewtonKernel ε p + (-1 : ℝ) • Gp p := by
        funext w
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [e, sweep_add hO (hcN p).continuousOn ((hGpc p hp).const_smul _), sweep_smul,
        sweep_harmonic (hlim p (hTsub p hp)).1]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hlims : Tendsto (fun k => sweep O s k y) atTop (𝓝 0) := by
      simp only [hssweep]
      have : (0 : ℝ) = ∑ p ∈ T, (Gp p y - Gp p y) := by simp
      rw [this]
      exact tendsto_finsetSum T fun p hp => ((hlim p (hTsub p hp)).2.2.1 y hy).sub tendsto_const_nhds
    have hup : ∀ k, sweep O g k y ≤ A * sweep O s k y := by
      intro k
      have h := sweep_mono hO hg.continuousOn (hsc.const_smul A)
        (fun w hw => (le_abs_self _).trans (hdom w hw)) k y hy
      rwa [sweep_smul] at h
    have hlow : ∀ k, -(A * sweep O s k y) ≤ sweep O g k y := by
      intro k
      have h := sweep_mono hO (hsc.const_smul A).neg hg.continuousOn
        (fun w hw => by
          have := (neg_abs_le (g w)).trans' (neg_le_neg (hdom w hw))
          simpa using this) k y hy
      have e : -(A • s) = (-A) • s := by funext w; simp
      rw [e, sweep_smul] at h
      simpa using h
    have hlim0 : Tendsto (fun k => sweep O g k y) atTop (𝓝 0) := by
      have hu : Tendsto (fun k => A * sweep O s k y) atTop (𝓝 0) := by
        simpa using hlims.const_mul A
      have hl : Tendsto (fun k => -(A * sweep O s k y)) atTop (𝓝 0) := by simpa using hu.neg
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl hu hlow hup
    have := tendsto_nhds_unique hlimg hlim0
    linarith

end HarmonicBalls
