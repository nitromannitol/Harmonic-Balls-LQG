import HarmonicBalls.Proofs.Sec10.PoleAvoidingGoodAnnulusDecay
import HarmonicBalls.Proofs.Sec6.LowMass

/-! # Multiscale decay for components avoiding the pole -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Section6
open scoped ENNReal Pointwise

/-- The shell iteration of Lemma 6.13 extends to a component avoiding the pole,
provided the one-annulus decay is available for that component. The containing
disc itself may contain the pole. -/
theorem pole_avoiding_component_lowMass_smallOdometer
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {βminus βplus : ℝ} (hV : VolumeGrowth μ 1 βminus βplus)
    {β : ℝ} {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1)
    {t : ℝ} (ht : 0 < t) {a b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1)
    {N₀ : ℕ} (hN₀ : 200 ≤ N₀) {C₃ : ℝ} (hC₃ : 0 < C₃)
    {ρ : ℝ} (hρ : 0 < ρ) {x₀ : ℂ} (hball : closedBall x₀ ρ ⊆ ball 0 1)
    (hVG3 : VeryGoodCriterionThree μ ρ x₀ N₀ a b C₃)
    {Λ : Set ℂ} (hΛ : Λ ∈ connectedComponentsIn (cluster μ 1 z t ∩ ball x₀ ρ))
    (hzΛ : z ∉ Λ)
    (hdec : ∀ r : ℝ, 0 < r → ∀ w : ℂ, closedBall w (5 * r) ⊆ ball x₀ ρ →
      IsGoodAnnulus μ r w a b →
      μ (Λ ∩ annulus w (3 * r) (5 * r)) ≤ ENNReal.ofReal a * μ (annulus w (3 * r) (5 * r)) →
      (⨆ x ∈ Λ ∩ ball w (4 * r), odometerExt μ z t x) ≤
        ENNReal.ofReal b * ⨆ x ∈ Λ ∩ annulus w (3 * r) (5 * r), odometerExt μ z t x)
    (j : ℕ)
    (hmass : ∀ r : ℝ, 0 < r → ∀ w ∈ ball (0 : ℂ) 1,
      annulus w r (7 * r) ⊆ annulus x₀ (ρ / 2) (shellOuterRadius ρ j) →
      μ (Λ ∩ annulus w (3 * r) (5 * r)) ≤
        ENNReal.ofReal a * annulusBallMassSize μ β ρ x₀ * ENNReal.ofReal (shellScale N₀ j ^ β)) :
    (⨆ x ∈ Λ ∩ annulus x₀ (ρ / 2) (shellOuterRadius ρ (j + 1)), odometerExt μ z t x) ≤
      ENNReal.ofReal (b ^ (Real.log 2 / (2 * Real.log 7) * C₃ * ((N₀ : ℝ) + j))) *
        ⨆ x ∈ Λ ∩ annulus x₀ (ρ / 2) (shellOuterRadius ρ j), odometerExt μ z t x := by
  have hΛ' : Λ ∈ connectedComponentsIn (ball x₀ ρ ∩ cluster μ 1 z t) := by
    simpa only [inter_comm] using hΛ
  set ε := shellScale N₀ j with hεdef
  set S₀ := ⨆ x ∈ Λ ∩ annulus x₀ (ρ / 2) (shellOuterRadius ρ j), odometerExt μ z t x with hS₀
  set M := annulusBallMassSize μ β ρ x₀ with hMdef
  have hε0 : 0 < ε := by rw [hεdef, shellScale, dyadicScale]; positivity
  have hεsmall : ε ≤ (2 : ℝ)⁻¹ ^ 200 := by
    rw [hεdef, shellScale, dyadicScale]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hε1 : ε ≤ 1 := hεsmall.trans (by norm_num)
  have hsq : ε ≤ Real.sqrt ε := Real.le_sqrt_of_sq_le (by nlinarith)
  have hsq0 : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε0
  have hερ0 : 0 < ε * ρ := by positivity
  have hsqρ : ε * ρ ≤ Real.sqrt ε * ρ := mul_le_mul_of_nonneg_right hsq hρ.le
  have hερs : ε * ρ ≤ (2 : ℝ)⁻¹ ^ 200 * ρ := mul_le_mul_of_nonneg_right hεsmall hρ.le
  have hΛsub : Λ ⊆ cluster μ 1 z t ∩ ball x₀ ρ := by
    obtain ⟨y, -, rfl⟩ := hΛ; exact connectedComponentIn_subset _ _
  have hB1 : ball x₀ ρ ⊆ ball 0 1 := fun x hx => hball (ball_subset_closedBall hx)
  have hjρ : shellOuterRadius ρ j ≤ 7 / 8 * ρ := shellOuterRadius_le hρ j
  have hA0ρ : annulus x₀ (ρ / 2) (shellOuterRadius ρ j) ⊆ ball x₀ ρ :=
    sdiff_subset.trans (ball_subset_ball (by linarith))
  -- the bound at points of `Λ̃_t ∩ S_j`
  have key : ∀ x ∈ Λ ∩ shell x₀ ρ j,
      odometerExt μ z t x ≤ ENNReal.ofReal (b ^ (Real.log 2 / (2 * Real.log 7) * C₃ * ((N₀ : ℝ) + j))) * S₀ := by
    rintro x ⟨hxΛ, hxS⟩
    have hδ : 0 < ε * ρ / 100 := by positivity
    obtain ⟨jj, kk, hxw⟩ := exists_lattice_near x hδ
    set w : ℂ := ((ε * ρ / 100 : ℝ) : ℂ) * ((jj : ℂ) + (kk : ℂ) * Complex.I) with hw_def
    have hbx := ball_subset_of_mem_shell hρ hN₀ hxS
    rw [← hεdef] at hbx
    have hxw' : dist w x ≤ ε * ρ / 100 := by rw [dist_comm, dist_eq_norm]; exact hxw
    have hin : ∀ y : ℂ, ∀ s : ℝ, dist y w < s → s + ε * ρ / 100 < 8 * Real.sqrt ε * ρ →
        y ∈ annulus x₀ (ρ / 2) (shellOuterRadius ρ j) := fun y s hy hs =>
      hbx (mem_ball.2 (by linarith [dist_triangle y w x]))
    have h8 : ε * ρ / 100 < 8 * Real.sqrt ε * ρ := by linarith
    have hwA : w ∈ annulus x₀ (ρ / 2) ρ :=
      annulus_subset_annulus le_rfl (by linarith) (hin w (ε * ρ / 100 / 2) (by rw [dist_self]; positivity)
        (by linarith))
    have hw1 : w ∈ ball (0 : ℂ) 1 := hB1 hwA.1
    -- (VG-iii) at `w`, scale `n = N₀ + j`
    have hvg := hVG3 (N₀ + j) (Nat.le_add_right _ _) w ⟨⟨jj, kk, rfl⟩, hwA⟩
    set R : Set ℝ := {r : ℝ | r ∈ Icc (dyadicScale (N₀ + j) * ρ) (Real.sqrt (dyadicScale (N₀ + j)) * ρ) ∧
      (∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus μ r w a b} with hRdef
    have hRfin : R.Finite :=
      finite_of_geometric (q := (7 : ℝ)⁻¹) (A := ρ) (lo := ε * ρ) (by norm_num) (by norm_num) (by positivity)
        fun r hr => ⟨hr.1.1, by obtain ⟨k, -, hk⟩ := hr.2.1; exact ⟨k, hk⟩⟩
    -- facts at each good radius
    have hR : ∀ r ∈ R, ε * ρ ≤ r ∧ r ≤ Real.sqrt ε * ρ ∧ IsGoodAnnulus μ r w a b ∧
        ∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k := fun r hr => ⟨hr.1.1, hr.1.2, hr.2.2, hr.2.1⟩
    have hann7 : ∀ r ∈ R, annulus w r (7 * r) ⊆ annulus x₀ (ρ / 2) (shellOuterRadius ρ j) := by
      intro r hr y hy
      obtain ⟨h1, h2, -, -⟩ := hR r hr
      exact hin y (7 * r) hy.1 (by linarith)
    have h35 : ∀ r : ℝ, 0 < r → annulus w (3 * r) (5 * r) ⊆ annulus w r (7 * r) :=
      fun r hr => annulus_subset_annulus (by linarith) (by linarith)
    have hdecay : ∀ r ∈ R, ⨆ y ∈ Λ ∩ ball w (4 * r), odometerExt μ z t y ≤
        ENNReal.ofReal b * ⨆ y ∈ Λ ∩ annulus w (3 * r) (5 * r), odometerExt μ z t y := by
      intro r hr
      obtain ⟨h1, h2, hgood, -⟩ := hR r hr
      have hr0 : 0 < r := lt_of_lt_of_le (by positivity) h1
      have hcl : closedBall w (5 * r) ⊆ ball x₀ ρ := fun y hy =>
        hA0ρ (hin y (5 * r + ε * ρ / 200) (lt_of_le_of_lt (mem_closedBall.1 hy) (by linarith))
          (by linarith))
      -- Step 1: the mass condition
      have hm1 := hmass r hr0 w hw1 (hann7 r hr)
      set c : ℂ := w + ((4 * r : ℝ) : ℂ) with hc_def
      have hcw : dist c w = 4 * r := by
        rw [hc_def, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity)]
      have hcA : c ∈ annulus x₀ (ρ / 2) ρ :=
        annulus_subset_annulus le_rfl (by linarith) (hin c (4 * r + ε * ρ / 200) (by linarith)
          (by linarith))
      have hερ : ε * ρ ∈ Ioo 0 (ρ / 4) := ⟨hερ0, by norm_num at hερs ⊢; linarith⟩
      have hMc : M ≤ μ (ball c (ε * ρ)) / ENNReal.ofReal ((ε * ρ / ρ) ^ β) :=
        iInf₂_le_of_le c hcA (iInf₂_le (ε * ρ) hερ)
      rw [mul_div_cancel_right₀ ε hρ.ne'] at hMc
      have hεβ : ENNReal.ofReal (ε ^ β) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
      have hMc' : M * ENNReal.ofReal (ε ^ β) ≤ μ (ball c (ε * ρ)) :=
        (ENNReal.le_div_iff_mul_le (Or.inl hεβ) (Or.inl ENNReal.ofReal_ne_top)).1 hMc
      have hballc : ball c (ε * ρ) ⊆ annulus w (3 * r) (5 * r) := by
        intro y hy
        have hyc := mem_ball.1 hy
        have t1 := dist_triangle y c w
        have t2 := dist_triangle c y w
        rw [dist_comm c y] at t2
        refine ⟨mem_ball.2 (by linarith), fun hc' => ?_⟩
        have := mem_closedBall.1 hc'
        linarith
      have hmass' : μ (Λ ∩ annulus w (3 * r) (5 * r)) ≤
          ENNReal.ofReal a * μ (annulus w (3 * r) (5 * r)) := by
        calc μ (Λ ∩ annulus w (3 * r) (5 * r)) ≤ ENNReal.ofReal a * M * ENNReal.ofReal (ε ^ β) := hm1
          _ = ENNReal.ofReal a * (M * ENNReal.ofReal (ε ^ β)) := by ring
          _ ≤ ENNReal.ofReal a * μ (ball c (ε * ρ)) := mul_le_mul_right hMc' _
          _ ≤ ENNReal.ofReal a * μ (annulus w (3 * r) (5 * r)) := mul_le_mul_right (measure_mono hballc) _
      exact hdec r hr0 w hcl hgood hmass'
    -- Step 3: the iteration
    set F := hRfin.toFinset with hF
    have hmemF : ∀ r, r ∈ F ↔ r ∈ R := fun r => Set.Finite.mem_toFinset hRfin
    have hiter := iterate_over_radii (F := F) (B := ENNReal.ofReal b) (S₀ := S₀)
      (f := fun r => ⨆ y ∈ Λ ∩ ball w (4 * r), odometerExt μ z t y)
      (g := fun r => ⨆ y ∈ Λ ∩ annulus w (3 * r) (5 * r), odometerExt μ z t y)
      (fun r hr => hdecay r ((hmemF r).1 hr))
      (fun r hr => biSup_mono fun y hy =>
        ⟨hy.1, hann7 r ((hmemF r).1 hr) (h35 r (lt_of_lt_of_le (by positivity) ((hR r ((hmemF r).1 hr)).1)) hy.2)⟩)
      (fun r hr r' hr' hlt => by
        obtain ⟨h1, -, -, k, -, hk⟩ := hR r ((hmemF r).1 hr)
        obtain ⟨-, -, -, k', -, hk'⟩ := hR r' ((hmemF r').1 hr')
        have hr0 : 0 < r := lt_of_lt_of_le (by positivity) h1
        have h7 : 7 * r ≤ r' := by
          rw [hk, hk'] at hlt ⊢
          have hkk : k' < k := by
            by_contra hcon
            have : (7 : ℝ)⁻¹ ^ k' ≤ (7 : ℝ)⁻¹ ^ k :=
              pow_le_pow_of_le_one (by norm_num) (by norm_num) (not_lt.1 hcon)
            have := mul_le_mul_of_nonneg_left this hρ.le
            linarith
          have : (7 : ℝ)⁻¹ ^ (k' + 1) ≥ (7 : ℝ)⁻¹ ^ k :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) hkk
          rw [pow_succ] at this
          have h7ρ := mul_le_mul_of_nonneg_left this (le_of_lt (by positivity : (0 : ℝ) < 7 * ρ))
          linarith
        exact biSup_mono fun y hy => ⟨hy.1, ball_subset_ball (by linarith) hy.2.1⟩)
    -- the smallest good radius covers `x`
    have hcount : C₃ * Real.logb 7 (dyadicScale (N₀ + j) ^ (-(1 / 2 : ℝ))) ≤ (R.ncard : ℝ) := hvg
    have hRne : F.Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      have h0 : R.ncard = 0 := by rw [Set.ncard_eq_toFinset_card R hRfin, ← hF, hne, Finset.card_empty]
      rw [h0, Nat.cast_zero] at hcount
      have hpos : 0 < Real.logb 7 (dyadicScale (N₀ + j) ^ (-(1 / 2 : ℝ))) := by
        refine Real.logb_pos (by norm_num) ?_
        refine Real.one_lt_rpow_of_pos_of_lt_one_of_neg hε0 ?_ (by norm_num)
        exact lt_of_le_of_lt hεsmall (by norm_num)
      linarith [mul_pos hC₃ hpos]
    set rm := F.min' hRne with hrm
    have hrmF : rm ∈ F := Finset.min'_mem F hRne
    obtain ⟨hrm1, -, -, -⟩ := hR rm ((hmemF rm).1 hrmF)
    have hxball : x ∈ Λ ∩ ball w (4 * rm) := ⟨hxΛ, mem_ball.2 (by rw [dist_comm]; linarith)⟩
    have hfilter : (F.filter (rm ≤ ·)).card = R.ncard := by
      rw [Finset.filter_true_of_mem (fun r hr => Finset.min'_le F r hr), Set.ncard_eq_toFinset_card R hRfin]
    have h1 : odometerExt μ z t x ≤ ENNReal.ofReal b ^ R.ncard * S₀ := by
      have := hiter rm hrmF
      rw [hfilter] at this
      exact le_trans (le_iSup₂_of_le (f := fun y (_ : y ∈ Λ ∩ ball w (4 * rm)) => odometerExt μ z t y)
        x hxball le_rfl) this
    refine h1.trans (mul_le_mul_left ?_ _)
    rw [← ENNReal.ofReal_pow hb.1.le]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_ge hb.1 hb.2.le ?_
    -- `C' C₃ (N₀ + j) = C₃ log₇ ε^{-1/2} ≤ |R|`
    have hlogb : Real.logb 7 (dyadicScale (N₀ + j) ^ (-(1 / 2 : ℝ))) =
        Real.log 2 / (2 * Real.log 7) * ((N₀ : ℝ) + j) := by
      rw [dyadicScale, two_inv_pow_rpow, Real.logb, Real.log_rpow (by norm_num)]
      push_cast
      ring
    rw [hlogb] at hcount
    calc Real.log 2 / (2 * Real.log 7) * C₃ * ((N₀ : ℝ) + j)
        = C₃ * (Real.log 2 / (2 * Real.log 7) * ((N₀ : ℝ) + j)) := by ring
      _ ≤ _ := hcount
  -- the disc step
  have hdj : sphere x₀ (shellRadius ρ j) ⊆ shell x₀ ρ j := fun s hs =>
    ⟨s, hs, 0, mem_ball_self (shellWidth_pos hρ j), add_zero s⟩
  have hdpos : 0 < shellRadius ρ j := by
    have := shellRadius_ge hρ j
    have : ρ * (2 : ℝ)⁻¹ ^ 50 ≤ ρ / 2 ^ 40 := by
      have h : (2 : ℝ)⁻¹ ^ 50 ≤ 1 / 2 ^ 40 := by norm_num
      calc ρ * (2 : ℝ)⁻¹ ^ 50 ≤ ρ * (1 / 2 ^ 40) := mul_le_mul_of_nonneg_left h hρ.le
        _ = ρ / 2 ^ 40 := by ring
    linarith
  have hsucc : shellOuterRadius ρ (j + 1) < shellRadius ρ j := by
    have h1 := shellRadius_le_sub_of_lt hρ (Nat.lt_succ_self j)
    have h2 := shellWidth_anti hρ (Nat.le_succ j)
    have h3 := shellWidth_pos hρ j
    rw [shellOuterRadius]
    linarith
  have hcl : closedBall x₀ (shellRadius ρ j) ⊆ ball x₀ ρ :=
    closedBall_subset_ball (by linarith [shellRadius_le hρ j])
  calc ⨆ x ∈ Λ ∩ annulus x₀ (ρ / 2) (shellOuterRadius ρ (j + 1)), odometerExt μ z t x
      ≤ ⨆ x ∈ Λ ∩ ball x₀ (shellRadius ρ j), odometerExt μ z t x :=
        biSup_mono fun x hx => ⟨hx.1, ball_subset_ball hsucc.le hx.2.1⟩
    _ ≤ ⨆ x ∈ Λ ∩ sphere x₀ (shellRadius ρ j), odometerExt μ z t x :=
        odometerExt_component_iSup_ball_le_iSup_sphere_of_pole_not_mem
          hμ hV hz ht isOpen_ball (ball_subset_closedBall.trans hball) hΛ' hzΛ x₀ hdpos hcl
    _ ≤ ENNReal.ofReal (b ^ (Real.log 2 / (2 * Real.log 7) * C₃ * ((N₀ : ℝ) + j))) * S₀ :=
        iSup₂_le fun x hx => key x ⟨hx.1, hdj hx.2⟩

end HarmonicBalls
