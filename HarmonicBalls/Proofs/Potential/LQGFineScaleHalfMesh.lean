import HarmonicBalls.Proofs.Potential.LQGFineScaleBallPower

/-! # Fine-scale increments on half-mesh grids

Half-mesh spatial grids support simultaneous fine-scale increment estimates.
-/

noncomputable section
open Filter MeasureTheory Real Metric Set ProbabilityTheory Function Topology
open scoped ENNReal NNReal
open LatticeProb LatticeProb.Gauss LatticeProb.LQG
open LatticeProb.LQG.GMCScaleGrid LatticeProb.LQG.GMCRatioLimit

namespace HarmonicBalls

/-- Fine-scale increments are controlled on half-mesh spatial grids. -/
theorem ae_fine_scale_affine_gff_increment_on_half_mesh_grid
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {g : ℂ → ℝ} (hgc : Continuous g) (hgs : HasCompactSupport g)
    {T : ℝ} (hT : 0 < T) (hgT : ∀ z, g z ≠ 0 → ‖z‖ + 1 ≤ T) :
    ∃ K c : ℝ, 0 ≤ K ∧ 0 < c ∧ ∀ (a t R : ℝ), 0 ≤ a → 0 < R →
      0 ≤ t → t < 1 →
      ((2 : ℝ)⁻¹ ^ (-(a / 2))) * ((2 : ℝ)⁻¹ ^ c) ≤ t ^ 2 →
      ∃ m : ℕ, ∃ S : ℕ → Finset ℂ,
        (∀ j, ((S j).card : ℝ) ≤ (4 * (2 * R + 1) + 1) ^ 2 * (4 : ℝ) ^ j) ∧
        (∀ j x, x ∈ S j → ‖x‖ ≤ R + 1) ∧
        (∀ j z, z ∈ Metric.ball (0 : ℂ) R →
          ∃ x ∈ S j, dist z x < dyadicScale j / 2) ∧
        ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
          (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
          LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc →
          ∀ᵐ ω ∂P, ∀ᶠ j in atTop, ∀ n, m * j ≤ n → ∀ x ∈ S j,
            ∀ l ≤ gridCount a (n + j),
              |∫ w, g w *
                (gridScale (fun k => gridCount a (k + j)) n l ^ (γ ^ 2 / 2) * exp (γ *
                  (affineRecentredCircle (hcirc ω) (dyadicScale j) x
                    (gridScale (fun k => gridCount a (k + j)) n l) w -
                   affineRecentredCircle (hcirc ω) (dyadicScale j) x T 0)) -
                 dyadicScale n ^ (γ ^ 2 / 2) * exp (γ *
                  (affineRecentredCircle (hcirc ω) (dyadicScale j) x (dyadicScale n) w -
                   affineRecentredCircle (hcirc ω) (dyadicScale j) x T 0)))| < 1 := by
  obtain ⟨K, c, hK, hc, hgrid⟩ := ae_fine_scale_affine_gff_increment hγ hγ2 hgc hgs hT hgT
  refine ⟨K, c, hK, hc, ?_⟩
  intro a t R ha hR ht ht1 hdecay
  let q : ℝ := (2 : ℝ)⁻¹ ^ (-(a / 2))
  have hq : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  obtain ⟨m, hm⟩ := hgrid (4 * q) q t (2 * ((4 * (2 * R + 1) + 1) ^ 2 + 1))
    (by positivity) hq.le (by positivity) ht ht1 hdecay
  obtain ⟨S, hS⟩ := exists_bounded_half_mesh_grids R hR
  refine ⟨m, S, fun j => (hS j).1, fun j x hx => (hS j).2.1 x hx,
    fun j z hz => (hS j).2.2 z hz, ?_⟩
  intro Ω _ P hC hcirc hG
  let Q : ℕ → ℕ → ℕ := fun j n => gridCount a (n + j)
  obtain ⟨z, k, hk, hcover⟩ := exists_spatial_radial_enumeration S Q
  let s : ℕ → ℕ → ℕ → ℝ := fun j n i =>
    gridScale (fun r => gridCount a (r + j)) n (k j n i)
  have hs : ∀ j n i, dyadicScale n / 2 ≤ s j n i ∧ s j n i ≤ dyadicScale n := by
    intro j n i
    exact gridScale_mem_Icc _ (hk j n i)
  have hN : ∀ j n, (((S j).card * (Q j n + 1) : ℕ) : ℝ) + 1 ≤
      (2 * ((4 * (2 * R + 1) + 1) ^ 2 + 1)) * ((4 * q) ^ j * q ^ n) := by
    intro j n
    simpa only [Q, q, mul_assoc] using
      spatial_radial_grid_count_le (R := 2 * R + 1) ha (by linarith) (fun j => (hS j).1) j n
  have he := hm P hC hcirc hG (fun j n => (S j).card * (Q j n + 1)) s z hN hs
  filter_upwards [he] with ω hω
  filter_upwards [hω] with j hj n hn x hx l hl
  obtain ⟨i, hi, hzi, hki⟩ := hcover j n x hx l hl
  have hi0 := hj n hn i hi
  simpa [s, hzi, hki, HarmonicBalls.dyadicScale, LatticeProb.LQG.dyadicScale] using hi0




theorem ae_fine_scale_affine_ball_le_half_mesh_band
    {γ R : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hR : 0 < R) :
    ∃ m : ℕ, ∃ S : ℕ → Finset ℂ,
      (∀ j x, x ∈ S j → ‖x‖ ≤ R + 1) ∧
      (∀ j z, z ∈ Metric.ball (0 : ℂ) R →
        ∃ x ∈ S j, dist z x < LatticeProb.LQG.dyadicScale j / 2) ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc →
        ∀ᵐ ω ∂P, ∀ᶠ j in atTop, ∀ n, m * j ≤ n → ∀ x ∈ S j,
          ∀ t, LatticeProb.LQG.dyadicScale n / 2 ≤ t → t ≤ LatticeProb.LQG.dyadicScale n →
            LatticeProb.LQG.lqgApprox γ (affineRecentredCircle (hcirc ω) (LatticeProb.LQG.dyadicScale j) x) t (ball 0 1) ≤
              ENNReal.ofReal (rexp (γ ^ 2 / 2 * Real.log 2 + γ)) *
                (LatticeProb.LQG.lqgApprox γ (affineRecentredCircle (hcirc ω) (LatticeProb.LQG.dyadicScale j) x)
                    (LatticeProb.LQG.dyadicScale n) (ball 0 2) +
                  ENNReal.ofReal (rexp (γ *
                    affineRecentredCircle (hcirc ω) (LatticeProb.LQG.dyadicScale j) x 4 0))) := by
  have hg : ∀ z, Gauss.ballCutoff z ≠ 0 → ‖z‖ + 1 ≤ (4 : ℝ) := by
    intro z hz
    have hz2 : ‖z‖ < 2 := by
      by_contra h
      exact hz (Gauss.ballCutoff_eq_zero (not_lt.mp h))
    linarith
  obtain ⟨K, c, hK, hc, hinc⟩ :=
    ae_fine_scale_affine_gff_increment_on_half_mesh_grid hγ hγ2
      Gauss.ballCutoff_continuous Gauss.ballCutoff_hasCompactSupport (by norm_num : (0 : ℝ) < 4) hg
  obtain ⟨a, q, ha, hq, hq1, hdec⟩ := exists_fine_scale_grid_rate hc
  obtain ⟨m, S, hcard, hbound, hcover, hgrid⟩ := hinc a q R ha.le hR hq hq1 hdec
  refine ⟨m, S, hbound, hcover, ?_⟩
  intro Ω _ P hC hcirc hh
  filter_upwards [hgrid P hC hcirc hh, ae_fine_scale_grid_circle_comparison hh ha R,
    hh.ae_continuousOn_circle] with ω hgridω hmodω hcontω
  filter_upwards [hgridω, hmodω] with j hj hmj n hn x hx t ht1 ht2
  obtain ⟨i, hi, hmod⟩ := hmj n t ht1 ht2
  have hs := gridScale_mem_Icc (fun k => gridCount a (k + j)) hi
  have hη : ∀ z, Gauss.ballCutoff z ≠ 0 →
      |affineRecentredCircle (hcirc ω) (LatticeProb.LQG.dyadicScale j) x t z -
        affineRecentredCircle (hcirc ω) (LatticeProb.LQG.dyadicScale j) x
          (gridScale (fun k => gridCount a (k + j)) n i) z| ≤ 1 := by
    intro z hz
    have hz2 : ‖z‖ ≤ 2 := by
      by_contra h
      exact hz (Gauss.ballCutoff_eq_zero (not_le.mp h).le)
    exact hmod x (hbound j x hx) z hz2
  have hcont : ∀ r, 0 < r →
      Continuous (affineRecentredCircle (hcirc ω) (LatticeProb.LQG.dyadicScale j) x r) := by
    intro r hr
    have hd : 0 < LatticeProb.LQG.dyadicScale j := pow_pos (by norm_num) j
    have hslice := LatticeProb.LQG.GMCRatioLimit.continuous_slice hcontω (mul_pos hd hr)
    exact (hslice.comp ((continuous_const.mul continuous_id).add continuous_const)).sub continuous_const
  have h := lqgApprox_ball_le_of_band_grid hγ hcont ht1 ht2 hs.1 hs.2 hη (hj n hn x hx i hi)
  simpa only [mul_one] using h


/-- The affine band comparison, expressed for the original field and balls
at the spatial grid scale. -/
theorem ae_fine_scale_ball_le_half_mesh_band
    {γ R : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hR : 0 < R) :
    ∃ m : ℕ, ∃ S : ℕ → Finset ℂ,
      (∀ j x, x ∈ S j → ‖x‖ ≤ R + 1) ∧
      (∀ j z, z ∈ Metric.ball (0 : ℂ) R →
        ∃ x ∈ S j, dist z x < LatticeProb.LQG.dyadicScale j / 2) ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc →
        ∀ᵐ ω ∂P, ∀ᶠ j in atTop, ∀ n, m * j ≤ n → ∀ x ∈ S j,
          ∀ t, LatticeProb.LQG.dyadicScale n / 2 ≤ t → t ≤ LatticeProb.LQG.dyadicScale n →
            LatticeProb.LQG.lqgApprox γ (hcirc ω) (LatticeProb.LQG.dyadicScale j * t) (ball x (LatticeProb.LQG.dyadicScale j)) ≤
              ENNReal.ofReal (rexp (γ ^ 2 / 2 * Real.log 2 + γ)) *
                (LatticeProb.LQG.lqgApprox γ (hcirc ω) (LatticeProb.LQG.dyadicScale j * LatticeProb.LQG.dyadicScale n)
                    (ball x (LatticeProb.LQG.dyadicScale j * 2)) +
                  LQGDyadicScaling.dyadicFactor γ j (hcirc ω (LatticeProb.LQG.dyadicScale j) x) *
                    ENNReal.ofReal (rexp (γ *
                      affineRecentredCircle (hcirc ω) (LatticeProb.LQG.dyadicScale j) x 4 0))) := by
  obtain ⟨m, S, hb, hc, h⟩ := ae_fine_scale_affine_ball_le_half_mesh_band hγ hγ2 hR
  refine ⟨m, S, hb, hc, ?_⟩
  intro Ω _ P hC hcirc hh
  filter_upwards [h P hC hcirc hh] with ω hω
  filter_upwards [hω] with j hj n hn x hx t ht1 ht2
  have ht : 0 ≤ t := le_trans (div_nonneg (show 0 ≤ LatticeProb.LQG.dyadicScale n from (pow_pos (by norm_num) n).le) (by norm_num)) ht1
  have hd : 0 ≤ LatticeProb.LQG.dyadicScale n := (show 0 < LatticeProb.LQG.dyadicScale n from pow_pos (by norm_num) n).le
  have hscale := lqgApprox_ball_dyadic hγ.ne' (hcirc ω) j x ht 1
  have hscale' := lqgApprox_ball_dyadic hγ.ne' (hcirc ω) j x hd 2
  simp only [mul_one] at hscale
  change LatticeProb.LQG.lqgApprox γ (hcirc ω) (LatticeProb.LQG.dyadicScale j * t) (ball x (LatticeProb.LQG.dyadicScale j)) =
    LQGDyadicScaling.dyadicFactor γ j (hcirc ω (LatticeProb.LQG.dyadicScale j) x) *
      LatticeProb.LQG.lqgApprox γ (affineRecentredCircle (hcirc ω) (LatticeProb.LQG.dyadicScale j) x) t (ball 0 1) at hscale
  change LatticeProb.LQG.lqgApprox γ (hcirc ω) (LatticeProb.LQG.dyadicScale j * LatticeProb.LQG.dyadicScale n) (ball x (LatticeProb.LQG.dyadicScale j * 2)) =
    LQGDyadicScaling.dyadicFactor γ j (hcirc ω (LatticeProb.LQG.dyadicScale j) x) *
      LatticeProb.LQG.lqgApprox γ (affineRecentredCircle (hcirc ω) (LatticeProb.LQG.dyadicScale j) x) (LatticeProb.LQG.dyadicScale n) (ball 0 2) at hscale'
  rw [hscale]
  calc
    _ ≤ LQGDyadicScaling.dyadicFactor γ j (hcirc ω (LatticeProb.LQG.dyadicScale j) x) *
        (ENNReal.ofReal (rexp (γ ^ 2 / 2 * Real.log 2 + γ)) *
          (LatticeProb.LQG.lqgApprox γ (affineRecentredCircle (hcirc ω) (LatticeProb.LQG.dyadicScale j) x)
            (LatticeProb.LQG.dyadicScale n) (ball 0 2) +
           ENNReal.ofReal (rexp (γ * affineRecentredCircle (hcirc ω) (LatticeProb.LQG.dyadicScale j) x 4 0)))) :=
      mul_le_mul_right (hj n hn x hx t ht1 ht2) _
    _ = ENNReal.ofReal (rexp (γ ^ 2 / 2 * Real.log 2 + γ)) *
        (LatticeProb.LQG.lqgApprox γ (hcirc ω) (LatticeProb.LQG.dyadicScale j * LatticeProb.LQG.dyadicScale n) (ball x (LatticeProb.LQG.dyadicScale j * 2)) +
          LQGDyadicScaling.dyadicFactor γ j (hcirc ω (LatticeProb.LQG.dyadicScale j) x) *
            ENNReal.ofReal (rexp (γ * affineRecentredCircle (hcirc ω) (LatticeProb.LQG.dyadicScale j) x 4 0))) := by
      rw [hscale']
      simp only [mul_add]
      ac_rfl



/-- Fine-band masses have positive power bounds at half-mesh grid centers. -/
theorem IsWholePlaneGFF.ae_fine_scale_half_mesh_ball_power
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ R : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hR : 0 < R) :
    ∃ m : ℕ, ∃ S : ℕ → Finset ℂ,
      (∀ j x, x ∈ S j → ‖x‖ ≤ R + 1) ∧
      (∀ j z, z ∈ ball (0 : ℂ) R → ∃ x ∈ S j, dist z x < LatticeProb.LQG.dyadicScale j / 2) ∧
      ∀ᵐ ω ∂P, ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ᶠ j in atTop,
        ∀ n, m * j ≤ n → ∀ x ∈ S j, ∀ t,
          LatticeProb.LQG.dyadicScale n / 2 ≤ t →
          t ≤ LatticeProb.LQG.dyadicScale n →
          LatticeProb.LQG.lqgApprox γ (hcirc ω) (LatticeProb.LQG.dyadicScale j * t)
              (ball x (LatticeProb.LQG.dyadicScale j)) ≤
            ENNReal.ofReal (C * LatticeProb.LQG.dyadicScale j ^ κ) := by
  obtain ⟨m, S, hS, hcover, hband⟩ := ae_fine_scale_ball_le_half_mesh_band hγ hγ2 hR
  obtain ⟨β, hβ, hdyad⟩ := hh.ae_ordinary_approximant_ball_power hγ hγ2 (R + 1)
  have hlp : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc :=
    (LPBridge.isWholePlaneGFF_iff P hC hcirc).mp hh
  refine ⟨m, S, hS, hcover, ?_⟩
  filter_upwards [hband P hC hcirc hlp, hdyad,
    hh.ae_compact_affine_circle_error_positive_power hγ hγ2] with ω hbandω hdyadω herrω
  obtain ⟨A, hA, hdyadω⟩ := hdyadω
  obtain ⟨B, η, hB, hη, herrω⟩ := herrω (R + 1)
  let K : ℝ := Real.exp (γ ^ 2 / 2 * Real.log 2 + γ)
  refine ⟨K * (A * (2 : ℝ) ^ β + B), min β η, by
    dsimp [K]; positivity, lt_min hβ hη, ?_⟩
  filter_upwards [hbandω, eventually_ge_atTop 2] with j hj hj2 n hn x hx t ht1 ht2
  let d := LatticeProb.LQG.dyadicScale j
  have hd : 0 < d := by unfold d LatticeProb.LQG.dyadicScale; positivity
  have hd1 : d ≤ 1 := by
    unfold d LatticeProb.LQG.dyadicScale
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hd2 : d * 2 ≤ 1 := by
    have hpow : LatticeProb.LQG.dyadicScale j ≤ LatticeProb.LQG.dyadicScale 1 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    norm_num [LatticeProb.LQG.dyadicScale] at hpow
    dsimp [d, LatticeProb.LQG.dyadicScale]
    norm_num
    linarith
  have he := herrω (j - 2) x (hS j x hx)
  have hidx : j - 2 + 2 = j := by omega
  rw [hidx] at he
  have ho := hdyadω (j + n) x (hS j x hx) (d * 2) (by positivity) hd2
  change LatticeProb.LQG.lqgApprox γ (hcirc ω)
    (LatticeProb.LQG.dyadicScale (j + n)) (ball x (d * 2)) ≤ _ at ho
  rw [LatticeProb.LQG.dyadicScale_add] at ho
  have hpow : (d * 2) ^ β = (2 : ℝ) ^ β * d ^ β := by
    rw [Real.mul_rpow hd.le (by norm_num)]
    ring
  rw [hpow] at ho
  have hb : d ^ β ≤ d ^ min β η := Real.rpow_le_rpow_of_exponent_ge hd hd1 (min_le_left _ _)
  have hc : d ^ η ≤ d ^ min β η := Real.rpow_le_rpow_of_exponent_ge hd hd1 (min_le_right _ _)
  have hreal : A * ((2 : ℝ) ^ β * d ^ β) + B * d ^ η ≤
      (A * (2 : ℝ) ^ β + B) * d ^ min β η := by
    have h1 := mul_le_mul_of_nonneg_left hb (show 0 ≤ A * (2 : ℝ) ^ β by positivity)
    have h2 := mul_le_mul_of_nonneg_left hc hB.le
    nlinarith
  have hsum : ENNReal.ofReal (A * ((2 : ℝ) ^ β * d ^ β)) +
      ENNReal.ofReal (B * d ^ η) ≤
        ENNReal.ofReal ((A * (2 : ℝ) ^ β + B) * d ^ min β η) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal hreal
  calc
    _ ≤ ENNReal.ofReal K * (LatticeProb.LQG.lqgApprox γ (hcirc ω)
      (LatticeProb.LQG.dyadicScale j * LatticeProb.LQG.dyadicScale n) (ball x (d * 2)) +
      LQGDyadicScaling.dyadicFactor γ j (hcirc ω d x) *
        ENNReal.ofReal (Real.exp (γ * affineRecentredCircle (hcirc ω) d x 4 0))) :=
          hj n hn x hx t ht1 ht2
    _ ≤ ENNReal.ofReal K * (ENNReal.ofReal (A * ((2 : ℝ) ^ β * d ^ β)) +
        ENNReal.ofReal (B * d ^ η)) := by gcongr
    _ ≤ ENNReal.ofReal K *
        ENNReal.ofReal ((A * (2 : ℝ) ^ β + B) * d ^ min β η) := by gcongr
    _ = ENNReal.ofReal (K * (A * (2 : ℝ) ^ β + B) * d ^ min β η) := by
      rw [← ENNReal.ofReal_mul (show 0 ≤ K by dsimp [K]; positivity)]
      congr 1
      ring




/-- Fine-scale ordinary masses obey a positive power bound uniformly over
all centers in a bounded disk. -/
theorem IsWholePlaneGFF.ae_fine_scale_ball_power
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ R : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hR : 0 < R) :
    ∃ m : ℕ, ∀ᵐ ω ∂P, ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ᶠ j in atTop,
      ∀ n, m * j ≤ n → ∀ z ∈ ball (0 : ℂ) R, ∀ t,
        LatticeProb.LQG.dyadicScale n / 2 ≤ t →
        t ≤ LatticeProb.LQG.dyadicScale n →
        LatticeProb.LQG.lqgApprox γ (hcirc ω) (LatticeProb.LQG.dyadicScale j * t)
            (ball z (LatticeProb.LQG.dyadicScale j / 2)) ≤
          ENNReal.ofReal (C * LatticeProb.LQG.dyadicScale j ^ κ) := by
  obtain ⟨m, S, _, hcover, hbound⟩ := hh.ae_fine_scale_half_mesh_ball_power hγ hγ2 hR
  refine ⟨m, ?_⟩
  filter_upwards [hbound] with ω hω
  obtain ⟨C, κ, hC, hκ, hω⟩ := hω
  refine ⟨C, κ, hC, hκ, ?_⟩
  filter_upwards [hω] with j hj n hn z hz t ht1 ht2
  obtain ⟨x, hx, hdist⟩ := hcover j z hz
  have hsub : ball z (LatticeProb.LQG.dyadicScale j / 2) ⊆
      ball x (LatticeProb.LQG.dyadicScale j) := by
    intro w hw
    rw [mem_ball] at hw ⊢
    have htri := dist_triangle w z x
    linarith
  exact (measure_mono hsub).trans (hj n hn x hx t ht1 ht2)


/-- The fine-band estimate controls every positive smoothing radius below
the scale-dependent threshold. -/
theorem IsWholePlaneGFF.ae_fine_smoothing_ball_power
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ R : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hR : 0 < R) :
    ∃ m : ℕ, ∀ᵐ ω ∂P, ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ᶠ j in atTop,
      ∀ z ∈ ball (0 : ℂ) R, ∀ s, 0 < s →
        s < LatticeProb.LQG.dyadicScale j * LatticeProb.LQG.dyadicScale (m * j) →
        LatticeProb.LQG.lqgApprox γ (hcirc ω) s
            (ball z (LatticeProb.LQG.dyadicScale j / 2)) ≤
          ENNReal.ofReal (C * LatticeProb.LQG.dyadicScale j ^ κ) := by
  obtain ⟨m, hm⟩ := hh.ae_fine_scale_ball_power hγ hγ2 hR
  refine ⟨m, ?_⟩
  filter_upwards [hm] with ω hω
  obtain ⟨C, κ, hC, hκ, hω⟩ := hω
  refine ⟨C, κ, hC, hκ, ?_⟩
  filter_upwards [hω] with j hj z hz s hs hsbound
  have hd : 0 < LatticeProb.LQG.dyadicScale j := by
    unfold LatticeProb.LQG.dyadicScale
    positivity
  have ht : 0 < s / LatticeProb.LQG.dyadicScale j := div_pos hs hd
  have htd : s / LatticeProb.LQG.dyadicScale j <
      LatticeProb.LQG.dyadicScale (m * j) := (div_lt_iff₀ hd).2 (by simpa [mul_comm] using hsbound)
  have hd1 : LatticeProb.LQG.dyadicScale (m * j) ≤ 1 := by
    unfold LatticeProb.LQG.dyadicScale
    exact pow_le_one₀ (by norm_num) (by norm_num)
  obtain ⟨n, hn1, hn2⟩ := LatticeProb.LQG.exists_dyadicScale_bracket ht (htd.trans_le hd1)
  have hn : m * j ≤ n := by
    by_contra h
    have hle : n + 1 ≤ m * j := by omega
    have hmono := LatticeProb.LQG.dyadicScale_le_of_le hle
    linarith
  have hband := hj n hn z hz (s / LatticeProb.LQG.dyadicScale j)
    (by simpa [LatticeProb.LQG.dyadicScale_succ_eq_half] using hn1) hn2.le
  have he : LatticeProb.LQG.dyadicScale j * (s / LatticeProb.LQG.dyadicScale j) = s := by
    field_simp
  simpa only [he] using hband


/-- On bounded disks, ordinary masses of arbitrary sufficiently small balls
have a positive power bound when the smoothing scale is sufficiently fine. -/
theorem IsWholePlaneGFF.ae_fine_smoothing_small_ball_power
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ R : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hR : 0 < R) :
    ∃ m : ℕ, ∀ᵐ ω ∂P, ∃ C κ r₀ : ℝ, 0 < C ∧ 0 < κ ∧ 0 < r₀ ∧
      ∀ z ∈ ball (0 : ℂ) R, ∀ r, 0 < r → r < r₀ → ∀ s, 0 < s →
        s < r ^ (m + 1) →
        LatticeProb.LQG.lqgApprox γ (hcirc ω) s (ball z r) ≤
          ENNReal.ofReal (C * r ^ κ) := by
  obtain ⟨m, hm⟩ := hh.ae_fine_smoothing_ball_power hγ hγ2 hR
  refine ⟨m, ?_⟩
  filter_upwards [hm] with ω hω
  obtain ⟨C, κ, hC, hκ, hω⟩ := hω
  obtain ⟨J, hJ⟩ := eventually_atTop.1 hω
  refine ⟨C * (4 : ℝ) ^ κ, κ, LatticeProb.LQG.dyadicScale (J + 2), by positivity,
    hκ, by unfold LatticeProb.LQG.dyadicScale; positivity, ?_⟩
  intro z hz r hr hr0 s hs hsr
  have hd1 : LatticeProb.LQG.dyadicScale (J + 2) ≤ 1 := by
    unfold LatticeProb.LQG.dyadicScale
    exact pow_le_one₀ (by norm_num) (by norm_num)
  obtain ⟨n, hn1, hn2⟩ := LatticeProb.LQG.exists_dyadicScale_bracket hr (hr0.trans_le hd1)
  have hn : J + 2 ≤ n := by
    by_contra h
    have hle : n + 1 ≤ J + 2 := by omega
    have hmono := LatticeProb.LQG.dyadicScale_le_of_le hle
    linarith
  let j := n - 1
  have hj : J ≤ j := by dsimp [j]; omega
  have hn' : j + 1 = n := by dsimp [j]; omega
  have hd : 0 < LatticeProb.LQG.dyadicScale j := by
    unfold LatticeProb.LQG.dyadicScale
    positivity
  have hrad : r ≤ LatticeProb.LQG.dyadicScale j / 2 := by
    rw [← LatticeProb.LQG.dyadicScale_succ_eq_half, hn']
    exact hn2.le
  have hrle : r ≤ LatticeProb.LQG.dyadicScale j := by linarith
  have hdle : LatticeProb.LQG.dyadicScale j ≤ 4 * r := by
    have hnext : LatticeProb.LQG.dyadicScale (n + 1) =
        LatticeProb.LQG.dyadicScale j / 4 := by
      rw [← hn', LatticeProb.LQG.dyadicScale_succ_eq_half,
        LatticeProb.LQG.dyadicScale_succ_eq_half]
      ring
    rw [hnext] at hn1
    linarith
  have hscale : LatticeProb.LQG.dyadicScale j *
      LatticeProb.LQG.dyadicScale (m * j) =
        LatticeProb.LQG.dyadicScale j ^ (m + 1) := by
    unfold LatticeProb.LQG.dyadicScale
    rw [pow_mul, pow_succ]
    ring
  have hs' : s < LatticeProb.LQG.dyadicScale j *
      LatticeProb.LQG.dyadicScale (m * j) := by
    rw [hscale]
    exact hsr.trans_le (pow_le_pow_left₀ hr.le hrle _)
  have hmass := hJ j hj z hz s hs hs'
  have hpow : LatticeProb.LQG.dyadicScale j ^ κ ≤ (4 * r) ^ κ :=
    Real.rpow_le_rpow hd.le hdle hκ.le
  have hsub : ball z r ⊆ ball z (LatticeProb.LQG.dyadicScale j / 2) :=
    ball_subset_ball hrad
  calc
    _ ≤ LatticeProb.LQG.lqgApprox γ (hcirc ω) s
        (ball z (LatticeProb.LQG.dyadicScale j / 2)) := measure_mono hsub
    _ ≤ ENNReal.ofReal (C * LatticeProb.LQG.dyadicScale j ^ κ) := hmass
    _ ≤ ENNReal.ofReal (C * (4 * r) ^ κ) := ENNReal.ofReal_le_ofReal (by gcongr)
    _ = ENNReal.ofReal (C * (4 : ℝ) ^ κ * r ^ κ) := by
      rw [Real.mul_rpow (by norm_num) hr.le]
      ring

end HarmonicBalls
