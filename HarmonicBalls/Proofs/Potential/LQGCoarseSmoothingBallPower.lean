import HarmonicBalls.Proofs.Potential.LQGCompactRadialOscillation
import HarmonicBalls.Proofs.Potential.LQGActualApproximantPower
import HarmonicBalls.Proofs.Potential.LQGFineScaleHalfMesh
import HarmonicBalls.Proofs.Potential.LQGApproxCompactScaleBall

/-! # Comparison of GMC masses at nearby smoothing scales

Uniform circle-average increments compare the corresponding approximant masses.
-/

noncomputable section
open MeasureTheory Set Metric Filter

namespace HarmonicBalls

/-- A bound on circle averages and on the smoothing scales compares the masses. -/
theorem lqgApprox_apply_le_of_scale_le {γ s t K : ℝ} (hγ : 0 ≤ γ)
    (hs : 0 ≤ s) (hst : s ≤ t) {h : ℝ → ℂ → ℝ} {A : Set ℂ}
    (hA : MeasurableSet A) (hK : ∀ z ∈ A, h s z ≤ h t z + K) :
    lqgApprox γ h s A ≤ ENNReal.ofReal (Real.exp (γ * K)) * lqgApprox γ h t A := by
  simp only [lqgApprox]
  rw [withDensity_apply _ hA, withDensity_apply _ hA, ← lintegral_const_mul' _ _
    ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' hA fun z hz => ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  have hp : s ^ (γ ^ 2 / 2) ≤ t ^ (γ ^ 2 / 2) :=
    Real.rpow_le_rpow hs hst (by positivity)
  have he : Real.exp (γ * h s z) ≤ Real.exp (γ * K) * Real.exp (γ * h t z) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [hK z hz])
  calc
    s ^ (γ ^ 2 / 2) * Real.exp (γ * h s z) ≤
        t ^ (γ ^ 2 / 2) * (Real.exp (γ * K) * Real.exp (γ * h t z)) :=
      mul_le_mul hp he (Real.exp_pos _).le (Real.rpow_nonneg (hs.trans hst) _)
    _ = Real.exp (γ * K) * (t ^ (γ ^ 2 / 2) * Real.exp (γ * h t z)) := by ring

/-- In each sufficiently small dyadic band, masses on compact-center balls
are controlled by the mass at the upper endpoint. -/
theorem IsWholePlaneGFF.ae_eventually_lqgApprox_ball_le_dyadic
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ δ : ℝ} (hγ : 0 ≤ γ)
    (hδ : 0 < δ) (R : ℝ) :
    ∀ᵐ ω ∂P, ∀ᶠ k : ℕ in atTop, ∀ z : ℂ, ‖z‖ ≤ R → ∀ r,
      r ≤ 1 → ∀ s, dyadicScale k / 2 ≤ s → s ≤ dyadicScale k →
      lqgApprox γ (hcirc ω) s (ball z r) ≤
        ENNReal.ofReal (Real.exp (γ * (δ * (k + 1)))) *
          lqgApprox γ (hcirc ω) (dyadicScale k) (ball z r) := by
  have hlp : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc :=
    (LPBridge.isWholePlaneGFF_iff P hC hcirc).mp hh
  filter_upwards [ae_eventually_compact_radial_oscillation hlp (R + 1) hδ] with ω hω
  filter_upwards [hω] with k hk z hz r hr s hs1 hs2
  have hd : 0 < dyadicScale k := by simp [dyadicScale]
  apply lqgApprox_apply_le_of_scale_le hγ (by linarith) hs2 isOpen_ball.measurableSet
  intro w hw
  have hwz : ‖w - z‖ < r := by simpa [mem_ball, dist_eq_norm] using hw
  have hwR : ‖w‖ ≤ R + 1 := by
    have h := norm_add_le (w - z) z
    have he : w - z + z = w := by abel
    rw [he] at h
    linarith
  have h := hk w hwR s hs1 hs2
  linarith [le_abs_self (hcirc ω s w - hcirc ω (dyadicScale k) w)]

/-- The cost of a sublinear dyadic-band oscillation is absorbed by half of a
positive ball-power exponent when the smoothing scale is not too small. -/
theorem exp_dyadic_oscillation_mul_rpow_le {γ β r : ℝ} (hγ : 0 < γ) (hβ : 0 < β)
    (hr : 0 < r) (m k : ℕ) (hrk : r ^ (m + 1) ≤ dyadicScale k) :
    let δ := β * Real.log 2 / (2 * γ * (m + 1))
    Real.exp (γ * (δ * (k + 1))) * r ^ β ≤
      Real.exp (γ * δ) * r ^ (β / 2) := by
  dsimp only
  let p : ℝ := m + 1
  let δ : ℝ := β * Real.log 2 / (2 * γ * p)
  have hp : 0 < p := by dsimp [p]; positivity
  have hd : 0 < dyadicScale k := by simp [dyadicScale]
  have hlog := Real.log_le_log (pow_pos hr (m + 1)) hrk
  have hlogd : Real.log (dyadicScale k) = -((k : ℝ) * Real.log 2) := by
    simp [dyadicScale, Real.log_pow, Real.log_inv]
  rw [Real.log_pow, hlogd] at hlog
  have hcoeff : γ * δ = β / (2 * p) * Real.log 2 := by
    dsimp [δ]
    field_simp
  have hlog' : p * Real.log r ≤ -((k : ℝ) * Real.log 2) := by simpa [p] using hlog
  have hm := mul_le_mul_of_nonneg_left hlog' (show 0 ≤ β / (2 * p) by positivity)
  have hm' : β / 2 * Real.log r ≤ -(γ * δ * (k : ℝ)) := by
    calc
      β / 2 * Real.log r = β / (2 * p) * (p * Real.log r) := by field_simp
      _ ≤ β / (2 * p) * (-((k : ℝ) * Real.log 2)) := hm
      _ = -(γ * δ * (k : ℝ)) := by rw [hcoeff]; ring
  have he : γ * (δ * ((k : ℝ) + 1)) + β * Real.log r ≤
      γ * δ + (β / 2) * Real.log r := by nlinarith
  rw [Real.rpow_def_of_pos hr, Real.rpow_def_of_pos hr, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simpa [δ, p, mul_comm, mul_left_comm, mul_assoc] using he

/-- Ordinary approximants have a compact-center ball-power bound at small
smoothing scales that are at least a fixed power of the ball radius. -/
theorem IsWholePlaneGFF.ae_coarse_smoothing_small_scale_ball_power
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (R : ℝ) (m : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᵐ ω ∂P, ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧
      ∀ z : ℂ, ‖z‖ ≤ R → ∀ r, 0 < r → r ≤ 1 → ∀ s,
        0 < s → s ≤ ε₀ → r ^ (m + 1) ≤ s →
        lqgApprox γ (hcirc ω) s (ball z r) ≤ ENNReal.ofReal (C * r ^ κ) := by
  obtain ⟨β, hβ, hdyad⟩ := hh.ae_ordinary_approximant_ball_power hγ hγ2 R
  let δ : ℝ := β * Real.log 2 / (2 * γ * (m + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨β / 2, by positivity, ?_⟩
  filter_upwards [hdyad, hh.ae_eventually_lqgApprox_ball_le_dyadic hγ.le hδ R] with ω hdyadω hbandω
  obtain ⟨C, hC, hdyadω⟩ := hdyadω
  obtain ⟨N, hN⟩ := eventually_atTop.1 hbandω
  refine ⟨C * Real.exp (γ * δ), dyadicScale (N + 1), by positivity,
    by simp [dyadicScale], ?_⟩
  intro z hz r hr hr1 s hs hsN hrs
  have hdN1 : dyadicScale N ≤ 1 := by
    unfold dyadicScale
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hdN : 0 < dyadicScale N := by simp [dyadicScale]
  have hnext : dyadicScale (N + 1) = dyadicScale N / 2 := by
    exact LatticeProb.LQG.dyadicScale_succ_eq_half N
  have hsN' : s < dyadicScale N := by rw [hnext] at hsN; linarith
  obtain ⟨k, hk1, hk2⟩ := LatticeProb.LQG.exists_dyadicScale_bracket hs (hsN'.trans_le hdN1)
  have hkN : N ≤ k := by
    by_contra h
    have hle : k + 1 ≤ N := by omega
    have hmono := LatticeProb.LQG.dyadicScale_le_of_le hle
    change dyadicScale N ≤ dyadicScale (k + 1) at hmono
    change dyadicScale (k + 1) ≤ s at hk1
    linarith
  have hkhalf : dyadicScale k / 2 ≤ s := by
    change LatticeProb.LQG.dyadicScale (k + 1) ≤ s at hk1
    rw [LatticeProb.LQG.dyadicScale_succ_eq_half] at hk1
    exact hk1
  have hmass := hN k hkN z hz r hr1 s hkhalf hk2.le
  have hpow := hdyadω k z hz r hr.le hr1
  have hfactor := exp_dyadic_oscillation_mul_rpow_le hγ hβ hr m k (hrs.trans hk2.le)
  change Real.exp (γ * (δ * (k + 1))) * r ^ β ≤
    Real.exp (γ * δ) * r ^ (β / 2) at hfactor
  calc
    _ ≤ ENNReal.ofReal (Real.exp (γ * (δ * (k + 1)))) *
        lqgApprox γ (hcirc ω) (dyadicScale k) (ball z r) := hmass
    _ ≤ ENNReal.ofReal (Real.exp (γ * (δ * (k + 1)))) *
        ENNReal.ofReal (C * r ^ β) := by gcongr
    _ = ENNReal.ofReal (C * (Real.exp (γ * (δ * (k + 1))) * r ^ β)) := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 1
      ring
    _ ≤ ENNReal.ofReal (C * (Real.exp (γ * δ) * r ^ (β / 2))) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hfactor hC.le)
    _ = ENNReal.ofReal (C * Real.exp (γ * δ) * r ^ (β / 2)) := by ring

/-- Ordinary approximants at every smoothing scale in `(0, 1]` have a
common compact-center small-ball power bound. -/
theorem IsWholePlaneGFF.ae_ordinary_continuum_small_ball_power
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ R : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hR : 0 < R) :
    ∀ᵐ ω ∂P, ∃ C κ r₀ : ℝ, 0 < C ∧ 0 < κ ∧ 0 < r₀ ∧
      ∀ z ∈ ball (0 : ℂ) R, ∀ r, 0 < r → r < r₀ → ∀ s, 0 < s → s ≤ 1 →
        lqgApprox γ (hcirc ω) s (ball z r) ≤ ENNReal.ofReal (C * r ^ κ) := by
  obtain ⟨m, hfine⟩ := hh.ae_fine_smoothing_small_ball_power hγ hγ2 hR
  obtain ⟨β, hβ, hcoarse⟩ := hh.ae_coarse_smoothing_small_scale_ball_power hγ hγ2 R m
  filter_upwards [hfine, hcoarse, hh.ae_singular_approximant_compact_scale_ball_bound γ 0]
    with ω hf hc hcompact
  obtain ⟨A, η, r₁, hA, hη, hr₁, hf⟩ := hf
  obtain ⟨B, ε, hB, hε, hc⟩ := hc
  obtain ⟨D, hD, hcompact⟩ := hcompact ε 1 hε R
  let κ := min η (min β 2)
  have hκ : 0 < κ := lt_min hη (lt_min hβ (by norm_num))
  refine ⟨A + B + D, κ, min r₁ 1, by positivity, hκ, lt_min hr₁ zero_lt_one, ?_⟩
  intro z hz r hr hr₀ s hs hs1
  have hr1 : r ≤ 1 := (hr₀.trans_le (min_le_right _ _)).le
  have hrsmall : r < r₁ := hr₀.trans_le (min_le_left _ _)
  have hzR : ‖z‖ ≤ R := by
    have hz' : ‖z‖ < R := by simpa [mem_ball, dist_zero_right] using hz
    exact hz'.le
  have hpη : r ^ η ≤ r ^ κ := Real.rpow_le_rpow_of_exponent_ge hr hr1 (min_le_left _ _)
  have hpβ : r ^ β ≤ r ^ κ := Real.rpow_le_rpow_of_exponent_ge hr hr1
    ((min_le_right η (min β 2)).trans (min_le_left β 2))
  have hp2 : r ^ (2 : ℝ) ≤ r ^ κ := Real.rpow_le_rpow_of_exponent_ge hr hr1
    ((min_le_right η (min β 2)).trans (min_le_right β 2))
  have hpow : 0 ≤ r ^ κ := (Real.rpow_pos_of_pos hr _).le
  by_cases hsfine : s < r ^ (m + 1)
  · have hmass := hf z hz r hr hrsmall s hs hsfine
    change lqgApprox γ (hcirc ω) s (ball z r) ≤ ENNReal.ofReal (A * r ^ η) at hmass
    exact hmass.trans (ENNReal.ofReal_le_ofReal (by
      nlinarith [mul_le_mul_of_nonneg_left hpη hA.le, mul_nonneg hB.le hpow, mul_nonneg hD.le hpow]))
  · have hrs : r ^ (m + 1) ≤ s := le_of_not_gt hsfine
    by_cases hsε : s ≤ ε
    · exact (hc z hzR r hr hr1 s hs hsε hrs).trans
        (ENNReal.ofReal_le_ofReal (by
          nlinarith [mul_le_mul_of_nonneg_left hpβ hB.le, mul_nonneg hA.le hpow, mul_nonneg hD.le hpow]))
    · have hmass := hcompact s ⟨le_of_not_ge hsε, hs1⟩ z hzR r hr.le hr1
      have heq : fieldCircleAverage 0 (hcirc ω) = hcirc ω := by
        funext t w
        simp [fieldCircleAverage]
      rw [heq] at hmass
      rw [← Real.rpow_natCast] at hmass
      change lqgApprox γ (hcirc ω) s (ball z r) ≤ ENNReal.ofReal (D * r ^ (2 : ℝ)) at hmass
      exact hmass.trans (ENNReal.ofReal_le_ofReal (by
        nlinarith [mul_le_mul_of_nonneg_left hp2 hD.le, mul_nonneg hA.le hpow, mul_nonneg hB.le hpow]))

end HarmonicBalls
