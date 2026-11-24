import HarmonicBalls.Proofs.Potential.LQGCoarseSmoothingBallPower
import HarmonicBalls.Proofs.Potential.LQGApproxGreenTail

/-! # Singular approximants at the insertion

A geometric dyadic bound gives a continuum ball-power estimate at the origin.
-/

noncomputable section
open MeasureTheory Filter Metric Set

namespace HarmonicBalls

/-- Singular masses of sufficiently small origin-centered balls have a positive
power bound for every smoothing scale no larger than the ball radius. -/
theorem IsWholePlaneGFF.ae_singular_continuum_origin_ball_power
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ) :
    ∃ β : ℝ, 0 < β ∧ ∀ᵐ ω ∂P, ∃ A r₀ : ℝ, 0 < A ∧ 0 < r₀ ∧
      ∀ r, 0 < r → r < r₀ → ∀ s, 0 < s → s ≤ r →
        lqgApprox γ (fieldCircleAverage α (hcirc ω)) s (ball 0 r) ≤
          ENNReal.ofReal (A * r ^ β) := by
  let β : ℝ := γ * (lqgQ γ - α) / 2
  let q : ℝ := Real.exp (-β * Real.log 2)
  let C : ℝ := Real.exp (γ * (|α| * Real.log 2)) / (1 - q)
  have hβ : 0 < β := by dsimp [β]; positivity
  have hq : q < 1 := by
    dsimp [q]
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by have := Real.log_pos (show (1 : ℝ) < 2 by norm_num); nlinarith)
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hlp : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc :=
    (LPBridge.isWholePlaneGFF_iff P hC hcirc).mp hh
  refine ⟨β, hβ, ?_⟩
  filter_upwards [ae_eventually_lqgApprox_fieldCircleAverage_ball_le_geometric hlp hγ hγ2 hαQ]
    with ω hω
  obtain ⟨N, hN⟩ := eventually_atTop.1 hω
  refine ⟨C * (2 : ℝ) ^ β, dyadicScale (N + 1), by positivity,
    by simp [dyadicScale], ?_⟩
  intro r hr hr₀ s hs hsr
  have hdN1 : dyadicScale N ≤ 1 := by
    unfold dyadicScale
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hdN : 0 < dyadicScale N := by simp [dyadicScale]
  have hnext : dyadicScale (N + 1) = dyadicScale N / 2 :=
    LatticeProb.LQG.dyadicScale_succ_eq_half N
  have hrN : r < dyadicScale N := by rw [hnext] at hr₀; linarith
  obtain ⟨k, hk1, hk2⟩ := LatticeProb.LQG.exists_dyadicScale_bracket hr (hrN.trans_le hdN1)
  have hkN : N ≤ k := by
    by_contra h
    have hle : k + 1 ≤ N := by omega
    have hmono := LatticeProb.LQG.dyadicScale_le_of_le hle
    change dyadicScale N ≤ dyadicScale (k + 1) at hmono
    change dyadicScale (k + 1) ≤ r at hk1
    linarith
  have hdk : 0 < dyadicScale k := by simp [dyadicScale]
  have hdkle : dyadicScale k ≤ 2 * r := by
    change LatticeProb.LQG.dyadicScale (k + 1) ≤ r at hk1
    rw [LatticeProb.LQG.dyadicScale_succ_eq_half] at hk1
    change dyadicScale k / 2 ≤ r at hk1
    linarith
  have hmass := hN k hkN s hs (hsr.trans_lt hk2)
  change lqgApprox γ (fieldCircleAverage α (hcirc ω)) s (ball 0 (dyadicScale k)) ≤
    ENNReal.ofReal (Real.exp (γ * (|α| * Real.log 2)) *
      (Real.exp (-(γ * (lqgQ γ - α) * Real.log 2 / 2)) ^ k /
        (1 - Real.exp (-(γ * (lqgQ γ - α) * Real.log 2 / 2))))) at hmass
  have heq : q ^ k = dyadicScale k ^ β := by
    rw [Real.rpow_def_of_pos hdk]
    unfold dyadicScale
    rw [Real.log_pow, Real.log_inv]
    dsimp [q]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hbound : C * dyadicScale k ^ β ≤ C * ((2 : ℝ) ^ β * r ^ β) := by
    have hp := Real.rpow_le_rpow hdk.le hdkle hβ.le
    rw [Real.mul_rpow (by norm_num) hr.le] at hp
    gcongr
  have hmass' : lqgApprox γ (fieldCircleAverage α (hcirc ω)) s (ball 0 (dyadicScale k)) ≤
      ENNReal.ofReal (C * dyadicScale k ^ β) := by
    convert hmass using 1
    rw [← heq]
    dsimp [C, q, β]
    congr 1
    ring
  calc
    _ ≤ lqgApprox γ (fieldCircleAverage α (hcirc ω)) s (ball 0 (dyadicScale k)) :=
      measure_mono (ball_subset_ball hk2.le)
    _ ≤ ENNReal.ofReal (C * dyadicScale k ^ β) := hmass'
    _ ≤ ENNReal.ofReal (C * ((2 : ℝ) ^ β * r ^ β)) := ENNReal.ofReal_le_ofReal hbound
    _ = ENNReal.ofReal (C * (2 : ℝ) ^ β * r ^ β) := by ring

/-- A lower bound on the smoothing scale controls the singular weight on a
bounded set, including points arbitrarily close to the insertion. -/
theorem singular_approximant_apply_le_ordinary_of_scale
    {γ α ε d R : ℝ} (hγ : 0 ≤ γ) (hd : 0 < d) (hdε : d ≤ ε) (hε1 : ε ≤ 1)
    (h : ℝ → ℂ → ℝ) {A : Set ℂ} (hA : MeasurableSet A)
    (hA_bound : ∀ z ∈ A, ‖z‖ ≤ R) :
    lqgApprox γ (fieldCircleAverage α h) ε A ≤
      ENNReal.ofReal (Real.exp (γ * (|α| *
        (|Real.log d| + |Real.log (max 1 R)|)))) * lqgApprox γ h ε A := by
  have hε : 0 < ε := hd.trans_le hdε
  apply LatticeProb.LQG.lqgApprox_apply_le_of_le_add hγ hε.le hA
  intro z hz
  have hlo : d ≤ max ε ‖z‖ := hdε.trans (le_max_left _ _)
  have hhi : max ε ‖z‖ ≤ max 1 R := max_le_max hε1 (hA_bound z hz)
  have hloglo : Real.log d ≤ Real.log (max ε ‖z‖) := Real.log_le_log hd hlo
  have hloghi : Real.log (max ε ‖z‖) ≤ Real.log (max 1 R) :=
    Real.log_le_log (hd.trans_le hlo) hhi
  have hlog : |Real.log (max ε ‖z‖)| ≤
      |Real.log d| + |Real.log (max 1 R)| := by
    apply abs_le.mpr
    constructor <;> linarith [neg_abs_le (Real.log d), le_abs_self (Real.log (max 1 R)),
      abs_nonneg (Real.log d), abs_nonneg (Real.log (max 1 R))]
  have hprod : |α * Real.log (max ε ‖z‖)| ≤
      |α| * (|Real.log d| + |Real.log (max 1 R)|) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hlog (abs_nonneg α)
  have hc : Real.circleAverage (fun y : ℂ => Real.log ‖y‖) z ε =
      Real.log (max ε ‖z‖) := by
    simpa only [sub_zero] using LatticeProb.Gauss.circleAverage_log_norm_sub_eq_log_max hε z 0
  simp only [fieldCircleAverage, hc]
  linarith [neg_abs_le (α * Real.log (max ε ‖z‖))]

/-- A lower bound on either the smoothing scale or the distance from the
insertion compares singular and ordinary mass on a bounded set. -/
theorem singular_approximant_apply_le_ordinary_of_scale_or_distance
    {γ α ε d R : ℝ} (hγ : 0 ≤ γ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hd : 0 < d)
    (h : ℝ → ℂ → ℝ) {A : Set ℂ} (hA : MeasurableSet A)
    (hA_bound : ∀ z ∈ A, ‖z‖ ≤ R)
    (hsep : d ≤ ε ∨ ∀ z ∈ A, d ≤ ‖z‖) :
    lqgApprox γ (fieldCircleAverage α h) ε A ≤
      ENNReal.ofReal (Real.exp (γ * (|α| *
        (|Real.log d| + |Real.log (max 1 R)|)))) * lqgApprox γ h ε A := by
  rcases hsep with hscale | hdist
  · exact singular_approximant_apply_le_ordinary_of_scale hγ hd hscale hε1 h hA hA_bound
  · exact singular_approximant_apply_le_ordinary hγ hε hε1 hd h hA
      (fun z hz => ⟨hdist z hz, hA_bound z hz⟩)

/-- The logarithmic cost of a power-sized separation reduces the mass exponent
by the corresponding insertion weight. -/
theorem exp_log_insertion_mul_rpow {r a γ α κ R : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (ha : 0 ≤ a) :
    Real.exp (γ * (|α| *
      (|Real.log (r ^ a / 2)| + |Real.log (max 1 R)|))) * r ^ κ =
      Real.exp (γ * |α| * (Real.log 2 + |Real.log (max 1 R)|)) *
        r ^ (κ - a * (γ * |α|)) := by
  have hra : r ^ a ≤ 1 := Real.rpow_le_one hr.le hr1 ha
  have hd : 0 < r ^ a / 2 := by positivity
  have hd1 : r ^ a / 2 ≤ 1 := by linarith
  have hl : Real.log (r ^ a / 2) ≤ 0 := Real.log_nonpos hd.le hd1
  rw [abs_of_nonpos hl, Real.log_div (Real.rpow_pos_of_pos hr a).ne' (by norm_num),
    Real.log_rpow hr, Real.rpow_def_of_pos hr κ,
    Real.rpow_def_of_pos hr (κ - a * (γ * |α|)), ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

private theorem radius_le_half_rpow {a r : ℝ} (ha : a < 1) (hr : 0 < r)
    (hr0 : r ≤ (1 / 2 : ℝ) ^ (1 / (1 - a))) : r ≤ r ^ a / 2 := by
  have hp : 0 < 1 - a := sub_pos.mpr ha
  have hpow := Real.rpow_le_rpow hr.le hr0 hp.le
  have hbound : r ^ (1 - a) ≤ (1 / 2 : ℝ) := by
    convert hpow using 1
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [div_mul_cancel₀ 1 hp.ne', Real.rpow_one]
  rw [Real.rpow_sub hr, Real.rpow_one] at hbound
  have hra : 0 < r ^ a := Real.rpow_pos_of_pos hr _
  exact (div_le_iff₀ hra).mp hbound |>.trans_eq (by ring)

/-- Singular approximants at all smoothing scales in `(0, 1]` have a common
small-ball power bound, uniformly over centers in a bounded disk. -/
theorem IsWholePlaneGFF.ae_singular_continuum_small_ball_power
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ α R : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ) (hR : 0 < R) :
    ∀ᵐ ω ∂P, ∃ C κ r₀ : ℝ, 0 < C ∧ 0 < κ ∧ 0 < r₀ ∧
      ∀ z ∈ ball (0 : ℂ) R, ∀ r, 0 < r → r < r₀ → ∀ s, 0 < s → s ≤ 1 →
        lqgApprox γ (fieldCircleAverage α (hcirc ω)) s (ball z r) ≤
          ENNReal.ofReal (C * r ^ κ) := by
  obtain ⟨β, hβ, horigin⟩ := hh.ae_singular_continuum_origin_ball_power hγ hγ2 hαQ
  filter_upwards [horigin, hh.ae_ordinary_continuum_small_ball_power hγ hγ2 hR] with ω ho hord
  obtain ⟨A, r₁, hA, hr₁, ho⟩ := ho
  obtain ⟨B, η, r₂, hB, hη, hr₂, hord⟩ := hord
  obtain ⟨b, hb, hbη⟩ := exists_pos_mul_lt hη (γ * |α|)
  let a : ℝ := min b (1 / 2)
  have ha : 0 < a := lt_min hb (by norm_num)
  have ha1 : a < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have haη : a * (γ * |α|) < η := by
    have hle := mul_le_mul_of_nonneg_left (min_le_left b (1 / 2))
      (mul_nonneg hγ.le (abs_nonneg α))
    exact lt_of_le_of_lt (by simpa only [mul_comm] using hle) hbη
  let D : ℝ := Real.exp (γ * |α| * (Real.log 2 + |Real.log (max 1 (R + 1))|))
  let κ : ℝ := min (a * β) (η - a * (γ * |α|))
  let t : ℝ := (1 / 2 : ℝ) ^ (1 / (1 - a))
  let u : ℝ := (r₁ / 4) ^ (1 / a)
  have hD : 0 < D := Real.exp_pos _
  have hκ : 0 < κ := lt_min (mul_pos ha hβ) (sub_pos.mpr haη)
  have ht : 0 < t := Real.rpow_pos_of_pos (by norm_num) _
  have hu : 0 < u := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨A * (2 : ℝ) ^ β + B * D, κ, min (min 1 r₂) (min t u),
    by positivity, hκ, lt_min (lt_min zero_lt_one hr₂) (lt_min ht hu), ?_⟩
  intro z hz r hr hr₀ s hs hs1
  have hr1 : r ≤ 1 := (hr₀.trans_le ((min_le_left _ _).trans (min_le_left _ _))).le
  have hr₂' : r < r₂ := hr₀.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hrt : r ≤ t := (hr₀.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hru : r < u := hr₀.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hra : 0 < r ^ a := Real.rpow_pos_of_pos hr _
  have hrhalf : r ≤ r ^ a / 2 := radius_le_half_rpow ha1 hr hrt
  have hrao : r ^ a < r₁ / 4 := by
    have hp := Real.rpow_lt_rpow hr.le hru ha
    have he : u ^ a = r₁ / 4 := by
      dsimp [u]
      rw [← Real.rpow_mul (by positivity : 0 ≤ r₁ / 4), div_mul_cancel₀ 1 ha.ne', Real.rpow_one]
    rwa [he] at hp
  have hzR : ‖z‖ < R := by simpa [mem_ball, dist_zero_right] using hz
  have hpnear : r ^ (a * β) ≤ r ^ κ :=
    Real.rpow_le_rpow_of_exponent_ge hr hr1 (min_le_left _ _)
  have hpfar : r ^ (η - a * (γ * |α|)) ≤ r ^ κ :=
    Real.rpow_le_rpow_of_exponent_ge hr hr1 (min_le_right _ _)
  have hpow : 0 ≤ r ^ κ := (Real.rpow_pos_of_pos hr _).le
  by_cases hnear : ‖z‖ ≤ r ^ a ∧ s ≤ 2 * r ^ a
  · have hsub : ball z r ⊆ ball (0 : ℂ) (2 * r ^ a) := by
      apply ball_subset_ball'
      simpa only [dist_zero_right, add_comm] using (show ‖z‖ + r ≤ 2 * r ^ a by linarith [hnear.1])
    have hmass := ho (2 * r ^ a) (by positivity) (by linarith) s hs hnear.2
    have heq : (2 * r ^ a) ^ β = (2 : ℝ) ^ β * r ^ (a * β) := by
      rw [Real.mul_rpow (by norm_num) hra.le, ← Real.rpow_mul hr.le]
    rw [heq] at hmass
    refine (measure_mono hsub).trans (hmass.trans (ENNReal.ofReal_le_ofReal ?_))
    have hp := mul_le_mul_of_nonneg_left hpnear (show 0 ≤ A * (2 : ℝ) ^ β by positivity)
    nlinarith [mul_nonneg (mul_nonneg hB.le hD.le) hpow]
  · have hsep : r ^ a / 2 ≤ s ∨ ∀ w ∈ ball z r, r ^ a / 2 ≤ ‖w‖ := by
      by_cases hsz : s > 2 * r ^ a
      · left; linarith
      · right
        intro w hw
        have hnorm : r ^ a < ‖z‖ := by
          by_contra hz'
          exact hnear ⟨le_of_not_gt hz', le_of_not_gt hsz⟩
        have hwz : ‖w - z‖ < r := by simpa [mem_ball, dist_eq_norm] using hw
        have htri := norm_add_le (z - w) w
        rw [sub_add_cancel, norm_sub_rev] at htri
        linarith
    have hupper : ∀ w ∈ ball z r, ‖w‖ ≤ R + 1 := by
      intro w hw
      have hwz : ‖w - z‖ < r := by simpa [mem_ball, dist_eq_norm] using hw
      have htri := norm_add_le (w - z) z
      rw [sub_add_cancel] at htri
      linarith
    have hcomp := singular_approximant_apply_le_ordinary_of_scale_or_distance (α := α) hγ.le hs hs1
      (show 0 < r ^ a / 2 by positivity) (hcirc ω) isOpen_ball.measurableSet hupper hsep
    have hmass := hord z hz r hr hr₂' s hs hs1
    have hcomp' : ENNReal.ofReal (Real.exp (γ * (|α| *
        (|Real.log (r ^ a / 2)| + |Real.log (max 1 (R + 1))|)))) *
        lqgApprox γ (hcirc ω) s (ball z r) ≤
        ENNReal.ofReal (Real.exp (γ * (|α| *
        (|Real.log (r ^ a / 2)| + |Real.log (max 1 (R + 1))|)))) *
        ENNReal.ofReal (B * r ^ η) := by gcongr
    refine hcomp.trans (hcomp'.trans ?_)
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    apply ENNReal.ofReal_le_ofReal
    have heq := exp_log_insertion_mul_rpow (γ := γ) (α := α) (κ := η) (R := R + 1) hr hr1 ha.le
    have hp := mul_le_mul_of_nonneg_left hpfar (show 0 ≤ B * D by positivity)
    have he : Real.exp (γ * (|α| *
        (|Real.log (r ^ a / 2)| + |Real.log (max 1 (R + 1))|))) * (B * r ^ η) =
        B * D * r ^ (η - a * (γ * |α|)) := by
      calc
        _ = B * (Real.exp (γ * (|α| *
            (|Real.log (r ^ a / 2)| + |Real.log (max 1 (R + 1))|))) * r ^ η) := by ring
        _ = B * (Real.exp (γ * |α| * (Real.log 2 + |Real.log (max 1 (R + 1))|)) *
            r ^ (η - a * (γ * |α|))) := by rw [heq]
        _ = _ := by dsimp [D]; ring
    rw [he]
    nlinarith [mul_nonneg (show 0 ≤ A * (2 : ℝ) ^ β by positivity) hpow]

/-- One event provides the continuum small-ball bound for every bounded disk. -/
theorem IsWholePlaneGFF.ae_singular_continuum_small_ball_power_all_disks
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ) :
    ∀ᵐ ω ∂P, ∀ R : ℝ, ∃ C κ r₀ : ℝ, 0 < C ∧ 0 < κ ∧ 0 < r₀ ∧
      ∀ z : ℂ, ‖z‖ ≤ R → ∀ r, 0 < r → r < r₀ → ∀ s, 0 < s → s ≤ 1 →
        lqgApprox γ (fieldCircleAverage α (hcirc ω)) s (ball z r) ≤
          ENNReal.ofReal (C * r ^ κ) := by
  filter_upwards [ae_all_iff.mpr (fun n : ℕ =>
    hh.ae_singular_continuum_small_ball_power hγ hγ2 hαQ
      (R := (n : ℝ) + 1) (by positivity))] with ω hω R
  obtain ⟨n, hn⟩ := exists_nat_ge R
  obtain ⟨C, κ, r₀, hC, hκ, hr₀, hbound⟩ := hω n
  refine ⟨C, κ, r₀, hC, hκ, hr₀, ?_⟩
  intro z hz r hr hrr s hs hs1
  apply hbound z ?_ r hr hrr s hs hs1
  simpa [mem_ball, dist_zero_right] using (show ‖z‖ < (n : ℝ) + 1 by linarith)

end HarmonicBalls
