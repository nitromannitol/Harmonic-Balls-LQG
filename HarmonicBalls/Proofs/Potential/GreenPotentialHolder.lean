import HarmonicBalls.Proofs.Potential.GreenBall
import HarmonicBalls.Defs.Obstacle

/-!
# Hölder continuity of Green potentials on a disc under an upper volume growth bound

Bou-Rabee and Gwynne, *Harmonic balls in Liouville quantum gravity* (arXiv:2208.11795): the Green clause of
Proposition 2.5 (prop:lbm-exit-time, line 524) for `O = B_R(0)`, and property 1 of the potential
`q_{B_R}` of Appendix A (eq:expected-exit-time, lines 3532-3543).

Let `μ` be a measure on `ℂ`, finite on `B_R(0)`, with the upper volume growth bound `μ(B_r(z)) ≤ r^{β⁺}` for
`z ∈ B_R(0)` and `0 < r < r₀` (the upper half of the volume growth condition `VolumeGrowth`, eq:volume-growth,
line 3526). For `f` bounded and measurable, the Green potential `q(x) = ∫_{B_R} G_{B_R}(x,y) f(y) μ(dy)` converges
absolutely for every `x ∈ closedBall 0 R` and is Hölder continuous there, with exponent `α = min(β⁺,1)/2` and
constant `C(β⁺, r₀, μ(B_R)) ‖f‖_∞` (`greenPotentialHolderConstant`).

## Route

The paper's proof cites the Campanato embedding (Ponce 2016, §16.2). We use a direct argument instead.

1. *Kernel estimate* (`abs_greenFunction_ball_sub_le`). For `0 < α ≤ 1`, `x, x' ∈ closedBall 0 R`, `y ≠ x, x'`:
   `|G(x,y) - G(x',y)| ≤ (πα)⁻¹ |x - x'|^α (|x - y|^{-α} + |x' - y|^{-α})`.
   It follows from the explicit formula `G_{B_R}(x,y) = max ((2π)⁻¹ log (|R² - ȳ x| / (R |y - x|))) 0`
   (`greenFunction_ball_eq_max`, symmetry), the bound `|R² - ȳ x| ≥ R |x - y|` and the elementary inequality
   `|log a - log b| ≤ α⁻¹ |a - b|^α (a^{-α} + b^{-α})` (`abs_log_sub_log_le`).
2. *Riesz potential bound* (`lintegral_norm_sub_rpow_neg_le`). If `ν(ℂ) ≤ m` and `ν(closedBall x r) ≤ A r^β` for all
   `r > 0`, then `∫ |x - y|^{-α} ν(dy) ≤ m + A α / (β - α)` for `0 < α < β` (layer-cake formula).
3. The upper volume growth bound gives step 2 for `ν = μ|_{B_R}`, uniformly in `x ∈ closedBall 0 R`, with
   `A = 2^{β⁺} + μ(B_R) (2 / r₀)^{β⁺}`; it also excludes atoms. Integrating step 1 against `|f| ≤ M` gives
   `|q(x) - q(x')| ≤ 2 (πα)⁻¹ K M |x - x'|^α`, `K = μ(B_R) + A α / (β⁺ - α)`.

## Main statements

* `greenPotential_ball_holder_of_upper`: the quantitative statement with explicit constant;
* `VolumeGrowth.greenPotential_ball_holder`: the same from `VolumeGrowth`, constant independent of `f`
  (Hölder seminorm `≤ C(μ, R) ‖f‖_∞`, as needed for Lemma 4.2);
* `greenPotential_ball_holderOnWith`: the Green clause of Proposition 2.5 for `O = B_R(0)` in the shape of
  `GreenPotentialLiouvilleHolderStmt` (`f ∈ L^∞(closure O)`, `closure (ball 0 R) = closedBall 0 R`);
* `greenPotentialBall_continuousOn`: the body of `GreenPotentialBallContinuousStep` (Steps/SecA/Basic.lean), property
  1 of `q_{B_R}` (line 3538), as the case `f = 1`.

Only the upper bound `μ(B_r(z)) ≤ r^{β⁺}` and `μ(B_R) < ∞` are used; the lower bound `r^{β⁻} ≤ μ(B_r(z))` is not.
-/

namespace HarmonicBalls

open MeasureTheory Metric Filter Topology Set ComplexConjugate
open scoped ENNReal NNReal

/-! ## Elementary inequalities -/

/-- Hölder-type modulus of the logarithm: for `a, b > 0` and `0 < α ≤ 1`,
`|log a - log b| ≤ α⁻¹ |a - b|^α (a^{-α} + b^{-α})`. -/
theorem abs_log_sub_log_le {a b α : ℝ} (ha : 0 < a) (hb : 0 < b) (hα : 0 < α) (hα1 : α ≤ 1) :
    |Real.log a - Real.log b| ≤ α⁻¹ * |a - b| ^ α * (a ^ (-α) + b ^ (-α)) := by
  have hα' : 0 ≤ α⁻¹ := inv_nonneg.2 hα.le
  have key : ∀ a b : ℝ, 0 < a → 0 < b → b ≤ a →
      Real.log a - Real.log b ≤ α⁻¹ * (a - b) ^ α * b ^ (-α) := by
    intro a b ha hb hba
    have hbα : 0 < b ^ α := Real.rpow_pos_of_pos hb α
    have h1 : Real.log a - Real.log b = α⁻¹ * Real.log ((a / b) ^ α) := by
      rw [Real.log_rpow (div_pos ha hb), Real.log_div ha.ne' hb.ne', ← mul_assoc,
        inv_mul_cancel₀ hα.ne', one_mul]
    have h2 : Real.log ((a / b) ^ α) ≤ (a / b) ^ α - 1 :=
      Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos (div_pos ha hb) α)
    have h3 : (a / b) ^ α - 1 = (a ^ α - b ^ α) * b ^ (-α) := by
      rw [Real.div_rpow ha.le hb.le, Real.rpow_neg hb.le, sub_mul, mul_inv_cancel₀ hbα.ne',
        div_eq_mul_inv]
    have h4 : a ^ α - b ^ α ≤ (a - b) ^ α := by
      have := Real.rpow_add_le_add_rpow (sub_nonneg.2 hba) hb.le hα.le hα1
      rw [sub_add_cancel] at this
      linarith
    have hbα' : 0 ≤ b ^ (-α) := (Real.rpow_pos_of_pos hb _).le
    calc Real.log a - Real.log b = α⁻¹ * Real.log ((a / b) ^ α) := h1
      _ ≤ α⁻¹ * ((a ^ α - b ^ α) * b ^ (-α)) := by
        rw [← h3]; exact mul_le_mul_of_nonneg_left h2 hα'
      _ ≤ α⁻¹ * ((a - b) ^ α * b ^ (-α)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h4 hbα') hα'
      _ = α⁻¹ * (a - b) ^ α * b ^ (-α) := by ring
  have haα : 0 ≤ a ^ (-α) := (Real.rpow_pos_of_pos ha _).le
  have hbα : 0 ≤ b ^ (-α) := (Real.rpow_pos_of_pos hb _).le
  rcases le_total b a with hba | hab
  · rw [abs_of_nonneg (sub_nonneg.2 (Real.log_le_log hb hba)), abs_of_nonneg (sub_nonneg.2 hba)]
    calc _ ≤ α⁻¹ * (a - b) ^ α * b ^ (-α) := key a b ha hb hba
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left haα)
          (mul_nonneg hα' (Real.rpow_nonneg (sub_nonneg.2 hba) _))
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (Real.log_le_log ha hab)), abs_sub_comm,
      abs_of_nonneg (sub_nonneg.2 hab)]
    calc _ ≤ α⁻¹ * (b - a) ^ α * a ^ (-α) := key b a hb ha hab
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hbα)
          (mul_nonneg hα' (Real.rpow_nonneg (sub_nonneg.2 hab) _))

/-- `R |x - y| ≤ |R² - x̄ y|` for `|x|, |y| ≤ R` (from `|R² - x̄ y|² = R² |x - y|² + (R² - |x|²)(R² - |y|²)`). -/
theorem mul_norm_sub_le_norm_sub_conj_mul {R : ℝ} {x y : ℂ} (hx : ‖x‖ ≤ R)
    (hy : ‖y‖ ≤ R) : R * ‖x - y‖ ≤ ‖(R : ℂ) ^ 2 - conj x * y‖ := by
  refine le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) ?_
  rw [mul_pow, norm_sq_sub_conj_mul]
  have h1 : 0 ≤ R ^ 2 - ‖x‖ ^ 2 := sub_nonneg.2 (pow_le_pow_left₀ (norm_nonneg x) hx 2)
  have h2 : 0 ≤ R ^ 2 - ‖y‖ ^ 2 := sub_nonneg.2 (pow_le_pow_left₀ (norm_nonneg y) hy 2)
  linarith [mul_nonneg h1 h2]

/-! ## The kernel estimate -/

/-- Hölder estimate of the explicit Green kernel of the disc in its second variable. -/
theorem abs_greenBall_sub_le {R α : ℝ} (hR : 0 < R) (hα : 0 < α) (hα1 : α ≤ 1) {y x x' : ℂ}
    (hy : ‖y‖ ≤ R) (hx : ‖x‖ ≤ R) (hx' : ‖x'‖ ≤ R) (hxy : x ≠ y) (hx'y : x' ≠ y) :
    |greenBall R y x - greenBall R y x'| ≤
      (Real.pi * α)⁻¹ * (‖x - x'‖ ^ α * (‖x - y‖ ^ (-α) + ‖x' - y‖ ^ (-α))) := by
  have e : ∀ z : ℂ, z ≠ y → ‖z‖ ≤ R → greenBall R y z = (2 * Real.pi)⁻¹ *
      (Real.log ‖(R : ℂ) ^ 2 - conj y * z‖ - Real.log R - Real.log ‖y - z‖) := by
    intro z hzy hz
    have hb := norm_pos_iff.2 (sub_ne_zero.2 hzy.symm)
    have ha := (mul_pos hR hb).trans_le (mul_norm_sub_le_norm_sub_conj_mul hy hz)
    rw [greenBall, Real.log_div ha.ne' (mul_pos hR hb).ne', Real.log_mul hR.ne' hb.ne']
    ring
  have hb : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy.symm)
  have hb' : 0 < ‖y - x'‖ := norm_pos_iff.2 (sub_ne_zero.2 hx'y.symm)
  have hab := mul_norm_sub_le_norm_sub_conj_mul hy hx
  have hab' := mul_norm_sub_le_norm_sub_conj_mul hy hx'
  have hdiff : |‖(R : ℂ) ^ 2 - conj y * x‖ - ‖(R : ℂ) ^ 2 - conj y * x'‖| ≤ R * ‖x - x'‖ := by
    refine (abs_norm_sub_norm_le _ _).trans ?_
    have : ((R : ℂ) ^ 2 - conj y * x) - ((R : ℂ) ^ 2 - conj y * x') = conj y * (x' - x) := by ring
    rw [this, norm_mul, Complex.norm_conj, norm_sub_rev x' x]
    exact mul_le_mul_of_nonneg_right hy (norm_nonneg _)
  have hdiff' : |‖y - x‖ - ‖y - x'‖| ≤ ‖x - x'‖ := by
    refine (abs_norm_sub_norm_le _ _).trans_eq ?_
    rw [sub_sub_sub_cancel_left, norm_sub_rev]
  rw [e x hxy hx, e x' hx'y hx', norm_sub_rev x y, norm_sub_rev x' y]
  set a := ‖(R : ℂ) ^ 2 - conj y * x‖ with ha_def
  set a' := ‖(R : ℂ) ^ 2 - conj y * x'‖ with ha'_def
  set b := ‖y - x‖ with hb_def
  set b' := ‖y - x'‖ with hb'_def
  set d := ‖x - x'‖ with hd_def
  have ha : 0 < a := (mul_pos hR hb).trans_le hab
  have ha' : 0 < a' := (mul_pos hR hb').trans_le hab'
  have hα' : 0 ≤ α⁻¹ := inv_nonneg.2 hα.le
  have hdα : 0 ≤ d ^ α := Real.rpow_nonneg (norm_nonneg _) _
  have hbsum : 0 ≤ b ^ (-α) + b' ^ (-α) :=
    add_nonneg (Real.rpow_nonneg hb.le _) (Real.rpow_nonneg hb'.le _)
  have hRR : R ^ α * R ^ (-α) = 1 := by
    rw [Real.rpow_neg hR.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hR α).ne']
  have hL1 : |Real.log a - Real.log a'| ≤ α⁻¹ * (d ^ α * (b ^ (-α) + b' ^ (-α))) := by
    have h1 : |a - a'| ^ α ≤ R ^ α * d ^ α := by
      rw [← Real.mul_rpow hR.le (norm_nonneg _)]
      exact Real.rpow_le_rpow (abs_nonneg _) hdiff hα.le
    have h2 : a ^ (-α) ≤ R ^ (-α) * b ^ (-α) := by
      rw [← Real.mul_rpow hR.le hb.le]
      exact Real.rpow_le_rpow_of_nonpos (mul_pos hR hb) hab (neg_nonpos.2 hα.le)
    have h3 : a' ^ (-α) ≤ R ^ (-α) * b' ^ (-α) := by
      rw [← Real.mul_rpow hR.le hb'.le]
      exact Real.rpow_le_rpow_of_nonpos (mul_pos hR hb') hab' (neg_nonpos.2 hα.le)
    calc |Real.log a - Real.log a'| ≤ α⁻¹ * |a - a'| ^ α * (a ^ (-α) + a' ^ (-α)) :=
          abs_log_sub_log_le ha ha' hα hα1
      _ ≤ α⁻¹ * (R ^ α * d ^ α) * (R ^ (-α) * b ^ (-α) + R ^ (-α) * b' ^ (-α)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 hα') (add_le_add h2 h3)
            (add_nonneg (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg ha'.le _))
            (mul_nonneg hα' (mul_nonneg (Real.rpow_nonneg hR.le _) hdα))
      _ = α⁻¹ * (d ^ α * (b ^ (-α) + b' ^ (-α))) * (R ^ α * R ^ (-α)) := by ring
      _ = α⁻¹ * (d ^ α * (b ^ (-α) + b' ^ (-α))) := by rw [hRR, mul_one]
  have hL2 : |Real.log b - Real.log b'| ≤ α⁻¹ * (d ^ α * (b ^ (-α) + b' ^ (-α))) := by
    calc |Real.log b - Real.log b'| ≤ α⁻¹ * |b - b'| ^ α * (b ^ (-α) + b' ^ (-α)) :=
          abs_log_sub_log_le hb hb' hα hα1
      _ ≤ α⁻¹ * d ^ α * (b ^ (-α) + b' ^ (-α)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (abs_nonneg _) hdiff' hα.le) hα') hbsum
      _ = α⁻¹ * (d ^ α * (b ^ (-α) + b' ^ (-α))) := by ring
  have hsplit : (2 * Real.pi)⁻¹ * (Real.log a - Real.log R - Real.log b) -
      (2 * Real.pi)⁻¹ * (Real.log a' - Real.log R - Real.log b') =
      (2 * Real.pi)⁻¹ * ((Real.log a - Real.log a') - (Real.log b - Real.log b')) := by ring
  have hπ : 0 < (2 * Real.pi)⁻¹ := inv_pos.2 (mul_pos two_pos Real.pi_pos)
  rw [hsplit, abs_mul, abs_of_pos hπ]
  calc (2 * Real.pi)⁻¹ * |(Real.log a - Real.log a') - (Real.log b - Real.log b')|
      ≤ (2 * Real.pi)⁻¹ * (|Real.log a - Real.log a'| + |Real.log b - Real.log b'|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) hπ.le
    _ ≤ (2 * Real.pi)⁻¹ * (α⁻¹ * (d ^ α * (b ^ (-α) + b' ^ (-α))) +
        α⁻¹ * (d ^ α * (b ^ (-α) + b' ^ (-α)))) :=
        mul_le_mul_of_nonneg_left (add_le_add hL1 hL2) hπ.le
    _ = (Real.pi * α)⁻¹ * (d ^ α * (b ^ (-α) + b' ^ (-α))) := by
        rw [mul_inv, mul_inv]; ring

/-- **Kernel estimate.** For `0 < α ≤ 1`, `x, x' ∈ closedBall 0 R` and `y ∉ {x, x'}`,
`|G_{B_R}(x,y) - G_{B_R}(x',y)| ≤ (πα)⁻¹ |x - x'|^α (|x - y|^{-α} + |x' - y|^{-α})`. -/
theorem abs_greenFunction_ball_sub_le {R α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {x x' y : ℂ}
    (hx : x ∈ closedBall (0 : ℂ) R) (hx' : x' ∈ closedBall (0 : ℂ) R) (hxy : x ≠ y) (hx'y : x' ≠ y) :
    |greenFunction (ball 0 R) x y - greenFunction (ball 0 R) x' y| ≤
      (Real.pi * α)⁻¹ * (‖x - x'‖ ^ α * (‖x - y‖ ^ (-α) + ‖x' - y‖ ^ (-α))) := by
  by_cases hy : y ∈ ball (0 : ℂ) R
  · have hR : 0 < R := (norm_nonneg y).trans_lt (mem_ball_zero_iff.1 hy)
    rw [greenFunction_ball_comm R x y, greenFunction_ball_comm R x' y, greenFunction_ball_eq_max hy hxy,
      greenFunction_ball_eq_max hy hx'y]
    exact (abs_max_sub_max_le_abs _ _ _).trans (abs_greenBall_sub_le hR hα hα1
      (mem_ball_zero_iff.1 hy).le (mem_closedBall_zero_iff.1 hx) (mem_closedBall_zero_iff.1 hx') hxy hx'y)
  · rw [greenFunction_of_notMem_right hy x, greenFunction_of_notMem_right hy x', sub_zero, abs_zero]
    exact mul_nonneg (inv_nonneg.2 (mul_nonneg Real.pi_pos.le hα.le))
      (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
        (add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (norm_nonneg _) _)))

/-- `y ↦ G_{B_R}(x,y)` is Borel measurable. -/
theorem measurable_greenFunction_ball (R : ℝ) (x : ℂ) :
    Measurable (greenFunction (ball (0 : ℂ) R) x) := by
  by_cases hx : x ∈ ball (0 : ℂ) R
  · have : greenFunction (ball (0 : ℂ) R) x = fun z => if z = x then 0 else max (greenBall R x z) 0 := by
      funext z
      split_ifs with h
      · rw [h, greenFunction_self]
      · exact greenFunction_ball_eq_max hx h
    rw [this]
    refine Measurable.ite (measurableSet_singleton x) measurable_const (Measurable.max ?_ measurable_const)
    unfold greenBall
    fun_prop
  · rw [show greenFunction (ball (0 : ℂ) R) x = fun _ => 0 from funext (greenFunction_of_notMem_left hx)]
    exact measurable_const

/-! ## Riesz potentials of measures with polynomial growth -/

/-- **Riesz potential bound** (layer-cake formula). If `ν(ℂ) ≤ m` and `ν(closedBall x r) ≤ A r^β` for every
`r > 0`, then `∫ |x - y|^{-α} ν(dy) ≤ m + A α / (β - α)` for `0 < α < β`. -/
theorem lintegral_norm_sub_rpow_neg_le {ν : Measure ℂ} {x : ℂ} {m A α β : ℝ} (hα : 0 < α) (hαβ : α < β)
    (hm : 0 ≤ m) (hA : 0 ≤ A) (hν : ν univ ≤ ENNReal.ofReal m)
    (hball : ∀ r, 0 < r → ν (closedBall x r) ≤ ENNReal.ofReal (A * r ^ β)) :
    ∫⁻ y, ENNReal.ofReal (‖x - y‖ ^ (-α)) ∂ν ≤ ENNReal.ofReal (m + A * (α / (β - α))) := by
  have hmeas : Measurable fun y : ℂ => ‖x - y‖ ^ (-α) := by fun_prop
  rw [lintegral_eq_lintegral_meas_le ν (ae_of_all _ fun y => Real.rpow_nonneg (norm_nonneg _) _)
    hmeas.aemeasurable, ← Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ),
    lintegral_union measurableSet_Ioi (Ioc_disjoint_Ioi le_rfl),
    ENNReal.ofReal_add hm (mul_nonneg hA (div_nonneg hα.le (sub_pos.2 hαβ).le))]
  refine add_le_add ?_ ?_
  · calc ∫⁻ t in Ioc (0 : ℝ) 1, ν {a | t ≤ ‖x - a‖ ^ (-α)}
        ≤ ∫⁻ _ in Ioc (0 : ℝ) 1, ENNReal.ofReal m :=
          lintegral_mono fun t => (measure_mono (subset_univ _)).trans hν
      _ = ENNReal.ofReal m := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one]
  · have hlt : -(β / α) < -1 := neg_lt_neg ((one_lt_div hα).2 hαβ)
    have hsub : ∀ t ∈ Ioi (1 : ℝ),
        ν {a | t ≤ ‖x - a‖ ^ (-α)} ≤ ENNReal.ofReal (A * t ^ (-(β / α))) := by
      intro t ht
      have ht0 : 0 < t := zero_lt_one.trans ht
      calc ν {a | t ≤ ‖x - a‖ ^ (-α)} ≤ ν (closedBall x (t ^ (-α⁻¹))) := by
            refine measure_mono fun a ha => ?_
            have ha : t ≤ ‖x - a‖ ^ (-α) := ha
            have hd : 0 < ‖x - a‖ := by
              rcases (norm_nonneg (x - a)).eq_or_lt with h | h
              · rw [← h, Real.zero_rpow (neg_ne_zero.2 hα.ne')] at ha
                linarith
              · exact h
            rw [mem_closedBall, dist_comm, dist_eq_norm]
            calc ‖x - a‖ = (‖x - a‖ ^ (-α)) ^ (-α⁻¹) := by
                  rw [← Real.rpow_mul hd.le, neg_mul_neg, mul_inv_cancel₀ hα.ne', Real.rpow_one]
              _ ≤ t ^ (-α⁻¹) :=
                  Real.rpow_le_rpow_of_nonpos ht0 ha (neg_nonpos.2 (inv_nonneg.2 hα.le))
        _ ≤ ENNReal.ofReal (A * (t ^ (-α⁻¹)) ^ β) := hball _ (Real.rpow_pos_of_pos ht0 _)
        _ = ENNReal.ofReal (A * t ^ (-(β / α))) := by
            rw [← Real.rpow_mul ht0.le, neg_mul, inv_mul_eq_div]
    have hint : IntegrableOn (fun t : ℝ => A * t ^ (-(β / α))) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt hlt zero_lt_one).const_mul A
    have hnn : 0 ≤ᵐ[volume.restrict (Ioi (1 : ℝ))] fun t : ℝ => A * t ^ (-(β / α)) :=
      (ae_restrict_iff' measurableSet_Ioi).2
        (ae_of_all _ fun t ht => mul_nonneg hA (Real.rpow_nonneg (zero_lt_one.trans ht).le _))
    have hβα : -(β / α) + 1 = -((β - α) / α) := by rw [sub_div, div_self hα.ne']; ring
    calc ∫⁻ t in Ioi (1 : ℝ), ν {a | t ≤ ‖x - a‖ ^ (-α)}
        ≤ ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (A * t ^ (-(β / α))) :=
          setLIntegral_mono' measurableSet_Ioi hsub
      _ = ENNReal.ofReal (∫ t in Ioi (1 : ℝ), A * t ^ (-(β / α))) :=
          (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
      _ = ENNReal.ofReal (A * (α / (β - α))) := by
          rw [integral_const_mul, integral_Ioi_rpow_of_lt hlt zero_lt_one, Real.one_rpow, hβα,
            neg_div_neg_eq, one_div_div]

/-- A measure with `ν(closedBall x r) ≤ A r^β` for all `r > 0` (`β > 0`) has no atom at `x`. -/
theorem measure_singleton_eq_zero_of_le_rpow {ν : Measure ℂ} {x : ℂ} {A β : ℝ} (hβ : 0 < β)
    (hball : ∀ r, 0 < r → ν (closedBall x r) ≤ ENNReal.ofReal (A * r ^ β)) : ν {x} = 0 := by
  have ht : Tendsto (fun r : ℝ => ENNReal.ofReal (A * r ^ β)) (𝓝[>] 0) (𝓝 0) := by
    have h := ((Real.continuous_rpow_const hβ.le).tendsto 0).const_mul A
    rw [Real.zero_rpow hβ.ne', mul_zero] at h
    simpa using (ENNReal.tendsto_ofReal h).mono_left nhdsWithin_le_nhds
  refine le_zero_iff.1 (ge_of_tendsto ht ?_)
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (measure_mono (singleton_subset_iff.2 (mem_closedBall_self (le_of_lt hr)))).trans (hball r hr)

/-- Integrability and integral bound of `y ↦ |x - y|^{-α}` from a bound on its lower integral. -/
theorem integrable_norm_sub_rpow_neg {ν : Measure ℂ} {x : ℂ} {α K : ℝ} (hK0 : 0 ≤ K)
    (h : ∫⁻ y, ENNReal.ofReal (‖x - y‖ ^ (-α)) ∂ν ≤ ENNReal.ofReal K) :
    Integrable (fun y => ‖x - y‖ ^ (-α)) ν ∧ ∫ y, ‖x - y‖ ^ (-α) ∂ν ≤ K := by
  have hnn : 0 ≤ᵐ[ν] fun y => ‖x - y‖ ^ (-α) := ae_of_all _ fun y => Real.rpow_nonneg (norm_nonneg _) _
  have hm : Measurable fun y : ℂ => ‖x - y‖ ^ (-α) := by fun_prop
  refine ⟨⟨hm.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal hnn).2 (h.trans_lt ENNReal.ofReal_lt_top)⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hm.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hK0 h

/-! ## Hölder continuity of Green potentials -/

/-- **Abstract form.** Let `ν` be a measure on `ℂ` without atoms in `closedBall 0 R` whose Riesz potentials of order
`α ∈ (0,1]` are bounded by `K` on `closedBall 0 R`. For `f` measurable with `|f| ≤ M` `ν`-a.e., the Green potential
`x ↦ ∫ G_{B_R}(x,y) f(y) ν(dy)` converges absolutely on `closedBall 0 R` and
`|q(x) - q(x')| ≤ 2 (πα)⁻¹ K M |x - x'|^α` there. -/
theorem greenPotential_ball_integrable_and_sub_le {ν : Measure ℂ} {R α K M : ℝ} (hR : 0 < R)
    (hα : 0 < α) (hα1 : α ≤ 1) (hK0 : 0 ≤ K)
    (hK : ∀ x ∈ closedBall (0 : ℂ) R, ∫⁻ y, ENNReal.ofReal (‖x - y‖ ^ (-α)) ∂ν ≤ ENNReal.ofReal K)
    (hatom : ∀ x ∈ closedBall (0 : ℂ) R, ν {x} = 0) {f : ℂ → ℝ} (hf : AEStronglyMeasurable f ν)
    (hM : 0 ≤ M) (hfM : ∀ᵐ y ∂ν, |f y| ≤ M) :
    (∀ x ∈ closedBall (0 : ℂ) R, Integrable (fun y => greenFunction (ball 0 R) x y * f y) ν) ∧
    ∀ x ∈ closedBall (0 : ℂ) R, ∀ x' ∈ closedBall (0 : ℂ) R,
      |∫ y, greenFunction (ball 0 R) x y * f y ∂ν - ∫ y, greenFunction (ball 0 R) x' y * f y ∂ν| ≤
        2 * (Real.pi * α)⁻¹ * K * M * ‖x - x'‖ ^ α := by
  set c := (Real.pi * α)⁻¹ with hc_def
  have hc : 0 ≤ c := inv_nonneg.2 (mul_nonneg Real.pi_pos.le hα.le)
  have hint := fun x hx => integrable_norm_sub_rpow_neg hK0 (hK x hx)
  have hne : ∀ x ∈ closedBall (0 : ℂ) R, ∀ᵐ y ∂ν, y ≠ x := fun x hx =>
    ae_iff.2 (by simpa using hatom x hx)
  have hbound : ∀ x ∈ closedBall (0 : ℂ) R, ∀ x' ∈ closedBall (0 : ℂ) R, ∀ᵐ y ∂ν,
      ‖(greenFunction (ball 0 R) x y - greenFunction (ball 0 R) x' y) * f y‖ ≤
        M * (c * (‖x - x'‖ ^ α * (‖x - y‖ ^ (-α) + ‖x' - y‖ ^ (-α)))) := by
    intro x hx x' hx'
    filter_upwards [hne x hx, hne x' hx', hfM] with y hyx hyx' hy
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul hy (abs_greenFunction_ball_sub_le hα hα1 hx hx' (Ne.symm hyx) (Ne.symm hyx'))
      (abs_nonneg _) hM
  have hdom : ∀ x ∈ closedBall (0 : ℂ) R, ∀ x' ∈ closedBall (0 : ℂ) R,
      Integrable (fun y => M * (c * (‖x - x'‖ ^ α * (‖x - y‖ ^ (-α) + ‖x' - y‖ ^ (-α))))) ν :=
    fun x hx x' hx' => ((((hint x hx).1.add (hint x' hx').1).const_mul _).const_mul _).const_mul _
  have hmeasG : ∀ x, AEStronglyMeasurable (fun y => greenFunction (ball 0 R) x y * f y) ν :=
    fun x => (measurable_greenFunction_ball R x).aestronglyMeasurable.mul hf
  -- the boundary point `x₀ = R`, where `G_{B_R}(x₀, ·) = 0`
  have hx₀ : (R : ℂ) ∈ closedBall (0 : ℂ) R := by
    rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_of_nonneg hR.le]
  have hG₀ : ∀ y, greenFunction (ball (0 : ℂ) R) (R : ℂ) y = 0 := greenFunction_of_notMem_left (by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg hR.le]; exact lt_irrefl R)
  have hI : ∀ x ∈ closedBall (0 : ℂ) R, Integrable (fun y => greenFunction (ball 0 R) x y * f y) ν := by
    intro x hx
    refine (hdom x hx _ hx₀).mono' (hmeasG x) ?_
    filter_upwards [hbound x hx _ hx₀] with y hy
    rwa [hG₀, sub_zero] at hy
  refine ⟨hI, fun x hx x' hx' => ?_⟩
  rw [← integral_sub (hI x hx) (hI x' hx'), ← Real.norm_eq_abs]
  calc ‖∫ y, (greenFunction (ball 0 R) x y * f y - greenFunction (ball 0 R) x' y * f y) ∂ν‖
      ≤ ∫ y, M * (c * (‖x - x'‖ ^ α * (‖x - y‖ ^ (-α) + ‖x' - y‖ ^ (-α)))) ∂ν := by
        refine norm_integral_le_of_norm_le (hdom x hx x' hx') ?_
        filter_upwards [hbound x hx x' hx'] with y hy
        rwa [sub_mul] at hy
    _ = M * (c * (‖x - x'‖ ^ α * (∫ y, ‖x - y‖ ^ (-α) ∂ν + ∫ y, ‖x' - y‖ ^ (-α) ∂ν))) := by
        rw [integral_const_mul, integral_const_mul, integral_const_mul,
          integral_add (hint x hx).1 (hint x' hx').1]
    _ ≤ M * (c * (‖x - x'‖ ^ α * (K + K))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (add_le_add (hint x hx).2 (hint x' hx').2) (Real.rpow_nonneg (norm_nonneg _) _)) hc) hM
    _ = 2 * c * K * M * ‖x - x'‖ ^ α := by ring

/-- The Hölder exponent `α = min(β⁺, 1) / 2` of the Green potentials; it depends on `β⁺` only. -/
noncomputable def greenPotentialHolderExponent (βplus : ℝ) : ℝ := min βplus 1 / 2

theorem greenPotentialHolderExponent_pos {βplus : ℝ} (h : 0 < βplus) :
    0 < greenPotentialHolderExponent βplus := by
  unfold greenPotentialHolderExponent; have := lt_min h one_pos; linarith

theorem greenPotentialHolderExponent_le_one (βplus : ℝ) : greenPotentialHolderExponent βplus ≤ 1 := by
  unfold greenPotentialHolderExponent; have := min_le_right βplus 1; linarith

theorem greenPotentialHolderExponent_lt {βplus : ℝ} (h : 0 < βplus) :
    greenPotentialHolderExponent βplus < βplus := by
  unfold greenPotentialHolderExponent; have := min_le_left βplus 1; linarith

/-- The constant `A = 2^{β⁺} + m (2 / r₀)^{β⁺}` of the bound `μ|_{B_R}(closedBall x r) ≤ A r^{β⁺}` (all `r > 0`,
`x ∈ closedBall 0 R`), where `m = μ(B_R)` and `μ(B_r(z)) ≤ r^{β⁺}` for `z ∈ B_R`, `r < r₀`. -/
noncomputable def volumeGrowthAllScalesConstant (βplus r₀ m : ℝ) : ℝ :=
  2 ^ βplus + m * (2 / r₀) ^ βplus

/-- The Riesz potential bound `K = m + A α / (β⁺ - α)` (`α = greenPotentialHolderExponent β⁺`). -/
noncomputable def greenPotentialRieszBound (βplus r₀ m : ℝ) : ℝ :=
  m + volumeGrowthAllScalesConstant βplus r₀ m *
    (greenPotentialHolderExponent βplus / (βplus - greenPotentialHolderExponent βplus))

/-- The Hölder constant per unit of `‖f‖_∞`: `2 (πα)⁻¹ K`, with `K = greenPotentialRieszBound β⁺ r₀ μ(B_R)`. -/
noncomputable def greenPotentialHolderConstant (βplus r₀ m : ℝ) : ℝ :=
  2 * (Real.pi * greenPotentialHolderExponent βplus)⁻¹ * greenPotentialRieszBound βplus r₀ m

theorem volumeGrowthAllScalesConstant_nonneg {βplus r₀ m : ℝ} (hr₀ : 0 < r₀) (hm : 0 ≤ m) :
    0 ≤ volumeGrowthAllScalesConstant βplus r₀ m :=
  add_nonneg (Real.rpow_nonneg zero_le_two _)
    (mul_nonneg hm (Real.rpow_nonneg (div_nonneg zero_le_two hr₀.le) _))

theorem greenPotentialRieszBound_nonneg {βplus r₀ m : ℝ} (hβ : 0 < βplus) (hr₀ : 0 < r₀) (hm : 0 ≤ m) :
    0 ≤ greenPotentialRieszBound βplus r₀ m :=
  add_nonneg hm (mul_nonneg (volumeGrowthAllScalesConstant_nonneg hr₀ hm)
    (div_nonneg (greenPotentialHolderExponent_pos hβ).le
      (sub_pos.2 (greenPotentialHolderExponent_lt hβ)).le))

theorem greenPotentialHolderConstant_nonneg {βplus r₀ m : ℝ} (hβ : 0 < βplus) (hr₀ : 0 < r₀)
    (hm : 0 ≤ m) : 0 ≤ greenPotentialHolderConstant βplus r₀ m :=
  mul_nonneg (mul_nonneg zero_le_two (inv_nonneg.2 (mul_nonneg Real.pi_pos.le
    (greenPotentialHolderExponent_pos hβ).le))) (greenPotentialRieszBound_nonneg hβ hr₀ hm)

/-- The upper volume growth bound on open balls centred in `B_R` gives the bound `μ(closedBall x r) ≤ (2r)^{β⁺}`
for closed balls centred in `closedBall 0 R`, `2r < r₀`. -/
theorem measure_closedBall_le_of_upper {μ : Measure ℂ} {R r₀ βplus : ℝ} (hR : 0 < R)
    (hup : ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R, μ (ball z r) ≤ ENNReal.ofReal (r ^ βplus))
    {x : ℂ} (hx : x ∈ closedBall (0 : ℂ) R) {r : ℝ} (hr : 0 < r) (hr₀ : 2 * r < r₀) :
    μ (closedBall x r) ≤ ENNReal.ofReal ((2 * r) ^ βplus) := by
  rw [← closure_ball (0 : ℂ) hR.ne'] at hx
  obtain ⟨z, hz, hxz⟩ := Metric.mem_closure_iff.1 hx r hr
  refine (measure_mono fun y hy => ?_).trans (hup (2 * r) (by linarith) hr₀ z hz)
  rw [mem_ball]
  calc dist y z ≤ dist y x + dist x z := dist_triangle _ _ _
    _ < r + r := add_lt_add_of_le_of_lt (mem_closedBall.1 hy) hxz
    _ = 2 * r := by ring

/-- All-scales growth of `μ|_{B_R}` around points of `closedBall 0 R`:
`μ|_{B_R}(closedBall x r) ≤ A r^{β⁺}` for every `r > 0`, `A = volumeGrowthAllScalesConstant β⁺ r₀ μ(B_R)`. -/
theorem restrict_ball_closedBall_le {μ : Measure ℂ} {R r₀ βplus : ℝ} (hR : 0 < R) (hr₀ : 0 < r₀)
    (hβ : 0 < βplus)
    (hup : ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R, μ (ball z r) ≤ ENNReal.ofReal (r ^ βplus))
    (hfin : μ (ball (0 : ℂ) R) ≠ ⊤) {x : ℂ} (hx : x ∈ closedBall (0 : ℂ) R) {r : ℝ} (hr : 0 < r) :
    μ.restrict (ball 0 R) (closedBall x r) ≤
      ENNReal.ofReal (volumeGrowthAllScalesConstant βplus r₀ (μ (ball (0 : ℂ) R)).toReal * r ^ βplus) := by
  set m := (μ (ball (0 : ℂ) R)).toReal with hm_def
  have hm : 0 ≤ m := ENNReal.toReal_nonneg
  have hrβ : 0 ≤ r ^ βplus := Real.rpow_nonneg hr.le _
  have h2 : 0 ≤ m * (2 / r₀) ^ βplus * r ^ βplus :=
    mul_nonneg (mul_nonneg hm (Real.rpow_nonneg (div_nonneg zero_le_two hr₀.le) _)) hrβ
  have h2' : 0 ≤ 2 ^ βplus * r ^ βplus := mul_nonneg (Real.rpow_nonneg zero_le_two _) hrβ
  unfold volumeGrowthAllScalesConstant
  rcases lt_or_ge (2 * r) r₀ with h | h
  · calc μ.restrict (ball 0 R) (closedBall x r) ≤ μ (closedBall x r) := Measure.restrict_apply_le _ _
      _ ≤ ENNReal.ofReal ((2 * r) ^ βplus) := measure_closedBall_le_of_upper hR hup hx hr h
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [Real.mul_rpow zero_le_two hr.le, add_mul]
          linarith
  · calc μ.restrict (ball 0 R) (closedBall x r) ≤ μ.restrict (ball 0 R) univ := measure_mono (subset_univ _)
      _ = ENNReal.ofReal m := by rw [Measure.restrict_apply_univ, hm_def, ENNReal.ofReal_toReal hfin]
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : 1 ≤ (2 / r₀ * r) ^ βplus :=
            Real.one_le_rpow (by rw [div_mul_eq_mul_div, le_div_iff₀ hr₀]; linarith) hβ.le
          have h3 : m ≤ m * (2 / r₀) ^ βplus * r ^ βplus := by
            rw [mul_assoc, ← Real.mul_rpow (div_nonneg zero_le_two hr₀.le) hr.le]
            exact le_mul_of_one_le_right hm h1
          rw [add_mul]
          linarith

/-- **Hölder continuity of Green potentials on a disc, quantitative form.** Let `μ` be finite on `B_R` with
`μ(B_r(z)) ≤ r^{β⁺}` for `z ∈ B_R`, `0 < r < r₀`. For `f` measurable with `|f| ≤ M` `μ`-a.e. on `B_R`, the Green
potential `q(x) = ∫_{B_R} G_{B_R}(x,y) f(y) μ(dy)` converges absolutely for `x ∈ closedBall 0 R`, and
`|q(x) - q(x')| ≤ C M |x - x'|^α` there, with `α = min(β⁺,1)/2` and `C = greenPotentialHolderConstant β⁺ r₀ μ(B_R)`. -/
theorem greenPotential_ball_holder_of_upper {μ : Measure ℂ} {R r₀ βplus M : ℝ} (hR : 0 < R)
    (hr₀ : 0 < r₀) (hβ : 0 < βplus)
    (hup : ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R, μ (ball z r) ≤ ENNReal.ofReal (r ^ βplus))
    (hfin : μ (ball (0 : ℂ) R) ≠ ⊤) {f : ℂ → ℝ} (hf : AEStronglyMeasurable f (μ.restrict (ball 0 R)))
    (hM : 0 ≤ M) (hfM : ∀ᵐ y ∂μ.restrict (ball 0 R), |f y| ≤ M) :
    (∀ x ∈ closedBall (0 : ℂ) R,
      IntegrableOn (fun y => greenFunction (ball 0 R) x y * f y) (ball 0 R) μ) ∧
    ∀ x ∈ closedBall (0 : ℂ) R, ∀ x' ∈ closedBall (0 : ℂ) R,
      |∫ y in ball 0 R, greenFunction (ball 0 R) x y * f y ∂μ -
          ∫ y in ball 0 R, greenFunction (ball 0 R) x' y * f y ∂μ| ≤
        greenPotentialHolderConstant βplus r₀ (μ (ball (0 : ℂ) R)).toReal * M *
          ‖x - x'‖ ^ greenPotentialHolderExponent βplus := by
  set m := (μ (ball (0 : ℂ) R)).toReal with hm_def
  have hm : 0 ≤ m := ENNReal.toReal_nonneg
  have hα := greenPotentialHolderExponent_pos hβ
  have hball := fun x (hx : x ∈ closedBall (0 : ℂ) R) r (hr : 0 < r) =>
    restrict_ball_closedBall_le hR hr₀ hβ hup hfin hx hr
  have hν : μ.restrict (ball 0 R) univ ≤ ENNReal.ofReal m := by
    rw [Measure.restrict_apply_univ, hm_def, ENNReal.ofReal_toReal hfin]
  exact greenPotential_ball_integrable_and_sub_le hR hα (greenPotentialHolderExponent_le_one βplus)
    (greenPotentialRieszBound_nonneg hβ hr₀ hm)
    (fun x hx => lintegral_norm_sub_rpow_neg_le hα (greenPotentialHolderExponent_lt hβ) hm
      (volumeGrowthAllScalesConstant_nonneg hr₀ hm) hν (hball x hx))
    (fun x hx => measure_singleton_eq_zero_of_le_rpow hβ (hball x hx)) hf hM hfM

/-- **Hölder continuity of Green potentials on a disc under the volume growth condition.** The constant `C` does
not depend on `f` (Hölder seminorm `≤ C ‖f‖_∞`); the exponent is `min(β⁺,1)/2`. -/
theorem VolumeGrowth.greenPotential_ball_holder {μ : Measure ℂ} [IsLocallyFiniteMeasure μ]
    {R βminus βplus : ℝ} (hR : 0 < R) (hμ : VolumeGrowth μ R βminus βplus) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℂ → ℝ) (M : ℝ), AEStronglyMeasurable f (μ.restrict (ball 0 R)) → 0 ≤ M →
      (∀ᵐ y ∂μ.restrict (ball 0 R), |f y| ≤ M) →
      (∀ x ∈ closedBall (0 : ℂ) R,
        IntegrableOn (fun y => greenFunction (ball 0 R) x y * f y) (ball 0 R) μ) ∧
      ∀ x ∈ closedBall (0 : ℂ) R, ∀ x' ∈ closedBall (0 : ℂ) R,
        |∫ y in ball 0 R, greenFunction (ball 0 R) x y * f y ∂μ -
            ∫ y in ball 0 R, greenFunction (ball 0 R) x' y * f y ∂μ| ≤
          C * M * ‖x - x'‖ ^ greenPotentialHolderExponent βplus := by
  obtain ⟨-, hβ, r₀, hr₀, hgr⟩ := hμ
  have hup : ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R, μ (ball z r) ≤ ENNReal.ofReal (r ^ βplus) :=
    fun r hr hrr z hz => (hgr r hr hrr z hz).2
  exact ⟨_, greenPotentialHolderConstant_nonneg hβ hr₀ ENNReal.toReal_nonneg,
    fun f M hf hM hfM => greenPotential_ball_holder_of_upper hR hr₀ hβ hup measure_ball_lt_top.ne hf hM hfM⟩

/-- A real function with `|f x - f y| ≤ C |x - y|^r` on `s` is Hölder on `s`. -/
theorem holderOnWith_of_dist_le {f : ℂ → ℝ} {s : Set ℂ} {C r : ℝ≥0}
    (h : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ C * dist x y ^ (r : ℝ)) : HolderOnWith C r f s := by
  intro x hx y hy
  rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg (NNReal.coe_nonneg r), ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_mul (NNReal.coe_nonneg C)]
  exact ENNReal.ofReal_le_ofReal (h x hx y hy)

/-- **Proposition 2.5, Green clause, for `O = B_R(0)`** (prop:lbm-exit-time, line 524; deterministic form). Let `μ` be a locally finite measure satisfying the volume growth condition on `B_R`. For every
`f ∈ L^∞(closedBall 0 R, μ)` the Green potential `q(x) = ∫_{B_R} G_{B_R}(x,y) f(y) μ(dy)` converges absolutely for
`x ∈ closedBall 0 R = closure (B_R)` and is Hölder continuous there (exponent `min(β⁺,1)/2`). -/
theorem greenPotential_ball_holderOnWith {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] {R βminus βplus : ℝ}
    (hR : 0 < R) (hμ : VolumeGrowth μ R βminus βplus) {f : ℂ → ℝ}
    (hf : MemLp f ⊤ (μ.restrict (closedBall 0 R))) :
    (∀ x ∈ closedBall (0 : ℂ) R,
      IntegrableOn (fun y => greenFunction (ball 0 R) x y * f y) (ball 0 R) μ) ∧
    ∃ C r : ℝ≥0, 0 < r ∧
      HolderOnWith C r (fun x => ∫ y in ball 0 R, greenFunction (ball 0 R) x y * f y ∂μ)
        (closedBall 0 R) := by
  have hβ : 0 < βplus := hμ.2.1
  obtain ⟨C, hC, hH⟩ := hμ.greenPotential_ball_holder hR
  set M := (eLpNorm f ⊤ (μ.restrict (closedBall 0 R))).toReal with hM_def
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  have hfM' : ∀ᵐ y ∂μ.restrict (closedBall 0 R), |f y| ≤ M := by
    filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := μ.restrict (closedBall 0 R))] with y hy
    rw [Real.enorm_eq_ofReal_abs] at hy
    exact (ENNReal.ofReal_le_iff_le_toReal hf.ne).1 (hy.trans eLpNormEssSup_le_eLpNorm_top)
  have hfM : ∀ᵐ y ∂μ.restrict (ball 0 R), |f y| ≤ M :=
    ae_restrict_of_ae_restrict_of_subset ball_subset_closedBall hfM'
  obtain ⟨hI, hD⟩ := hH f M (hf.aestronglyMeasurable.mono_set ball_subset_closedBall) hM hfM
  refine ⟨hI, ⟨C * M, mul_nonneg hC hM⟩, ⟨_, (greenPotentialHolderExponent_pos hβ).le⟩,
    greenPotentialHolderExponent_pos hβ, holderOnWith_of_dist_le fun x hx x' hx' => ?_⟩
  rw [Real.dist_eq, dist_eq_norm]
  exact hD x hx x' hx'

/-- **Property 1 of `q_{B_R}` (Appendix A, line 3538).** Under the volume growth condition, the potential
`q_{B_R}(x) = ∫_{B_R} G_{B_R}(y,x) μ(dy)` is continuous on `closedBall 0 R` (indeed Hölder, case `f = 1` of
`greenPotential_ball_holderOnWith`, by the symmetry of `G_{B_R}`). The statement is verbatim the body of
`GreenPotentialBallContinuousStep` (Steps/SecA/Basic.lean), which cannot be imported here: that file declares
`continuousOn_greenFunction_ball`, a name already taken by Proofs/Potential/GreenBall.lean. -/
theorem greenPotentialBall_continuousOn : ∀ μ : Measure ℂ, IsLocallyFiniteMeasure μ →
    ∀ R βminus βplus : ℝ, 0 < R → VolumeGrowth μ R βminus βplus →
      ContinuousOn (greenPotentialBall μ R) (closedBall 0 R) := by
  intro μ _ R βminus βplus hR hμ
  obtain ⟨-, C, r, hr, h⟩ := greenPotential_ball_holderOnWith hR hμ (memLp_top_const (1 : ℝ))
  refine (h.continuousOn hr).congr fun x _ => ?_
  simp only [greenPotentialBall, mul_one]
  congr 1
  funext y
  exact greenFunction_ball_comm R y x

end HarmonicBalls
