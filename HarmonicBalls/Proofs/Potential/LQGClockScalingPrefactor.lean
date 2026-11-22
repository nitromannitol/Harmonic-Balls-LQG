import HarmonicBalls.Proofs.Potential.LQGClockTimeChangeReduction
import HarmonicBalls.Proofs.Sec6.BrownianScaling
import HarmonicBalls.Proofs.Sec11.SingularCompactNull
import LatticeProb.LQG.GMCCircleLaw

/-! # Scaling of the LQG clock of the inserted field

Bertacco and Gwynne (*Liouville Brownian motion and quantum cones in dimension `d > 2`*,
arXiv:2501.15936v2), proof of Theorem 5.12 (B4), in the plane and for the inserted field
`h = h^ℂ - α log |·|` with the clock normalization `ε^{γ²/2} e^{γ h_ε}`. For `n > 0` let
`h^{(n)}_r(z) = h^ℂ_{n r}(n z) - h^ℂ_n(0)` be the circle averages of the rescaled field
`h^ℂ(n ·) - h^ℂ_n(0)` (again a whole-plane GFF, by the affine invariance of the whole-plane GFF),
and let `b̃_u = n⁻¹ b_{n² u}` be the rescaled path (again a planar Brownian motion from `0`, by
Brownian scaling). Since `log max(ε, n |w|) = log n + log max(ε / n, |w|)`, the approximating
clocks satisfy the exact identity
`∫_0^{n² t} ε^{γ²/2} e^{γ h_ε(b_s)} ds`
`= n^{2 + γ²/2 - γ α} e^{γ h^ℂ_n(0)} ∫_0^t (ε/n)^{γ²/2} e^{γ h^{(n)}_{ε/n}(b̃_u)} du`,
where `h^{(n)}` carries the same insertion `-α log |·|`. Along the dyadic scales with `n = 2^m`
this passes to the LQG clocks: almost surely `F(4^m t) = c_m F^{(m)}(b̃)(t)` for all `t`, with the
prefactor `c_m = 2^{m (2 + γ²/2 - γ α)} e^{γ h^ℂ_{2^m}(0)}`. Since `h^ℂ_{2^m}(0)` is a centered
Gaussian of variance `m log 2` and `2 + γ²/2 - γ α = γ (Q - α) > 0` for `α < Q`, the Gaussian
Borel-Cantelli lemma gives `c_m → ∞` almost surely.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal
namespace HarmonicBalls

/-- The circle averages `(r, z) ↦ h_{n r}(n z) - h_n(0)` of the rescaled field `h(n ·) - h_n(0)`,
written as in the affine invariance of the whole-plane GFF with `a = n` and `b = 0`. -/
noncomputable def rescaledCircleAverage (hcirc : ℝ → ℂ → ℝ) (n r : ℝ) (z : ℂ) : ℝ :=
  hcirc (‖(n : ℂ)‖ * r) ((n : ℂ) * z + 0) - hcirc ‖(n : ℂ)‖ 0

/-- The density of the approximating clock of the inserted field at `n w` and scale `ε` is
`n^{γ²/2 - γ α} e^{γ h_n(0)}` times the density of the rescaled field at `w` and scale `ε / n`. -/
theorem rpow_mul_exp_fieldCircleAverage_mul (hcirc : ℝ → ℂ → ℝ) (α γ : ℝ) {n ε : ℝ}
    (hn : 0 < n) (hε : 0 < ε) (w : ℂ) :
    ε ^ (γ ^ 2 / 2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α hcirc ε ((n : ℂ) * w)) =
      n ^ (γ ^ 2 / 2 - γ * α) * Real.exp (γ * hcirc n 0) *
        ((ε / n) ^ (γ ^ 2 / 2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α
          (rescaledCircleAverage hcirc n) (ε / n) w)) := by
  have hεn : 0 < ε / n := div_pos hε hn
  have hnorm : ‖(n : ℂ)‖ = n := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn]
  have h1 : ‖(n : ℂ)‖ * (ε / n) = ε := by
    rw [hnorm]
    field_simp
  simp only [LatticeProb.Gauss.fieldCircleAverage, rescaledCircleAverage]
  rw [h1, hnorm, add_zero, circleAverage_log_norm_eq_log_max hε,
    circleAverage_log_norm_eq_log_max hεn]
  have hmax : max ε ‖(n : ℂ) * w‖ = n * max (ε / n) ‖w‖ := by
    rw [norm_mul, hnorm, mul_max_of_nonneg _ _ hn.le, mul_div_cancel₀ _ hn.ne']
  have hlogmax : Real.log (max ε ‖(n : ℂ) * w‖) = Real.log n + Real.log (max (ε / n) ‖w‖) := by
    rw [hmax, Real.log_mul hn.ne' (lt_max_of_lt_left hεn).ne']
  rw [hlogmax, Real.rpow_def_of_pos hε, Real.rpow_def_of_pos hn, Real.rpow_def_of_pos hεn,
    Real.log_div hε.ne' hn.ne']
  simp only [← Real.exp_add]
  congr 1
  ring

/-- Brownian scaling of the approximating clock of the inserted field: at time `n² t` and scale
`ε` it is `n^{2 + γ²/2 - γ α} e^{γ h_n(0)}` times the approximating clock of the rescaled field at
time `t` and scale `ε / n` along the rescaled path `u ↦ n⁻¹ b(n² u)`. -/
theorem lqgClockApprox_fieldCircleAverage_mul_time (hcirc : ℝ → ℂ → ℝ) (α γ : ℝ) {n ε : ℝ}
    (hn : 0 < n) (hε : 0 < ε) (b : ContinuousPath ℂ) (t : ℝ≥0) :
    lqgClockApprox γ (LatticeProb.Gauss.fieldCircleAverage α hcirc) ε b ((n ^ 2).toNNReal * t) =
      n ^ (2 + γ ^ 2 / 2 - γ * α) * Real.exp (γ * hcirc n 0) *
        lqgClockApprox γ (LatticeProb.Gauss.fieldCircleAverage α (rescaledCircleAverage hcirc n))
          (ε / n) (Section6.scaledCenteredPlanarPath 0 (n ^ 2).toNNReal b) t := by
  have hc : 0 < n ^ 2 := by positivity
  let f : ℝ → ℝ := fun s => ε ^ (γ ^ 2 / 2) *
    Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α hcirc ε (b s.toNNReal))
  let g : ℝ → ℝ := fun u => (ε / n) ^ (γ ^ 2 / 2) *
    Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (rescaledCircleAverage hcirc n) (ε / n)
      (Section6.scaledCenteredPlanarPath 0 (n ^ 2).toNNReal b u.toNNReal))
  have hsqrt : Real.sqrt ((n ^ 2).toNNReal : ℝ) = n := by
    rw [Real.coe_toNNReal _ hc.le, Real.sqrt_sq hn.le]
  have hpath (u : ℝ) : b (n ^ 2 * u).toNNReal =
      (n : ℂ) * Section6.scaledCenteredPlanarPath 0 (n ^ 2).toNNReal b u.toNNReal := by
    simp only [Section6.scaledCenteredPlanarPath, ContinuousMap.coe_mk, sub_zero, hsqrt]
    rw [Real.toNNReal_mul hc.le, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
      mul_inv_cancel₀ hn.ne', Complex.ofReal_one, one_mul]
  have hfg (u : ℝ) : f (n ^ 2 * u) =
      n ^ (γ ^ 2 / 2 - γ * α) * Real.exp (γ * hcirc n 0) * g u := by
    simp only [f, g]
    rw [hpath u]
    exact rpow_mul_exp_fieldCircleAverage_mul hcirc α γ hn hε _
  have hsub : ∫ s in (0 : ℝ)..n ^ 2 * t, f s = n ^ 2 * ∫ u in (0 : ℝ)..t, f (n ^ 2 * u) := by
    rw [intervalIntegral.integral_comp_mul_left f hc.ne', mul_zero, smul_eq_mul,
      ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
  have hcoe : (((n ^ 2).toNNReal * t : ℝ≥0) : ℝ) = n ^ 2 * t := by
    rw [NNReal.coe_mul, Real.coe_toNNReal _ hc.le]
  have hpow : n ^ (2 + γ ^ 2 / 2 - γ * α) = n ^ 2 * n ^ (γ ^ 2 / 2 - γ * α) := by
    rw [show 2 + γ ^ 2 / 2 - γ * α = (2 : ℝ) + (γ ^ 2 / 2 - γ * α) by ring,
      Real.rpow_add hn, Real.rpow_two]
  show (∫ s in (0 : ℝ)..(((n ^ 2).toNNReal * t : ℝ≥0) : ℝ), f s) =
    n ^ (2 + γ ^ 2 / 2 - γ * α) * Real.exp (γ * hcirc n 0) * ∫ u in (0 : ℝ)..(t : ℝ), g u
  rw [hcoe, hsub]
  simp only [hfg, intervalIntegral.integral_const_mul, hpow]
  ring

/-- The dyadic scale `2^{-k}` divided by `2^m` is the dyadic scale `2^{-(k+m)}`. -/
theorem dyadicScale_div_two_pow (k m : ℕ) : dyadicScale k / (2 : ℝ) ^ m = dyadicScale (k + m) := by
  rw [dyadicScale, dyadicScale, pow_add, inv_pow 2 m, div_eq_mul_inv]

/-- Brownian scaling of the dyadic approximating clocks with `n = 2^m`. -/
theorem lqgClockApprox_fieldCircleAverage_dyadic_mul_time (hcirc : ℝ → ℂ → ℝ) (α γ : ℝ)
    (m k : ℕ) (b : ContinuousPath ℂ) (t : ℝ≥0) :
    lqgClockApprox γ (LatticeProb.Gauss.fieldCircleAverage α hcirc) (dyadicScale k) b
        ((((2 : ℝ) ^ m) ^ 2).toNNReal * t) =
      ((2 : ℝ) ^ m) ^ (2 + γ ^ 2 / 2 - γ * α) * Real.exp (γ * hcirc ((2 : ℝ) ^ m) 0) *
        lqgClockApprox γ
          (LatticeProb.Gauss.fieldCircleAverage α (rescaledCircleAverage hcirc ((2 : ℝ) ^ m)))
          (dyadicScale (k + m))
          (Section6.scaledCenteredPlanarPath 0 (((2 : ℝ) ^ m) ^ 2).toNNReal b) t := by
  rw [lqgClockApprox_fieldCircleAverage_mul_time hcirc α γ (n := (2 : ℝ) ^ m) (by positivity)
    (dyadicScale_pos k), dyadicScale_div_two_pow]

/-- Brownian scaling of LQG clocks of the inserted field from the origin: if `F` is an LQG clock
of the field and `F'` one of the field rescaled by `n = 2^m`, then almost surely
`F(4^m t) = 2^{m (2 + γ²/2 - γ α)} e^{γ h_{2^m}(0)} F'(b̃)(t)` for all `t`, where
`b̃_u = 2^{-m} b(4^m u)` is the rescaled path. -/
theorem ae_lqgClock_mul_time_eq {hcirc : ℝ → ℂ → ℝ} {α γ : ℝ} (m : ℕ)
    {F F' : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hF : IsLQGClock planarBrownianMotion γ (LatticeProb.Gauss.fieldCircleAverage α hcirc) 0 F)
    (hF' : IsLQGClock planarBrownianMotion γ
      (LatticeProb.Gauss.fieldCircleAverage α (rescaledCircleAverage hcirc ((2 : ℝ) ^ m))) 0 F') :
    ∀ᵐ b ∂(planarBrownianMotion 0), ∀ t : ℝ≥0, F b ((((2 : ℝ) ^ m) ^ 2).toNNReal * t) =
      ((2 : ℝ) ^ m) ^ (2 + γ ^ 2 / 2 - γ * α) * Real.exp (γ * hcirc ((2 : ℝ) ^ m) 0) *
        F' (Section6.scaledCenteredPlanarPath 0 (((2 : ℝ) ^ m) ^ 2).toNNReal b) t := by
  set c : ℝ≥0 := (((2 : ℝ) ^ m) ^ 2).toNNReal with hcdef
  have hc : 0 < c := by
    rw [hcdef, Real.toNNReal_pos]
    positivity
  set K : ℝ := ((2 : ℝ) ^ m) ^ (2 + γ ^ 2 / 2 - γ * α) * Real.exp (γ * hcirc ((2 : ℝ) ^ m) 0)
    with hK
  have hK0 : 0 < K := by rw [hK]; positivity
  let S : ContinuousPath ℂ → ContinuousPath ℂ := Section6.scaledCenteredPlanarPath 0 c
  have hSm : Measurable S := (Section6.continuous_scaledCenteredPlanarPath 0 c).measurable
  have hSmap : (planarBrownianMotion 0).map S = planarBrownianMotion 0 :=
    Section6.planarBrownianMotion_map_scaledCenteredPlanarPath 0 hc.ne'
  let G : ContinuousPath ℂ → ℝ≥0 → ℝ := fun b t => K * F' (S b) (t / c)
  have hG :
      IsLQGClock planarBrownianMotion γ (LatticeProb.Gauss.fieldCircleAverage α hcirc) 0 G := by
    intro T η hη
    have hlim := (hF' (T / c) (η / K) (div_pos hη hK0)).comp (tendsto_add_atTop_nat m)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun k => zero_le) fun k => ?_
    simp only [Function.comp_apply]
    set X : Set (ContinuousPath ℂ) := {b' | ∃ t ≤ T / c, η / K ≤ |lqgClockApprox γ
      (LatticeProb.Gauss.fieldCircleAverage α (rescaledCircleAverage hcirc ((2 : ℝ) ^ m)))
        (dyadicScale (k + m)) b' t - F' b' t|} with hX
    have h2 : (planarBrownianMotion 0) (S ⁻¹' X) ≤ (planarBrownianMotion 0) X :=
      (Measure.le_map_apply hSm.aemeasurable X).trans_eq (by rw [hSmap])
    refine le_trans (measure_mono ?_) h2
    rintro b ⟨t, htT, hb⟩
    refine ⟨t / c, by gcongr, ?_⟩
    have hct : c * (t / c) = t := mul_div_cancel₀ t hc.ne'
    have hA := lqgClockApprox_fieldCircleAverage_dyadic_mul_time hcirc α γ m k b (t / c)
    rw [← hcdef, hct] at hA
    have hb' : η ≤ |K * (lqgClockApprox γ
        (LatticeProb.Gauss.fieldCircleAverage α (rescaledCircleAverage hcirc ((2 : ℝ) ^ m)))
        (dyadicScale (k + m)) (S b) (t / c) - F' (S b) (t / c))| := by
      rw [mul_sub]
      simpa only [G, S, hA, hK] using hb
    rw [abs_mul, abs_of_pos hK0] at hb'
    rw [div_le_iff₀ hK0, mul_comm]
    exact hb'
  filter_upwards [ae_eq_of_isLQGClock hF hG] with b hb t
  rw [hb]
  simp only [G, S]
  rw [mul_div_cancel_left₀ t hc.ne']

/-- The prefactors `(2^m)^a e^{γ h_{2^m}(0)}`, `a > 0`, of a whole-plane GFF tend to infinity
almost surely: `h_{2^m}(0)` is a centered Gaussian of variance `m log 2`, so by the Gaussian
Borel-Cantelli lemma `|γ h_{2^m}(0)| ≤ a m log 2 / 2` for all large `m`. -/
theorem ae_tendsto_rpow_mul_exp_circle_atTop {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ : ℝ) {a : ℝ} (ha : 0 < a) :
    ∀ᵐ ω ∂P, Tendsto (fun m : ℕ => ((2 : ℝ) ^ m) ^ a * Real.exp (γ * hcirc ω ((2 : ℝ) ^ m) 0))
      atTop atTop := by
  have hP := hh.isProbabilityMeasure
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hG (j : ℕ) := hh.hasLaw_circle_origin (R := (2 : ℝ) ^ j) (by positivity)
  have hσ (j : ℕ) : (((2 * Real.log (max ((2 : ℝ) ^ j) 1) - Real.log ((2 : ℝ) ^ j)).toNNReal : ℝ≥0)
      : ℝ) ≤ Real.log 2 * j + 0 := by
    have hmax : max ((2 : ℝ) ^ j) 1 = (2 : ℝ) ^ j := max_eq_left (one_le_pow₀ one_le_two)
    rw [hmax, Real.log_pow]
    have h0 : (0 : ℝ) ≤ 2 * ((j : ℝ) * Real.log 2) - (j : ℝ) * Real.log 2 := by
      have : (0 : ℝ) ≤ (j : ℝ) * Real.log 2 := by positivity
      linarith
    rw [Real.coe_toNNReal _ h0]
    exact le_of_eq (by ring)
  set η : ℝ := a * Real.log 2 / (2 * (|γ| + 1)) with hηdef
  have hη : 0 < η := by positivity
  filter_upwards [LatticeProb.GaussBC.ae_eventually_abs_lt hlog2 hG hσ hη] with ω hω
  have hexp : Tendsto (fun j : ℕ => Real.exp ((j : ℝ) * (a * Real.log 2 / 2))) atTop atTop :=
    Real.tendsto_exp_atTop.comp
      (tendsto_natCast_atTop_atTop.atTop_mul_const (by positivity))
  refine tendsto_atTop_mono' atTop ?_ hexp
  filter_upwards [hω] with j hj
  have hγη : |γ| * η ≤ a * Real.log 2 / 2 := by
    have h1 : (|γ| + 1) * η = a * Real.log 2 / 2 := by
      rw [hηdef]
      field_simp
    nlinarith [abs_nonneg γ]
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hlow : -(a * Real.log 2 / 2) * j ≤ γ * hcirc ω ((2 : ℝ) ^ j) 0 := by
    have h1 : |γ * hcirc ω ((2 : ℝ) ^ j) 0| ≤ |γ| * (η * j) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hj.le (abs_nonneg γ)
    have h2 := neg_abs_le (γ * hcirc ω ((2 : ℝ) ^ j) 0)
    have h3 : |γ| * η * j ≤ a * Real.log 2 / 2 * j := mul_le_mul_of_nonneg_right hγη hj0
    nlinarith
  rw [Real.rpow_def_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) j), ← Real.exp_add, Real.log_pow]
  refine Real.exp_le_exp.mpr ?_
  nlinarith

end HarmonicBalls
