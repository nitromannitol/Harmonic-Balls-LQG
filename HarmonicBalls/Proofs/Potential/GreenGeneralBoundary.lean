import Mathlib
import HarmonicBalls.Draft.Section2
import HarmonicBalls.Proofs.Potential.SmoothDomainExteriorSphere
import HarmonicBalls.Proposed.GilbargTrudinger

/-!
# Uniform boundary estimate for the Dirichlet solution on a smooth bounded open set

Stage 1 of the general-domain Green potential estimate (Proposition 2.5, Green clause), steps4-final
Section 1, lines 125-199. The only literature input is `GilbargTrudingerThm2_14`
(Gilbarg-Trudinger, Theorem 2.14, p. 26; barrier (2.34), p. 27), taken as a hypothesis.

Contents:
* the weak maximum principle for functions harmonic on a bounded open set, proved from the mean value
  property (Mathlib `InnerProductSpace.HarmonicOnNhd.circleAverage_eq`) applied to `v + ε‖x‖²`;
* the logarithmic exterior barrier `log (dist x w / d)` and its two-sided bounds;
* the boundary modulus `|u x - g z| ≤ C |x - z|^κ`, `κ = a/(a+2)`, by barrier comparison (lines 125-151).
-/

namespace HarmonicBalls

namespace GreenGeneral

open Metric Set Filter Topology
open InnerProductSpace

/-! ## 1. Circle averages of `‖x‖²` -/

/-- The circle average of `x ↦ ‖x‖²` over the circle of centre `q` and radius `r` is `‖q‖² + r²`. -/
lemma circleAverage_norm_sq (q : ℂ) (r : ℝ) :
    Real.circleAverage (fun x : ℂ => ‖x‖ ^ 2) q r = ‖q‖ ^ 2 + r ^ 2 := by
  have hpt : ∀ θ : ℝ, ‖circleMap q r θ‖ ^ 2 =
      (q.re ^ 2 + q.im ^ 2 + r ^ 2) + (2 * r * q.re) * Real.cos θ + (2 * r * q.im) * Real.sin θ := by
    intro θ
    have hre : (circleMap q r θ).re = q.re + r * Real.cos θ := by
      simp [circleMap, Complex.exp_ofReal_mul_I_re]
    have him : (circleMap q r θ).im = q.im + r * Real.sin θ := by
      simp [circleMap, Complex.exp_ofReal_mul_I_im]
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hnorm : ‖q‖ ^ 2 = q.re ^ 2 + q.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hint : ∫ θ in (0 : ℝ)..2 * Real.pi,
      ((q.re ^ 2 + q.im ^ 2 + r ^ 2) + (2 * r * q.re) * Real.cos θ + (2 * r * q.im) * Real.sin θ)
        = 2 * Real.pi * (q.re ^ 2 + q.im ^ 2 + r ^ 2) := by
    rw [intervalIntegral.integral_add, intervalIntegral.integral_add,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_cos, integral_sin]
    · simp
      ring
    all_goals (apply Continuous.intervalIntegrable; fun_prop)
  unfold Real.circleAverage
  have hfun : (fun θ : ℝ => (fun x : ℂ => ‖x‖ ^ 2) (circleMap q r θ)) =
      fun θ : ℝ => (q.re ^ 2 + q.im ^ 2 + r ^ 2) + (2 * r * q.re) * Real.cos θ
        + (2 * r * q.im) * Real.sin θ := by
    funext θ
    exact hpt θ
  rw [hfun, hint, smul_eq_mul]
  field_simp
  rw [hnorm]

/-- Circle averages commute with constant multiples of the squared norm. -/
lemma circleAverage_const_mul_norm_sq (ε : ℝ) (q : ℂ) (r : ℝ) :
    Real.circleAverage (fun x : ℂ => ε * ‖x‖ ^ 2) q r =
      ε * Real.circleAverage (fun x : ℂ => ‖x‖ ^ 2) q r := by
  unfold Real.circleAverage
  simp only [intervalIntegral.integral_const_mul, smul_eq_mul]
  ring

/-! ## 2. Weak maximum principle for harmonic functions on a bounded open set -/

/-- Weak maximum principle. If `v` is harmonic on a bounded open set `U`, continuous on `closure U`,
and `v ≤ M` on `frontier U`, then `v ≤ M` on `closure U`. Proof: for `ε > 0` the function
`w = v + ε‖x‖²` attains its maximum over `closure U` at some `q`; if `q ∈ U`, the circle average of
`w` about `q` equals `w q + ε r²` by the mean value property of `v`, which contradicts `w ≤ w q` on
the circle. Hence `q ∈ frontier U`, and the bound follows as `ε ↓ 0`. -/
theorem le_of_frontier_le {U : Set ℂ} (hU : IsOpen U) (hb : Bornology.IsBounded U)
    {v : ℂ → ℝ} (hv : HarmonicOnNhd v U) (hc : ContinuousOn v (closure U)) {M : ℝ}
    (hM : ∀ z ∈ frontier U, v z ≤ M) : ∀ z ∈ closure U, v z ≤ M := by
  have hK : IsCompact (closure U) := hb.isCompact_closure
  obtain ⟨D, hD⟩ : ∃ D : ℝ, ∀ x ∈ closure U, ‖x‖ ≤ D :=
    isBounded_iff_forall_norm_le.mp hb.closure
  have key : ∀ ε : ℝ, 0 < ε → ∀ z ∈ closure U, v z ≤ M + ε * (D ^ 2 + 1) := by
    intro ε hε z hz
    have hwc : ContinuousOn (fun x => v x + ε * ‖x‖ ^ 2) (closure U) :=
      hc.add (Continuous.continuousOn (by fun_prop))
    obtain ⟨q, hq, hqmax⟩ := hK.exists_isMaxOn ⟨z, hz⟩ hwc
    have hqmax' : ∀ x ∈ closure U, v x + ε * ‖x‖ ^ 2 ≤ v q + ε * ‖q‖ ^ 2 :=
      fun x hx => isMaxOn_iff.mp hqmax x hx
    have hqU : q ∉ U := by
      intro hqU
      obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hU q hqU
      obtain ⟨r, hr, hrρ⟩ : ∃ r : ℝ, 0 < r ∧ r < ρ := ⟨ρ / 2, by positivity, by linarith⟩
      have hsub : closedBall q r ⊆ U := (Metric.closedBall_subset_ball hrρ).trans hball
      have hsub' : closedBall q |r| ⊆ U := by rw [abs_of_pos hr]; exact hsub
      have hcont : ContinuousOn v (sphere q r) :=
        hc.mono (fun x hx => subset_closure (hsub (sphere_subset_closedBall hx)))
      have hharm : HarmonicOnNhd v (closedBall q |r|) := hv.mono hsub'
      have hvq : Real.circleAverage v q r = v q :=
        InnerProductSpace.HarmonicOnNhd.circleAverage_eq (R := r) hharm
      have hI : CircleIntegrable v q r := hcont.circleIntegrable hr.le
      have hcontw : ContinuousOn (fun x : ℂ => ε * ‖x‖ ^ 2) (sphere q r) :=
        Continuous.continuousOn (by fun_prop)
      have hII : CircleIntegrable (fun x : ℂ => ε * ‖x‖ ^ 2) q r :=
        hcontw.circleIntegrable hr.le
      have hw_avg : Real.circleAverage (fun x => v x + ε * ‖x‖ ^ 2) q r =
          v q + ε * (‖q‖ ^ 2 + r ^ 2) := by
        rw [Real.circleAverage_fun_add hI hII, circleAverage_const_mul_norm_sq,
          circleAverage_norm_sq, hvq]
      have hwc2 : ContinuousOn (fun x : ℂ => v x + ε * ‖x‖ ^ 2) (sphere q r) :=
        ContinuousOn.add hcont hcontw
      have hwI : CircleIntegrable (fun x : ℂ => v x + ε * ‖x‖ ^ 2) q r :=
        hwc2.circleIntegrable hr.le
      have hw_le : Real.circleAverage (fun x => v x + ε * ‖x‖ ^ 2) q r ≤
          v q + ε * ‖q‖ ^ 2 := by
        have hmono := Real.circleAverage_mono (c := q) (R := r) hwI
          (circleIntegrable_const (v q + ε * ‖q‖ ^ 2) q r)
          (fun x hx => hqmax' x (subset_closure (hsub' (sphere_subset_closedBall hx))))
        rw [Real.circleAverage_const] at hmono
        exact hmono
      have hεr : 0 < ε * r ^ 2 := by positivity
      have hexp : v q + ε * (‖q‖ ^ 2 + r ^ 2) = v q + ε * ‖q‖ ^ 2 + ε * r ^ 2 := by ring
      linarith
    have hqfr : q ∈ frontier U := ⟨hq, fun h => hqU (hU.interior_eq ▸ h)⟩
    have hDq : ‖q‖ ≤ D := hD q hq
    have hq2 : ‖q‖ ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hDq 2
    have h3 : ε * ‖q‖ ^ 2 ≤ ε * D ^ 2 := mul_le_mul_of_nonneg_left hq2 hε.le
    have h4 : 0 ≤ ε * ‖z‖ ^ 2 := by positivity
    have hzq := hqmax' z hz
    have h5 : ε * D ^ 2 ≤ ε * (D ^ 2 + 1) := by nlinarith
    linarith [hM q hqfr]
  intro z hz
  by_contra hcon
  have hlt : M < v z := not_le.mp hcon
  have hδ : 0 < v z - M := by linarith
  have hD2 : 0 < D ^ 2 + 1 := by positivity
  have hε : 0 < (v z - M) / (2 * (D ^ 2 + 1)) := div_pos hδ (by positivity)
  have h := key _ hε z hz
  have h2 : (v z - M) / (2 * (D ^ 2 + 1)) * (D ^ 2 + 1) = (v z - M) / 2 := by
    field_simp
  linarith

/-- Two-sided weak maximum principle: if `|v| ≤ M` on `frontier U` then `|v| ≤ M` on `closure U`. -/
theorem abs_le_of_frontier_abs_le {U : Set ℂ} (hU : IsOpen U) (hb : Bornology.IsBounded U)
    {v : ℂ → ℝ} (hv : HarmonicOnNhd v U) (hc : ContinuousOn v (closure U)) {M : ℝ}
    (hM : ∀ z ∈ frontier U, |v z| ≤ M) : ∀ z ∈ closure U, |v z| ≤ M := by
  intro z hz
  have h1 := le_of_frontier_le hU hb hv hc (fun w hw => (le_abs_self _).trans (hM w hw)) z hz
  have h2 := le_of_frontier_le hU hb hv.neg hc.neg
    (fun w hw => by simp only [Pi.neg_apply]; exact (neg_le_abs _).trans (hM w hw)) z hz
  simp only [Pi.neg_apply] at h2
  exact abs_le.mpr ⟨by linarith, h1⟩

/-! ## 3. The logarithmic exterior barrier -/

/-- `y ↦ log (dist y w / d)` is harmonic at every point `x ≠ w` (Mathlib: log of the norm of an
analytic function without zero at the point). -/
lemma harmonicAt_log_dist_div {w x : ℂ} (hx : x ≠ w) {d : ℝ} (hd : 0 < d) :
    HarmonicAt (fun y : ℂ => Real.log (dist y w / d)) x := by
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hf : AnalyticAt ℂ (fun y : ℂ => (y - w) / (d : ℂ)) x :=
    (analyticAt_id.sub analyticAt_const).div analyticAt_const hdC
  have hfx : (fun y : ℂ => (y - w) / (d : ℂ)) x ≠ 0 := by
    simp only [div_ne_zero_iff, sub_ne_zero]
    exact ⟨hx, hdC⟩
  have h := AnalyticAt.harmonicAt_log_norm hf hfx
  have heq : (fun y : ℂ => Real.log (dist y w / d)) =
      fun y : ℂ => Real.log ‖(fun y : ℂ => (y - w) / (d : ℂ)) y‖ := by
    funext y
    simp only [dist_eq_norm, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
  rw [heq]
  exact h

/-- The barrier constant `c = 1 / (4 d² (1 + T²/(2d²)))`, where `T` bounds the diameter of `closure O`. -/
noncomputable def barrierConst (d T : ℝ) : ℝ := 1 / (4 * d ^ 2 * (1 + T ^ 2 / (2 * d ^ 2)))

lemma barrierConst_pos {d T : ℝ} (hd : 0 < d) : 0 < barrierConst d T := by
  unfold barrierConst
  positivity

/-- For `t ≥ 0`: `t / (1 + t) ≤ log (1 + t)`. -/
lemma div_one_add_le_log_one_add {t : ℝ} (ht : 0 ≤ t) : t / (1 + t) ≤ Real.log (1 + t) := by
  have hpos : (0 : ℝ) < 1 + t := by linarith
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at h
  have h2 : (1 + t)⁻¹ - 1 = -(t / (1 + t)) := by
    field_simp
    ring
  linarith

/-- Two-sided bounds for the exterior barrier `b(y) = log (dist y w / d)`, where `dist w z = d` and
the exterior sphere inequality `d² + ½ dist y z² ≤ dist y w²` holds. -/
lemma barrier_bounds {d T : ℝ} (hd : 0 < d) {z w y : ℂ} (hwz : dist w z = d)
    (hyw : d ^ 2 + (1 / 2 : ℝ) * dist y z ^ 2 ≤ dist y w ^ 2) (hyT : dist y z ≤ T) :
    barrierConst d T * dist y z ^ 2 ≤ Real.log (dist y w / d) ∧
      Real.log (dist y w / d) ≤ dist y z / d := by
  have hZ0 : 0 ≤ dist y z := dist_nonneg
  have hA0 : 0 ≤ dist y w := dist_nonneg
  have hAd : d ≤ dist y w := by nlinarith [sq_nonneg (dist y z)]
  have hdpos : 0 < dist y w / d := div_pos (lt_of_lt_of_le hd hAd) hd
  constructor
  · -- lower bound through `(A/d)² ≥ 1 + t`, `t = Z²/(2d²)`
    have ht0 : 0 ≤ dist y z ^ 2 / (2 * d ^ 2) := by positivity
    have hsq : 1 + dist y z ^ 2 / (2 * d ^ 2) ≤ (dist y w / d) ^ 2 := by
      rw [div_pow, le_div_iff₀ (by positivity)]
      field_simp
      nlinarith [hyw]
    have hlog2 : Real.log (1 + dist y z ^ 2 / (2 * d ^ 2)) ≤ 2 * Real.log (dist y w / d) := by
      have hpow : Real.log ((dist y w / d) ^ 2) = 2 * Real.log (dist y w / d) := by
        rw [Real.log_pow]
        norm_num
      rw [← hpow]
      exact Real.log_le_log (by positivity) hsq
    have hT' : dist y z ^ 2 / (2 * d ^ 2) ≤ T ^ 2 / (2 * d ^ 2) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [hyT, hZ0]
    have hfrac : dist y z ^ 2 / (2 * d ^ 2) / (1 + T ^ 2 / (2 * d ^ 2)) ≤
        dist y z ^ 2 / (2 * d ^ 2) / (1 + dist y z ^ 2 / (2 * d ^ 2)) := by
      apply div_le_div_of_nonneg_left ht0 (by positivity)
      linarith
    have hkey := div_one_add_le_log_one_add ht0
    have hconst : barrierConst d T * dist y z ^ 2 =
        (1 / 2) * (dist y z ^ 2 / (2 * d ^ 2) / (1 + T ^ 2 / (2 * d ^ 2))) := by
      unfold barrierConst
      field_simp
      ring
    nlinarith [hlog2, hkey, hfrac, hconst]
  · -- upper bound through `log y ≤ y - 1` and `dist y w ≤ dist y z + d`
    have hAZ : dist y w ≤ dist y z + d := by
      have h := dist_triangle y z w
      rw [dist_comm z w, hwz] at h
      exact h
    have h1 := Real.log_le_sub_one_of_pos hdpos
    have h2 : dist y w / d - 1 ≤ dist y z / d := by
      have h3 := div_le_div_of_nonneg_right hAZ hd.le
      rw [add_div, div_self hd.ne'] at h3
      linarith
    linarith

/-! ## 4. The boundary modulus from the barrier -/

/-- Power identities for `κ = a/(a+2)` and the scale `s = r^(1/(a+2))`. -/
lemma rpow_identities {r a : ℝ} (hr : 0 < r) (ha : 0 < a) :
    (r ^ (1 / (a + 2))) ^ a = r ^ (a / (a + 2)) ∧
      r / (r ^ (1 / (a + 2))) ^ 2 = r ^ (a / (a + 2)) := by
  have ha2 : (0 : ℝ) < a + 2 := by linarith
  constructor
  · rw [← Real.rpow_mul hr.le]
    congr 1
    field_simp
  · have h2 : (r ^ (1 / (a + 2))) ^ 2 = r ^ (2 / (a + 2)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
      congr 1
      push_cast
      field_simp
    rw [h2, show a / (a + 2) = 1 - 2 / (a + 2) by field_simp; ring, Real.rpow_sub hr, Real.rpow_one]

/-- One-sided barrier comparison. Let `z ∈ ∂O` carry an exterior sphere of radius `d` centred at `w`
(`hw`). If `u` is harmonic on `U ⊆ O`, continuous on `closure U`, equal to `g` on `∂U`, and `g` is
`a`-Hölder with constant `L` and bounded by `B` on `∂O`, then for `0 < s ≤ 1` we get
`u ≤ g z + L s^a + k · log (dist · w / d)` on `closure U`, where `k = 2B / (c s²)`. -/
lemma upper_barrier_bound {O U : Set ℂ} (hUO : U ⊆ O) (hU : IsOpen U)
    (hbU : Bornology.IsBounded U) (hfr : frontier U ⊆ frontier O)
    {d T : ℝ} (hd : 0 < d) (hT : ∀ x ∈ closure O, ∀ y ∈ closure O, dist x y ≤ T)
    {a L B : ℝ} (ha : 0 < a) (hL : 0 ≤ L) (hB : 0 ≤ B) {g : ℂ → ℝ}
    (hgL : ∀ x ∈ frontier O, ∀ y ∈ frontier O, |g x - g y| ≤ L * dist x y ^ a)
    (hgB : ∀ x ∈ frontier O, |g x| ≤ B)
    {u : ℂ → ℝ} (hu : HarmonicOnNhd u U) (huc : ContinuousOn u (closure U))
    (hub : ∀ ξ ∈ frontier U, u ξ = g ξ)
    {z : ℂ} (hz : z ∈ frontier O) {w : ℂ} (hwz : dist w z = d)
    (hw : ∀ x ∈ closure O, d ^ 2 + (1 / 2 : ℝ) * dist x z ^ 2 ≤ dist x w ^ 2)
    {s : ℝ} (hs0 : 0 < s) :
    ∀ y ∈ closure U, u y ≤ g z + L * s ^ a +
      (2 * B / (barrierConst d T * s ^ 2)) * Real.log (dist y w / d) := by
  have hc : 0 < barrierConst d T := barrierConst_pos hd
  have hk0 : 0 ≤ 2 * B / (barrierConst d T * s ^ 2) := by positivity
  have hbnd : ∀ y ∈ closure O, d ≤ dist y w := by
    intro y hy
    have h := hw y hy
    have hsq : d ^ 2 ≤ dist y w ^ 2 := by nlinarith [sq_nonneg (dist y z)]
    exact (pow_le_pow_iff_left₀ hd.le dist_nonneg two_ne_zero).mp hsq
  have hbh : HarmonicOnNhd (fun y : ℂ => Real.log (dist y w / d)) U := by
    intro y hy
    have hyO : y ∈ closure O := subset_closure (hUO hy)
    have hne : y ≠ w := by
      intro h
      have := hbnd y hyO
      rw [h, dist_self] at this
      linarith
    exact harmonicAt_log_dist_div hne hd
  have hbc : ContinuousOn (fun y : ℂ => Real.log (dist y w / d)) (closure U) := by
    intro y hy
    have hyO : y ∈ closure O := closure_mono hUO hy
    have hne : dist y w / d ≠ 0 := (div_pos (lt_of_lt_of_le hd (hbnd y hyO)) hd).ne'
    apply ContinuousAt.continuousWithinAt
    exact ContinuousAt.log ((continuous_id.dist continuous_const |>.div_const d).continuousAt) hne
  have hvh : HarmonicOnNhd (fun y => u y - (2 * B / (barrierConst d T * s ^ 2)) *
      Real.log (dist y w / d)) U := by
    have hkh : HarmonicOnNhd ((2 * B / (barrierConst d T * s ^ 2)) •
        fun y : ℂ => Real.log (dist y w / d)) U := hbh.const_smul
    exact hu.sub hkh
  have hvc : ContinuousOn (fun y => u y - (2 * B / (barrierConst d T * s ^ 2)) *
      Real.log (dist y w / d)) (closure U) :=
    huc.sub (continuousOn_const.mul hbc)
  have hfrontier : ∀ ξ ∈ frontier U, u ξ - (2 * B / (barrierConst d T * s ^ 2)) *
      Real.log (dist ξ w / d) ≤ g z + L * s ^ a := by
    intro ξ hξ
    have hξO : ξ ∈ frontier O := hfr hξ
    have hξcl : ξ ∈ closure O := frontier_subset_closure hξO
    obtain ⟨hlow, -⟩ := barrier_bounds (T := T) hd hwz (hw ξ hξcl)
      (hT ξ hξcl z (frontier_subset_closure hz))
    rw [hub ξ hξ]
    have hlogpos : 0 ≤ Real.log (dist ξ w / d) :=
      le_trans (mul_nonneg hc.le (sq_nonneg _)) hlow
    have hLs : 0 ≤ L * s ^ a := mul_nonneg hL (Real.rpow_nonneg hs0.le _)
    rcases lt_or_ge (dist ξ z) s with hlt | hle
    · have h1 : |g ξ - g z| ≤ L * s ^ a :=
        (hgL ξ hξO z hz).trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow dist_nonneg hlt.le ha.le) hL)
      have hk : 0 ≤ (2 * B / (barrierConst d T * s ^ 2)) * Real.log (dist ξ w / d) :=
        mul_nonneg hk0 hlogpos
      have h2 := (abs_le.mp h1).2
      linarith
    · have hs2 : s ^ 2 ≤ dist ξ z ^ 2 := pow_le_pow_left₀ hs0.le hle 2
      have hcs2 : barrierConst d T * s ^ 2 ≤ barrierConst d T * dist ξ z ^ 2 :=
        mul_le_mul_of_nonneg_left hs2 hc.le
      have hkb : (2 * B / (barrierConst d T * s ^ 2)) * (barrierConst d T * s ^ 2) ≤
          (2 * B / (barrierConst d T * s ^ 2)) * Real.log (dist ξ w / d) :=
        mul_le_mul_of_nonneg_left (hcs2.trans hlow) hk0
      have hk_term : (2 * B / (barrierConst d T * s ^ 2)) * (barrierConst d T * s ^ 2) = 2 * B := by
        field_simp
      have hgξ : g ξ ≤ B := (abs_le.mp (hgB ξ hξO)).2
      have hgz : -B ≤ g z := (abs_le.mp (hgB z hz)).1
      linarith
  intro y hy
  have h : u y - (2 * B / (barrierConst d T * s ^ 2)) * Real.log (dist y w / d) ≤
      g z + L * s ^ a := le_of_frontier_le hU hbU hvh hvc hfrontier y hy
  linarith

/-- Boundary modulus. Let `z ∈ ∂O` and let `O` carry the exterior sphere of radius `d` at each of its
boundary points. If `u` is harmonic on `U ⊆ O`, continuous on `closure U`, equal to the `a`-Hölder datum
`g` on `∂U`, then `|u x - g z| ≤ (L + 2B/(c d)) |x - z|^κ` for `x ∈ closure U`, `|x - z| ≤ 1`,
where `κ = a/(a+2)`, `c = barrierConst d T` (steps4-final Section 1, lines 137-151). -/
theorem boundary_modulus {O U : Set ℂ} (hO : IsOpen O) (hUO : U ⊆ O) (hU : IsOpen U)
    (hbU : Bornology.IsBounded U) (hfr : frontier U ⊆ frontier O)
    {d T : ℝ} (hd : 0 < d) (hT : ∀ x ∈ closure O, ∀ y ∈ closure O, dist x y ≤ T)
    (hgeom : ∀ z ∈ frontier O, ∃ w : ℂ, dist w z = d ∧
      ∀ x ∈ closure O, d ^ 2 + (1 / 2 : ℝ) * dist x z ^ 2 ≤ dist x w ^ 2)
    {a L B : ℝ} (ha : 0 < a) (hL : 0 ≤ L) (hB : 0 ≤ B) {g : ℂ → ℝ}
    (hgL : ∀ x ∈ frontier O, ∀ y ∈ frontier O, |g x - g y| ≤ L * dist x y ^ a)
    (hgB : ∀ x ∈ frontier O, |g x| ≤ B)
    {u : ℂ → ℝ} (hu : HarmonicOnNhd u U) (huc : ContinuousOn u (closure U))
    (hub : ∀ ξ ∈ frontier U, u ξ = g ξ) :
    ∀ z ∈ frontier O, ∀ x ∈ closure U, dist x z ≤ 1 →
      |u x - g z| ≤ (L + 2 * B / (barrierConst d T * d)) * dist x z ^ (a / (a + 2)) := by
  intro z hz x hx hxz
  obtain ⟨w, hwz, hw⟩ := hgeom z hz
  have hzO : z ∉ O := fun h => hz.2 (by rw [hO.interior_eq]; exact h)
  rcases eq_or_lt_of_le (dist_nonneg : (0 : ℝ) ≤ dist x z) with h0 | hpos
  · -- `x = z` lies on `∂U`, where `u = g`
    have hxz' : x = z := dist_eq_zero.mp h0.symm
    have hxU : x ∉ U := fun h => hzO (hUO (hxz' ▸ h))
    have hxfr : x ∈ frontier U := ⟨hx, fun h => hxU (interior_subset h)⟩
    rw [hub x hxfr, hxz', sub_self, abs_zero]
    have hc := barrierConst_pos (T := T) hd
    positivity
  · have hκ : 0 < a / (a + 2) := by positivity
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s = dist x z ^ (1 / (a + 2)) := ⟨_, rfl⟩
    have hs0 : 0 < s := by rw [hs]; exact Real.rpow_pos_of_pos hpos _
    have hid := rpow_identities hpos ha
    have hid1 : s ^ a = dist x z ^ (a / (a + 2)) := by rw [hs]; exact hid.1
    have hid2 : dist x z / s ^ 2 = dist x z ^ (a / (a + 2)) := by rw [hs]; exact hid.2
    have hxO : x ∈ closure O := closure_mono hUO hx
    -- upper comparison
    have hup := upper_barrier_bound hUO hU hbU hfr hd hT ha hL hB hgL hgB hu huc hub hz hwz hw
      hs0 x hx
    -- lower comparison: apply the same bound to `-u` and `-g`
    have hlow := upper_barrier_bound hUO hU hbU hfr hd hT ha hL hB (g := fun y => -g y)
      (fun p hp q hq => by
        rw [show -g p - -g q = -(g p - g q) by ring, abs_neg]
        exact hgL p hp q hq)
      (fun p hp => by rw [abs_neg]; exact hgB p hp)
      (u := fun y => -u y) hu.neg huc.neg (fun ξ hξ => by simp only [hub ξ hξ]) hz hwz hw
      hs0 x hx
    have hlow' : -u x ≤ -g z + L * s ^ a +
        (2 * B / (barrierConst d T * s ^ 2)) * Real.log (dist x w / d) := hlow
    have hup' : u x ≤ g z + L * s ^ a +
        (2 * B / (barrierConst d T * s ^ 2)) * Real.log (dist x w / d) := hup
    -- the barrier upper bound `log(dist x w / d) ≤ dist x z / d`
    have hb := (barrier_bounds (T := T) hd hwz (hw x hxO)
      (hT x hxO z (frontier_subset_closure hz))).2
    have hk0 : 0 ≤ 2 * B / (barrierConst d T * s ^ 2) := by
      have := barrierConst_pos (T := T) hd
      positivity
    have hkb : (2 * B / (barrierConst d T * s ^ 2)) * Real.log (dist x w / d) ≤
        (2 * B / (barrierConst d T * s ^ 2)) * (dist x z / d) :=
      mul_le_mul_of_nonneg_left hb hk0
    have hK : (2 * B / (barrierConst d T * s ^ 2)) * (dist x z / d) =
        (2 * B / (barrierConst d T * d)) * dist x z ^ (a / (a + 2)) := by
      have := barrierConst_pos (T := T) hd
      rw [← hid2]
      field_simp
    have hLs : L * s ^ a = L * dist x z ^ (a / (a + 2)) := by rw [hid1]
    rw [add_mul]
    have hu1 : u x - g z ≤ L * dist x z ^ (a / (a + 2)) +
        2 * B / (barrierConst d T * d) * dist x z ^ (a / (a + 2)) := by
      linarith [hup', hkb, hK, hLs]
    have hu2 : -(u x - g z) ≤ L * dist x z ^ (a / (a + 2)) +
        2 * B / (barrierConst d T * d) * dist x z ^ (a / (a + 2)) := by
      linarith [hlow', hkb, hK, hLs]
    exact abs_le.mpr ⟨by linarith, hu1⟩

/-! ## 5. Translation argument: the Hölder estimate on the closure -/

/-- Translation `p ↦ p + e` is continuous. -/
lemma continuous_add_const_right (e : ℂ) : Continuous fun p : ℂ => p + e :=
  continuous_id.add continuous_const

/-- Harmonicity is invariant under translation: the Laplacian commutes with translations. -/
lemma harmonicAt_comp_add {u : ℂ → ℝ} {x e : ℂ} (h : HarmonicAt u (x + e)) :
    HarmonicAt (fun p => u (p + e)) x := by
  refine ⟨?_, ?_⟩
  · exact h.1.comp x (contDiffAt_id.add contDiffAt_const)
  · have hlap : ∀ p : ℂ, Laplacian.laplacian (fun q => u (q + e)) p =
        Laplacian.laplacian u (p + e) := by
      intro p
      rw [laplacian_eq_iteratedFDeriv_complexPlane, laplacian_eq_iteratedFDeriv_complexPlane]
      simp only [iteratedFDeriv_comp_add_right]
    have hT : Tendsto (fun p : ℂ => p + e) (𝓝 x) (𝓝 (x + e)) :=
      ((continuous_id.add continuous_const).tendsto x)
    have hev : ∀ᶠ p in 𝓝 x, Laplacian.laplacian u (p + e) = 0 := hT.eventually h.2
    filter_upwards [hev] with p hp
    rw [hlap p]
    exact hp

/-- Hölder estimate from the boundary modulus, by the translation argument. Let `u` be harmonic on the
bounded open set `U`, continuous on `closure U`, equal to `g` on `∂U`, and satisfy the boundary modulus
`|u x - g z| ≤ C |x - z|^κ` (for `z ∈ ∂O`, `x ∈ closure U`, `|x - z| ≤ 1`). Then `|u x - u y| ≤ C |x - y|^κ`
for `x, y ∈ closure U` with `|x - y| ≤ 1`. Proof: for `e = y - x`, the function `p ↦ u (p + e) - u p`
is harmonic on `U' = U ∩ (U - e)`; on `∂U'` it is bounded by `C |e|^κ` by the boundary modulus, so the
weak maximum principle gives the bound at `x`. -/
theorem holder_of_boundary_modulus {O U : Set ℂ} (hU : IsOpen U) (hbU : Bornology.IsBounded U)
    (hfr : frontier U ⊆ frontier O) {u g : ℂ → ℝ} {κ C : ℝ}
    (hu : HarmonicOnNhd u U) (huc : ContinuousOn u (closure U))
    (hub : ∀ ξ ∈ frontier U, u ξ = g ξ)
    (hbm : ∀ z ∈ frontier O, ∀ x ∈ closure U, dist x z ≤ 1 → |u x - g z| ≤ C * dist x z ^ κ) :
    ∀ x ∈ closure U, ∀ y ∈ closure U, dist x y ≤ 1 → |u x - u y| ≤ C * dist x y ^ κ := by
  intro x hx y hy hxy
  by_cases hxf : x ∈ frontier U
  · have hxO : x ∈ frontier O := hfr hxf
    have h1 := hbm x hxO y hy (by rwa [dist_comm])
    rw [hub x hxf, abs_sub_comm, dist_comm]
    exact h1
  by_cases hyf : y ∈ frontier U
  · have hyO : y ∈ frontier O := hfr hyf
    have h1 := hbm y hyO x hx hxy
    rw [hub y hyf]
    exact h1
  have hxU : x ∈ U := by
    by_contra h
    exact hxf ⟨hx, fun h' => h (interior_subset h')⟩
  have hyU : y ∈ U := by
    by_contra h
    exact hyf ⟨hy, fun h' => h (interior_subset h')⟩
  set e : ℂ := y - x with he
  set U' : Set ℂ := U ∩ (fun p => p + e) ⁻¹' U with hU'
  have hU'open : IsOpen U' := hU.inter (hU.preimage (continuous_add_const_right e))
  have hU'sub : U' ⊆ U := inter_subset_left
  have hU'bdd : Bornology.IsBounded U' := hbU.subset hU'sub
  have hτ : ∀ p ∈ closure U', p + e ∈ closure U := by
    intro p hp
    have himg : (fun q => q + e) p ∈ closure ((fun q => q + e) '' U') :=
      image_closure_subset_closure_image (continuous_add_const_right e) ⟨p, hp, rfl⟩
    refine closure_mono ?_ himg
    rintro _ ⟨q, hq, rfl⟩
    exact hq.2
  have hwh : HarmonicOnNhd (fun p => u (p + e) - u p) U' := by
    intro p hp
    have hpU : p ∈ U := hU'sub hp
    have hpeU : p + e ∈ U := hp.2
    have h1 := harmonicAt_comp_add (e := e) (hu (p + e) hpeU)
    have h2 := hu p hpU
    exact h1.sub h2
  have hwc : ContinuousOn (fun p => u (p + e) - u p) (closure U') := by
    have hc1 : ContinuousOn (fun p => u (p + e)) (closure U') :=
      huc.comp (continuous_add_const_right e).continuousOn hτ
    have hc2 : ContinuousOn (fun p => u p) (closure U') :=
      huc.mono (closure_mono hU'sub)
    exact hc1.sub hc2
  have hδ : ∀ p : ℂ, dist (p + e) p = dist x y := by
    intro p
    rw [dist_eq_norm, add_sub_cancel_left, he, ← dist_eq_norm, dist_comm]
  have hfrb : ∀ p ∈ frontier U', |u (p + e) - u p| ≤ C * dist x y ^ κ := by
    intro p hp
    have hpcl : p ∈ closure U := closure_mono hU'sub (frontier_subset_closure hp)
    have hpU' : p ∉ U' := by
      rw [← hU'open.interior_eq]
      exact hp.2
    have hnot : ¬ (p ∈ U ∧ p + e ∈ U) := fun h => hpU' ⟨h.1, h.2⟩
    have hdist1 : dist (p + e) p ≤ 1 := by rw [hδ p]; exact hxy
    have hdist2 : dist p (p + e) ≤ 1 := by rw [dist_comm]; exact hdist1
    by_cases hpU : p ∈ U
    · have hpeU : p + e ∉ U := fun h => hnot ⟨hpU, h⟩
      have hpef : p + e ∈ frontier U := ⟨hτ p (frontier_subset_closure hp), fun h => hpeU (interior_subset h)⟩
      have hpefO : p + e ∈ frontier O := hfr hpef
      have h1 := hbm (p + e) hpefO p hpcl hdist2
      rw [hub (p + e) hpef, abs_sub_comm]
      rw [dist_comm, hδ p] at h1
      exact h1
    · have hpf : p ∈ frontier U := ⟨hpcl, fun h => hpU (interior_subset h)⟩
      have hpO : p ∈ frontier O := hfr hpf
      have h1 := hbm p hpO (p + e) (hτ p (frontier_subset_closure hp)) hdist1
      rw [hub p hpf]
      rw [hδ p] at h1
      exact h1
  have hxe : x + e = y := by rw [he]; ring
  have hxU' : x ∈ U' := ⟨hxU, by show x + e ∈ U; rw [hxe]; exact hyU⟩
  have hbound : |u (x + e) - u x| ≤ C * dist x y ^ κ :=
    abs_le_of_frontier_abs_le hU'open hU'bdd hwh hwc hfrb x (subset_closure hxU')
  rw [hxe] at hbound
  rw [abs_sub_comm]
  exact hbound

/-! ## 6. Components of a smooth bounded open set, and the global extension -/

/-- The boundary of a connected component of an open set lies in the boundary of the set. -/
lemma frontier_connectedComponentIn_subset {O : Set ℂ} (hO : IsOpen O) (x : ℂ) :
    frontier (connectedComponentIn O x) ⊆ frontier O := by
  intro p hp
  have hCo : IsOpen (connectedComponentIn O x) := hO.connectedComponentIn
  have hpcl : p ∈ closure (connectedComponentIn O x) := hp.1
  have hpC : p ∉ connectedComponentIn O x := fun h => hp.2 (by rw [hCo.interior_eq]; exact h)
  refine ⟨closure_mono (connectedComponentIn_subset O x) hpcl, fun hpint => ?_⟩
  rw [hO.interior_eq] at hpint
  have hD : IsOpen (connectedComponentIn O p) := hO.connectedComponentIn
  obtain ⟨c, hcD, hcC⟩ := mem_closure_iff.mp hpcl (connectedComponentIn O p) hD
    (mem_connectedComponentIn hpint)
  have h1 : connectedComponentIn O x = connectedComponentIn O c := connectedComponentIn_eq hcC
  have h2 : connectedComponentIn O p = connectedComponentIn O c := connectedComponentIn_eq hcD
  apply hpC
  rw [h1, ← h2]
  exact mem_connectedComponentIn hpint

/-- A segment from a point of the open set `C` to a point outside `C` meets the boundary of `C`. -/
lemma exists_frontier_mem_segment {C : Set ℂ} (hC : IsOpen C) {x y : ℂ} (hx : x ∈ C) (hy : y ∉ C) :
    ∃ p ∈ segment ℝ x y, p ∈ frontier C := by
  by_contra hcon
  have hsub : segment ℝ x y ⊆ C ∪ (closure C)ᶜ := by
    intro p hp
    by_cases hpC : p ∈ C
    · exact Or.inl hpC
    · by_cases hpcl : p ∈ closure C
      · exact (hcon ⟨p, hp, hpcl, fun h => hpC (interior_subset h)⟩).elim
      · exact Or.inr hpcl
  have hdisj : Disjoint C (closure C)ᶜ := disjoint_compl_right_iff_subset.mpr subset_closure
  have hopen : IsOpen (closure C)ᶜ := isClosed_closure.isOpen_compl
  have hpre : IsPreconnected (segment ℝ x y) := (convex_segment x y).isPreconnected
  have hsub2 := hpre.subset_left_of_subset_union hC hopen hdisj hsub
    ⟨x, left_mem_segment ℝ x y, hx⟩
  exact hy (hsub2 (right_mem_segment ℝ x y))

/-- Points of a segment are within the length of the segment from both endpoints. -/
lemma dist_le_of_mem_segment {x y p : ℂ} (hp : p ∈ segment ℝ x y) :
    dist x p ≤ dist x y ∧ dist y p ≤ dist x y := by
  have h := (mem_segment_iff_wbtw.mp hp).dist_add_dist
  constructor
  · linarith [dist_nonneg (x := p) (y := y)]
  · linarith [dist_comm y p, dist_nonneg (x := x) (y := p)]

/-- The exterior sphere condition at a boundary point of a subset `C ⊆ O` whose frontier lies in `∂O`,
from the uniform exterior sphere inequality of `∂O`. -/
lemma exteriorSphereAt_of_subset {O C : Set ℂ} (hCO : C ⊆ O) (hfrC : frontier C ⊆ frontier O) {d : ℝ}
    (hd : 0 < d)
    (hgeom : ∀ z ∈ frontier O, ∃ w : ℂ, dist w z = d ∧
      ∀ x ∈ closure O, d ^ 2 + (1 / 2 : ℝ) * dist x z ^ 2 ≤ dist x w ^ 2)
    {z : ℂ} (hz : z ∈ frontier C) : HarmonicBalls.ExteriorSphereAt C z := by
  obtain ⟨w, hwz, hw⟩ := hgeom z (hfrC hz)
  refine ⟨w, d, hd, by rw [dist_comm]; exact hwz, ?_⟩
  intro y hy hycl
  have hyO : y ∈ closure O := closure_mono hCO hycl
  have h1 := hw y hyO
  rw [mem_ball] at hy
  have h2 : dist y w ^ 2 < d ^ 2 := by
    have := dist_nonneg (x := y) (y := w)
    nlinarith
  linarith [sq_nonneg (dist y z)]

/-- Dirichlet data: `u` is continuous on `closure S`, harmonic on `S`, and equal to `g` on `∂S`. -/
def DirichletGood (S : Set ℂ) (g u : ℂ → ℝ) : Prop :=
  ContinuousOn u (closure S) ∧ InnerProductSpace.HarmonicOnNhd u S ∧ ∀ z ∈ frontier S, u z = g z

/-- A bound `|f x - f y| ≤ C · dist x y ^ κ` gives `HolderOnWith` with the same constants. -/
lemma holderOnWith_of_bound {S : Set ℂ} {f : ℂ → ℝ} {C κ : NNReal}
    (h : ∀ x ∈ S, ∀ y ∈ S, |f x - f y| ≤ (C : ℝ) * dist x y ^ (κ : ℝ)) :
    HolderOnWith C κ f S := by
  intro x hx y hy
  have h1 := h x hx y hy
  have hd0 : (0 : ℝ) ≤ dist x y := dist_nonneg
  rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg hd0 (NNReal.coe_nonneg κ),
    ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg C)]
  exact ENNReal.ofReal_le_ofReal (by rw [Real.dist_eq]; exact h1)

/-- The Stage 1 global statement (steps4-final Section 1, lines 125-199). For a smooth bounded open set
`O` (`IsSmoothBoundedOpen`) and an `a`-Hölder datum `g` on `∂O`, with constant `L` and bound `B`, the
Dirichlet problem on `O` has a solution `H`, harmonic on `O`, equal to `g` on `∂O`, and Hölder continuous
on `closure O` with exponent `a/(a+2)`. The literature input `GilbargTrudingerThm2_14` is a hypothesis. -/
theorem exists_dirichlet_holderOnWith {O : Set ℂ} (hO : IsSmoothBoundedOpen O)
    (hGT : GilbargTrudingerThm2_14) {g : ℂ → ℝ} {a L B : ℝ} (ha : 0 < a) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hgc : ContinuousOn g (frontier O))
    (hgL : ∀ x ∈ frontier O, ∀ y ∈ frontier O, |g x - g y| ≤ L * dist x y ^ a)
    (hgB : ∀ x ∈ frontier O, |g x| ≤ B) :
    ∃ H : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd H O ∧ (∀ z ∈ frontier O, H z = g z) ∧
      ∃ C r : NNReal, 0 < r ∧ HolderOnWith C r H (closure O) := by
  classical
  have hO' := hO
  obtain ⟨hbddO, ρ, hρC, hOρ, -⟩ := hO
  have hOopen : IsOpen O := by
    rw [hOρ]
    exact isOpen_lt hρC.continuous continuous_const
  obtain ⟨d, hd, hgeom⟩ :=
    HarmonicBalls.SmoothDomainExteriorSphere.exists_half_radius_geometry_of_isSmoothBoundedOpen hO'
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hbddO.closure
  have hT : ∀ x ∈ closure O, ∀ y ∈ closure O, dist x y ≤ 2 * R := by
    intro x hx y hy
    rw [dist_eq_norm]
    linarith [norm_sub_le x y, hR x hx, hR y hy]
  -- one Dirichlet solution on each component
  have hex : ∀ x ∈ O, ∃ u : ℂ → ℝ, DirichletGood (connectedComponentIn O x) g u := by
    intro x hx
    have hCO : connectedComponentIn O x ⊆ O := connectedComponentIn_subset O x
    have hCopen : IsOpen (connectedComponentIn O x) := hOopen.connectedComponentIn
    have hCconn : IsConnected (connectedComponentIn O x) :=
      isConnected_connectedComponentIn_iff.mpr hx
    have hCbdd : Bornology.IsBounded (connectedComponentIn O x) := hbddO.subset hCO
    have hfrC := frontier_connectedComponentIn_subset hOopen x
    have hext : ∀ z ∈ frontier (connectedComponentIn O x),
        HarmonicBalls.ExteriorSphereAt (connectedComponentIn O x) z :=
      fun z hz => exteriorSphereAt_of_subset hCO hfrC hd hgeom hz
    have hφ : ContinuousOn g (frontier (connectedComponentIn O x)) := hgc.mono hfrC
    obtain ⟨u, huc, hu, hub⟩ := hGT _ hCopen hCconn hCbdd hext g hφ
    exact ⟨u, huc, hu, hub⟩
  let solC : Set ℂ → ℂ → ℝ := fun S => Classical.epsilon (DirichletGood S g)
  have hsolC : ∀ x ∈ O, DirichletGood (connectedComponentIn O x) g
      (solC (connectedComponentIn O x)) :=
    fun x hx => Classical.epsilon_spec (hex x hx)
  let H : ℂ → ℝ := fun x => if x ∈ O then solC (connectedComponentIn O x) x else g x
  have hH_O : ∀ x ∈ O, H x = solC (connectedComponentIn O x) x := fun x hx => by
    simp [H, hx]
  have hH_fr : ∀ z ∈ frontier O, H z = g z := by
    intro z hz
    have hzO : z ∉ O := fun h => hz.2 (by rw [hOopen.interior_eq]; exact h)
    simp [H, hzO]
  have hcomp : ∀ x ∈ O, ∀ y ∈ connectedComponentIn O x,
      H y = solC (connectedComponentIn O x) y := by
    intro x hx y hy
    rw [hH_O y (connectedComponentIn_subset O x hy), connectedComponentIn_eq hy]
  have hclos : ∀ x ∈ O, ∀ y ∈ closure (connectedComponentIn O x),
      H y = solC (connectedComponentIn O x) y := by
    intro x hx y hy
    by_cases hyC : y ∈ connectedComponentIn O x
    · exact hcomp x hx y hyC
    · have hyf : y ∈ frontier (connectedComponentIn O x) :=
        ⟨hy, fun h => hyC (interior_subset h)⟩
      rw [hH_fr y (frontier_connectedComponentIn_subset hOopen x hyf)]
      exact ((hsolC x hx).2.2 y hyf).symm
  have hH_harm : InnerProductSpace.HarmonicOnNhd H O := by
    intro x hx
    have hCopen : IsOpen (connectedComponentIn O x) := hOopen.connectedComponentIn
    have hmem : connectedComponentIn O x ∈ 𝓝 x := hCopen.mem_nhds (mem_connectedComponentIn hx)
    have heq : H =ᶠ[𝓝 x] solC (connectedComponentIn O x) := by
      filter_upwards [hmem] with y hy
      exact hcomp x hx y hy
    exact (InnerProductSpace.harmonicAt_congr_nhds heq).mpr
      ((hsolC x hx).2.1 x (mem_connectedComponentIn hx))
  -- the boundary modulus on each component
  have hbmx : ∀ x ∈ O, ∀ z ∈ frontier O, ∀ y ∈ closure (connectedComponentIn O x),
      dist y z ≤ 1 → |solC (connectedComponentIn O x) y - g z| ≤
        (L + 2 * B / (barrierConst d (2 * R) * d)) * dist y z ^ (a / (a + 2)) := by
    intro x hx z hz y hy hyz
    have hCO : connectedComponentIn O x ⊆ O := connectedComponentIn_subset O x
    have hCopen : IsOpen (connectedComponentIn O x) := hOopen.connectedComponentIn
    have hfrC := frontier_connectedComponentIn_subset hOopen x
    exact boundary_modulus hOopen hCO hCopen (hbddO.subset hCO) hfrC hd hT hgeom ha hL hB hgL hgB
      (hsolC x hx).2.1 (hsolC x hx).1 (hsolC x hx).2.2 z hz y hy hyz
  -- the Hölder estimate on each component closure
  have hholdx : ∀ x ∈ O, ∀ y ∈ closure (connectedComponentIn O x),
      ∀ y' ∈ closure (connectedComponentIn O x), dist y y' ≤ 1 →
      |solC (connectedComponentIn O x) y - solC (connectedComponentIn O x) y'| ≤
        (L + 2 * B / (barrierConst d (2 * R) * d)) * dist y y' ^ (a / (a + 2)) := by
    intro x hx y hy y' hy' hyy'
    have hCopen : IsOpen (connectedComponentIn O x) := hOopen.connectedComponentIn
    have hfrC := frontier_connectedComponentIn_subset hOopen x
    exact holder_of_boundary_modulus hCopen (hbddO.subset (connectedComponentIn_subset O x)) hfrC
      (hsolC x hx).2.1 (hsolC x hx).1 (hsolC x hx).2.2 (fun z hz p hp hpz => hbmx x hx z hz p hp hpz)
      y hy y' hy' hyy'
  -- the maximum principle gives `|solC| ≤ B` on each component closure
  have hsolB : ∀ x ∈ O, ∀ y ∈ closure (connectedComponentIn O x),
      |solC (connectedComponentIn O x) y| ≤ B := by
    intro x hx
    have hCO : connectedComponentIn O x ⊆ O := connectedComponentIn_subset O x
    have hCopen : IsOpen (connectedComponentIn O x) := hOopen.connectedComponentIn
    have hfrC := frontier_connectedComponentIn_subset hOopen x
    exact fun y hy => abs_le_of_frontier_abs_le hCopen (hbddO.subset hCO) (hsolC x hx).2.1
      (hsolC x hx).1 (M := B)
      (fun z hz => by rw [(hsolC x hx).2.2 z hz]; exact hgB z (hfrC hz)) y hy
  have hHB : ∀ z ∈ closure O, |H z| ≤ B := by
    intro z hz
    by_cases hzO : z ∈ O
    · rw [hH_O z hzO]
      exact hsolB z hzO z (subset_closure (mem_connectedComponentIn hzO))
    · have hzf : z ∈ frontier O := ⟨hz, fun h => hzO (interior_subset h)⟩
      rw [hH_fr z hzf]
      exact hgB z hzf
  -- constants
  set κ : ℝ := a / (a + 2) with hκdef
  have hκ : 0 < κ := by rw [hκdef]; positivity
  have hκa : κ ≤ a := by
    rw [hκdef, div_le_iff₀ (by positivity)]
    nlinarith
  set C0 : ℝ := L + 2 * B / (barrierConst d (2 * R) * d) with hC0def
  have hC0 : 0 ≤ C0 := by
    have := barrierConst_pos (T := 2 * R) hd
    rw [hC0def]
    positivity
  set Cf : ℝ := L + 2 * C0 + 2 * B with hCfdef
  have hCf : 0 ≤ Cf := by
    rw [hCfdef]
    positivity
  have hpowle : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t ^ a ≤ t ^ κ := by
    intro t ht0 ht1
    rcases eq_or_lt_of_le ht0 with h0 | hpos
    · rw [← h0, Real.zero_rpow (ne_of_gt ha), Real.zero_rpow (ne_of_gt hκ)]
    · exact Real.rpow_le_rpow_of_exponent_ge hpos ht1 hκa
  -- the mixed case: `x ∈ O`, `y ∈ closure O`, `dist x y ≤ 1`
  have hmixed : ∀ x ∈ O, ∀ y ∈ closure O, dist x y ≤ 1 →
      |H x - H y| ≤ Cf * dist x y ^ κ := by
    intro x hx y hy hxy
    have hpow0 : 0 ≤ dist x y ^ κ := Real.rpow_nonneg dist_nonneg _
    by_cases hyC : y ∈ closure (connectedComponentIn O x)
    · rw [hclos x hx y hyC, hH_O x hx]
      have h1 := hholdx x hx x (subset_closure (mem_connectedComponentIn hx)) y hyC hxy
      have h2 : C0 * dist x y ^ κ ≤ Cf * dist x y ^ κ :=
        mul_le_mul_of_nonneg_right (by rw [hCfdef]; linarith [hL, hB, hC0]) hpow0
      exact h1.trans h2
    · have hyC' : y ∉ connectedComponentIn O x := fun h => hyC (subset_closure h)
      by_cases hyO : y ∈ O
      · obtain ⟨p, hpseg, hpfr⟩ := exists_frontier_mem_segment hOopen.connectedComponentIn
          (mem_connectedComponentIn hx) hyC'
        have hpO : p ∈ frontier O := frontier_connectedComponentIn_subset hOopen x hpfr
        obtain ⟨hxp, hyp⟩ := dist_le_of_mem_segment hpseg
        have hyp1 : dist y p ≤ 1 := hyp.trans hxy
        have hA := hbmx x hx p hpO x (subset_closure (mem_connectedComponentIn hx))
          (hxp.trans hxy)
        have hA' := hbmx y hyO p hpO y (subset_closure (mem_connectedComponentIn hyO)) hyp1
        rw [hH_O x hx, hH_O y hyO]
        have htri := abs_sub_le (solC (connectedComponentIn O x) x) (g p)
          (solC (connectedComponentIn O y) y)
        have hBy : |g p - solC (connectedComponentIn O y) y| =
            |solC (connectedComponentIn O y) y - g p| := abs_sub_comm _ _
        have hxpk : dist x p ^ κ ≤ dist x y ^ κ := Real.rpow_le_rpow dist_nonneg hxp hκ.le
        have hypk : dist y p ^ κ ≤ dist x y ^ κ := Real.rpow_le_rpow dist_nonneg hyp hκ.le
        have hC0k : C0 * dist x p ^ κ ≤ C0 * dist x y ^ κ := mul_le_mul_of_nonneg_left hxpk hC0
        have hC0k' : C0 * dist y p ^ κ ≤ C0 * dist x y ^ κ :=
          mul_le_mul_of_nonneg_left hypk hC0
        have hCf2 : 2 * C0 * dist x y ^ κ ≤ Cf * dist x y ^ κ :=
          mul_le_mul_of_nonneg_right (by rw [hCfdef]; linarith [hL, hB]) hpow0
        linarith [htri, hA, hA', hBy, hC0k, hC0k', hCf2]
      · have hyf : y ∈ frontier O := ⟨hy, fun h => hyO (interior_subset h)⟩
        rw [hH_fr y hyf, hH_O x hx]
        have hA := hbmx x hx y hyf x (subset_closure (mem_connectedComponentIn hx)) hxy
        have hC0k : C0 * dist x y ^ κ ≤ Cf * dist x y ^ κ :=
          mul_le_mul_of_nonneg_right (by rw [hCfdef]; linarith [hL, hB]) hpow0
        exact hA.trans hC0k
  -- the full estimate on `closure O`
  have hmain : ∀ x ∈ closure O, ∀ y ∈ closure O, |H x - H y| ≤ Cf * dist x y ^ κ := by
    intro x hx y hy
    have hpow0 : 0 ≤ dist x y ^ κ := Real.rpow_nonneg dist_nonneg _
    by_cases hdist : dist x y ≤ 1
    · by_cases hxO : x ∈ O
      · exact hmixed x hxO y hy hdist
      · by_cases hyO : y ∈ O
        · have h1 := hmixed y hyO x hx (by rw [dist_comm]; exact hdist)
          rw [abs_sub_comm, dist_comm]
          exact h1
        · have hxf : x ∈ frontier O := ⟨hx, fun h => hxO (interior_subset h)⟩
          have hyf : y ∈ frontier O := ⟨hy, fun h => hyO (interior_subset h)⟩
          rw [hH_fr x hxf, hH_fr y hyf]
          have hgxy := hgL x hxf y hyf
          have hL' : L * dist x y ^ a ≤ L * dist x y ^ κ :=
            mul_le_mul_of_nonneg_left (hpowle _ dist_nonneg hdist) hL
          have hL'' : L * dist x y ^ κ ≤ Cf * dist x y ^ κ :=
            mul_le_mul_of_nonneg_right (by rw [hCfdef]; linarith [hC0, hB]) hpow0
          linarith [hgxy, hL', hL'']
    · have hfar : 1 ≤ dist x y ^ κ := Real.one_le_rpow (le_of_lt (not_le.mp hdist)) hκ.le
      have hC2 : 2 * B ≤ Cf := by
        rw [hCfdef]
        linarith [hL, hC0]
      calc |H x - H y| ≤ |H x| + |H y| := abs_sub _ _
        _ ≤ 2 * B := by linarith [hHB x hx, hHB y hy]
        _ ≤ Cf * dist x y ^ κ := by nlinarith [hfar, hCf, hB]
  refine ⟨H, hH_harm, hH_fr, Cf.toNNReal, κ.toNNReal, Real.toNNReal_pos.mpr hκ, ?_⟩
  apply holderOnWith_of_bound
  intro x hx y hy
  rw [Real.coe_toNNReal _ hCf, Real.coe_toNNReal _ hκ.le]
  exact hmain x hx y hy

end GreenGeneral

end HarmonicBalls
