import HarmonicBalls.Draft.Section2
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Closure

/-!
# Uniform exterior sphere condition for smooth bounded open sets

For a smooth bounded open set `O ⊆ ℂ` (`IsSmoothBoundedOpen O`, `Draft/Section2`: `O` is bounded and `O = {ρ < 0}` for
some `ρ ∈ C^∞(ℂ, ℝ)` whose differential does not vanish on `{ρ = 0}`), every boundary point `z ∈ ∂O` is touched from
outside by a sphere of one common radius `R > 0` whose disc lies outside `closure O`: the exterior sphere condition of
potential theory (Armitage-Gardiner), with a radius independent of the boundary point. No connectedness of `O` and no
boundary-measure assumption is used. The half-radius form (centre `w` at distance `R/2` from `z`, with
`d² + |x - z|²/2 ≤ |x - w|²` on `closure O`) is deduced from the same sphere by the parallelogram identity.

Proof. `∂O` is compact and `∂O = {ρ = 0}`. Compactness gives a bound `M₀` on the second derivative of `ρ` on the
closed unit neighbourhood of `∂O`, and a bound `g > 0` on `‖∇ρ‖` on `∂O`. For `z ∈ ∂O` and `x` with `|x - z| ≤ 1`,
Taylor's inequality `|ρ x - ρ z - dρ(z)(x - z)| ≤ M₀ |x - z|² / 2` and `ρ ≤ 0` on `closure O` give
`dρ(z)(x - z) ≤ M₀ |x - z|² / 2`. The centre `a = z + (R / |∇ρ(z)|) ∇ρ(z)` then satisfies `|x - a| ≥ R` once
`R ≤ min (1/2) (g / (2 (M₀ + 1)))`; for `|x - z| > 1` the bound `|x - a| ≥ |x - z| - R ≥ 1/2 ≥ R` is immediate.
-/

noncomputable section

namespace HarmonicBalls

open Metric Set

namespace SmoothDomainExteriorSphere

/-- The complex number `G(z) = dρ(z)(1) + dρ(z)(i) · i` representing the real differential of `ρ` at `z`, so that
`dρ(z) v = Re (conj G · v) = G.re * v.re + G.im * v.im` (`fderiv_apply_eq_gradC`). -/
def gradC (ρ : ℂ → ℝ) (z : ℂ) : ℂ :=
  ((fderiv ℝ ρ z 1 : ℝ) : ℂ) + ((fderiv ℝ ρ z Complex.I : ℝ) : ℂ) * Complex.I

lemma gradC_re (ρ : ℂ → ℝ) (z : ℂ) : (gradC ρ z).re = fderiv ℝ ρ z 1 := by
  simp [gradC]

lemma gradC_im (ρ : ℂ → ℝ) (z : ℂ) : (gradC ρ z).im = fderiv ℝ ρ z Complex.I := by
  simp [gradC]

/-- The real differential of `ρ` at `z` in coordinates: `dρ(z) v = G.re * v.re + G.im * v.im`. -/
lemma fderiv_apply_eq_gradC (ρ : ℂ → ℝ) (z v : ℂ) :
    fderiv ℝ ρ z v = (gradC ρ z).re * v.re + (gradC ρ z).im * v.im := by
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    apply Complex.ext <;> simp
  rw [gradC_re, gradC_im]
  conv_lhs => rw [hv]
  simp only [map_add, map_smul, smul_eq_mul]
  ring

lemma gradC_ne_zero {ρ : ℂ → ℝ} {z : ℂ} (h : fderiv ℝ ρ z ≠ 0) : gradC ρ z ≠ 0 := by
  intro h0
  apply h
  ext v
  rw [fderiv_apply_eq_gradC, h0]
  simp

lemma continuous_gradC {ρ : ℂ → ℝ} (hρ : ContDiff ℝ 2 ρ) : Continuous (gradC ρ) := by
  have hd : Continuous (fderiv ℝ ρ) := hρ.continuous_fderiv (by norm_num)
  have h1 : Continuous fun z => fderiv ℝ ρ z 1 := hd.clm_apply continuous_const
  have h2 : Continuous fun z => fderiv ℝ ρ z Complex.I := hd.clm_apply continuous_const
  exact (Complex.continuous_ofReal.comp h1).add
    ((Complex.continuous_ofReal.comp h2).mul continuous_const)

/-- A positive lower bound for `‖gradC ρ‖` on a compact set on which `dρ` does not vanish
(the empty set is allowed). -/
lemma exists_gradC_lower_bound {ρ : ℂ → ℝ} (hρ : ContDiff ℝ 2 ρ) {Γ : Set ℂ} (hΓ : IsCompact Γ)
    (hnz : ∀ z ∈ Γ, fderiv ℝ ρ z ≠ 0) :
    ∃ g : ℝ, 0 < g ∧ ∀ z ∈ Γ, g ≤ ‖gradC ρ z‖ := by
  rcases Set.eq_empty_or_nonempty Γ with hE | hne
  · exact ⟨1, one_pos, fun z hz => by simp [hE] at hz⟩
  · obtain ⟨z₀, hz₀, hmin⟩ :=
      hΓ.exists_isMinOn hne (f := fun z => ‖gradC ρ z‖) (continuous_gradC hρ).norm.continuousOn
    exact ⟨‖gradC ρ z₀‖, norm_pos_iff.mpr (gradC_ne_zero (hnz z₀ hz₀)),
      fun z hz => isMinOn_iff.mp hmin z hz⟩

/-- A uniform bound on the second derivative of `ρ` on the closed unit neighbourhood of a compact set. -/
lemma exists_hessian_bound {ρ : ℂ → ℝ} (hρ : ContDiff ℝ 2 ρ) {Γ : Set ℂ} (hΓ : IsCompact Γ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ Γ, ∀ y ∈ closedBall z 1, ‖fderiv ℝ (fderiv ℝ ρ) y‖ ≤ M := by
  have hd2 : Continuous fun y => ‖fderiv ℝ (fderiv ℝ ρ) y‖ :=
    ((hρ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)).norm
  have hK : IsCompact (cthickening 1 Γ) := hΓ.cthickening
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hd2.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun z hz y hy => ?_⟩
  have hyK : y ∈ cthickening 1 Γ := mem_cthickening_of_dist_le y z 1 Γ hz (mem_closedBall.mp hy)
  have hy' : ‖fderiv ℝ (fderiv ℝ ρ) y‖ ≤ C :=
    (le_of_eq (Real.norm_of_nonneg (norm_nonneg (fderiv ℝ (fderiv ℝ ρ) y))).symm).trans (hC y hyK)
  exact hy'.trans (le_max_left _ _)

/-- Mean value inequality for the differential: `‖dρ(y) - dρ(z)‖ ≤ M ‖y - z‖` on `closedBall z 1`. -/
lemma norm_fderiv_sub_le {ρ : ℂ → ℝ} (hρ : ContDiff ℝ 2 ρ) {z y : ℂ} {M : ℝ}
    (hM : ∀ w ∈ closedBall z 1, ‖fderiv ℝ (fderiv ℝ ρ) w‖ ≤ M) (hy : y ∈ closedBall z 1) :
    ‖fderiv ℝ ρ y - fderiv ℝ ρ z‖ ≤ M * ‖y - z‖ := by
  have hd : ∀ w ∈ closedBall z 1, DifferentiableAt ℝ (fderiv ℝ ρ) w := fun w _ =>
    ((hρ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) w
  have hz : z ∈ closedBall z 1 := mem_closedBall_self zero_le_one
  exact (convex_closedBall z 1).norm_image_sub_le_of_norm_fderiv_le hd hM hz hy

/-- Taylor's inequality with quadratic remainder: for `‖v‖ ≤ 1`,
`|ρ (z + v) - ρ z - dρ(z) v| ≤ M ‖v‖² / 2`, where `M` bounds the second derivative on `closedBall z 1`. -/
lemma abs_sub_sub_fderiv_le {ρ : ℂ → ℝ} (hρ : ContDiff ℝ 2 ρ) {z v : ℂ} {M : ℝ}
    (hM : ∀ w ∈ closedBall z 1, ‖fderiv ℝ (fderiv ℝ ρ) w‖ ≤ M) (hv : ‖v‖ ≤ 1) :
    |ρ (z + v) - ρ z - fderiv ℝ ρ z v| ≤ M * ‖v‖ ^ 2 / 2 := by
  have hdiff : Differentiable ℝ ρ := hρ.differentiable (by norm_num)
  -- the remainder along the segment `s ↦ z + s v`
  have hF : ∀ t : ℝ, HasDerivAt (fun s : ℝ => ρ (z + s • v) - ρ z - s * fderiv ℝ ρ z v)
      (fderiv ℝ ρ (z + t • v) v - fderiv ℝ ρ z v) t := by
    intro t
    have hline : HasDerivAt (fun s : ℝ => z + s • v) v t := by
      simpa using ((hasDerivAt_id' t).smul_const v).const_add z
    have h1 : HasDerivAt (fun s : ℝ => ρ (z + s • v)) (fderiv ℝ ρ (z + t • v) v) t :=
      (hdiff (z + t • v)).hasFDerivAt.comp_hasDerivAt t hline
    exact (h1.sub_const (ρ z)).sub (hasDerivAt_mul_const (fderiv ℝ ρ z v))
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1,
      ‖fderiv ℝ ρ (z + t • v) v - fderiv ℝ ρ z v‖ ≤ M * ‖v‖ ^ 2 * t := by
    intro t ht
    have hnorm : ‖t • v‖ = t * ‖v‖ := by rw [norm_smul, Real.norm_of_nonneg ht.1]
    have hmem : z + t • v ∈ closedBall z 1 := by
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, hnorm]
      nlinarith [norm_nonneg v, ht.1, ht.2]
    have hdn := norm_fderiv_sub_le hρ hM hmem
    rw [add_sub_cancel_left, hnorm] at hdn
    calc ‖fderiv ℝ ρ (z + t • v) v - fderiv ℝ ρ z v‖
        = ‖(fderiv ℝ ρ (z + t • v) - fderiv ℝ ρ z) v‖ := by rw [sub_apply]
      _ ≤ ‖fderiv ℝ ρ (z + t • v) - fderiv ℝ ρ z‖ * ‖v‖ :=
          (fderiv ℝ ρ (z + t • v) - fderiv ℝ ρ z).le_opNorm v
      _ ≤ (M * (t * ‖v‖)) * ‖v‖ := mul_le_mul_of_nonneg_right hdn (norm_nonneg v)
      _ = M * ‖v‖ ^ 2 * t := by ring
  have hB : ∀ t : ℝ, HasDerivAt (fun s : ℝ => M * ‖v‖ ^ 2 * s ^ 2 / 2) (M * ‖v‖ ^ 2 * t) t := by
    intro t
    have h := ((hasDerivAt_pow 2 t).const_mul (M * ‖v‖ ^ 2)).div_const 2
    convert h using 1
    norm_num
    try ring
  have hcont : ContinuousOn (fun s : ℝ => ρ (z + s • v) - ρ z - s * fderiv ℝ ρ z v) (Icc 0 1) :=
    fun s _ => (hF s).continuousAt.continuousWithinAt
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := fun s : ℝ => ρ (z + s • v) - ρ z - s * fderiv ℝ ρ z v)
    (f' := fun s : ℝ => fderiv ℝ ρ (z + s • v) v - fderiv ℝ ρ z v)
    (a := 0) (b := 1) hcont (fun s _ => (hF s).hasDerivWithinAt)
    (B := fun s : ℝ => M * ‖v‖ ^ 2 * s ^ 2 / 2) (B' := fun s : ℝ => M * ‖v‖ ^ 2 * s)
    (by simp) hB hbound
  have h1 := key (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩)
  simpa using h1

/-- Algebraic core of the exterior sphere estimate: `2 c L ≤ N` whenever `L ≤ M₀ N / 2`, `c n = R`, `g ≤ n`
and `R M₀ ≤ g`. -/
lemma exterior_core {c g R M₀ L N n : ℝ} (hc : 0 ≤ c) (hg : 0 < g) (hn : g ≤ n) (hcn : c * n = R)
    (hR : 0 ≤ R) (hRM : R * M₀ ≤ g) (hN : 0 ≤ N) (hL : L ≤ M₀ * N / 2) : 2 * c * L ≤ N := by
  rcases le_or_gt L 0 with hL0 | hL0
  · nlinarith [mul_nonneg hc (neg_nonneg.mpr hL0)]
  · have hcL : 0 ≤ 2 * c * L := mul_nonneg (mul_nonneg (by norm_num) hc) hL0.le
    have h1 : 2 * c * L * g ≤ 2 * c * L * n := mul_le_mul_of_nonneg_left hn hcL
    have h2 : 2 * c * L * n = 2 * R * L := by rw [← hcn]; ring
    have h3 : 2 * R * L ≤ R * M₀ * N := by
      nlinarith [mul_le_mul_of_nonneg_left hL (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hR)]
    have h4 : R * M₀ * N ≤ g * N := mul_le_mul_of_nonneg_right hRM hN
    have h5 : 2 * c * L * g ≤ N * g := by nlinarith
    exact le_of_mul_le_mul_right h5 hg

/-- **Uniform exterior sphere condition** (Armitage-Gardiner): for a smooth bounded open set `O` there is one radius
`R > 0` such that every `z ∈ ∂O` is the point of a sphere `{|· - a| = R}` with `|a - z| = R` whose centre `a` satisfies
`R ≤ |a - x|` for all `x ∈ closure O`. Empty boundaries and disconnected `O` are allowed. -/
theorem exists_uniform_exterior_ball_of_isSmoothBoundedOpen {O : Set ℂ} (hO : IsSmoothBoundedOpen O) :
    ∃ R : ℝ, 0 < R ∧ ∀ z ∈ frontier O, ∃ a : ℂ, dist a z = R ∧ ∀ x ∈ closure O, R ≤ dist a x := by
  obtain ⟨hbdd, ρ, hρs, hOρ, hnz⟩ := hO
  have hρ : ContDiff ℝ 2 ρ := hρs.of_le (by norm_num)
  have hcont : Continuous ρ := hρ.continuous
  have hOopen : IsOpen O := by
    rw [hOρ]
    exact isOpen_lt hcont continuous_const
  have hcl : ∀ x ∈ closure O, ρ x ≤ 0 := by
    intro x hx
    have hsub : closure O ⊆ {z | ρ z ≤ 0} := by
      rw [hOρ]
      exact closure_lt_subset_le hcont (continuous_const : Continuous fun _ : ℂ => (0 : ℝ))
    exact hsub hx
  have hfr : ∀ z ∈ frontier O, ρ z = 0 := by
    intro z hz
    have h1 : ρ z ≤ 0 := hcl z (frontier_subset_closure hz)
    have h2 : 0 ≤ ρ z := by
      by_contra hneg
      have hneg' : ρ z < 0 := not_le.mp hneg
      have hzO : z ∈ O := by
        rw [hOρ]
        exact hneg'
      have hz' : z ∈ closure O \ interior O := hz
      have hzint : z ∉ interior O := hz'.2
      rw [hOopen.interior_eq] at hzint
      exact hzint hzO
    linarith
  have hΓc : IsCompact (frontier O) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_frontier
      (hbdd.closure.subset frontier_subset_closure)
  obtain ⟨M₀, hM₀, hM⟩ := exists_hessian_bound hρ hΓc
  obtain ⟨g, hg, hgΓ⟩ := exists_gradC_lower_bound hρ hΓc (fun z hz => hnz z (hfr z hz))
  have hRpos : (0 : ℝ) < min (1 / 2) (g / (2 * (M₀ + 1))) :=
    lt_min (by norm_num) (div_pos hg (by linarith))
  have hRle : min (1 / 2) (g / (2 * (M₀ + 1))) * (2 * (M₀ + 1)) ≤ g :=
    (le_div_iff₀ (by linarith)).mp (min_le_right _ _)
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = min (1 / 2) (g / (2 * (M₀ + 1))) := ⟨_, rfl⟩
  rw [← hRdef] at hRpos hRle
  have hR0 : 0 < R := hRpos
  have hRhalf : R ≤ 1 / 2 := by
    rw [hRdef]
    exact min_le_left _ _
  have hRM : R * M₀ ≤ g := by nlinarith [mul_nonneg hR0.le hM₀]
  refine ⟨R, hR0, fun z hz => ?_⟩
  have hz0 : ρ z = 0 := hfr z hz
  have hMz : ∀ w ∈ closedBall z 1, ‖fderiv ℝ (fderiv ℝ ρ) w‖ ≤ M₀ := hM z hz
  have hGpos : 0 < ‖gradC ρ z‖ := lt_of_lt_of_le hg (hgΓ z hz)
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = R / ‖gradC ρ z‖ := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by
    rw [hcdef]
    exact div_nonneg hR0.le hGpos.le
  have hcn : c * ‖gradC ρ z‖ = R := by
    rw [hcdef]
    exact div_mul_cancel₀ R hGpos.ne'
  have hcG : ‖(c : ℂ) * gradC ρ z‖ = R := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0, hcn]
  refine ⟨z + (c : ℂ) * gradC ρ z, ?_, fun x hx => ?_⟩
  · rw [dist_eq_norm, add_sub_cancel_left, hcG]
  · rw [dist_eq_norm]
    have hax : z + (c : ℂ) * gradC ρ z - x = (c : ℂ) * gradC ρ z - (x - z) := by ring
    rw [hax]
    by_cases hv : ‖x - z‖ ≤ 1
    · -- near case: Taylor's inequality on the closed unit neighbourhood of `z`
      have htay := abs_sub_sub_fderiv_le hρ hMz hv
      have hxz : z + (x - z) = x := by ring
      rw [hxz, hz0] at htay
      have hlow := (abs_le.mp htay).1
      have hL : fderiv ℝ ρ z (x - z) ≤ M₀ * ‖x - z‖ ^ 2 / 2 := by
        linarith [hcl x hx]
      rw [fderiv_apply_eq_gradC] at hL
      have hkey := exterior_core hc0 hg (hgΓ z hz) hcn hR0.le hRM (sq_nonneg ‖x - z‖) hL
      have hGsq : ‖gradC ρ z‖ ^ 2 = (gradC ρ z).re ^ 2 + (gradC ρ z).im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        ring
      have hR2 : R ^ 2 = c ^ 2 * ((gradC ρ z).re ^ 2 + (gradC ρ z).im ^ 2) := by
        rw [← hGsq, ← hcn]
        ring
      have hsq : ‖(c : ℂ) * gradC ρ z - (x - z)‖ ^ 2 =
          c ^ 2 * ((gradC ρ z).re ^ 2 + (gradC ρ z).im ^ 2)
            - 2 * c * ((gradC ρ z).re * (x - z).re + (gradC ρ z).im * (x - z).im)
            + ‖x - z‖ ^ 2 := by
        simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
          Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
        ring
      have hfinal : R ^ 2 ≤ ‖(c : ℂ) * gradC ρ z - (x - z)‖ ^ 2 := by
        rw [hsq, hR2]
        linarith [hkey]
      exact (sq_le_sq₀ hR0.le (norm_nonneg _)).mp hfinal
    · -- far case: the triangle inequality with `‖x - z‖ > 1` and `R ≤ 1/2`
      have hv' : 1 < ‖x - z‖ := not_le.mp hv
      have h1 := norm_sub_norm_le (x - z) ((c : ℂ) * gradC ρ z)
      rw [hcG] at h1
      rw [norm_sub_rev]
      linarith

/-- **Half-radius geometry** of a smooth bounded open set: a common radius `d > 0` and, at each `z ∈ ∂O`, a centre `w`
with `|w - z| = d` and `d² + |x - z|²/2 ≤ |x - w|²` for every `x ∈ closure O`. The centre is the midpoint of `z` and the
centre `a` of the uniform exterior sphere, and the inequality is the parallelogram identity
`|x - w|² = (|x - z|² + |x - a|²)/2 - |a - z|²/4` together with `|x - a| ≥ R`. -/
theorem exists_half_radius_geometry_of_isSmoothBoundedOpen {O : Set ℂ} (hO : IsSmoothBoundedOpen O) :
    ∃ d : ℝ, 0 < d ∧ ∀ z ∈ frontier O, ∃ w : ℂ, dist w z = d ∧
      ∀ x ∈ closure O, d ^ 2 + (1 / 2 : ℝ) * dist x z ^ 2 ≤ dist x w ^ 2 := by
  obtain ⟨R, hR0, h⟩ := exists_uniform_exterior_ball_of_isSmoothBoundedOpen hO
  refine ⟨R / 2, by linarith, fun z hz => ?_⟩
  obtain ⟨a, haz, ha⟩ := h z hz
  have haz' : ‖a - z‖ = R := by
    rw [← dist_eq_norm]
    exact haz
  refine ⟨z + (1 / 2 : ℝ) • (a - z), ?_, fun x hx => ?_⟩
  · rw [dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), haz']
    ring
  · have hxw : x - (z + (1 / 2 : ℝ) • (a - z)) = (x - z) - (1 / 2 : ℝ) • (a - z) := by
      rw [sub_add_eq_sub_sub]
    have hxa : R ≤ ‖x - a‖ := by
      have h' := ha x hx
      rw [dist_eq_norm, norm_sub_rev] at h'
      exact h'
    have hid : ‖(x - z) - (1 / 2 : ℝ) • (a - z)‖ ^ 2 =
        (‖x - z‖ ^ 2 + ‖x - a‖ ^ 2) / 2 - ‖a - z‖ ^ 2 / 4 := by
      simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
        Complex.smul_re, Complex.smul_im, smul_eq_mul]
      ring
    have hsq : R ^ 2 ≤ ‖x - a‖ ^ 2 := (sq_le_sq₀ hR0.le (norm_nonneg _)).mpr hxa
    have hdz : dist x z = ‖x - z‖ := dist_eq_norm x z
    have hdw : dist x (z + (1 / 2 : ℝ) • (a - z)) = ‖(x - z) - (1 / 2 : ℝ) • (a - z)‖ := by
      rw [dist_eq_norm, hxw]
    rw [hdz, hdw, hid, haz']
    nlinarith [hsq]

end SmoothDomainExteriorSphere

end HarmonicBalls
