import HarmonicBalls.Steps.Sec11.MetricArcLength
import HarmonicBalls.Steps.Sec11.WeylLocalEdges
import HarmonicBalls.Steps.Sec11.WeylBumpTopology

/-! # Local lower comparison for Weyl scaling

A global lower bound on the weight prevents a low-cost path between nearby
points from making a long excursion outside a neighborhood. -/

namespace HarmonicBalls

open MeasureTheory Set
open scoped ENNReal

/-- A lower bound on the exponent along a path bounds its weighted cost. -/
theorem lengthParametrized_cost_lower_bound
    {D : ℂ → ℂ → ℝ} {ξ B : ℝ} {f : ℂ → ℝ}
    {p : ℝ → ℂ} {T : ℝ} (_hp : IsLengthParametrized D p T)
    (hweight : ∀ t ∈ Icc 0 T, B ≤ ξ * f (p t)) :
    ENNReal.ofReal (Real.exp B * T) ≤
      ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * f (p t))) := by
  rw [ENNReal.ofReal_mul (Real.exp_nonneg B)]
  calc
    _ = ∫⁻ _ in Icc (0 : ℝ) T, ENNReal.ofReal (Real.exp B) := by
      simp [lintegral_const, Real.volume_Icc]
    _ ≤ _ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (hweight t ht))

/-- If a nonpositive Weyl weight has a global lower bound and its exponent
is at least `B` near `x`, sufficiently short edges near `x` are bounded below
by the corresponding exponential multiple of their original length. -/
theorem IsEuclideanLengthMetric.weylScaling_local_edge_lower_bound
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {ξ c B : ℝ} (hξ : 0 ≤ ξ) (f : ℂ → ℝ)
    (hl : ∀ z, c ≤ f z) (hu : ∀ z, f z ≤ 0)
    {x : ℂ} {R : ℝ} (hR : 0 < R)
    (hweight : ∀ z, D x z < R → B ≤ ξ * f z) :
    ∃ r : ℝ, 0 < r ∧ ∀ y z, D x y < r → D x z < r →
      Real.exp B * D y z ≤ (weylScaling D ξ f y z).toReal := by
  let a := Real.exp (ξ * c)
  let b := Real.exp B
  have ha : 0 < a := Real.exp_pos _
  have hb : 0 < b := Real.exp_pos _
  let r := min (R / 4) (a * R / (4 * (b + 1)))
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  refine ⟨r, hr, ?_⟩
  intro y z hy hz
  have hnonneg (u v : ℂ) : 0 ≤ D u v := by
    have ht := hD.triangle u v u
    rw [hD.self_eq_zero, hD.symm v u] at ht
    linarith
  have hdist : D y z < 2 * r := by
    have ht := hD.triangle y x z
    rw [hD.symm y x] at ht
    linarith
  have hrR : r ≤ R / 4 := min_le_left _ _
  have hra : r ≤ a * R / (4 * (b + 1)) := min_le_right _ _
  have hrbound : b * (2 * r) ≤ a * (R / 2) := by
    have h := (le_div_iff₀ (show 0 < 4 * (b + 1) by positivity)).mp hra
    nlinarith [mul_nonneg hr.le (show 0 ≤ (1 : ℝ) by norm_num)]
  have hpath : ∀ T p, IsLengthParametrized D p T → p 0 = y → p T = z →
      ENNReal.ofReal (b * D y z) ≤
        ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * f (p t))) := by
    intro T p hp hp0 hpT
    have hdy : D y z ≤ T := by
      have h := hD.ofReal_dist_start_le_lengthParametrized hp ⟨hp.1, le_rfl⟩
      rw [hp0, hpT] at h
      exact (ENNReal.ofReal_le_ofReal_iff hp.1).mp h
    by_cases hT : T < R / 2
    · have hinside : ∀ t ∈ Icc 0 T, D x (p t) < R := by
        intro t ht
        have h := hD.ofReal_dist_start_le_lengthParametrized hp ht
        rw [hp0] at h
        have h' : D y (p t) ≤ T := (ENNReal.ofReal_le_ofReal_iff hp.1).mp h
        have ht := hD.triangle x y (p t)
        linarith
      exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hdy hb.le)).trans
        (lengthParametrized_cost_lower_bound hp (fun t ht => hweight _ (hinside t ht)))
    · have hcost := lengthParametrized_cost_lower_bound hp
        (B := ξ * c) (fun t _ => mul_le_mul_of_nonneg_left (hl (p t)) hξ)
      apply (ENNReal.ofReal_le_ofReal ?_).trans hcost
      dsimp only [a, b] at *
      have hT' : R / 2 ≤ T := le_of_not_gt hT
      have hm := mul_le_mul_of_nonneg_left hT' (Real.exp_nonneg (ξ * c))
      nlinarith
  have hbound : ENNReal.ofReal (b * D y z) ≤ weylScaling D ξ f y z := by
    unfold weylScaling
    exact le_iInf fun T => le_iInf fun p => le_iInf fun hp => le_iInf fun hp0 =>
      le_iInf fun hpT => hpath T p hp hp0 hpT
  have hfin := (weylScaling_negative_bump_real_bounds hD hξ f hl hu (hD.weylScaling_zero ξ) y z).1
  have := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hfin.ne).2 hbound
  simpa [ENNReal.toReal_ofReal (mul_nonneg hb.le (hnonneg y z)), b] using this

/-- A continuous bounded nonpositive Weyl weight has the expected local
multiplicative bounds, uniformly over pairs of points near the center. -/
theorem IsEuclideanLengthMetric.weylScaling_local_comparison
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {ξ c : ℝ} (hξ : 0 ≤ ξ) (f : ℂ → ℝ) (hf : Continuous f)
    (hl : ∀ z, c ≤ f z) (hu : ∀ z, f z ≤ 0)
    (x : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ y z, D x y < r → D x z < r →
      Real.exp (ξ * f x - ε) * D y z ≤ (weylScaling D ξ f y z).toReal ∧
      (weylScaling D ξ f y z).toReal ≤ Real.exp (ξ * f x + ε) * D y z := by
  let U := {z : ℂ | ξ * f x - ε < ξ * f z ∧ ξ * f z < ξ * f x + ε}
  have hU : IsOpen U := by
    exact isOpen_Ioo.preimage (continuous_const.mul hf)
  have hx : x ∈ U := by simp only [U, mem_ofPred_eq]; constructor <;> linarith
  obtain ⟨R, hR, hRin⟩ := (hD.isOpen_iff U).mp hU x hx
  have hlow : ∀ z, D x z < R → ξ * f x - ε ≤ ξ * f z := by
    intro z hz
    exact (hRin z hz).1.le
  have hupp : ∀ z, D x z < R → ξ * f z ≤ ξ * f x + ε := by
    intro z hz
    exact (hRin z hz).2.le
  obtain ⟨r₁, hr₁, h₁⟩ := hD.weylScaling_local_edge_lower_bound hξ f hl hu hR hlow
  have hnonneg (u v : ℂ) : 0 ≤ D u v := by
    have ht := hD.triangle u v u
    rw [hD.self_eq_zero, hD.symm v u] at ht
    linarith
  have hscale (u v : ℂ) :
      ENNReal.ofReal ((weylScaling D ξ f u v).toReal) = weylScaling D ξ f u v :=
    ENNReal.ofReal_toReal
      (weylScaling_negative_bump_real_bounds hD hξ f hl hu (hD.weylScaling_zero ξ) u v).1.ne
  obtain ⟨r₂, hr₂, h₂⟩ := hD.weylScaling_local_edge_bound hnonneg
    (hD.weylScaling_zero ξ) hscale hR hupp
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, ?_⟩
  intro y z hy hz
  exact ⟨h₁ y z (lt_of_lt_of_le hy (min_le_left _ _))
      (lt_of_lt_of_le hz (min_le_left _ _)),
    h₂ y z (lt_of_lt_of_le hy (min_le_right _ _))
      (lt_of_lt_of_le hz (min_le_right _ _))⟩

#print axioms IsEuclideanLengthMetric.weylScaling_local_edge_lower_bound
#print axioms IsEuclideanLengthMetric.weylScaling_local_comparison

end HarmonicBalls
