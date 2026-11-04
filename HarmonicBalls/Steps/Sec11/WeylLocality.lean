import HarmonicBalls.Steps.Sec11.WeylPathSegments
import HarmonicBalls.Steps.Sec11.PinchLocalEdgeCover

/-! # Locality of Weyl-scaled internal metrics

On an open set where two weights agree, their Weyl-scaled length metrics
have the same internal distances. The ambient distances may use paths that
leave the set, so the proof first controls sufficiently short edges.
-/

namespace HarmonicBalls

open MeasureTheory Set
open scoped ENNReal

/-- A sufficiently short Weyl path cannot exit a neighborhood: its cost up
to any time bounds its shifted distance from the starting point. -/
theorem IsEuclideanLengthMetric.weylScaling_le_of_eqOn_near
    {D E F : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hF : IsEuclideanLengthMetric F) (ξ : ℝ) (f g : ℂ → ℝ)
    (hE : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y)
    (hFscale : ∀ x y, ENNReal.ofReal (F x y) = weylScaling D ξ g x y)
    {U : Set ℂ} (hU : IsOpen U) (hfg : ∀ z ∈ U, f z = g z)
    {x : ℂ} (hx : x ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ∀ y z, F x y < r → F x z < r → E y z ≤ F y z := by
  obtain ⟨R, hR, hRU⟩ := (hF.isOpen_iff U).mp hU x hx
  have hnonneg (u v : ℂ) : 0 ≤ F u v := by
    have h := hF.triangle u v u
    rw [hF.self_eq_zero, hF.symm v u] at h
    linarith
  refine ⟨R / 4, by positivity, ?_⟩
  intro y z hy hz
  have hyz : F y z < R / 2 := by
    have h := hF.triangle y x z
    rw [hF.symm y x] at h
    linarith
  have hcmp : weylScaling D ξ f y z ≤ weylScaling D ξ g y z := by
    by_contra hn
    have hlt : weylScaling D ξ g y z < weylScaling D ξ f y z := lt_of_not_ge hn
    have hsmall : weylScaling D ξ g y z < ENNReal.ofReal (R / 2) := by
      rw [← hFscale]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (hnonneg y z)).2 hyz
    have hmin : weylScaling D ξ g y z <
        min (weylScaling D ξ f y z) (ENNReal.ofReal (R / 2)) := lt_min hlt hsmall
    unfold weylScaling at hmin
    obtain ⟨T, hmin⟩ := iInf_lt_iff.mp hmin
    obtain ⟨p, hmin⟩ := iInf_lt_iff.mp hmin
    obtain ⟨hp, hmin⟩ := iInf_lt_iff.mp hmin
    obtain ⟨hp0, hmin⟩ := iInf_lt_iff.mp hmin
    obtain ⟨hpT, hmin⟩ := iInf_lt_iff.mp hmin
    have hinside : ∀ t ∈ Icc (0 : ℝ) T, p t ∈ U := by
      intro t ht
      apply hRU
      have hprefix := hD.weylScaling_le_segment_cost ξ g hp le_rfl ht.1 ht.2
      rw [hp0, ← hFscale] at hprefix
      have hcost : (∫⁻ s in Icc (0 : ℝ) t,
          ENNReal.ofReal (Real.exp (ξ * g (p s)))) ≤
          ∫⁻ s in Icc (0 : ℝ) T, ENNReal.ofReal (Real.exp (ξ * g (p s))) :=
        lintegral_mono' (Measure.restrict_mono_set volume (Icc_subset_Icc le_rfl ht.2)) le_rfl
      have hsmall' : ENNReal.ofReal (F y (p t)) < ENNReal.ofReal (R / 2) :=
        (hprefix.trans hcost).trans_lt (lt_of_lt_of_le hmin (min_le_right _ _))
      have hd : F y (p t) < R / 2 :=
        (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (hnonneg y (p t))).mp hsmall'
      have htri := hF.triangle x y (p t)
      linarith
    have heq : (∫⁻ t in Icc (0 : ℝ) T, ENNReal.ofReal (Real.exp (ξ * f (p t)))) =
        ∫⁻ t in Icc (0 : ℝ) T, ENNReal.ofReal (Real.exp (ξ * g (p t))) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rw [hfg (p t) (hinside t ht)]
    have hbound : weylScaling D ξ f y z ≤
        ∫⁻ t in Icc (0 : ℝ) T, ENNReal.ofReal (Real.exp (ξ * f (p t))) := by
      unfold weylScaling
      exact (iInf₂_le T p).trans ((iInf₂_le hp hp0).trans (iInf_le _ hpT))
    rw [heq] at hbound
    exact (not_lt_of_ge hbound) (lt_of_lt_of_le hmin (min_le_left _ _))
  rw [← hE, ← hFscale] at hcmp
  exact (ENNReal.ofReal_le_ofReal_iff (hnonneg y z)).mp hcmp

/-- Two Weyl-scaled Euclidean length metrics have identical internal
metrics on every open set where their weights agree. No global boundedness or
continuity of the weights is required. -/
theorem IsEuclideanLengthMetric.internalMetric_weylScaling_eq_of_eqOn
    {D E F : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) (hF : IsEuclideanLengthMetric F)
    (ξ : ℝ) (f g : ℂ → ℝ)
    (hEscale : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y)
    (hFscale : ∀ x y, ENNReal.ofReal (F x y) = weylScaling D ξ g x y)
    {U : Set ℂ} (hU : IsOpen U) (hfg : ∀ z ∈ U, f z = g z)
    (x y : ℂ) : internalMetric E U x y = internalMetric F U x y := by
  have hEnonneg (u v : ℂ) : 0 ≤ E u v := by
    have h := hE.triangle u v u
    rw [hE.self_eq_zero, hE.symm v u] at h
    linarith
  have hFnonneg (u v : ℂ) : 0 ≤ F u v := by
    have h := hF.triangle u v u
    rw [hF.self_eq_zero, hF.symm v u] at h
    linarith
  have hEF : internalMetric E U x y ≤ internalMetric F U x y := by
    have hl : ∀ z ∈ U, ∃ r : ℝ, 0 < r ∧ ∀ a b,
        F z a < r → F z b < r → E a b ≤ (1 : ℝ) * F a b := by
      intro z hz
      simpa only [one_mul] using
        hD.weylScaling_le_of_eqOn_near hF ξ f g hEscale hFscale hU hfg hz
    have hh := hF.internalMetric_le_const_mul_of_short_edges hE hEnonneg hU
      (show (0 : ℝ) < 1 by norm_num)
      (fun p hp => hF.path_short_edge_comparison_of_local 1 hl p hp) x y
    simpa only [ENNReal.ofReal_one, one_mul] using hh
  have hFE : internalMetric F U x y ≤ internalMetric E U x y := by
    have hl : ∀ z ∈ U, ∃ r : ℝ, 0 < r ∧ ∀ a b,
        E z a < r → E z b < r → F a b ≤ (1 : ℝ) * E a b := by
      intro z hz
      simpa only [one_mul] using
        hD.weylScaling_le_of_eqOn_near hE ξ g f hFscale hEscale hU
          (fun z hz => (hfg z hz).symm) hz
    have hh := hE.internalMetric_le_const_mul_of_short_edges hF hFnonneg hU
      (show (0 : ℝ) < 1 by norm_num)
      (fun p hp => hE.path_short_edge_comparison_of_local 1 hl p hp) x y
    simpa only [ENNReal.ofReal_one, one_mul] using hh
  exact le_antisymm hEF hFE

#print axioms IsEuclideanLengthMetric.weylScaling_le_of_eqOn_near
#print axioms IsEuclideanLengthMetric.internalMetric_weylScaling_eq_of_eqOn

end HarmonicBalls
