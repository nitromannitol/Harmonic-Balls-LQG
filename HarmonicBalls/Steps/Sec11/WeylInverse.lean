import HarmonicBalls.Steps.Sec11.WeylInversePath
import HarmonicBalls.Steps.Sec11.CurveLengthReparam

/-! # Inverse Weyl scaling for bounded nonpositive shifts -/

namespace HarmonicBalls

open MeasureTheory Set
open scoped ENNReal

/-- Every unit-speed path in the shifted metric has inverse Weyl cost at
least the original distance between its endpoints. -/
theorem IsEuclideanLengthMetric.ofReal_le_inverse_weyl_cost
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {ξ c : ℝ} (hξ : 0 ≤ ξ) (f : ℂ → ℝ) (hf : Continuous f)
    (hl : ∀ z, c ≤ f z) (hu : ∀ z, f z ≤ 0)
    (hE : IsEuclideanLengthMetric (fun u v => (weylScaling D ξ f u v).toReal))
    {q : ℝ → ℂ} {T : ℝ}
    (hq : IsLengthParametrized (fun u v => (weylScaling D ξ f u v).toReal) q T) :
    ENNReal.ofReal (D (q 0) (q T)) ≤
      ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * (-f (q t)))) := by
  let E : ℂ → ℂ → ℝ := fun u v => (weylScaling D ξ f u v).toReal
  let a : ℝ := Real.exp (ξ * c)
  have ha : 0 < a := Real.exp_pos _
  have hpoint (u v : ℂ) : a * D u v ≤ E u v :=
    (weylScaling_negative_bump_real_bounds hD hξ f hl hu (hD.weylScaling_zero ξ) u v).2.1
  have hle := mul_curveLength_le_of_boundOn q 0 T (ENNReal.ofReal a) (D := D) (E := E) (by
    intro s hs t ht
    rw [← ENNReal.ofReal_mul ha.le]
    exact ENNReal.ofReal_le_ofReal (hpoint _ _))
  rw [hq.2.2 0 T le_rfl hq.1 le_rfl, sub_zero] at hle
  have hqD : curveLength D q 0 T < ∞ := by
    by_contra h
    have htop : curveLength D q 0 T = ∞ := top_unique (le_of_not_gt h)
    rw [htop, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr ha))] at hle
    exact (not_le_of_gt ENNReal.ofReal_lt_top) hle
  let A : ℝ → ℝ := fun t => (curveLength D q 0 t).toReal
  let R : ℝ := A T
  obtain ⟨p, hp, hp0, hpR, htrackD⟩ := hD.exists_lengthParametrized_with_tracking hq.1 hq.2.1 hqD
  obtain ⟨S, r, hr, hr0, hrS, hcost, hS, htrackE⟩ := hD.exists_inverse_weyl_path hξ f hf hl hu hp hE
  have hcomp (t : ℝ) (ht : t ∈ Icc 0 T) :
      (curveLength E p 0 (A t)).toReal = t :=
    hD.cumulative_length_comp_of_tracking hE hq hqD htrackD ht
  have hS' : S = T := by
    rw [hS]
    exact hcomp T ⟨hq.1, le_rfl⟩
  have hArange : ∀ t ∈ Icc 0 T, A t ∈ Icc 0 R := by
    obtain ⟨_, hmono, _, _⟩ := hD.cumulative_curveLength_properties hq.1 hq.2.1 hqD
    intro t ht
    exact ⟨ENNReal.toReal_nonneg, hmono ht ⟨hq.1, le_rfl⟩ ht.2⟩
  have hrq : EqOn r q (Icc 0 T) := by
    intro t ht
    have ht' := htrackE (A t) (hArange t ht)
    rw [hcomp t ht] at ht'
    exact ht'.trans (htrackD t ht)
  have hcost' : (∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * (-f (q t))))) =
      ENNReal.ofReal R := by
    rw [hS'] at hcost
    calc
      _ = ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * (-f (r t)))) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        rw [hrq ht]
      _ = _ := hcost
  have hend := hD.ofReal_dist_start_le_lengthParametrized hp ⟨hp.1, le_rfl⟩
  rw [hp0, hpR] at hend
  exact hend.trans_eq hcost'.symm

/-- Weyl scaling by a bounded nonpositive continuous function is inverted by
the opposite Weyl weight. -/
theorem IsEuclideanLengthMetric.inverse_weylScaling
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {ξ c : ℝ} (hξ : 0 ≤ ξ) (f : ℂ → ℝ) (hf : Continuous f)
    (hl : ∀ z, c ≤ f z) (hu : ∀ z, f z ≤ 0)
    (hE : IsEuclideanLengthMetric (fun u v => (weylScaling D ξ f u v).toReal))
    (x y : ℂ) :
    ENNReal.ofReal (D x y) =
      weylScaling (fun u v => (weylScaling D ξ f u v).toReal) ξ (fun z => -f z) x y := by
  apply le_antisymm
  · unfold weylScaling
    refine le_iInf fun T => le_iInf fun q => le_iInf fun hq => le_iInf fun hq0 =>
      le_iInf fun hqT => ?_
    have h := hD.ofReal_le_inverse_weyl_cost hξ f hf hl hu hE hq
    rwa [hq0, hqT] at h
  · exact hD.inverse_weylScaling_le hξ f hf hl hu hE x y


end HarmonicBalls
