import HarmonicBalls.Proofs.Sec6.BrownianScaling
import LatticeProb.Prob.BrownianModulus

/-! # Brownian modulus estimates

A fixed-scale oscillation bound for Brownian motion started at an arbitrary point.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Filter
open scoped NNReal ENNReal

namespace HarmonicBalls

/-- A real Brownian path started at any point satisfies the Gaussian modulus tail bound. -/
theorem realBrownianMotion_modulus_tail (x : ℝ) (T η : ℝ≥0) (hη : 0 < η)
    {a : ℝ} (ha : 0 < a) :
    brownianMotion x {ω | ∃ s t : ℝ≥0, s ≤ T ∧ t ≤ T ∧
      |(s : ℝ) - t| ≤ η ∧ a ≤ |ω s - ω t|} ≤
      ((⌈(T : ℝ) / η⌉₊ + 1 : ℕ) : ℝ≥0∞) *
        (4 * ENNReal.ofReal (Real.exp (-((a / 2) ^ 2 / (32 * (2 * (η : ℝ))))))) := by
  have hB : ProbabilityTheory.IsBrownianReal
      (fun (t : ℝ≥0) (ω : ContinuousPath ℝ) => ω t - x) (brownianMotion x) :=
    ⟨Section6.isPreBrownianReal_brownianMotion x,
      Filter.Eventually.of_forall fun ω => ω.continuous.sub continuous_const⟩
  simpa only [sub_sub_sub_cancel_right] using
    LatticeProb.measure_exists_modulus_le hB T η hη ha

/-- The planar Brownian modulus has a Gaussian tail, uniformly in the starting point. -/
theorem planarBrownianMotion_modulus_tail (x : ℂ) (T η : ℝ≥0) (hη : 0 < η)
    {a : ℝ} (ha : 0 < a) :
    planarBrownianMotion x {ω | ∃ s t : ℝ≥0, s ≤ T ∧ t ≤ T ∧
      |(s : ℝ) - t| ≤ η ∧ a ≤ ‖ω s - ω t‖} ≤
      2 * (((⌈(T : ℝ) / η⌉₊ + 1 : ℕ) : ℝ≥0∞) *
        (4 * ENNReal.ofReal (Real.exp (-(((a / 2) / 2) ^ 2 /
          (32 * (2 * (η : ℝ)))))))) := by
  let A : Set (ContinuousPath ℝ) := {ω | ∃ s t : ℝ≥0, s ≤ T ∧ t ≤ T ∧
    |(s : ℝ) - t| ≤ η ∧ a / 2 ≤ |ω s - ω t|}
  let f : ContinuousPath ℂ → ContinuousPath ℝ := fun ω => (reImPath ω).1
  let g : ContinuousPath ℂ → ContinuousPath ℝ := fun ω => (reImPath ω).2
  have hf : Measurable f := measurable_fst.comp measurable_reImPath
  have hg : Measurable g := measurable_snd.comp measurable_reImPath
  have hsub : {ω : ContinuousPath ℂ | ∃ s t : ℝ≥0, s ≤ T ∧ t ≤ T ∧
      |(s : ℝ) - t| ≤ η ∧ a ≤ ‖ω s - ω t‖} ⊆ f ⁻¹' A ∪ g ⁻¹' A := by
    rintro ω ⟨s, t, hs, ht, hst, hab⟩
    have hn := Complex.norm_le_abs_re_add_abs_im (ω s - ω t)
    simp only [Complex.sub_re, Complex.sub_im] at hn
    by_cases h : a / 2 ≤ |(ω s).re - (ω t).re|
    · exact Or.inl ⟨s, t, hs, ht, hst, h⟩
    · refine Or.inr ⟨s, t, hs, ht, hst, ?_⟩
      change a / 2 ≤ |(ω s).im - (ω t).im|
      linarith
  have h1 : planarBrownianMotion x (f ⁻¹' A) ≤ brownianMotion x.re A := by
    calc
      _ ≤ (planarBrownianMotion x).map f A := Measure.le_map_apply hf.aemeasurable A
      _ = _ := by rw [planarBrownianMotion_map_re]
  have h2 : planarBrownianMotion x (g ⁻¹' A) ≤ brownianMotion x.im A := by
    calc
      _ ≤ (planarBrownianMotion x).map g A := Measure.le_map_apply hg.aemeasurable A
      _ = _ := by rw [planarBrownianMotion_map_im]
  calc
    _ ≤ planarBrownianMotion x (f ⁻¹' A) + planarBrownianMotion x (g ⁻¹' A) :=
      (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ brownianMotion x.re A + brownianMotion x.im A := add_le_add h1 h2
    _ ≤ _ := by
      have hr := realBrownianMotion_modulus_tail x.re T η hη (half_pos ha)
      have hi := realBrownianMotion_modulus_tail x.im T η hη (half_pos ha)
      simpa only [two_mul] using add_le_add hr hi

end HarmonicBalls
