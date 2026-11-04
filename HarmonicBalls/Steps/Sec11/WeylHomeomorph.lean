import HarmonicBalls.Defs.LQGMetric

/-! # Weyl scaling and changes of coordinates

The length-parametrized path formula is invariant under pulling a metric and
its Weyl weight back by a homeomorphism. No regularity of the weight is needed.
-/

namespace HarmonicBalls
open Set MeasureTheory

/-- Length parametrization is preserved when a path and metric are pulled back
by a homeomorphism. -/
theorem IsLengthParametrized.comp_homeomorph_symm
    {D : ℂ → ℂ → ℝ} {p : ℝ → ℂ} {T : ℝ} (hp : IsLengthParametrized D p T)
    (e : ℂ ≃ₜ ℂ) :
    IsLengthParametrized (fun x y => D (e x) (e y)) (e.symm ∘ p) T := by
  refine ⟨hp.1, e.symm.continuous.comp_continuousOn hp.2.1, ?_⟩
  intro s t hs hst ht
  have heq : curveLength (fun x y => D (e x) (e y)) (e.symm ∘ p) s t =
      curveLength D p s t := by
    simp only [curveLength, Function.comp_apply, e.apply_symm_apply]
  rw [heq]
  exact hp.2.2 s t hs hst ht

/-- Pulling back a distance and its Weyl weight commutes with Weyl scaling. -/
theorem weylScaling_comp_homeomorph (D : ℂ → ℂ → ℝ) (ξ : ℝ)
    (f : ℂ → ℝ) (e : ℂ ≃ₜ ℂ) (u v : ℂ) :
    weylScaling (fun x y => D (e x) (e y)) ξ (f ∘ e) u v =
      weylScaling D ξ f (e u) (e v) := by
  apply le_antisymm
  · unfold weylScaling
    apply le_iInf
    intro T
    apply le_iInf
    intro p
    apply le_iInf
    intro hp
    apply le_iInf
    intro hu
    apply le_iInf
    intro hv
    refine iInf_le_of_le T (iInf_le_of_le (e.symm ∘ p) ?_)
    refine iInf_le_of_le (hp.comp_homeomorph_symm e) ?_
    have hpu : (e.symm ∘ p) 0 = u := by simp [hu]
    have hpv : (e.symm ∘ p) T = v := by simp [hv]
    refine iInf_le_of_le hpu (iInf_le_of_le hpv ?_)
    simp only [Function.comp_apply, e.apply_symm_apply, le_refl]
  · unfold weylScaling
    apply le_iInf
    intro T
    apply le_iInf
    intro p
    apply le_iInf
    intro hp
    apply le_iInf
    intro hu
    apply le_iInf
    intro hv
    have hp' : IsLengthParametrized D (e ∘ p) T := by
      have h := hp.comp_homeomorph_symm e.symm
      simpa only [e.symm_symm, e.apply_symm_apply] using h
    refine iInf_le_of_le T (iInf_le_of_le (e ∘ p) ?_)
    refine iInf_le_of_le hp' ?_
    have hpu : (e ∘ p) 0 = e u := by simp [hu]
    have hpv : (e ∘ p) T = e v := by simp [hv]
    exact iInf_le_of_le hpu (iInf_le_of_le hpv (by simp only [Function.comp_apply, le_refl]))

#print axioms IsLengthParametrized.comp_homeomorph_symm
#print axioms weylScaling_comp_homeomorph

end HarmonicBalls
