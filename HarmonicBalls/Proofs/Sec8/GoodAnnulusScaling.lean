import HarmonicBalls.Proofs.Sec8.GoodRadiusScaling

/-! # Dilation of the good-annulus condition -/

open MeasureTheory Metric Set
open scoped ENNReal

namespace HarmonicBalls

/-- A positive dilation pulls back a closed ball with arbitrary center. -/
theorem preimage_inv_smul_closedBall {k : ℝ} (hk : 0 < k) (z : ℂ) (r : ℝ) :
    (fun x : ℂ => k⁻¹ • x) ⁻¹' closedBall z r = closedBall (k • z) (k * r) := by
  ext x
  simp only [mem_preimage, mem_closedBall, dist_eq_norm]
  have heq : k⁻¹ • x - z = k⁻¹ • (x - k • z) := by
    simp only [smul_sub, smul_smul, inv_mul_cancel₀ hk.ne', one_smul]
  rw [heq, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hk,
    inv_mul_le_iff₀ hk]

/-- A positive dilation pulls back a sphere with arbitrary center. -/
theorem preimage_inv_smul_sphere {k : ℝ} (hk : 0 < k) (z : ℂ) (r : ℝ) :
    (fun x : ℂ => k⁻¹ • x) ⁻¹' sphere z r = sphere (k • z) (k * r) := by
  ext x
  simp only [mem_preimage, mem_sphere, dist_eq_norm]
  have heq : k⁻¹ • x - z = k⁻¹ • (x - k • z) := by
    simp only [smul_sub, smul_smul, inv_mul_cancel₀ hk.ne', one_smul]
  rw [heq, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hk]
  rw [← div_eq_inv_mul, div_eq_iff hk.ne', mul_comm r k]

/-- A positive dilation pulls back an annulus with arbitrary center. -/
theorem preimage_inv_smul_annulus {k : ℝ} (hk : 0 < k) (z : ℂ) (a b : ℝ) :
    (fun x : ℂ => k⁻¹ • x) ⁻¹' annulus z a b = annulus (k • z) (k * a) (k * b) := by
  simp only [annulus, preimage_sdiff, preimage_inv_smul_ball hk,
    preimage_inv_smul_closedBall hk]

open MarkovProcess in
/-- The good-annulus condition is transported by dilation once Brownian
exit-event probabilities are transported for Borel test sets. -/
theorem isGoodAnnulus_map_inv_smul_of_exit_probability (μ : Measure ℂ)
    {k : ℝ} (hk : 0 < k) (r : ℝ) (z : ℂ) (a b : ℝ)
    (hprob : ∀ Y : Set ℂ, MeasurableSet Y → ∀ u : ℂ,
      planarBrownianMotion u
        {p | ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) p ≤
          ContinuousPath.exitTime Y p} =
      planarBrownianMotion (k • u)
        {p | ContinuousPath.exitTime (annulus (k • z) (3 * (k * r)) (5 * (k * r))) p ≤
          ContinuousPath.exitTime ((fun x : ℂ => k⁻¹ • x) ⁻¹' Y) p}) :
    IsGoodAnnulus (μ.map (fun x : ℂ => k⁻¹ • x)) r z a b ↔
      IsGoodAnnulus μ (k * r) (k • z) a b := by
  let f : ℂ → ℂ := fun x => k⁻¹ • x
  let g : ℂ → ℂ := fun x => k • x
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hg : Measurable g := by dsimp [g]; fun_prop
  have hfg (x : ℂ) : f (g x) = x := by
    simp only [f, g, smul_smul, inv_mul_cancel₀ hk.ne', one_smul]
  have hgf (x : ℂ) : g (f x) = x := by
    simp only [f, g, smul_smul, mul_inv_cancel₀ hk.ne', one_smul]
  have hback (Y : Set ℂ) : f ⁻¹' (g ⁻¹' Y) = Y := by
    ext x; simp only [mem_preimage, hgf]
  have hA : f ⁻¹' annulus z (3 * r) (5 * r) =
      annulus (k • z) (3 * (k * r)) (5 * (k * r)) := by
    rw [preimage_inv_smul_annulus hk]
    congr 1 <;> ring
  have hS : f ⁻¹' sphere z (4 * r) = sphere (k • z) (4 * (k * r)) := by
    rw [preimage_inv_smul_sphere hk]
    congr 1; ring
  have hAm : MeasurableSet (annulus z (3 * r) (5 * r)) :=
    (isOpen_ball.sdiff isClosed_closedBall).measurableSet
  have hmass : (μ.map f) (annulus z (3 * r) (5 * r)) =
      μ (annulus (k • z) (3 * (k * r)) (5 * (k * r))) := by
    rw [Measure.map_apply hf hAm, hA]
  change IsGoodAnnulus (μ.map f) r z a b ↔ IsGoodAnnulus μ (k * r) (k • z) a b
  unfold IsGoodAnnulus
  constructor
  · intro H Y hY hYA hsmall u hu
    have hY' : MeasurableSet (g ⁻¹' Y) := hg hY
    have hYA' : g ⁻¹' Y ⊆ annulus z (3 * r) (5 * r) := by
      intro x hx
      have ht : g x ∈ f ⁻¹' annulus z (3 * r) (5 * r) := by
        rw [hA]; exact hYA hx
      simpa only [mem_preimage, hfg] using ht
    have hsmall' : (μ.map f) (g ⁻¹' Y) ≤ ENNReal.ofReal a *
        (μ.map f) (annulus z (3 * r) (5 * r)) := by
      rwa [Measure.map_apply hf hY', hback, hmass]
    have hu' : f u ∈ sphere z (4 * r) := by
      have : u ∈ f ⁻¹' sphere z (4 * r) := by rwa [hS]
      exact this
    have ht := H (g ⁻¹' Y) hY' hYA' hsmall' (f u) hu'
    have hp := hprob (g ⁻¹' Y) hY' (f u)
    change planarBrownianMotion (f u) _ = planarBrownianMotion (g (f u)) _ at hp
    rw [hback, hgf] at hp
    exact hp ▸ ht
  · intro H Y hY hYA hsmall u hu
    have hY' : MeasurableSet (f ⁻¹' Y) := hf hY
    have hYA' : f ⁻¹' Y ⊆ annulus (k • z) (3 * (k * r)) (5 * (k * r)) := by
      rw [← hA]
      exact preimage_mono hYA
    have hsmall' : μ (f ⁻¹' Y) ≤ ENNReal.ofReal a *
        μ (annulus (k • z) (3 * (k * r)) (5 * (k * r))) := by
      rwa [← Measure.map_apply hf hY, ← hmass]
    have hu' : g u ∈ sphere (k • z) (4 * (k * r)) := by
      rw [← hS]
      simpa only [mem_preimage, hfg] using hu
    have ht := H (f ⁻¹' Y) hY' hYA' hsmall' (g u) hu'
    have hp := hprob Y hY u
    change planarBrownianMotion u _ = planarBrownianMotion (g u) _ at hp
    exact hp.symm ▸ ht

open MarkovProcess in
/-- Transport of Brownian exit probabilities yields transport of the complete
very-good-annulus event. -/
theorem isVeryGoodAnnulus_map_inv_smul_of_exit_probability (μ : Measure ℂ)
    {k : ℝ} (hk : 0 < k) (β ρ : ℝ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ : ℝ)
    (hprob : ∀ (r : ℝ) (z : ℂ) (Y : Set ℂ), MeasurableSet Y → ∀ u : ℂ,
      planarBrownianMotion u
        {p | ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) p ≤
          ContinuousPath.exitTime Y p} =
      planarBrownianMotion (k • u)
        {p | ContinuousPath.exitTime (annulus (k • z) (3 * (k * r)) (5 * (k * r))) p ≤
          ContinuousPath.exitTime ((fun x : ℂ => k⁻¹ • x) ⁻¹' Y) p}) :
    IsVeryGoodAnnulus (μ.map (fun x : ℂ => k⁻¹ • x)) β ρ 0 N₀
        a b C₁m C₁p C₂m C₂p C₃ ↔
      IsVeryGoodAnnulus μ β (k * ρ) 0 N₀ a b C₁m C₁p C₂m C₂p C₃ := by
  apply isVeryGoodAnnulus_map_inv_smul_of_good_transport μ hk
  intro r z
  exact isGoodAnnulus_map_inv_smul_of_exit_probability μ hk r z a b (hprob r z)

end HarmonicBalls
