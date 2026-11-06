import HarmonicBalls.Proofs.Sec5.SupersolutionScaling
import HarmonicBalls.Proofs.Sec6.GreenDilation
import HarmonicBalls.Proofs.Sec6.LaplacianTranslation
import HarmonicBalls.Proofs.Sec5.IrregularLeastSupersolution
import HarmonicBalls.Proofs.Sec5.PoleInfimumCharacterization

/-! # Affine covariance on general domains

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/

namespace HarmonicBalls

open MeasureTheory Set
open scoped Topology

/-- The Green kernel is invariant under a positive affine change of coordinates,
including on the diagonal where the kernel is defined to be zero. -/
theorem greenFunction_positive_affine (U : Set ℂ) (hU : Bornology.IsBounded U)
    {k : ℝ} (hk : 0 < k) (a x y : ℂ) :
    greenFunction ((fun z : ℂ => a + k • z) '' U) (a + k • x) (a + k • y) =
      greenFunction U x y := by
  have hset : (fun z : ℂ => a + k • z) '' U =
      (fun z : ℂ => z + a) '' ((fun z : ℂ => k • z) '' U) := by
    rw [Set.image_image]
    congr 1
    funext z
    simp only [add_comm]
  rw [hset, add_comm a (k • x), add_comm a (k • y),
    Section6.greenFunction_translate, Section6.greenFunction_dilation U hU hk]

/-- Pulling back a general-domain competitor by a dilation transports the
measure and the obstacle by the same positive factor. -/
theorem supersolutionsOn_comp_real_smul {μ : Measure ℂ} {U : Set ℂ}
    (hU : Bornology.IsBounded U) {k c t : ℝ} {z : ℂ}
    (hk : 0 < k) (hc : 0 < c) {w : ℂ → ℝ}
    (hw : w ∈ supersolutionsOn μ ((fun x : ℂ => k • x) '' U) (k • z) t) :
    (fun x => c * w (k • x)) ∈
      supersolutionsOn (ENNReal.ofReal c • Measure.map (fun x : ℂ => k⁻¹ • x) μ)
        U z (c * t) := by
  let e : ℂ ≃ₜ ℂ := Homeomorph.smulOfNeZero k hk.ne'
  have hset : (fun x : ℂ => k • x) ⁻¹' ((fun x : ℂ => k • x) '' U) = U :=
    Set.preimage_image_eq U (smul_right_injective ℂ hk.ne')
  have hclosure : ∀ x ∈ closure U, k • x ∈ closure ((fun x : ℂ => k • x) '' U) := by
    intro x hx
    exact image_closure_subset_closure_image e.continuous ⟨x, hx, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · exact continuousOn_const.mul (hw.1.comp (continuous_const_smul k).continuousOn hclosure)
  · have h := (hw.2.1.comp_real_smul hk).const_mul hc
    rwa [hset] at h
  · intro x hx hxz
    have hxz' : k • x ≠ k • z := fun h => hxz ((smul_right_injective ℂ hk.ne') h)
    have h := mul_le_mul_of_nonneg_left (hw.2.2 (k • x) (hclosure x hx) hxz') hc.le
    rw [Section6.greenFunction_dilation U hU hk] at h
    convert h using 1; ring

/-- Translation transports the distributional Laplacian inequality. -/
theorem LaplacianLE.comp_add_right {w : ℂ → ℝ} {μ : Measure ℂ} {U : Set ℂ}
    (hw : LaplacianLE w μ U) (b : ℂ) :
    LaplacianLE (fun z => w (z + b)) (Measure.map (fun z => z - b) μ)
      ((fun z : ℂ => z + b) ⁻¹' U) := by
  refine ⟨Section6.locallyIntegrableOn_comp_add_right hw.1 b, ?_⟩
  intro φ hφ hn hi
  let e : ℂ ≃ₜ ℂ := Homeomorph.addRight (-b)
  have ht : IsTestFunction U (fun z => φ (z - b)) := by
    have h := Section6.isTestFunction_comp_add_right hφ (-b)
    have heq : (fun z : ℂ => z + (-b)) ⁻¹' ((fun z : ℂ => z + b) ⁻¹' U) = U := by
      ext z
      simp only [mem_preimage, add_assoc, neg_add_cancel, add_zero]
    rw [heq] at h
    simpa only [sub_eq_add_neg] using h
  have hnonneg : 0 ≤ (fun z => φ (z - b)) := fun z => hn (z - b)
  have hint : Integrable (fun z => φ (z - b)) μ := by
    exact (integrable_map_equiv e.toMeasurableEquiv φ).mp hi
  have hineq := hw.2 _ ht hnonneg hint
  rw [Section6.integral_mul_laplacian_comp_add_right]
  convert hineq using 1
  exact integral_map_equiv e.toMeasurableEquiv φ

/-- Translation carries competitors to competitors with the translated measure. -/
theorem supersolutionsOn_comp_add_right {μ : Measure ℂ} {U : Set ℂ} {z : ℂ} {t : ℝ}
    (b : ℂ) {w : ℂ → ℝ}
    (hw : w ∈ supersolutionsOn μ ((fun x : ℂ => x + b) '' U) (z + b) t) :
    (fun x => w (x + b)) ∈
      supersolutionsOn (Measure.map (fun x : ℂ => x - b) μ) U z t := by
  have hset : (fun x : ℂ => x + b) ⁻¹' ((fun x : ℂ => x + b) '' U) = U :=
    Set.preimage_image_eq U (add_left_injective b)
  have hclosure : ∀ x ∈ closure U, x + b ∈ closure ((fun x : ℂ => x + b) '' U) := by
    intro x hx
    exact image_closure_subset_closure_image (continuous_id.add continuous_const) ⟨x, hx, rfl⟩
  refine ⟨hw.1.comp (continuous_id.add continuous_const).continuousOn hclosure, ?_, ?_⟩
  · have h := hw.2.1.comp_add_right b
    rwa [hset] at h
  · intro x hx hxz
    have h := hw.2.2 (x + b) (hclosure x hx) (by simpa using hxz)
    rwa [Section6.greenFunction_translate] at h

/-- Dilation and multiplication give the inverse competitor map. -/
theorem supersolutionsOn_comp_real_smul_inv {μ : Measure ℂ} {U : Set ℂ}
    (hU : Bornology.IsBounded U) {k c t : ℝ} {z : ℂ}
    (hk : 0 < k) (hc : 0 < c) {v : ℂ → ℝ}
    (hv : v ∈ supersolutionsOn
      (ENNReal.ofReal c • Measure.map (fun x : ℂ => k⁻¹ • x) μ) U z (c * t)) :
    (fun x => c⁻¹ * v (k⁻¹ • x)) ∈
      supersolutionsOn μ ((fun x : ℂ => k • x) '' U) (k • z) t := by
  have hset : (fun x : ℂ => k⁻¹ • x) '' ((fun x : ℂ => k • x) '' U) = U := by
    rw [Set.image_image]
    have hf : (fun x : ℂ => k⁻¹ • (k • x)) = id := by
      funext x
      simp only [smul_smul, inv_mul_cancel₀ hk.ne', one_smul, id_eq]
    rw [hf, Set.image_id]
  have hb : Bornology.IsBounded ((fun x : ℂ => k • x) '' U) :=
    hU.smul₀ k
  have hv' : v ∈ supersolutionsOn
      (ENNReal.ofReal c • Measure.map (fun x : ℂ => k⁻¹ • x) μ)
      ((fun x : ℂ => k⁻¹ • x) '' ((fun x : ℂ => k • x) '' U))
      (k⁻¹ • (k • z)) (c * t) := by
    simpa only [hset, smul_smul, inv_mul_cancel₀ hk.ne', one_smul] using hv
  have h := supersolutionsOn_comp_real_smul hb (inv_pos.mpr hk) (inv_pos.mpr hc) hv'
  simpa only [inv_inv, inverse_scaled_measure hk hc, ← mul_assoc,
    inv_mul_cancel₀ hc.ne', one_mul] using h

/-- The general-domain least supersolution scales at closed-domain points away
from the pole, where the frozen real infimum is bounded below. -/
theorem leastSupersolutionOn_comp_real_smul {μ : Measure ℂ} {U : Set ℂ}
    (hU : Bornology.IsBounded U) {k c t : ℝ} {z x : ℂ}
    (hk : 0 < k) (hc : 0 < c) (ht : 0 ≤ t)
    (hx : x ∈ closure U) (hxz : x ≠ z) :
    leastSupersolutionOn (ENNReal.ofReal c • Measure.map (fun y : ℂ => k⁻¹ • y) μ)
      U z (c * t) x = c * leastSupersolutionOn μ ((fun y : ℂ => k • y) '' U)
        (k • z) t (k • x) := by
  let S := (fun w : ℂ → ℝ => w (k • x)) ''
    supersolutionsOn μ ((fun y : ℂ => k • y) '' U) (k • z) t
  have heq : (fun v : ℂ → ℝ => v x) ''
      supersolutionsOn (ENNReal.ofReal c • Measure.map (fun y : ℂ => k⁻¹ • y) μ)
        U z (c * t) = (fun a : ℝ => c * a) '' S := by
    ext a
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨(fun y => c⁻¹ * v (k⁻¹ • y)) (k • x),
        ⟨_, supersolutionsOn_comp_real_smul_inv hU hk hc hv, rfl⟩, ?_⟩
      simp only [smul_smul, inv_mul_cancel₀ hk.ne', one_smul, ← mul_assoc,
        mul_inv_cancel₀ hc.ne', one_mul]
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨fun y => c * w (k • y), supersolutionsOn_comp_real_smul hU hk hc hw, rfl⟩
  have hb : Bornology.IsBounded ((fun y : ℂ => k • y) '' U) := hU.smul₀ k
  have hxc : k • x ∈ closure ((fun y : ℂ => k • y) '' U) :=
    image_closure_subset_closure_image (continuous_const_smul k) ⟨x, hx, rfl⟩
  have hxz' : k • x ≠ k • z := fun h => hxz ((smul_right_injective ℂ hk.ne') h)
  have hnonempty : S.Nonempty := ⟨0, 0, zero_mem_supersolutionsOn hb ht, rfl⟩
  have hbdd : BddBelow S := ⟨-t * greenFunction ((fun y : ℂ => k • y) '' U)
      (k • z) (k • x), by
    rintro _ ⟨w, hw, rfl⟩
    exact hw.2.2 (k • x) hxc hxz'⟩
  have hiso := (OrderIso.mulLeft₀ c hc).map_csInf' hnonempty hbdd
  change c * sInf S = sInf ((fun a : ℝ => c * a) '' S) at hiso
  change sInf _ = c * sInf S
  rw [heq]
  exact hiso.symm

/-- General-domain cluster covariance under dilation, with the pole handled
by its explicit branch in the definition. -/
theorem clusterOn_comp_real_smul {μ : Measure ℂ} {U : Set ℂ}
    (hU : Bornology.IsBounded U) {k c t : ℝ} {z : ℂ}
    (hk : 0 < k) (hc : 0 < c) (ht : 0 ≤ t) :
    clusterOn (ENNReal.ofReal c • Measure.map (fun x : ℂ => k⁻¹ • x) μ) U z (c * t) =
      (fun x : ℂ => k • x) ⁻¹'
        clusterOn μ ((fun x : ℂ => k • x) '' U) (k • z) t := by
  ext x
  have hm : k • x ∈ (fun y : ℂ => k • y) '' U ↔ x ∈ U := by
    constructor
    · rintro ⟨y, hy, heq⟩
      exact (smul_right_injective ℂ hk.ne' heq) ▸ hy
    · exact fun hx => ⟨x, hx, rfl⟩
  have hp : k • x = k • z ↔ x = z := (smul_right_injective ℂ hk.ne').eq_iff
  simp only [clusterOn, mem_ofPred_eq, mem_preimage, hm, hp]
  by_cases hx : x ∈ U
  · by_cases hxz : x = z
    · simp [hxz]
    · simp only [hx, hxz, false_or, true_and]
      rw [leastSupersolutionOn_comp_real_smul hU hk hc ht (subset_closure hx) hxz,
        Section6.greenFunction_dilation U hU hk]
      have hobs : -(c * t) * greenFunction U z x = c * (-t * greenFunction U z x) := by ring
      rw [hobs]
      exact mul_lt_mul_iff_right₀ hc
  · simp [hx]

/-- The inverse translation gives the reverse map on competitors. -/
theorem supersolutionsOn_comp_add_right_inv {μ : Measure ℂ} {U : Set ℂ} {z : ℂ} {t : ℝ}
    (b : ℂ) {v : ℂ → ℝ}
    (hv : v ∈ supersolutionsOn (Measure.map (fun x : ℂ => x - b) μ) U z t) :
    (fun x => v (x - b)) ∈ supersolutionsOn μ ((fun x : ℂ => x + b) '' U) (z + b) t := by
  have hset : (fun x : ℂ => x + -b) '' ((fun x : ℂ => x + b) '' U) = U := by
    rw [Set.image_image]
    have hf : (fun x : ℂ => (x + b) + -b) = id := by
      funext x
      simp
    rw [hf, Set.image_id]
  have hv' : v ∈ supersolutionsOn (Measure.map (fun x : ℂ => x - b) μ)
      ((fun x : ℂ => x + -b) '' ((fun x : ℂ => x + b) '' U)) ((z + b) + -b) t := by
    rw [hset]
    simpa only [add_assoc, add_neg_cancel, add_zero] using hv
  have h := supersolutionsOn_comp_add_right (-b) hv'
  have hmap : Measure.map (fun x : ℂ => x - -b) (Measure.map (fun x : ℂ => x - b) μ) = μ := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    have hf : (fun x : ℂ => x - -b) ∘ (fun x : ℂ => x - b) = id := by
      funext x
      simp
    rw [hf, Measure.map_id]
  rw [hmap] at h
  simpa only [sub_eq_add_neg] using h

/-- Translation of the real infimum at closed-domain points off the pole. -/
theorem leastSupersolutionOn_comp_add_right {μ : Measure ℂ} {U : Set ℂ}
    {z x : ℂ} {t : ℝ} (b : ℂ) :
    leastSupersolutionOn (Measure.map (fun y : ℂ => y - b) μ) U z t x =
      leastSupersolutionOn μ ((fun y : ℂ => y + b) '' U) (z + b) t (x + b) := by
  have heq : (fun v : ℂ → ℝ => v x) ''
      supersolutionsOn (Measure.map (fun y : ℂ => y - b) μ) U z t =
      (fun w : ℂ → ℝ => w (x + b)) ''
        supersolutionsOn μ ((fun y : ℂ => y + b) '' U) (z + b) t := by
    ext a
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨fun y => v (y - b), supersolutionsOn_comp_add_right_inv b hv, by simp⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨fun y => w (y + b), supersolutionsOn_comp_add_right b hw, rfl⟩
  exact congrArg sInf heq

/-- Translation of general-domain clusters, including the pole. -/
theorem clusterOn_comp_add_right {μ : Measure ℂ} {U : Set ℂ}
    {z : ℂ} {t : ℝ} (b : ℂ) :
    clusterOn (Measure.map (fun x : ℂ => x - b) μ) U z t =
      (fun x : ℂ => x + b) ⁻¹' clusterOn μ ((fun x : ℂ => x + b) '' U) (z + b) t := by
  ext x
  have hm : x + b ∈ (fun y : ℂ => y + b) '' U ↔ x ∈ U := by
    constructor
    · rintro ⟨y, hy, heq⟩
      exact (add_right_cancel heq) ▸ hy
    · exact fun hx => ⟨x, hx, rfl⟩
  simp only [clusterOn, mem_ofPred_eq, mem_preimage, hm, add_right_cancel_iff]
  by_cases hx : x ∈ U
  · by_cases hxz : x = z
    · simp [hxz]
    · simp only [hx, hxz, false_or, true_and]
      rw [leastSupersolutionOn_comp_add_right b,
        Section6.greenFunction_translate]
  · simp [hx]

/-- Dilation in the pushforward direction. -/
theorem clusterOn_map_real_smul {μ : Measure ℂ} {U : Set ℂ}
    (hU : Bornology.IsBounded U) {k c t : ℝ} {z : ℂ}
    (hk : 0 < k) (hc : 0 < c) (ht : 0 ≤ t) :
    clusterOn (ENNReal.ofReal c • Measure.map (fun x : ℂ => k • x) μ)
      ((fun x : ℂ => k • x) '' U) (k • z) (c * t) =
        (fun x : ℂ => k • x) '' clusterOn μ U z t := by
  have hset : (fun x : ℂ => k⁻¹ • x) '' ((fun x : ℂ => k • x) '' U) = U := by
    rw [Set.image_image]
    have hf : (fun x : ℂ => k⁻¹ • (k • x)) = id := by
      funext x
      simp only [smul_smul, inv_mul_cancel₀ hk.ne', one_smul, id_eq]
    rw [hf, Set.image_id]
  have h := clusterOn_comp_real_smul (μ := μ) (U := (fun x : ℂ => k • x) '' U)
    (z := k • z) (k := k⁻¹) (c := c) (t := t) (hU.smul₀ k)
    (inv_pos.mpr hk) hc ht
  rw [hset] at h
  simp only [inv_inv, smul_smul, inv_mul_cancel₀ hk.ne', one_smul] at h
  rw [h]
  ext x
  constructor
  · intro hx
    refine ⟨k⁻¹ • x, hx, ?_⟩
    simp only [smul_smul, mul_inv_cancel₀ hk.ne', one_smul]
  · rintro ⟨y, hy, rfl⟩
    simpa only [mem_preimage, smul_smul, inv_mul_cancel₀ hk.ne', one_smul] using hy

/-- Translation in the pushforward direction. -/
theorem clusterOn_map_add_right {μ : Measure ℂ} {U : Set ℂ} {z : ℂ} {t : ℝ} (b : ℂ) :
    clusterOn (Measure.map (fun x : ℂ => x + b) μ) ((fun x : ℂ => x + b) '' U)
      (z + b) t = (fun x : ℂ => x + b) '' clusterOn μ U z t := by
  have hset : (fun x : ℂ => x + -b) '' ((fun x : ℂ => x + b) '' U) = U := by
    rw [Set.image_image]
    have hf : (fun x : ℂ => (x + b) + -b) = id := by
      funext x
      simp
    rw [hf, Set.image_id]
  have h := clusterOn_comp_add_right (μ := μ) (U := (fun x : ℂ => x + b) '' U)
    (z := z + b) (t := t) (-b)
  rw [hset] at h
  simp only [sub_neg_eq_add, add_assoc, add_neg_cancel, add_zero] at h
  rw [h]
  ext x
  constructor
  · intro hx
    refine ⟨x - b, hx, ?_⟩
    simp
  · rintro ⟨y, hy, rfl⟩
    simpa only [mem_preimage, add_assoc, add_neg_cancel, add_zero] using hy

/-- Deterministic affine covariance of the actual general-domain cluster. -/
theorem clusterOn_positive_affine {μ : Measure ℂ} {U : Set ℂ}
    (hU : Bornology.IsBounded U) {k c t : ℝ} {z : ℂ}
    (hk : 0 < k) (hc : 0 < c) (ht : 0 ≤ t) (a : ℂ) :
    clusterOn (ENNReal.ofReal c • Measure.map (fun x : ℂ => a + k • x) μ)
      ((fun x : ℂ => a + k • x) '' U) (a + k • z) (c * t) =
        (fun x : ℂ => a + k • x) '' clusterOn μ U z t := by
  have h := clusterOn_map_add_right (μ := ENNReal.ofReal c •
    Measure.map (fun x : ℂ => k • x) μ)
    (U := (fun x : ℂ => k • x) '' U) (z := k • z) (t := c * t) a
  rw [clusterOn_map_real_smul hU hk hc ht] at h
  rw [Measure.map_smul _ (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)] at h
  simp only [Set.image_image, Function.comp_def, add_comm] at h
  exact h

/-- The off-pole least-supersolution identity in pushforward form. -/
theorem leastSupersolutionOn_map_real_smul {μ : Measure ℂ} {U : Set ℂ}
    (hU : Bornology.IsBounded U) {k c t : ℝ} {z x : ℂ}
    (hk : 0 < k) (hc : 0 < c) (ht : 0 ≤ t)
    (hx : x ∈ closure U) (hxz : x ≠ z) :
    leastSupersolutionOn (ENNReal.ofReal c • Measure.map (fun y : ℂ => k • y) μ)
      ((fun y : ℂ => k • y) '' U) (k • z) (c * t) (k • x) =
        c * leastSupersolutionOn μ U z t x := by
  have hset : (fun y : ℂ => k⁻¹ • y) '' ((fun y : ℂ => k • y) '' U) = U := by
    rw [Set.image_image]
    have hf : (fun y : ℂ => k⁻¹ • (k • y)) = id := by
      funext y
      simp only [smul_smul, inv_mul_cancel₀ hk.ne', one_smul, id_eq]
    rw [hf, Set.image_id]
  have hxc : k • x ∈ closure ((fun y : ℂ => k • y) '' U) :=
    image_closure_subset_closure_image (continuous_const_smul k) ⟨x, hx, rfl⟩
  have hxz' : k • x ≠ k • z := fun h => hxz ((smul_right_injective ℂ hk.ne') h)
  have h := leastSupersolutionOn_comp_real_smul (μ := μ)
    (U := (fun y : ℂ => k • y) '' U) (z := k • z) (x := k • x)
    (k := k⁻¹) (c := c) (t := t) (hU.smul₀ k) (inv_pos.mpr hk) hc ht hxc hxz'
  rw [hset] at h
  simpa only [inv_inv, smul_smul, inv_mul_cancel₀ hk.ne', one_smul] using h

/-- Affine covariance of the least supersolution away from the pole. -/
theorem leastSupersolutionOn_positive_affine {μ : Measure ℂ} {U : Set ℂ}
    (hU : Bornology.IsBounded U) {k c t : ℝ} {z x : ℂ}
    (hk : 0 < k) (hc : 0 < c) (ht : 0 ≤ t)
    (hx : x ∈ closure U) (hxz : x ≠ z) (a : ℂ) :
    leastSupersolutionOn (ENNReal.ofReal c • Measure.map (fun y : ℂ => a + k • y) μ)
      ((fun y : ℂ => a + k • y) '' U) (a + k • z) (c * t) (a + k • x) =
        c * leastSupersolutionOn μ U z t x := by
  have h := leastSupersolutionOn_comp_add_right
    (μ := ENNReal.ofReal c • Measure.map (fun y : ℂ => k • y) μ)
    (U := (fun y : ℂ => y + a) '' ((fun y : ℂ => k • y) '' U))
    (z := k • z + a) (x := k • x + a) (t := c * t) (-a)
  have hset : (fun y : ℂ => y + -a) '' ((fun y : ℂ => y + a) ''
      ((fun y : ℂ => k • y) '' U)) = (fun y : ℂ => k • y) '' U := by
    rw [Set.image_image]
    have hf : (fun y : ℂ => (y + a) + -a) = id := by
      funext y
      simp
    rw [hf, Set.image_id]
  rw [hset] at h
  simp only [sub_neg_eq_add, add_assoc] at h
  rw [Measure.map_smul _ (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)] at h
  simp only [Set.image_image, Function.comp_def, add_comm] at h
  rw [h]
  simp only [add_neg_cancel, add_zero]
  exact leastSupersolutionOn_map_real_smul hU hk hc ht hx hxz

/-- The off-pole odometer scales with the mass factor. -/
theorem odometerOn_positive_affine {μ : Measure ℂ} {U : Set ℂ}
    (hU : Bornology.IsBounded U) {k c t : ℝ} {z x : ℂ}
    (hk : 0 < k) (hc : 0 < c) (ht : 0 ≤ t)
    (hx : x ∈ closure U) (hxz : x ≠ z) (a : ℂ) :
    leastSupersolutionOn (ENNReal.ofReal c • Measure.map (fun y : ℂ => a + k • y) μ)
      ((fun y : ℂ => a + k • y) '' U) (a + k • z) (c * t) (a + k • x) +
      (c * t) * greenFunction ((fun y : ℂ => a + k • y) '' U) (a + k • z) (a + k • x) =
    c * (leastSupersolutionOn μ U z t x + t * greenFunction U z x) := by
  rw [leastSupersolutionOn_positive_affine hU hk hc ht hx hxz,
    greenFunction_positive_affine U hU hk]
  ring

/-- Pullback by an affine map and multiplication transport a competitor. -/
theorem supersolutionsOn_comp_positive_affine {μ : Measure ℂ} {U : Set ℂ}
    (hU : Bornology.IsBounded U) {k c t : ℝ} {z : ℂ}
    (hk : 0 < k) (hc : 0 < c) (a : ℂ) {w : ℂ → ℝ}
    (hw : w ∈ supersolutionsOn μ ((fun x : ℂ => a + k • x) '' U) (a + k • z) t) :
    (fun x => c * w (a + k • x)) ∈
      supersolutionsOn (ENNReal.ofReal c • Measure.map (fun x : ℂ => k⁻¹ • (x - a)) μ)
        U z (c * t) := by
  have hw' : w ∈ supersolutionsOn μ
      ((fun x : ℂ => x + a) '' ((fun x : ℂ => k • x) '' U)) (k • z + a) t := by
    simpa only [Set.image_image, Function.comp_def, add_comm] using hw
  have ht := supersolutionsOn_comp_add_right a hw'
  have h := supersolutionsOn_comp_real_smul hU hk hc ht
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at h
  simpa only [Function.comp_def, add_comm] using h

/-- The inverse affine transformation maps competitors back, giving the
bijection with `supersolutionsOn_comp_positive_affine`. -/
theorem supersolutionsOn_comp_positive_affine_inv {μ : Measure ℂ} {U : Set ℂ}
    (hU : Bornology.IsBounded U) {k c t : ℝ} {z : ℂ}
    (hk : 0 < k) (hc : 0 < c) (a : ℂ) {v : ℂ → ℝ}
    (hv : v ∈ supersolutionsOn
      (ENNReal.ofReal c • Measure.map (fun x : ℂ => k⁻¹ • (x - a)) μ) U z (c * t)) :
    (fun x => c⁻¹ * v (k⁻¹ • (x - a))) ∈
      supersolutionsOn μ ((fun x : ℂ => a + k • x) '' U) (a + k • z) t := by
  have hv' : v ∈ supersolutionsOn (ENNReal.ofReal c •
      Measure.map (fun x : ℂ => k⁻¹ • x) (Measure.map (fun x : ℂ => x - a) μ))
      U z (c * t) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    exact hv
  have h := supersolutionsOn_comp_real_smul_inv hU hk hc hv'
  have h' := supersolutionsOn_comp_add_right_inv a h
  simpa only [Set.image_image, Function.comp_def, add_comm] using h'

/-- Infimum covariance at any point whose competitor values are bounded below,
including the pole when an independent potential estimate supplies that bound. -/
theorem leastSupersolutionOn_comp_real_smul_of_bddBelow {μ : Measure ℂ} {U : Set ℂ}
    (hU : Bornology.IsBounded U) {k c t : ℝ} {z x : ℂ}
    (hk : 0 < k) (hc : 0 < c) (ht : 0 ≤ t)
    (hbdd : BddBelow ((fun w : ℂ → ℝ => w (k • x)) ''
      supersolutionsOn μ ((fun y : ℂ => k • y) '' U) (k • z) t)) :
    leastSupersolutionOn (ENNReal.ofReal c • Measure.map (fun y : ℂ => k⁻¹ • y) μ)
      U z (c * t) x = c * leastSupersolutionOn μ ((fun y : ℂ => k • y) '' U)
        (k • z) t (k • x) := by
  let S := (fun w : ℂ → ℝ => w (k • x)) ''
    supersolutionsOn μ ((fun y : ℂ => k • y) '' U) (k • z) t
  have heq : (fun v : ℂ → ℝ => v x) ''
      supersolutionsOn (ENNReal.ofReal c • Measure.map (fun y : ℂ => k⁻¹ • y) μ)
        U z (c * t) = (fun a : ℝ => c * a) '' S := by
    ext a
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨(fun y => c⁻¹ * v (k⁻¹ • y)) (k • x),
        ⟨_, supersolutionsOn_comp_real_smul_inv hU hk hc hv, rfl⟩, ?_⟩
      simp only [smul_smul, inv_mul_cancel₀ hk.ne', one_smul, ← mul_assoc,
        mul_inv_cancel₀ hc.ne', one_mul]
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨fun y => c * w (k • y), supersolutionsOn_comp_real_smul hU hk hc hw, rfl⟩
  have hnonempty : S.Nonempty := ⟨0, 0, zero_mem_supersolutionsOn (hU.smul₀ k) ht, rfl⟩
  have hiso := (OrderIso.mulLeft₀ c hc).map_csInf' hnonempty hbdd
  change c * sInf S = sInf ((fun a : ℝ => c * a) '' S) at hiso
  change sInf _ = c * sInf S
  rw [heq]
  exact hiso.symm

theorem leastSupersolutionOn_map_real_smul_of_bddBelow {μ : Measure ℂ} {U : Set ℂ}
    (hU : Bornology.IsBounded U) {k c t : ℝ} {z x : ℂ}
    (hk : 0 < k) (hc : 0 < c) (ht : 0 ≤ t)
    (hbdd : BddBelow ((fun w : ℂ → ℝ => w x) '' supersolutionsOn μ U z t)) :
    leastSupersolutionOn (ENNReal.ofReal c • Measure.map (fun y : ℂ => k • y) μ)
      ((fun y : ℂ => k • y) '' U) (k • z) (c * t) (k • x) =
        c * leastSupersolutionOn μ U z t x := by
  have hset : (fun y : ℂ => k⁻¹ • y) '' ((fun y : ℂ => k • y) '' U) = U := by
    rw [Set.image_image]
    have hf : (fun y : ℂ => k⁻¹ • (k • y)) = id := by
      funext y
      simp only [smul_smul, inv_mul_cancel₀ hk.ne', one_smul, id_eq]
    rw [hf, Set.image_id]
  have hbdd' : BddBelow ((fun w : ℂ → ℝ => w (k⁻¹ • (k • x))) ''
      supersolutionsOn μ ((fun y : ℂ => k⁻¹ • y) '' ((fun y : ℂ => k • y) '' U))
        (k⁻¹ • (k • z)) t) := by
    simpa only [hset, smul_smul, inv_mul_cancel₀ hk.ne', one_smul] using hbdd
  have h := leastSupersolutionOn_comp_real_smul_of_bddBelow (μ := μ)
    (U := (fun y : ℂ => k • y) '' U) (z := k • z) (x := k • x)
    (k := k⁻¹) (c := c) (t := t) (hU.smul₀ k) (inv_pos.mpr hk) hc ht hbdd'
  rw [hset] at h
  simpa only [inv_inv, smul_smul, inv_mul_cancel₀ hk.ne', one_smul] using h


theorem leastSupersolutionOn_positive_affine_of_bddBelow {μ : Measure ℂ} {U : Set ℂ}
    (hU : Bornology.IsBounded U) {k c t : ℝ} {z x : ℂ}
    (hk : 0 < k) (hc : 0 < c) (ht : 0 ≤ t)
    (hbdd : BddBelow ((fun w : ℂ → ℝ => w x) '' supersolutionsOn μ U z t)) (a : ℂ) :
    leastSupersolutionOn (ENNReal.ofReal c • Measure.map (fun y : ℂ => a + k • y) μ)
      ((fun y : ℂ => a + k • y) '' U) (a + k • z) (c * t) (a + k • x) =
        c * leastSupersolutionOn μ U z t x := by
  have h := leastSupersolutionOn_comp_add_right
    (μ := ENNReal.ofReal c • Measure.map (fun y : ℂ => k • y) μ)
    (U := (fun y : ℂ => y + a) '' ((fun y : ℂ => k • y) '' U))
    (z := k • z + a) (x := k • x + a) (t := c * t) (-a)
  have hset : (fun y : ℂ => y + -a) '' ((fun y : ℂ => y + a) ''
      ((fun y : ℂ => k • y) '' U)) = (fun y : ℂ => k • y) '' U := by
    rw [Set.image_image]
    have hf : (fun y : ℂ => (y + a) + -a) = id := by
      funext y
      simp
    rw [hf, Set.image_id]
  rw [hset] at h
  simp only [sub_neg_eq_add, add_assoc] at h
  rw [Measure.map_smul _ (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)] at h
  simp only [Set.image_image, Function.comp_def, add_comm] at h
  rw [h]
  simp only [add_neg_cancel, add_zero]
  exact leastSupersolutionOn_map_real_smul_of_bddBelow hU hk hc ht hbdd


/-- At the pole the affine infimum identity follows from the standard
local-finiteness and volume-growth estimate. -/
theorem leastSupersolutionOn_positive_affine_at_pole {μ : Measure ℂ}
    (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ} (hR : 0 < R)
    (hV : VolumeGrowth μ R βm βp) {U : Set ℂ} (hU : IsOpen U)
    (hsub : U ⊆ Metric.ball (0 : ℂ) R) {k c t : ℝ} {z : ℂ} (hz : z ∈ U)
    (hk : 0 < k) (hc : 0 < c) (ht : 0 ≤ t) (a : ℂ) :
    leastSupersolutionOn (ENNReal.ofReal c • Measure.map (fun y : ℂ => a + k • y) μ)
      ((fun y : ℂ => a + k • y) '' U) (a + k • z) (c * t) (a + k • z) =
        c * leastSupersolutionOn μ U z t z :=
  leastSupersolutionOn_positive_affine_of_bddBelow (Metric.isBounded_ball.subset hsub)
    hk hc ht (bddBelow_supersolutionsOn_values_pole hμ hR hV hU hsub hz) a

#print axioms greenFunction_positive_affine
#print axioms supersolutionsOn_comp_real_smul
#print axioms LaplacianLE.comp_add_right
#print axioms supersolutionsOn_comp_add_right
#print axioms supersolutionsOn_comp_real_smul_inv
#print axioms leastSupersolutionOn_comp_real_smul
#print axioms clusterOn_comp_real_smul
#print axioms supersolutionsOn_comp_add_right_inv
#print axioms leastSupersolutionOn_comp_add_right
#print axioms clusterOn_comp_add_right
#print axioms clusterOn_map_real_smul
#print axioms clusterOn_map_add_right
#print axioms clusterOn_positive_affine
#print axioms leastSupersolutionOn_positive_affine
#print axioms odometerOn_positive_affine
#print axioms supersolutionsOn_comp_positive_affine
#print axioms supersolutionsOn_comp_positive_affine_inv
#print axioms leastSupersolutionOn_comp_real_smul_of_bddBelow
#print axioms leastSupersolutionOn_positive_affine_of_bddBelow
#print axioms leastSupersolutionOn_positive_affine_at_pole

end HarmonicBalls
