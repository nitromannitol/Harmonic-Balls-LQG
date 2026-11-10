import HarmonicBalls.FirstPass.S11i.CertMeasurable
import HarmonicBalls.Steps.Sec11.MetricConstantScaling
import HarmonicBalls.Steps.Sec11.AnnulusGreenDilation

/-!
# Dilation covariance of the certificate event (fp-S11i, owner n3)

Deterministic part of Step 9 of `CHATGPT-n3-Q1-eq34.md` section 5: the rescaled pair `(c • μ.map (· / R), b D(R·, R·))`
has the certificate event at `(z, r)` iff the original pair has it at `(R z, R r)`. The mass and annulus-potential
scalings are `c`, the metric scaling is `b` (both factors cancel in the strict inequalities).

Existing inputs (no new mathematics): `internalMetric_const_mul`, `setDist_const_mul`, `internalMetric_comp_homeomorph`,
`setDist_comp_homeomorph`, `internalDiam_rescaledSet_eq`, `annulusGreenPotentialSup_comp_real_smul_measure`.
-/

namespace HarmonicBalls.FirstPassS11iCertDilate

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal Pointwise
open HarmonicBalls FirstPassS11i

/-- The image of a rescaled set under the dilation `x ↦ R x` is the rescaled set at `(R r, R z)`. -/
lemma image_rescaledSet_mul (R r : ℝ) (z : ℂ) (K : Set ℂ) :
    (fun x : ℂ => (R : ℂ) * x) '' rescaledSet K r z = rescaledSet K (R * r) ((R : ℂ) * z) := by
  ext w
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, by push_cast; ring⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(r : ℂ) * x + z, ⟨x, hx, rfl⟩, by push_cast; ring⟩

/-- The image of a sphere under the dilation `x ↦ R x`, `R > 0`, is the sphere of radius `R s` about `R z`. -/
lemma image_sphere_mul {R : ℝ} (hR : 0 < R) (s : ℝ) (z : ℂ) :
    (fun x : ℂ => (R : ℂ) * x) '' sphere z s = sphere ((R : ℂ) * z) (R * s) := by
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : dist x z = s := hx
    show dist ((R : ℂ) * x) ((R : ℂ) * z) = R * s
    rw [Complex.dist_eq, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le,
      ← Complex.dist_eq, hx']
  · intro hw
    have hw' : dist w ((R : ℂ) * z) = R * s := hw
    refine ⟨w / (R : ℂ), ?_, by field_simp⟩
    show dist (w / (R : ℂ)) z = s
    have e : w / (R : ℂ) - z = (w - (R : ℂ) * z) / (R : ℂ) := by field_simp
    rw [Complex.dist_eq, e, norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le, ← Complex.dist_eq, hw']
    field_simp

/-- Measure of a rescaled set under the rescaled mass `c • μ.map (· / R)`. -/
lemma smul_map_div_apply_rescaledSet (μ : Measure ℂ) {a R : ℝ} (hR : 0 < R) (r : ℝ) (z : ℂ)
    (U : Set ℂ) :
    (ENNReal.ofReal a • μ.map (fun w : ℂ => w / (R : ℂ))) (rescaledSet U r z) =
      ENNReal.ofReal a * μ (rescaledSet U (R * r) ((R : ℂ) * z)) := by
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  let g : ℂ ≃ₜ ℂ := Homeomorph.mulLeft₀ (R : ℂ)⁻¹ (inv_ne_zero hRc)
  have hg : (fun w : ℂ => w / (R : ℂ)) = g := by
    funext w
    simp [g, div_eq_inv_mul]
  have hpre : g ⁻¹' rescaledSet U r z = rescaledSet U (R * r) ((R : ℂ) * z) := by
    ext w
    constructor
    · rintro ⟨x, hx, hxw⟩
      refine ⟨x, hx, ?_⟩
      have hw : (R : ℂ)⁻¹ * w = (r : ℂ) * x + z := by
        have h1 : (R : ℂ)⁻¹ * w = g w := rfl
        rw [h1]
        exact hxw.symm
      have hw2 : w = (R : ℂ) * ((r : ℂ) * x + z) := by
        rw [← hw]
        field_simp
      push_cast
      rw [hw2]
      ring
    · rintro ⟨x, hx, hxw⟩
      refine ⟨x, hx, ?_⟩
      have hw : w = (R : ℂ) * ((r : ℂ) * x + z) := by
        rw [← hxw]
        push_cast
        ring
      show (r : ℂ) * x + z = (R : ℂ)⁻¹ * w
      rw [hw]
      field_simp
  rw [Measure.smul_apply, smul_eq_mul, hg, MeasurableEmbedding.map_apply g.measurableEmbedding, hpre]

/-- The dilation `w ↦ R w` of `ℂ` as a homeomorphism, for `R > 0`. -/
noncomputable def dilH (R : ℝ) (hR : 0 < R) : ℂ ≃ₜ ℂ :=
  Homeomorph.mulLeft₀ (R : ℂ) (by exact_mod_cast hR.ne')

/-- The `δ`-neighbourhood of `A` is carried by `w ↦ R w` to the `(R δ)`-neighbourhood of the image. -/
lemma image_thickening_dilate {R : ℝ} (hR : 0 < R) (δ : ℝ) (A : Set ℂ) :
    (fun w : ℂ => (R : ℂ) * w) '' thickening δ A =
      thickening (R * δ) ((fun w : ℂ => (R : ℂ) * w) '' A) := by
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨a, ha, hxa⟩ := mem_thickening_iff.1 hx
    refine mem_thickening_iff.2 ⟨(R : ℂ) * a, ⟨a, ha, rfl⟩, ?_⟩
    show dist ((R : ℂ) * x) ((R : ℂ) * a) < R * δ
    rw [Complex.dist_eq, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le,
      ← Complex.dist_eq]
    exact mul_lt_mul_of_pos_left hxa hR
  · intro hy
    obtain ⟨w, ⟨a, ha, rfl⟩, hd⟩ := mem_thickening_iff.1 hy
    have hd' : dist y ((R : ℂ) * a) < R * δ := hd
    refine ⟨y / (R : ℂ), mem_thickening_iff.2 ⟨a, ha, ?_⟩, by field_simp⟩
    have e : y / (R : ℂ) - a = (y - (R : ℂ) * a) / (R : ℂ) := by field_simp
    rw [Complex.dist_eq] at hd' ⊢
    rw [e, norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le, div_lt_iff₀ hR, mul_comm δ R]
    exact hd'

/-- Metric of the dilated pair: `D_{bD(R·,R·)}(U; x, y) = b · D(R U; R x, R y)` (scaling and homeomorphism
invariance of the internal metric). -/
lemma internalMetric_dilate (D : ℂ → ℂ → ℝ) {b R : ℝ} (hb : 0 < b) (hR : 0 < R) (U : Set ℂ) (x y : ℂ) :
    internalMetric (fun x y => b * D ((R : ℂ) * x) ((R : ℂ) * y)) U x y =
      ENNReal.ofReal b * internalMetric D ((fun w : ℂ => (R : ℂ) * w) '' U) ((R : ℂ) * x) ((R : ℂ) * y) := by
  have h := internalMetric_comp_homeomorph (fun x y => b * D x y) (dilH R hR) U x y
  rw [internalMetric_const_mul D hb] at h
  exact h

/-- Supremum of the internal metric from the centre over a sphere (the quantity `A` of rule [C43]). -/
lemma iSup_internalMetric_dilate (D : ℂ → ℂ → ℝ) {b R : ℝ} (hb : 0 < b) (hR : 0 < R) (U : Set ℂ)
    (z : ℂ) (s : ℝ) :
    (⨆ x ∈ sphere z s, internalMetric (fun x y => b * D ((R : ℂ) * x) ((R : ℂ) * y)) U z x) =
      ENNReal.ofReal b * ⨆ y ∈ sphere ((R : ℂ) * z) (R * s),
        internalMetric D ((fun w : ℂ => (R : ℂ) * w) '' U) ((R : ℂ) * z) y := by
  simp only [internalMetric_dilate D hb hR, ENNReal.mul_iSup]
  rw [← image_sphere_mul hR s z, iSup_image]

/-- Internal diameter under the dilated metric (`diam^δ`, Draft line 3252). -/
lemma internalDiam_dilate (D : ℂ → ℂ → ℝ) {b R : ℝ} (hb : 0 < b) (hR : 0 < R) (δ : ℝ) (A : Set ℂ) :
    internalDiam (fun x y => b * D ((R : ℂ) * x) ((R : ℂ) * y)) δ A =
      ENNReal.ofReal b * internalDiam D (R * δ) ((fun w : ℂ => (R : ℂ) * w) '' A) := by
  unfold internalDiam
  simp only [internalMetric_dilate D hb hR, ENNReal.mul_iSup, image_thickening_dilate hR δ A, iSup_image]

/-- Internal diameter of a rescaled set with buffer `r η` (the diameters of rules E₁, E₂, E₃). -/
lemma internalDiam_dilate_rescaled (D : ℂ → ℂ → ℝ) {b R : ℝ} (hb : 0 < b) (hR : 0 < R) (K : Set ℂ)
    (r η : ℝ) (z : ℂ) :
    internalDiam (fun x y => b * D ((R : ℂ) * x) ((R : ℂ) * y)) (r * η) (rescaledSet K r z) =
      ENNReal.ofReal b * internalDiam D (R * r * η) (rescaledSet K (R * r) ((R : ℂ) * z)) := by
  rw [internalDiam_dilate D hb hR, image_rescaledSet_mul, mul_assoc R r η]

/-- Set distance under the dilated metric (dilation by `R`, constant `b`). -/
lemma setDist_dilate (D : ℂ → ℂ → ℝ) {b R : ℝ} (hb : 0 ≤ b) (hR : 0 < R) (A B : Set ℂ) :
    setDist (fun x y => b * D ((R : ℂ) * x) ((R : ℂ) * y)) A B =
      b * setDist D ((fun w : ℂ => (R : ℂ) * w) '' A) ((fun w : ℂ => (R : ℂ) * w) '' B) := by
  have h := setDist_comp_homeomorph (fun x y => b * D x y) (dilH R hR) A B
  rw [setDist_const_mul D hb] at h
  exact h

lemma setDist_dilate_sphere (D : ℂ → ℂ → ℝ) {b R : ℝ} (hb : 0 ≤ b) (hR : 0 < R) (z : ℂ) (s t : ℝ) :
    setDist (fun x y => b * D ((R : ℂ) * x) ((R : ℂ) * y)) (sphere z s) (sphere z t) =
      b * setDist D (sphere ((R : ℂ) * z) (R * s)) (sphere ((R : ℂ) * z) (R * t)) := by
  rw [setDist_dilate D hb hR, image_sphere_mul hR, image_sphere_mul hR]

lemma setDist_dilate_point_sphere (D : ℂ → ℂ → ℝ) {b R : ℝ} (hb : 0 ≤ b) (hR : 0 < R) (z : ℂ) (s : ℝ) :
    setDist (fun x y => b * D ((R : ℂ) * x) ((R : ℂ) * y)) {z} (sphere z s) =
      b * setDist D {(R : ℂ) * z} (sphere ((R : ℂ) * z) (R * s)) := by
  rw [setDist_dilate D hb hR]
  simp only [Set.image_singleton]
  rw [image_sphere_mul hR]

lemma image_closure_dilate {R : ℝ} (hR : 0 < R) (A : Set ℂ) :
    (fun w : ℂ => (R : ℂ) * w) '' closure A = closure ((fun w : ℂ => (R : ℂ) * w) '' A) :=
  (dilH R hR).image_closure A

lemma image_frontier_dilate {R : ℝ} (hR : 0 < R) (A : Set ℂ) :
    (fun w : ℂ => (R : ℂ) * w) '' frontier A = frontier ((fun w : ℂ => (R : ℂ) * w) '' A) :=
  (dilH R hR).image_frontier A

/-- Dilation covariance of the certificate event `𝓔_r(z; M)` (rule [C43]; Step 9 of
`CHATGPT-n3-Q1-eq34.md` section 5). The pair `(c • μ.map (· / R), b D(R·, R·))` has the certificate event at
`(z, r)` iff `(μ, D)` has it at `(R z, R r)`; the masses scale by `c = a` and the metric by `b`, which cancel in
every strict inequality. -/
theorem certificateEvent_dilate_iff (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) (Ostar U V W T Q' Q : Set ℂ)
    (η M r : ℝ) (z : ℂ) {R a b : ℝ} (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) :
    CertificateEvent (ENNReal.ofReal a • μ.map (fun w : ℂ => w / (R : ℂ)))
        (fun u v => b * D ((R : ℂ) * u) ((R : ℂ) * v)) Ostar U V W T Q' Q η M r z ↔
      CertificateEvent μ D Ostar U V W T Q' Q η M (R * r) ((R : ℂ) * z) := by
  have hA : ENNReal.ofReal a ≠ 0 := (ENNReal.ofReal_pos.2 ha).ne'
  have hAt : ENNReal.ofReal a ≠ ⊤ := ENNReal.ofReal_ne_top
  have hB : ENNReal.ofReal b ≠ 0 := (ENNReal.ofReal_pos.2 hb).ne'
  have hBt : ENNReal.ofReal b ≠ ⊤ := ENNReal.ofReal_ne_top
  have hfun : (fun w : ℂ => w / (R : ℂ)) = (fun y : ℂ => (R : ℝ)⁻¹ • y) := by
    funext w
    rw [Complex.real_smul, Complex.ofReal_inv, div_eq_inv_mul]
  have e1 : (⨆ x ∈ sphere z (5 * r),
      internalMetric (fun u v => b * D ((R : ℂ) * u) ((R : ℂ) * v)) (rescaledSet Ostar r z) z x) =
      ENNReal.ofReal b * ⨆ y ∈ sphere ((R : ℂ) * z) (5 * (R * r)),
        internalMetric D (rescaledSet Ostar (R * r) ((R : ℂ) * z)) ((R : ℂ) * z) y := by
    rw [iSup_internalMetric_dilate D hb hR, image_rescaledSet_mul,
      show R * (5 * r) = 5 * (R * r) by ring]
  have e2 : ENNReal.ofReal (setDist (fun u v => b * D ((R : ℂ) * u) ((R : ℂ) * v))
      (closure (rescaledSet Q' r z)) (frontier (rescaledSet Q r z))) =
      ENNReal.ofReal b * ENNReal.ofReal (setDist D (closure (rescaledSet Q' (R * r) ((R : ℂ) * z)))
        (frontier (rescaledSet Q (R * r) ((R : ℂ) * z)))) := by
    rw [setDist_dilate D hb.le hR, image_closure_dilate hR, image_frontier_dilate hR,
      image_rescaledSet_mul, image_rescaledSet_mul, ENNReal.ofReal_mul hb.le]
  have e4 : ENNReal.ofReal (setDist (fun u v => b * D ((R : ℂ) * u) ((R : ℂ) * v)) {z}
      (sphere z (r * η))) =
      ENNReal.ofReal b * ENNReal.ofReal (setDist D {(R : ℂ) * z} (sphere ((R : ℂ) * z) (R * r * η))) := by
    rw [setDist_dilate_point_sphere D hb.le hR, ENNReal.ofReal_mul hb.le, mul_assoc R r η]
  have e6 : ENNReal.ofReal (setDist (fun u v => b * D ((R : ℂ) * u) ((R : ℂ) * v))
      (sphere z (r * η)) (sphere z (2 * r * η))) =
      ENNReal.ofReal b * ENNReal.ofReal (setDist D (sphere ((R : ℂ) * z) (R * r * η))
        (sphere ((R : ℂ) * z) (2 * (R * r) * η))) := by
    rw [setDist_dilate_sphere D hb.le hR, ENNReal.ofReal_mul hb.le, show R * (r * η) = R * r * η by ring,
      show R * (2 * r * η) = 2 * (R * r) * η by ring]
  have e7 : ENNReal.ofReal (setDist (fun u v => b * D ((R : ℂ) * u) ((R : ℂ) * v))
      (sphere z (2 * r * η)) (sphere z (3 * r * η))) =
      ENNReal.ofReal b * ENNReal.ofReal (setDist D (sphere ((R : ℂ) * z) (2 * (R * r) * η))
        (sphere ((R : ℂ) * z) (3 * (R * r) * η))) := by
    rw [setDist_dilate_sphere D hb.le hR, ENNReal.ofReal_mul hb.le,
      show R * (2 * r * η) = 2 * (R * r) * η by ring, show R * (3 * r * η) = 3 * (R * r) * η by ring]
  have e8 : ENNReal.ofReal M * annulusGreenPotentialSup (ENNReal.ofReal a • μ.map (fun w : ℂ => w / (R : ℂ)))
      z (3 * r) (6 * r) =
      ENNReal.ofReal a * (ENNReal.ofReal M * annulusGreenPotentialSup μ ((R : ℂ) * z) (3 * (R * r))
        (6 * (R * r))) := by
    rw [hfun, annulusGreenPotentialSup_comp_real_smul_measure μ hR (ENNReal.ofReal a) z (3 * r) (6 * r),
      Complex.real_smul, show R * (3 * r) = 3 * (R * r) by ring, show R * (6 * r) = 6 * (R * r) by ring]
    ring
  have e9 : (ENNReal.ofReal a • μ.map (fun w : ℂ => w / (R : ℂ))) (rescaledSet U r z) =
      ENNReal.ofReal a * μ (rescaledSet U (R * r) ((R : ℂ) * z)) :=
    smul_map_div_apply_rescaledSet μ hR r z U
  unfold CertificateEvent
  simp only [e1, e2, e4, e6, e7, e8, e9, internalDiam_dilate_rescaled D hb hR,
    ENNReal.mul_lt_mul_iff_right hB hBt, ENNReal.mul_lt_mul_iff_right hA hAt]

end HarmonicBalls.FirstPassS11iCertDilate
