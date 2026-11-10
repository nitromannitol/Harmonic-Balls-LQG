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

end HarmonicBalls.FirstPassS11iCertDilate
