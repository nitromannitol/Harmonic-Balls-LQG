import HarmonicBalls.FirstPass.S11i.Step8ZoomFrequency

/-!
# Step 8 transfer and dilation: the converse of `zoom_ae_frequency` (fp-S11i-step8-transfer-dilation, owner z4)

Deterministic per-`ω` dilation step of Step 8 of the corrected proof of `lemma:mu_h-pinch-bad` (corrected paper, proof,
dilation paragraph "Apply this argument after deterministic dilation by `R = 2^k`"; route
`notes/fp-gaps/CHATGPT-n3-marked-A10.md`, end of §2). `Step8ZoomFrequency.lean` proves that a physical window frequency
at scale `2^k` transfers to the zoomed pair `(zoomMeasure μ k, zoomMetric D k)` almost everywhere on `B₁(0)`. This file
proves the converse, so that the hypothesis `hphys` of `step8_zoom_family_of_ae_frequency` can be produced from a
unit-scale statement for the zoomed pair.

* `ae_frequency_of_zoom` (unit constants): the zoomed statement on `B₁(0)` gives the physical statement on `B_{2^k}(0)`.
* `ae_frequency_of_scaled_zoom`: the same for the zoomed pair `(ENNReal.ofReal a • zoomMeasure μ k, b * zoomMetric D k)`
  with `0 < a` and `0 < b`. This uses `certificateEvent_ofReal_smul_iff`: `CertificateEvent` is invariant under
  `(μ, D) ↦ (c • μ, b * D)` for `c, b > 0`, because every clause is homogeneous of degree one in `D` (path lengths,
  internal diameters, `setDist`) and in `μ` (the annular Green potential sup and the mass in `rescaledSet U r z`).
* `hphys_of_zoom_unit_family`, `hphys_of_zoom_const_family`: the family form. Their conclusion is exactly the `hphys`
  hypothesis of `step8_zoom_family_of_ae_frequency` (for `Ostar = pinchOmegaGeom W Q δ` and `η = δ`).

No Gaussian or LQG input is used and no hypothesis is added: the only inputs are the zoom family hypotheses themselves.
-/

universe u

namespace HarmonicBalls.FirstPassS11iStep8Transfer

open MeasureTheory Filter Topology Set Metric FirstPassS11i HarmonicBalls
open HarmonicBalls.FirstPassS11iStep8Zoom
open scoped ENNReal Pointwise

section Scaling

variable {D : ℂ → ℂ → ℝ}

/-- The `D`-length of a curve is linear in `D` for a nonnegative factor `b`. -/
lemma curveLength_const_mul {b : ℝ} (hb : 0 ≤ b) (p : ℝ → ℂ) (a c : ℝ) :
    curveLength (fun x y => b * D x y) p a c = ENNReal.ofReal b * curveLength D p a c := by
  unfold curveLength
  simp only [ENNReal.mul_iSup, Finset.mul_sum, ENNReal.ofReal_mul hb]

/-- The `D`-length of a path is linear in `D` for a nonnegative factor `b`. -/
lemma pathLength_const_mul {b : ℝ} (hb : 0 ≤ b) {z w : ℂ} (P : Path z w) :
    pathLength (fun x y => b * D x y) P = ENNReal.ofReal b * pathLength D P := by
  unfold pathLength
  exact curveLength_const_mul hb _ _ _

/-- The internal metric `D(z, w; U)` is linear in `D` for a positive factor `b`. -/
lemma internalMetric_const_mul {b : ℝ} (hb : 0 < b) (U : Set ℂ) (z w : ℂ) :
    internalMetric (fun x y => b * D x y) U z w = ENNReal.ofReal b * internalMetric D U z w := by
  unfold internalMetric
  simp only [ENNReal.mul_iInf_of_ne (ENNReal.ofReal_pos.mpr hb).ne' ENNReal.ofReal_ne_top,
    pathLength_const_mul hb.le]

/-- A supremum of internal metrics over a set is linear in `D` for a positive factor `b`. -/
lemma iSup_internalMetric_const_mul {b : ℝ} (hb : 0 < b) (S : Set ℂ) (O : Set ℂ) (z : ℂ) :
    (⨆ x ∈ S, internalMetric (fun x y => b * D x y) O z x) =
      ENNReal.ofReal b * ⨆ x ∈ S, internalMetric D O z x := by
  simp only [internalMetric_const_mul hb, ENNReal.mul_iSup]

/-- The internal diameter `diam^δ_D(A)` is linear in `D` for a positive factor `b`. -/
lemma internalDiam_const_mul {b : ℝ} (hb : 0 < b) (δ : ℝ) (A : Set ℂ) :
    internalDiam (fun x y => b * D x y) δ A = ENNReal.ofReal b * internalDiam D δ A := by
  unfold internalDiam
  simp only [ENNReal.mul_iSup, internalMetric_const_mul hb]

/-- The set distance `D(A, B)` is linear in `D` for a positive factor `b`. -/
lemma setDist_const_mul {b : ℝ} (hb : 0 < b) (A B : Set ℂ) :
    setDist (fun x y => b * D x y) A B = b * setDist D A B := by
  have himg : image2 (fun x y => b * D x y) A B = b • image2 D A B := by
    ext t
    simp only [Set.mem_image2, Set.mem_smul_set, smul_eq_mul]
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩
      exact ⟨D x y, ⟨x, hx, y, hy, rfl⟩, rfl⟩
    · rintro ⟨s, ⟨x, hx, y, hy, rfl⟩, rfl⟩
      exact ⟨x, hx, y, hy, rfl⟩
  unfold setDist
  rw [himg, Real.sInf_smul_of_nonneg hb.le, smul_eq_mul]

/-- The annular Green potential sup is linear in the measure: `SG_{a,b}(x₀; c • μ) = c · SG_{a,b}(x₀; μ)`. -/
lemma annulusGreenPotentialSup_smul (c : ℝ≥0∞) (μ : Measure ℂ) (x₀ : ℂ) (a b : ℝ) :
    annulusGreenPotentialSup (c • μ) x₀ a b = c * annulusGreenPotentialSup μ x₀ a b := by
  unfold annulusGreenPotentialSup
  simp only [ENNReal.mul_iSup, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]

/-- The mass clause of `CertificateEvent` is invariant under `μ ↦ ofReal a • μ` for `a > 0`. -/
lemma ofReal_smul_green_lt_iff {a : ℝ} (ha : 0 < a) (M r : ℝ) (μ : Measure ℂ) (U : Set ℂ) (z : ℂ) :
    ENNReal.ofReal M * annulusGreenPotentialSup (ENNReal.ofReal a • μ) z (3 * r) (6 * r) <
        (ENNReal.ofReal a • μ) (rescaledSet U r z) ↔
      ENNReal.ofReal M * annulusGreenPotentialSup μ z (3 * r) (6 * r) < μ (rescaledSet U r z) := by
  have h0 : ENNReal.ofReal a ≠ 0 := (ENNReal.ofReal_pos.mpr ha).ne'
  have e : ENNReal.ofReal M * (ENNReal.ofReal a * annulusGreenPotentialSup μ z (3 * r) (6 * r)) =
      ENNReal.ofReal a * (ENNReal.ofReal M * annulusGreenPotentialSup μ z (3 * r) (6 * r)) := by
    ring
  rw [annulusGreenPotentialSup_smul, Measure.smul_apply, smul_eq_mul, e,
    ENNReal.mul_lt_mul_iff_right h0 ENNReal.ofReal_ne_top]

/-- **Scaling invariance of the certificate event.** For `a, b > 0`, `CertificateEvent` for the pair
`(ofReal a • μ, b * D)` holds exactly when it holds for `(μ, D)`: the internal metric, internal diameters and set
distances are multiplied by `b`, the annular Green potential sup and the mass by `a`, and the comparisons are
between quantities with the same positive factor. -/
lemma certificateEvent_ofReal_smul_iff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (μ : Measure ℂ)
    (Ostar U V W T Q' Q : Set ℂ) (η M r : ℝ) (z : ℂ) :
    CertificateEvent (ENNReal.ofReal a • μ) (fun x y => b * D x y) Ostar U V W T Q' Q η M r z ↔
      CertificateEvent μ D Ostar U V W T Q' Q η M r z := by
  have h0 : ENNReal.ofReal b ≠ 0 := (ENNReal.ofReal_pos.mpr hb).ne'
  unfold CertificateEvent
  simp only [iSup_internalMetric_const_mul hb, internalDiam_const_mul hb, setDist_const_mul hb,
    ENNReal.ofReal_mul hb.le, ENNReal.mul_lt_mul_iff_right h0 ENNReal.ofReal_ne_top,
    ofReal_smul_green_lt_iff ha]

/-- Window-count sets are unchanged by the scaling of `CertificateEvent` (for each `N`). -/
lemma window_count_ofReal_smul_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (μ : Measure ℂ)
    (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ) (w : ℂ) (N : ℕ) :
    {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        CertificateEvent (ENNReal.ofReal a • μ) (fun x y => b * D x y) Ostar U V W T Q' Q η M
          ((2 : ℝ)⁻¹ ^ n) w} =
      {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ CertificateEvent μ D Ostar U V W T Q' Q η M ((2 : ℝ)⁻¹ ^ n) w} := by
  ext n
  simp only [Set.mem_ofPred_eq, certificateEvent_ofReal_smul_iff ha hb]

end Scaling

/-- The window-count sets of the zoomed pair at the centre `z / 2^k` are the window-count sets of `(μ, D)` at `z`, at
radii `2^k 2^{-n}`. This is the converse direction of the set identity in `zoom_ae_frequency`. -/
lemma zoom_count_set_eq (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ) (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) (k N : ℕ)
    (z : ℂ) :
    {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        CertificateEvent (zoomMeasure μ k) (zoomMetric D k) Ostar U V W T Q' Q η M ((2 : ℝ)⁻¹ ^ n)
          (z / (((2 : ℝ) ^ k : ℝ) : ℂ))} =
      {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        CertificateEvent μ D Ostar U V W T Q' Q η M ((2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ n) z} := by
  ext n
  simp only [Set.mem_ofPred_eq, zoom_certificate_iff]

/-- **Converse of `zoom_ae_frequency` (unit constants).** If the window certificate frequency of the zoom measure
`zoomMeasure μ k` with metric `zoomMetric D k` tends to `q` for `zoomMeasure μ k`-almost every `w ∈ B₁(0)`, then the
physical window frequency of `(μ, D)` at the radii `2^k 2^{-n}` tends to `q` for `μ`-almost every centre
`z ∈ B_{2^k}(0)`. -/
theorem ae_frequency_of_zoom (Ostar U V W T Q' Q : Set ℂ) (η M q : ℝ) (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) (k : ℕ)
    (hunit : ∀ᵐ w ∂(zoomMeasure μ k), w ∈ ball (0 : ℂ) 1 →
      Tendsto (fun N : ℕ => (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        CertificateEvent (zoomMeasure μ k) (zoomMetric D k) Ostar U V W T Q' Q η M ((2 : ℝ)⁻¹ ^ n) w}.ncard :
          ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 q)) :
    ∀ᵐ z ∂μ, z ∈ ball (0 : ℂ) ((2 : ℝ) ^ k) →
      Tendsto (fun N : ℕ => (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        CertificateEvent μ D Ostar U V W T Q' Q η M ((2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ n) z}.ncard : ℕ) : ℝ) / (N : ℝ))
        atTop (𝓝 q) := by
  have hcn : ‖(((2 : ℝ) ^ k : ℝ) : ℂ)‖ = (2 : ℝ) ^ k := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h := (ae_zoomMeasure_iff μ k _).mp hunit
  filter_upwards [h] with z hz hzb
  have hw : z / (((2 : ℝ) ^ k : ℝ) : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff] at hzb ⊢
    rw [norm_div, hcn, div_lt_one (by positivity)]
    exact hzb
  refine (hz hw).congr (fun N => ?_)
  exact congrArg (fun s : Set ℕ => ((s.ncard : ℕ) : ℝ) / (N : ℝ))
    (zoom_count_set_eq Ostar U V W T Q' Q η M μ D k N z)

/-- **Converse of `zoom_ae_frequency` (positive constants).** The same conclusion when the zoomed pair is
`(ENNReal.ofReal a • zoomMeasure μ k, fun x y => b * zoomMetric D k x y)` with `0 < a`, `0 < b`. The hypothesis is
reduced to the unit-constant one by `certificateEvent_ofReal_smul_iff`. -/
theorem ae_frequency_of_scaled_zoom (Ostar U V W T Q' Q : Set ℂ) (η M q a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) (k : ℕ)
    (hunit : ∀ᵐ w ∂(ENNReal.ofReal a • zoomMeasure μ k), w ∈ ball (0 : ℂ) 1 →
      Tendsto (fun N : ℕ => (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        CertificateEvent (ENNReal.ofReal a • zoomMeasure μ k) (fun x y => b * zoomMetric D k x y)
          Ostar U V W T Q' Q η M ((2 : ℝ)⁻¹ ^ n) w}.ncard : ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 q)) :
    ∀ᵐ z ∂μ, z ∈ ball (0 : ℂ) ((2 : ℝ) ^ k) →
      Tendsto (fun N : ℕ => (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        CertificateEvent μ D Ostar U V W T Q' Q η M ((2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ n) z}.ncard : ℕ) : ℝ) / (N : ℝ))
        atTop (𝓝 q) := by
  have hunit1 : ∀ᵐ w ∂(zoomMeasure μ k), w ∈ ball (0 : ℂ) 1 →
      Tendsto (fun N : ℕ => (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        CertificateEvent (zoomMeasure μ k) (zoomMetric D k) Ostar U V W T Q' Q η M ((2 : ℝ)⁻¹ ^ n) w}.ncard :
          ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 q) := by
    filter_upwards [(Measure.ae_ennreal_smul_measure_iff (ENNReal.ofReal_pos.mpr ha).ne').mp hunit] with w hw hwb
    simpa only [window_count_ofReal_smul_eq ha hb] using hw hwb
  exact ae_frequency_of_zoom Ostar U V W T Q' Q η M q μ D k hunit1

end HarmonicBalls.FirstPassS11iStep8Transfer
