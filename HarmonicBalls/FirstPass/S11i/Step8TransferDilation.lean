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

end HarmonicBalls.FirstPassS11iStep8Transfer
