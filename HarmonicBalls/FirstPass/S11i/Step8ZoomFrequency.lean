import HarmonicBalls.FirstPass.S11i.Corrected11_13
import HarmonicBalls.FirstPass.S11i.CertZoom

/-!
# Step 8 zoom family from the physical window frequency (fp-S11i-11-13c, owner n3)

Deterministic part of Step 8 of the corrected proof of `lemma:mu_h-pinch-bad` (corrected paper, proof, dilation paragraph
"Apply this argument after deterministic dilation by `R = 2^k`"). Suppose that for every `k` and almost every `ω`, for
`μ_ω`-almost every centre `z ∈ B_{2^k}(0)`, the physical window frequency of the certificate events of `(μ_ω, D_ω)` at the
radii `2^k 2^{-n}` about `z` tends to `q`. Then the zoom family `μk k ω = μ_ω(· / 2^k)` (unit constant),
`Dk k ω = D_ω(2^k ·, 2^k ·)` (unit constant) has window certificate frequency `q` for `μk`-almost every `w ∈ B₁(0)`.

The proof is the dilation identity `windowCert_zoom_iff` (CertZoom.lean) and the change of variables along the measurable
embedding `z ↦ z / 2^k`. No Gaussian or LQG input. The hypothesis `hphys` is the paper's conclusion of the rooted-field and
marked-identity argument (corrected paper lines 3848-3905 before the dilation paragraph); it is NOT proved here.

`step8_zoom_family_of_ae_frequency` is the second conjunct of `Step8IdentityStmt` (Corrected11_13.lean) for the paper's
`Ostar = pinchOmegaGeom W Q δ` and `η = δ`.
-/

universe u

namespace HarmonicBalls.FirstPassS11iStep8Zoom

open MeasureTheory Filter Topology Set Metric FirstPassS11i HarmonicBalls
open scoped ENNReal

/-- The zoom measure at scale `2^k` with unit constant: the image of `μ` under `z ↦ z / 2^k`. -/
noncomputable def zoomMeasure (μ : Measure ℂ) (k : ℕ) : Measure ℂ :=
  ENNReal.ofReal 1 • μ.map (fun x : ℂ => x / (((2 : ℝ) ^ k : ℝ) : ℂ))

/-- The zoom metric at scale `2^k` with unit constant: `(x, y) ↦ D(2^k x, 2^k y)`. -/
noncomputable def zoomMetric (D : ℂ → ℂ → ℝ) (k : ℕ) : ℂ → ℂ → ℝ :=
  fun x y => (1 : ℝ) * D ((((2 : ℝ) ^ k : ℝ) : ℂ) * x) ((((2 : ℝ) ^ k : ℝ) : ℂ) * y)

/-- Division by a nonzero complex constant is a measurable embedding of `ℂ`. -/
lemma measurableEmbedding_div_const {c : ℂ} (hc : c ≠ 0) :
    MeasurableEmbedding (fun x : ℂ => x / c) := by
  have h : (fun x : ℂ => x / c) = fun x => x * c⁻¹ := by
    funext x
    rw [div_eq_mul_inv]
  rw [h]
  exact (Homeomorph.mulRight₀ c⁻¹ (inv_ne_zero hc)).measurableEmbedding

/-- The window certificate of the zoom family at the point `z / 2^k` is the physical certificate of `(μ, D)` at the point
`z` and radius `2^k 2^{-n}`. -/
lemma zoom_certificate_iff (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ) (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) (k n : ℕ)
    (z : ℂ) :
    CertificateEvent (zoomMeasure μ k) (zoomMetric D k) Ostar U V W T Q' Q η M ((2 : ℝ)⁻¹ ^ n)
        (z / (((2 : ℝ) ^ k : ℝ) : ℂ)) ↔
      CertificateEvent μ D Ostar U V W T Q' Q η M ((2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ n) z := by
  have hc0 : (((2 : ℝ) ^ k : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have h := HarmonicBalls.FirstPassS11iCertZoom.windowCert_zoom_iff Ostar U V W T Q' Q η M
    (fun k (_ : Unit) => zoomMeasure μ k) (fun k (_ : Unit) => zoomMetric D k) μ D k ()
    (a := 1) (b := 1) one_pos one_pos rfl (fun _ _ => rfl) n (z / (((2 : ℝ) ^ k : ℝ) : ℂ))
  have hz : (((2 : ℝ) ^ k : ℝ) : ℂ) * (z / (((2 : ℝ) ^ k : ℝ) : ℂ)) = z := by
    field_simp
  rw [hz] at h
  exact h

/-- Almost everywhere for the zoom measure is almost everywhere for `μ` after the dilation `z ↦ z / 2^k`. -/
lemma ae_zoomMeasure_iff (μ : Measure ℂ) (k : ℕ) (p : ℂ → Prop) :
    (∀ᵐ w ∂(zoomMeasure μ k), p w) ↔ ∀ᵐ z ∂μ, p (z / (((2 : ℝ) ^ k : ℝ) : ℂ)) := by
  have hc0 : (((2 : ℝ) ^ k : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  simp only [zoomMeasure, ENNReal.ofReal_one, one_smul]
  exact (measurableEmbedding_div_const hc0).ae_map_iff

/-- **Zoom frequency, almost everywhere on `B₁`.** If the physical window frequency at radii `2^k 2^{-n}` tends to `q` for
`μ`-almost every centre in `B_{2^k}(0)`, then the window certificate frequency of the zoom measure tends to `q` for
`zoomMeasure μ k`-almost every `w ∈ B₁(0)`. -/
lemma zoom_ae_frequency (Ostar U V W T Q' Q : Set ℂ) (η M q : ℝ) (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) (k : ℕ)
    (hphys : ∀ᵐ z ∂μ, z ∈ ball (0 : ℂ) ((2 : ℝ) ^ k) →
      Tendsto (fun N : ℕ => (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        CertificateEvent μ D Ostar U V W T Q' Q η M ((2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ n) z}.ncard : ℕ) : ℝ) / (N : ℝ))
        atTop (𝓝 q)) :
    ∀ᵐ w ∂(zoomMeasure μ k), w ∈ ball (0 : ℂ) 1 →
      Tendsto (fun N : ℕ => (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        CertificateEvent (zoomMeasure μ k) (zoomMetric D k) Ostar U V W T Q' Q η M ((2 : ℝ)⁻¹ ^ n) w}.ncard : ℕ) : ℝ)
        / (N : ℝ)) atTop (𝓝 q) := by
  have hcn : ‖(((2 : ℝ) ^ k : ℝ) : ℂ)‖ = (2 : ℝ) ^ k := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  refine (ae_zoomMeasure_iff μ k _).mpr ?_
  filter_upwards [hphys] with z hz hw
  have hzb : z ∈ ball (0 : ℂ) ((2 : ℝ) ^ k) := by
    rw [mem_ball_zero_iff] at hw ⊢
    rw [norm_div, hcn, div_lt_one (by positivity)] at hw
    exact hw
  have hset : ∀ N : ℕ,
      {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        CertificateEvent (zoomMeasure μ k) (zoomMetric D k) Ostar U V W T Q' Q η M ((2 : ℝ)⁻¹ ^ n)
          (z / (((2 : ℝ) ^ k : ℝ) : ℂ))} =
      {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        CertificateEvent μ D Ostar U V W T Q' Q η M ((2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ n) z} := by
    intro N
    ext n
    simp only [Set.mem_ofPred_eq, zoom_certificate_iff]
  refine (hz hzb).congr (fun N => ?_)
  exact congrArg (fun s : Set ℕ => ((s.ncard : ℕ) : ℝ) / (N : ℝ)) (hset N).symm

/-- **Step 8 zoom family (second conjunct of `Step8IdentityStmt`).** Given the physical window frequency `hphys` (for
every `k`, almost surely, for `μ`-almost every centre in `B_{2^k}(0)`), the zoom family with unit constants witnesses the
almost-sure `μk`-almost-everywhere frequency conclusion on `B₁(0)` for the paper's `Ostar = pinchOmegaGeom W Q δ`, `η = δ`. -/
theorem step8_zoom_family_of_ae_frequency {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (U V W T Q' Q : Set ℂ) (δ M q : ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ)
    (hphys : ∀ k : ℕ, ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), z ∈ ball (0 : ℂ) ((2 : ℝ) ^ k) →
      Tendsto (fun N : ℕ => (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M
          ((2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ n) z}.ncard : ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 q)) :
    ∃ (μk : ℕ → Ω → Measure ℂ) (Dk : ℕ → Ω → ℂ → ℂ → ℝ),
      (∀ k : ℕ, ∀ᵐ ω ∂P, ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
        μk k ω = ENNReal.ofReal a • (μ ω).map (fun x : ℂ => x / ((((2 : ℝ) ^ k : ℝ)) : ℂ)) ∧
        ∀ x y : ℂ, Dk k ω x y = b * D ω ((((2 : ℝ) ^ k : ℝ) : ℂ) * x) ((((2 : ℝ) ^ k : ℝ) : ℂ) * y)) ∧
      ∀ k : ℕ, ∀ᵐ ω ∂P, ∀ᵐ w ∂(μk k ω), w ∈ ball (0 : ℂ) 1 →
        Tendsto (fun N : ℕ => ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
          FirstPassS11i.windowCert (pinchOmegaGeom W Q δ) U V W T Q' Q δ M μk Dk k ω n w}.ncard : ℝ) / (N : ℝ))
          atTop (𝓝 q) := by
  refine ⟨fun k ω => zoomMeasure (μ ω) k, fun k ω => zoomMetric (D ω) k, fun k =>
    ae_of_all _ (fun ω => ⟨1, 1, one_pos, one_pos, rfl, fun _ _ => rfl⟩), fun k => ?_⟩
  filter_upwards [hphys k] with ω hω
  exact zoom_ae_frequency (pinchOmegaGeom W Q δ) U V W T Q' Q δ M q (μ ω) (D ω) k hω

end HarmonicBalls.FirstPassS11iStep8Zoom
