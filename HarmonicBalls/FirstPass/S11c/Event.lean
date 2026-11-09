import HarmonicBalls.Draft.Section11
import HarmonicBalls.Steps.Sec11.AnnulusGreenDilation

/-!
# Proposition 11.7, invariance of the cone-mass event under the dilation (fp-S11c, owner n1)

FIRST-PASS NEW (deterministic). For a finite measure transformed by `c • map (w ↦ 2w)` (the LQG measure of the normalized
dilated profile, `isLQGLimit_dilate`, Vague.lean), the event `G̃_r(z; M, 𝒬)` (Draft `coneMassEvent`, line 2793) at scale `r`
and centre `z` is the event `G̃_{r/2}(z/2; M, 𝒬)` of the original measure: the scale index moves by one. Ingredients:
the cone is invariant under positive scalings (`IsCone`), the annuli and cone translates are dilated by `w ↦ 2w`, and the
Green potential sup transforms by `annulusGreenPotentialSup_comp_real_smul_measure` (Steps/Sec11/AnnulusGreenDilation).
-/

namespace HarmonicBalls

open MeasureTheory Set
open scoped ENNReal

/-- A cone is invariant under positive real scalings. -/
lemma isCone_smul_mem_iff {Q : Set ℂ} (hQ : IsCone Q) {t : ℝ} (ht : 0 < t) (x : ℂ) :
    t • x ∈ Q ↔ x ∈ Q := by
  have key : ∀ {R : Set ℂ}, IsOpenCone R → ∀ y : ℂ, t • y ∈ R ↔ y ∈ R := by
    rintro R ⟨-, -, -, v, w, hv, hw, rfl⟩ y
    simp only [openSector, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨c, d, hc, hd, h⟩
      refine ⟨c / t, d / t, div_pos hc ht, div_pos hd ht, ?_⟩
      calc y = t⁻¹ • (t • y) := by rw [smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
        _ = t⁻¹ • (c • v + d • w) := by rw [h]
        _ = (c / t) • v + (d / t) • w := by
          rw [smul_add, smul_smul, smul_smul, div_eq_inv_mul, div_eq_inv_mul]
    · rintro ⟨c, d, hc, hd, h⟩
      exact ⟨t * c, t * d, mul_pos ht hc, mul_pos ht hd, by rw [h, smul_add, smul_smul, smul_smul]⟩
  rcases hQ with hQ | hQ
  · exact key hQ x
  · have h := key hQ x
    simp only [mem_compl_iff] at h ⊢
    exact not_iff_not.1 h

/-- The distance scaling under `w ↦ 2w`. -/
lemma dist_two_smul_eq (w z : ℂ) : dist ((2 : ℝ) • w) z = 2 * dist w (z / 2) := by
  have hz : (2 : ℝ) • (z / 2) = z := by
    rw [Complex.real_smul]
    push_cast
    ring
  rw [dist_eq_norm, dist_eq_norm, ← hz, ← smul_sub, norm_smul]
  norm_num

/-- The preimage of an annulus under `w ↦ 2w` is the annulus with centre `z/2` and radii halved. -/
lemma preimage_two_smul_annulus (z : ℂ) (r₁ r₂ : ℝ) :
    (fun w : ℂ => (2 : ℝ) • w) ⁻¹' annulus z r₁ r₂ = annulus (z / 2) (r₁ / 2) (r₂ / 2) := by
  ext w
  simp only [mem_preimage, annulus, mem_sdiff, Metric.mem_ball, Metric.mem_closedBall, dist_two_smul_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, fun h => h2 (by linarith)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, fun h => h2 (by linarith)⟩

/-- The preimage of a cone translate under `w ↦ 2w` is the cone translate with centre `z/2`. -/
lemma preimage_two_smul_coneAt {Q : Set ℂ} (hQ : IsCone Q) (z : ℂ) :
    (fun w : ℂ => (2 : ℝ) • w) ⁻¹' coneAt Q z = coneAt Q (z / 2) := by
  have h2 : (0 : ℝ) < 2⁻¹ := by norm_num
  ext w
  simp only [mem_preimage, coneAt, mem_image]
  constructor
  · rintro ⟨q, hq, hqe⟩
    refine ⟨(2 : ℝ)⁻¹ • q, (isCone_smul_mem_iff hQ h2 q).2 hq, ?_⟩
    simp only [Complex.real_smul] at hqe ⊢
    push_cast at hqe ⊢
    linear_combination (1 / 2 : ℂ) * hqe
  · rintro ⟨q, hq, hqe⟩
    refine ⟨(2 : ℝ) • q, (isCone_smul_mem_iff hQ (by norm_num) q).2 hq, ?_⟩
    simp only [Complex.real_smul] at hqe ⊢
    push_cast at hqe ⊢
    linear_combination 2 * hqe

/-- The cone translate is a measurable set when the cone is. -/
lemma measurableSet_coneAt {Q : Set ℂ} (hQ : IsCone Q) (z : ℂ) : MeasurableSet (coneAt Q z) := by
  have hQm : MeasurableSet Q := by
    rcases hQ with h | h
    · exact h.2.1.measurableSet
    · have := h.2.1.measurableSet
      simpa using this.compl
  have e : coneAt Q z = (fun x : ℂ => x + (-z)) ⁻¹' Q := by
    ext x
    simp only [coneAt, mem_image, mem_preimage]
    constructor
    · rintro ⟨q, hq, rfl⟩
      simpa using hq
    · intro h
      exact ⟨x + -z, h, by ring⟩
  rw [e]
  exact hQm.preimage (measurable_add_const (-z))

/-- Invariance of the cone-mass event under the dilation: the event of the measure `c • map (w ↦ 2w) μ` at scale `r` and
centre `z` is the event of `μ` at scale `r/2` and centre `z/2` (paper Lemma 11.7, the scale index moves by one). -/
theorem coneMassEvent_map_smul_two (μ : Measure ℂ) {Q : Set ℂ} (hQ : IsCone Q) {M c : ℝ} (hc : 0 < c)
    (z : ℂ) (r : ℝ) :
    coneMassEvent (ENNReal.ofReal c • μ.map (fun w : ℂ => (2 : ℝ) • w)) Q M r z ↔
      coneMassEvent μ Q M (r / 2) (z / 2) := by
  unfold coneMassEvent
  have hfun : (fun w : ℂ => (2 : ℝ) • w) = (fun y : ℂ => ((2 : ℝ)⁻¹)⁻¹ • y) := by
    funext y
    rw [inv_inv]
  have hG := annulusGreenPotentialSup_comp_real_smul_measure μ (k := (2 : ℝ)⁻¹) (by norm_num)
    (ENNReal.ofReal c) z (3 * r) (6 * r)
  rw [← hfun] at hG
  have hz : (2 : ℝ)⁻¹ • z = z / 2 := by
    rw [Complex.real_smul]
    push_cast
    ring
  rw [hz, show (2 : ℝ)⁻¹ * (3 * r) = 3 * (r / 2) by ring, show (2 : ℝ)⁻¹ * (6 * r) = 6 * (r / 2) by ring] at hG
  have hσ : Measurable (fun w : ℂ => (2 : ℝ) • w) := measurable_const_smul (2 : ℝ)
  have hA : MeasurableSet (annulus z r (2 * r) ∩ coneAt Q z) :=
    ((measurableSet_ball.diff measurableSet_closedBall).inter (measurableSet_coneAt hQ z))
  have hmeasure : (ENNReal.ofReal c • μ.map (fun w : ℂ => (2 : ℝ) • w)) (annulus z r (2 * r) ∩ coneAt Q z) =
      ENNReal.ofReal c * μ (annulus (z / 2) (r / 2) (2 * (r / 2)) ∩ coneAt Q (z / 2)) := by
    rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply hσ hA, preimage_inter,
      preimage_two_smul_annulus, preimage_two_smul_coneAt hQ, show 2 * r / 2 = 2 * (r / 2) by ring]
  rw [hG, hmeasure, mul_left_comm]
  rw [mul_comm (ENNReal.ofReal c) (ENNReal.ofReal M * annulusGreenPotentialSup μ (z / 2) (3 * (r / 2)) (6 * (r / 2))),
    mul_comm (ENNReal.ofReal c)]
  exact ENNReal.mul_le_mul_iff_left (ENNReal.ofReal_pos.2 hc).ne' ENNReal.ofReal_ne_top

end HarmonicBalls
