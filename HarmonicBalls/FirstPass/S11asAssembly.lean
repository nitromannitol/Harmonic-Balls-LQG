import HarmonicBalls.FirstPass.S11as
import HarmonicBalls.FirstPass.S11asZoom

/-!
# Mass clause of the rooted local rescaling: deterministic assembly (fp-S11as, round 7)

For one sample point, the mass half of `RootedLocalRescaling` (`HarmonicBalls/FirstPass/S11as.lean`) follows from five
pointwise identities, each produced by an almost-sure lemma of this task:
* Block 2 (`FirstPassS11asMeasure.rootedMeasure_restrict_proportional`, root `z`, disc `ball z b`):
  `c₀ • μR|ball z b = c₁ • μ₁|ball z b`;
* Block 4 (`ae_isLQGLimit_rooted_translate` with uniqueness of the LQG limit): `μ₁ = E • (ν₁ ∘ (· + z)⁻¹)`;
* Weyl (`FirstPassS11asWeyl.lqgMeasure_restrict_eq_of_shift`, shift `0` on `ball 0 b`): `ν₁|ball 0 b = νU|ball 0 b`;
* canonical identification (`LQGCanonicalIdentificationStmt`): `νU = a • Dμ L`;
* dilation (`FirstPassS11asZoom.ae_decoders_dilOp_iterate`): `Dμ (dilOp^[n] L) = a_n • (Dμ L) ∘ (· / (1/2)^n)⁻¹`.
Here `μR` is the physical rooted mass translated to `0`, `Dμ L` the canonical decoded mass. The theorem below assembles
these into the conclusion of the mass clause of `RootedLocalRescaling` on `closedBall 0 r`, for any `r` with
`closedBall 0 r ⊆ ball 0 b` (for the cutoff radius `r = 7 · certScale n`, this holds once `cutRadius n < b`).
No Lean input is assumed in this file.
-/

namespace FirstPassS11asAssembly

open MeasureTheory Metric Set Filter
open scoped ENNReal

/-- Translation commutes with restriction to a ball: `(μ|ball z b) ∘ (· - z)⁻¹ = (μ ∘ (· - z)⁻¹)|ball 0 b`. -/
theorem map_sub_restrict_ball (μ : Measure ℂ) (z : ℂ) (b : ℝ) :
    (μ.restrict (ball z b)).map (fun w : ℂ => w - z) = (μ.map (fun w : ℂ => w - z)).restrict (ball 0 b) := by
  have hm : Measurable (fun w : ℂ => w - z) := by fun_prop
  have hpre : (fun w : ℂ => w - z) ⁻¹' ball 0 b = ball z b := by
    ext w
    simp [dist_eq_norm]
  rw [Measure.restrict_map hm measurableSet_ball, hpre]

/-- Translating a translate back: `((μ ∘ (· + z)⁻¹) ∘ (· - z)⁻¹) = μ`. -/
theorem map_sub_map_add (μ : Measure ℂ) (z : ℂ) :
    (μ.map (fun x : ℂ => x + z)).map (fun w : ℂ => w - z) = μ := by
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  simp [Function.comp_def]

/-- Translation pushes a scalar multiple through: `(c • μ) ∘ (· - z)⁻¹ = c • (μ ∘ (· - z)⁻¹)`. -/
theorem map_smul_sub (c : ℝ≥0∞) (μ : Measure ℂ) (z : ℂ) :
    ((c • μ).map (fun w : ℂ => w - z)) = c • μ.map (fun w : ℂ => w - z) :=
  Measure.map_smul c (by fun_prop : Measurable (fun w : ℂ => w - z)).aemeasurable

/-- Cancelling a nonzero finite ENNReal constant: `c • X = Y` gives `X = c⁻¹ • Y`. -/
theorem eq_inv_smul_of_smul_eq {X Y : Measure ℂ} {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (h : c • X = Y) : X = c⁻¹ • Y := by
  rw [← h, smul_smul, ENNReal.inv_mul_cancel hc0 hct, one_smul]

/-- Restriction to a smaller set after restriction to a larger one. -/
theorem restrict_restrict_ball_closedBall (m : Measure ℂ) {r b : ℝ} (hr : closedBall (0 : ℂ) r ⊆ ball 0 b) :
    (m.restrict (ball 0 b)).restrict (closedBall 0 r) = m.restrict (closedBall 0 r) := by
  rw [Measure.restrict_restrict measurableSet_closedBall, inter_eq_left.2 hr]

/-- **Mass clause, deterministic assembly.** From the five pointwise identities listed in the module docstring, the
physical rooted mass translated to `0` is a positive multiple of the decoded canonical mass rescaled by `2^{-n}`
on `closedBall 0 r`. -/
theorem mass_clause_of_chain (μR μ₁ ν₁ νU Dl μCn : Measure ℂ) (z : ℂ) {b r : ℝ} (n : ℕ)
    (hr : closedBall (0 : ℂ) r ⊆ ball (0 : ℂ) b)
    (h2 : ∃ c₀ c₁ : ℝ≥0∞, 0 < c₀ ∧ c₀ < ⊤ ∧ 0 < c₁ ∧ c₁ < ⊤ ∧
      c₀ • μR.restrict (ball z b) = c₁ • μ₁.restrict (ball z b))
    (h4 : ∃ E : ℝ≥0∞, 0 < E ∧ E < ⊤ ∧ μ₁ = E • ν₁.map (fun x : ℂ => x + z))
    (hW : ν₁.restrict (ball 0 b) = νU.restrict (ball 0 b))
    (hid : ∃ a : ℝ, 0 < a ∧ νU = ENNReal.ofReal a • Dl)
    (hit : ∃ a : ℝ, 0 < a ∧
      μCn = ENNReal.ofReal a • Dl.map (fun w : ℂ => w / (((1 / 2 : ℝ) ^ n : ℝ) : ℂ))) :
    ∃ A : ℝ, 0 < A ∧
      (μR.map (fun w : ℂ => w - z)).restrict (closedBall 0 r) =
        (ENNReal.ofReal A • μCn.map (fun w : ℂ => w / (((2 : ℝ) ^ n : ℝ) : ℂ))).restrict (closedBall 0 r) := by
  obtain ⟨c₀, c₁, hc₀, hc₀t, hc₁, hc₁t, hblk⟩ := h2
  obtain ⟨E, hE, hEt, hμ₁⟩ := h4
  obtain ⟨a, ha, hνU⟩ := hid
  obtain ⟨a', ha', hμC⟩ := hit
  -- push the Block 2 identity forward by the translation `· - z`
  have hkey : c₀ • (μR.map (fun w : ℂ => w - z)).restrict (ball 0 b) =
      (c₁ * E * ENNReal.ofReal a) • Dl.restrict (ball 0 b) := by
    have h := congrArg (fun m : Measure ℂ => m.map (fun w : ℂ => w - z)) hblk
    simp only [map_smul_sub, map_sub_restrict_ball, hμ₁, map_sub_map_add, Measure.restrict_smul,
      smul_smul] at h
    rw [hW, hνU, Measure.restrict_smul, smul_smul] at h
    exact h
  -- normalise: `μR.map (· - z)|ball 0 b = κ • Dl|ball 0 b`
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ≥0∞, κ = c₀⁻¹ * (c₁ * E * ENNReal.ofReal a) := ⟨_, rfl⟩
  have hκt : κ ≠ ⊤ := by
    rw [hκdef]
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hc₀.ne')
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top hc₁t.ne hEt.ne) ENNReal.ofReal_ne_top)
  have hκ0 : κ ≠ 0 := by
    rw [hκdef]
    exact mul_ne_zero (ENNReal.inv_ne_zero.2 hc₀t.ne)
      (mul_ne_zero (mul_ne_zero hc₁.ne' hE.ne') (ENNReal.ofReal_pos.2 ha).ne')
  have hmain : (μR.map (fun w : ℂ => w - z)).restrict (ball 0 b) = κ • Dl.restrict (ball 0 b) := by
    rw [hκdef, ← smul_smul]
    exact eq_inv_smul_of_smul_eq hc₀.ne' hc₀t.ne hkey
  -- the constant `A` with `ofReal A * ofReal a' = κ`
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = κ.toReal / a' := ⟨_, rfl⟩
  have hA0 : 0 < A := by
    rw [hAdef]
    exact div_pos (ENNReal.toReal_pos hκ0 hκt) ha'
  have hAκ : ENNReal.ofReal A * ENNReal.ofReal a' = κ := by
    rw [← ENNReal.ofReal_mul hA0.le, hAdef, div_mul_cancel₀ _ ha'.ne', ENNReal.ofReal_toReal hκt]
  refine ⟨A, hA0, ?_⟩
  -- the decoded canonical side: `μCn.map (· / 2^n) = a' • Dl`
  have hdec : μCn.map (fun w : ℂ => w / (((2 : ℝ) ^ n : ℝ) : ℂ)) = ENNReal.ofReal a' • Dl := by
    rw [hμC]
    exact HarmonicBalls.FirstPassS11asZoom.map_div_two_pow_decoded Dl (ENNReal.ofReal a') n
  rw [hdec, smul_smul, hAκ, Measure.restrict_smul]
  calc (μR.map (fun w : ℂ => w - z)).restrict (closedBall 0 r)
      = ((μR.map (fun w : ℂ => w - z)).restrict (ball 0 b)).restrict (closedBall 0 r) :=
        (restrict_restrict_ball_closedBall _ hr).symm
    _ = (κ • Dl.restrict (ball 0 b)).restrict (closedBall 0 r) := by rw [hmain]
    _ = κ • Dl.restrict (closedBall 0 r) := by
        rw [Measure.restrict_smul, restrict_restrict_ball_closedBall _ hr]

end FirstPassS11asAssembly
