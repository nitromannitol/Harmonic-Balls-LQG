import Mathlib
import HarmonicBalls.LPStage.GFF
import HarmonicBalls.LPStage.LQGMeasure
import HarmonicBalls.LPStage.LQGMeasureInputs
import HarmonicBalls.LPStage.LQGMeasureFullSupport

/-!
# LP stage: full support of the LQG measure, part 2 (z3, task `fp-lpstage-lqg-full-support-then-square-positive`, R57)

LP port of the rescaled-field step of the HB full-support chain:
* affine images of the field and of its LQG measure (`HarmonicBalls/Proofs/Sec2/AffineField.lean`);
* the Gaussian tail and the polynomial high-probability transfer (`HarmonicBalls/Proofs/Sec2/RescaledUniform.lean`, 1-130);
* the affine map `x ↦ 2R x - R(1+i)` of the unit square onto `[-R, R]²`.
The coordinate-change input is the LP Prop `LQGMeasureCoordChangeLP` (`LPStage/LQGMeasureInputs.lean`), used only as a
hypothesis.
-/

open MeasureTheory ProbabilityTheory Metric Filter Set Topology
open scoped ENNReal
open LatticeProb.Gauss

universe u

namespace LatticeProb.LQG

/-! ### Affine images of the LQG measure (`Proofs/Sec2/AffineField.lean`) -/

section AffineField

variable {Ω : Type*}

/-- Circle averages of `h^ℂ(a · + b) - h^ℂ_{|a|}(b)`. -/
noncomputable def affineCircle (hcirc : Ω → ℝ → ℂ → ℝ) (a b : ℂ) : Ω → ℝ → ℂ → ℝ :=
  fun ω r z => hcirc ω (‖a‖ * r) (a * z + b) - hcirc ω ‖a‖ b

/-- The candidate LQG measure of `h^ℂ(a · + b) - h^ℂ_{|a|}(b)`:
`e^{-γ (h^ℂ_{|a|}(b) + Q log |a|)} μ₀((· - b)/a)⁻¹`. -/
noncomputable def affineMeasure (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ₀ : Ω → Measure ℂ) (a b : ℂ) :
    Ω → Measure ℂ :=
  fun ω => ENNReal.ofReal (Real.exp (γ * (-(hcirc ω ‖a‖ b + lqgQ γ * Real.log ‖a‖)))) •
    (μ₀ ω).map fun x => (x - b) / a

/-- Adding a constant `c` to the circle averages multiplies the LQG limit by `e^{γc}`. -/
theorem IsLQGLimit.add_const {γ : ℝ} {hε : ℝ → ℂ → ℝ} {m : Measure ℂ} (h : IsLQGLimit γ hε m) (c : ℝ) :
    IsLQGLimit γ (fun ε z => hε ε z + c) (ENNReal.ofReal (Real.exp (γ * c)) • m) := by
  have hm := h.isLocallyFiniteMeasure
  have happrox : ∀ ε, lqgApprox γ (fun ε z => hε ε z + c) ε =
      ENNReal.ofReal (Real.exp (γ * c)) • lqgApprox γ hε ε := by
    intro ε
    simp only [lqgApprox]
    rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    funext z
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_add, Real.exp_add]
    ring_nf
  refine ⟨⟨fun x => ?_⟩, fun f hf hfc => ?_⟩
  · obtain ⟨U, hU, hfin⟩ := hm.finiteAtNhds x
    exact ⟨U, hU, by
      rw [Measure.smul_apply, smul_eq_mul]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin⟩
  · simp only [happrox, integral_smul_measure]
    exact (h.tendsto_integral f hf hfc).const_smul _

/-- The image of a ball under `x ↦ (x - b)/a`: `((x - b)/a)⁻¹' B_r(w) = B_{|a| r}(a w + b)`. -/
theorem map_affine_ball (m : Measure ℂ) {a : ℂ} (ha : a ≠ 0) (b w : ℂ) (r : ℝ) :
    (m.map fun x => (x - b) / a) (ball w r) = m (ball (a * w + b) (‖a‖ * r)) := by
  rw [Measure.map_apply (by fun_prop) measurableSet_ball]
  congr 1
  ext x
  simp only [mem_preimage, mem_ball, dist_eq_norm]
  have hna : 0 < ‖a‖ := norm_pos_iff.2 ha
  rw [show (x - b) / a - w = (x - (a * w + b)) / a by field_simp; ring, norm_div,
    div_lt_iff₀ hna, mul_comm r ‖a‖]

theorem affineMeasure_ball (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ₀ : Ω → Measure ℂ) {a : ℂ} (ha : a ≠ 0)
    (b : ℂ) (ω : Ω) (w : ℂ) (r : ℝ) :
    affineMeasure γ hcirc μ₀ a b ω (ball w r) =
      ENNReal.ofReal (Real.exp (γ * (-(hcirc ω ‖a‖ b + lqgQ γ * Real.log ‖a‖)))) *
        μ₀ ω (ball (a * w + b) (‖a‖ * r)) := by
  rw [affineMeasure, Measure.smul_apply, smul_eq_mul, map_affine_ball _ ha]

/-- `fieldCircleAverage 0` is the identity. -/
theorem fieldCircleAverage_zero_lp (hcirc : ℝ → ℂ → ℝ) : fieldCircleAverage 0 hcirc = hcirc := by
  funext r z; simp [fieldCircleAverage]

/-- The LQG measure of the affine image of the field (`α₀ = 0`), from `LQGMeasureCoordChangeLP`. -/
theorem isLQGMeasureOfField_affine [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ₀ : Ω → Measure ℂ} (hCC : LQGMeasureCoordChangeLP P γ 0 hC hcirc)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hμ₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀) {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    IsLQGMeasureOfField P γ 0 (affineCircle hcirc a b) (affineMeasure γ hcirc μ₀ a b) := by
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  filter_upwards [hCC hGFF hγ hγ2 hQ μ₀ hμ₀] with ω hω
  have h := (hω a ha b).add_const (-(hcirc ω ‖a‖ b + lqgQ γ * Real.log ‖a‖))
  rw [fieldCircleAverage_zero_lp] at h ⊢
  have heq : (fun ε z => hcirc ω (‖a‖ * ε) (a * z + b) + lqgQ γ * Real.log ‖a‖ +
      -(hcirc ω ‖a‖ b + lqgQ γ * Real.log ‖a‖)) = affineCircle hcirc a b ω := by
    funext ε z; simp only [affineCircle]; ring
  rw [heq] at h
  exact h

end AffineField

/-! ### Gaussian tail and polynomial high probability (`Proofs/Sec2/RescaledUniform.lean`, 31-82) -/

/-- For `a > 0` and `c > 0`, `ε^a ≤ c` for all small `ε > 0` (`Proofs/Sec2/PolyHighProb.lean:18`). -/
theorem exists_pos_forall_rpow_le_lp {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ∃ r₁ > 0, ∀ r : ℝ, 0 < r → r < r₁ → r ^ a ≤ c := by
  refine ⟨c ^ a⁻¹, Real.rpow_pos_of_pos hc _, fun r hr hr₁ => ?_⟩
  calc r ^ a ≤ (c ^ a⁻¹) ^ a := Real.rpow_le_rpow hr.le hr₁.le ha.le
    _ = c := by rw [← Real.rpow_mul hc.le, inv_mul_cancel₀ ha.ne', Real.rpow_one]

/-- Real reparametrization of the scale: `ε ↦ E(ε^a)` keeps `PolyHighProb` for `a > 0`. -/
theorem polyHighProb_comp_rpow_lp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E : ℝ → Set Ω}
    (h : PolyHighProb P E) {a : ℝ} (ha : 0 < a) : PolyHighProb P fun r => E (r ^ a) := by
  obtain ⟨p, hp, C, r₀, hr₀, hE⟩ := h
  obtain ⟨r₁, hr₁, h1⟩ := exists_pos_forall_rpow_le_lp ha (half_pos hr₀)
  refine ⟨a * p, mul_pos ha hp, C, r₁, hr₁, fun r hr hrr => ?_⟩
  calc P (E (r ^ a))ᶜ ≤ ENNReal.ofReal (C * (r ^ a) ^ p) :=
        hE _ (Real.rpow_pos_of_pos hr _) ((h1 r hr hrr).trans_lt (half_lt_self hr₀))
    _ = ENNReal.ofReal (C * r ^ (a * p)) := by rw [← Real.rpow_mul hr.le]

/-- Gaussian tail: for a centred Gaussian `X` with `Var X ≤ V`, `P[|X| ≥ L] ≤ 2 exp(-L²/(2V))`. -/
theorem measure_le_abs_le_of_hasGaussianLaw_lp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    (hG : HasGaussianLaw X P) (hmean : ∫ ω, X ω ∂P = 0) {V : ℝ} (hV : Var[X; P] ≤ V) (hV0 : 0 < V)
    {L : ℝ} (hL : 0 ≤ L) : P {ω | L ≤ |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-(L ^ 2) / (2 * V))) := by
  have hP := hG.isProbabilityMeasure
  set v : NNReal := (Var[X; P]).toNNReal with hv_def
  have hv : (v : ℝ) = Var[X; P] := Real.coe_toNNReal _ (variance_nonneg X P)
  have hlaw : HasLaw X (gaussianReal 0 v) P := ⟨hG.aemeasurable, by rw [hG.map_eq_gaussianReal, hmean]⟩
  have hint : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) P := by
    intro t
    have h := integrable_exp_mul_gaussianReal (μ := 0) (v := v) t
    rw [← hlaw.map_eq] at h
    exact (integrable_map_measure (by fun_prop) hG.aemeasurable).1 h
  have hvV : (v : ℝ) ≤ V := by rw [hv]; exact hV
  set s : ℝ := L / V with hs
  have hs0 : 0 ≤ s := by positivity
  have hbound : Real.exp (-s * L) * Real.exp (0 * s + v * s ^ 2 / 2) ≤ Real.exp (-(L ^ 2) / (2 * V)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    calc -s * L + (0 * s + v * s ^ 2 / 2) ≤ -s * L + V * s ^ 2 / 2 := by nlinarith [sq_nonneg s]
      _ = -(L ^ 2) / (2 * V) := by rw [hs]; field_simp; ring
  have hup : P.real {ω | L ≤ X ω} ≤ Real.exp (-(L ^ 2) / (2 * V)) := by
    refine (measure_ge_le_exp_mul_mgf L hs0 (hint s)).trans ?_
    rw [mgf_gaussianReal hlaw]; exact hbound
  have hlow : P.real {ω | X ω ≤ -L} ≤ Real.exp (-(L ^ 2) / (2 * V)) := by
    refine (measure_le_le_exp_mul_mgf (-L) (neg_nonpos.2 hs0) (hint (-s))).trans ?_
    rw [mgf_gaussianReal hlaw]
    convert hbound using 3 <;> ring
  have hsub : {ω | L ≤ |X ω|} ⊆ {ω | L ≤ X ω} ∪ {ω | X ω ≤ -L} := by
    intro ω hω
    rcases le_abs'.1 (show L ≤ |X ω| from hω) with h | h
    · exact Or.inr h
    · exact Or.inl h
  calc P {ω | L ≤ |X ω|} ≤ P {ω | L ≤ X ω} + P {ω | X ω ≤ -L} :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ = ENNReal.ofReal (P.real {ω | L ≤ X ω}) + ENNReal.ofReal (P.real {ω | X ω ≤ -L}) := by
        rw [ofReal_measureReal, ofReal_measureReal]
    _ ≤ ENNReal.ofReal (Real.exp (-(L ^ 2) / (2 * V))) + ENNReal.ofReal (Real.exp (-(L ^ 2) / (2 * V))) :=
        add_le_add (ENNReal.ofReal_le_ofReal hup) (ENNReal.ofReal_le_ofReal hlow)
    _ = ENNReal.ofReal (2 * Real.exp (-(L ^ 2) / (2 * V))) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

/-! ### The affine map of the unit square onto `[-R, R]²` (`Proofs/Sec2/RescaledUniform.lean`, 83-130) -/

/-- The linear part `2R` of the affine map `x ↦ 2R x - R(1+i)`. -/
noncomputable def squareA (R : ℝ) : ℂ := ((2 * R : ℝ) : ℂ)

/-- The translation part `-R(1+i)` of the affine map `x ↦ 2R x - R(1+i)`. -/
noncomputable def squareB (R : ℝ) : ℂ := -((R : ℂ) + (R : ℂ) * Complex.I)

theorem norm_squareA {R : ℝ} (hR : 0 < R) : ‖squareA R‖ = 2 * R := by
  rw [squareA, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]

theorem squareA_ne_zero {R : ℝ} (hR : 0 < R) : squareA R ≠ 0 := by
  rw [← norm_pos_iff, norm_squareA hR]; positivity

/-- Every point of `closedBall 0 R` is the image of a point of the unit square. -/
theorem exists_square_preimage {R : ℝ} (hR : 0 < R) {w : ℂ} (hw : w ∈ closedBall (0 : ℂ) R) :
    ∃ z ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1, squareA R * z + squareB R = w := by
  rw [mem_closedBall_zero_iff] at hw
  have hre := (abs_le.1 ((Complex.abs_re_le_norm w).trans hw))
  have him := (abs_le.1 ((Complex.abs_im_le_norm w).trans hw))
  refine ⟨⟨(w.re + R) / (2 * R), (w.im + R) / (2 * R)⟩, ?_, ?_⟩
  · rw [Complex.mem_reProdIm]
    refine ⟨⟨div_nonneg (by linarith) (by positivity), ?_⟩, ⟨div_nonneg (by linarith) (by positivity), ?_⟩⟩
    · show (w.re + R) / (2 * R) ≤ 1
      rw [div_le_one (by positivity)]; linarith
    · show (w.im + R) / (2 * R) ≤ 1
      rw [div_le_one (by positivity)]; linarith
  · apply Complex.ext
    · simp [squareA, squareB]
      field_simp
      ring
    · simp [squareA, squareB]
      field_simp
      ring

end LatticeProb.LQG
