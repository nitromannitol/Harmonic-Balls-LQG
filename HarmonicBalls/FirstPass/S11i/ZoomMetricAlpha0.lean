import HarmonicBalls.FirstPass.S11i.Step8PhysReduction
import HarmonicBalls.Steps.Sec11.WeylHomeomorph
import HarmonicBalls.Steps.Sec11.WeylMetricConstantScaling
import HarmonicBalls.Steps.Sec11.CurveConstantFiber

/-!
# Zoom of the insertion-`α` LQG metric with coefficient `Q - α`

`zoomMetricNormAlpha0_stmt : ZoomMetricNormAlpha0Stmt.{0}` (`FirstPass/S11i/Step8PhysReduction.lean`, the metric target) is proved for every insertion `α`, over probability spaces in `Type`. This is route 1: with `R = 2^k` and `C_{α,R} = h_R(0) + (Q_γ - α) log R`, the zoom of the
insertion-`α` metric is `D^α(R x, R y) = e^{ξ C_{α,R}} · D^{(R),α}(x, y)`, where `D^{(R),α}` is the Weyl scaling of the
normalized field `normField R` (`FirstPass/S11i/HzoomScale.lean:40`) with the same weight `-α log|·|`.

Proof. Only axioms I, III, IV of `IsLQGMetric` (`Defs/LQGMetric.lean:179`) are used. Dilation covariance of `weylScaling` is
`weylScaling_comp_homeomorph` (`Steps/Sec11/WeylHomeomorph.lean`); the positive multiple is
`IsEuclideanLengthMetric.weylScaling_const_mul` (`Steps/Sec11/WeylMetricConstantScaling.lean`); the log singularity at `0` is
harmless because a length-parametrized path spends Lebesgue-null time at a point
(`IsEuclideanLengthMetric.ae_ne_of_lengthParametrized`, `Steps/Sec11/CurveConstantFiber.lean`). The new facts proved here are
the constant shift of a general Weyl weight (`weylScaling_add_const`) and the congruence of Weyl weights off the origin
(`weylScaling_congr_of_ne_zero`). No Proposed input is used. The coefficient `Q - α` comes from the affine coordinate change
of axiom IV (`lqgQ γ log R`) together with the insertion term `-α log|R z| = -α log|z| - α log R`.
-/

namespace HarmonicBalls.FirstPassS11iZoomMetricAlpha0

open MeasureTheory Filter Topology Set
open scoped ENNReal
open HarmonicBalls.FirstPassS11iHzoom HarmonicBalls.FirstPassS11iStep8PhysReduction
open HarmonicBalls.FirstPassS11iStep8Zoom

/-- A Euclidean length metric is nonnegative: `0 = D(x, x) ≤ D(x, y) + D(y, x) = 2 D(x, y)` (triangle inequality and symmetry). -/
lemma isEuclideanLengthMetric_nonneg {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (x y : ℂ) :
    0 ≤ D x y := by
  linarith [hD.triangle x y x, hD.self_eq_zero x, hD.symm y x]

/-- **Constant shift of a Weyl weight.** `weylScaling D ξ (f + k) = e^{ξ k} · weylScaling D ξ f`: the integrand gains the
constant factor `e^{ξ k}`, which pulls out of each path integral and then out of the infimum over paths. -/
lemma weylScaling_add_const (D : ℂ → ℂ → ℝ) (ξ : ℝ) (f : ℂ → ℝ) (k : ℝ) (u v : ℂ) :
    weylScaling D ξ (fun z => f z + k) u v =
      ENNReal.ofReal (Real.exp (ξ * k)) * weylScaling D ξ f u v := by
  have hpos : ENNReal.ofReal (Real.exp (ξ * k)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hint : ∀ (T : ℝ) (p : ℝ → ℂ),
      ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * (f (p t) + k))) =
        ENNReal.ofReal (Real.exp (ξ * k)) * ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * f (p t))) := by
    intro T p
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun t => ?_
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  unfold weylScaling
  simp only [hint, ENNReal.mul_iInf_of_ne hpos ENNReal.ofReal_ne_top]

/-- **Congruence of Weyl weights off the origin.** If `f = g` away from `0`, then `weylScaling D ξ f = weylScaling D ξ g` for an
Euclidean length metric `D`. A length-parametrized path meets the point `0` only on a Lebesgue-null set of times
(`IsEuclideanLengthMetric.ae_ne_of_lengthParametrized`), so the value of the weight at `0` does not enter the integrals. This is
why the convention `Real.log 0 = 0` in `-α log‖·‖` does not affect the metric. -/
lemma weylScaling_congr_of_ne_zero {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (ξ : ℝ) (f g : ℂ → ℝ)
    (hfg : ∀ z : ℂ, z ≠ 0 → f z = g z) (u v : ℂ) :
    weylScaling D ξ f u v = weylScaling D ξ g u v := by
  have key : ∀ (T : ℝ) (p : ℝ → ℂ), IsLengthParametrized D p T →
      ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * f (p t))) =
        ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * g (p t))) := by
    intro T p hp
    refine lintegral_congr_ae ?_
    filter_upwards [hD.ae_ne_of_lengthParametrized hp 0] with t ht
    rw [hfg _ ht]
  unfold weylScaling
  refine iInf_congr fun T => iInf_congr fun p =>
    iInf_congr_Prop Iff.rfl fun hp => iInf_congr_Prop Iff.rfl fun _ => iInf_congr_Prop Iff.rfl fun _ => ?_
  exact key T p hp

/-- **Zoom identity of the insertion-`α` metric, one scale, almost surely.** For `R > 0` and almost every `ω`, for all `x, y`:
`D(R x, R y) = e^{ξ C} · weylScaling (𝔇 (normField R hC hcirc ω)) ξ (-α log|·|) (x, y)` in `ENNReal`, with
`C = h_R(0) + (Q_γ - α) log R` (`hcirc ω R 0 + (lqgQ γ - α) log R`). -/
theorem zoom_metric_alpha_identity {Ω₀ : Type} [MeasurableSpace Ω₀] {P : Measure Ω₀} {γ ξ α : ℝ}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (hM : IsLQGMetric γ ξ 𝔇)
    {hC : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc : Ω₀ → ℝ → ℂ → ℝ} {D : Ω₀ → ℂ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    (hDae : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) = weylScaling (𝔇 (hC ω)) ξ (fun x => -α * Real.log ‖x‖) u v)
    {R : ℝ} (hR : 0 < R) :
    ∀ᵐ ω ∂P, ∀ x y : ℂ, ENNReal.ofReal (D ω ((R : ℂ) * x) ((R : ℂ) * y)) =
      ENNReal.ofReal (Real.exp (ξ * (hcirc ω R 0 + (lqgQ γ - α) * Real.log R))) *
        weylScaling (𝔇 (normField R hC hcirc ω)) ξ (fun x => -α * Real.log ‖x‖) x y := by
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have hGN := isWholePlaneGFF_normalized hG hR.ne'
  have hWN := ae_weylScaling_of_isWholePlaneGFF hM hGN
  have hIV := (hM.satisfiesLQGMetricAxioms Ω₀ P hC hcirc (fun _ _ => (0 : ℝ)) hG
    (fun _ => continuous_const) (fun _ => measurable_const)).coordChange R hR 0
  have hI0 := (hM.satisfiesLQGMetricAxioms Ω₀ P hC hcirc (fun _ _ => (0 : ℝ)) hG
    (fun _ => continuous_const) (fun _ => measurable_const)).ae_isEuclideanLengthMetric
  have hIN := (hM.satisfiesLQGMetricAxioms Ω₀ P (normField R hC hcirc) (normCirc R hcirc)
    (fun _ _ => (0 : ℝ)) hGN (fun _ => continuous_const) (fun _ => measurable_const)).ae_isEuclideanLengthMetric
  filter_upwards [hDae, hWN, hIV, hI0, hIN] with ω hDω hWNω hIVω hI0ω hINω
  simp only [addFunPairing_fun_zero] at hI0ω hINω
  simp only [addFunPairing_fun_zero, add_zero,
    addFunPairing_affine_eq_normField (hC := hC) (hcirc := hcirc) γ hR ω] at hIVω
  -- The metric of `hC ω` at scale `R` is `e^{ξ c}` times the metric of the normalized field, `c = Q log R + h_R(0)`.
  have hc : ∀ a b : ℂ, 𝔇 (hC ω) ((R : ℂ) * a) ((R : ℂ) * b) =
      Real.exp (ξ * (lqgQ γ * Real.log R + hcirc ω R 0)) * 𝔇 (normField R hC hcirc ω) a b := by
    intro a b
    have hA := hWNω (fun _ => lqgQ γ * Real.log R + hcirc ω R 0) continuous_const a b
    rw [weylScaling_const] at hA
    have hB := hWNω (fun _ => (0 : ℝ)) continuous_const a b
    simp only [addFunPairing_fun_zero] at hB
    have hnn0 := isEuclideanLengthMetric_nonneg hI0ω ((R : ℂ) * a) ((R : ℂ) * b)
    have hnn1 := isEuclideanLengthMetric_nonneg hINω a b
    rw [← ENNReal.ofReal_eq_ofReal_iff hnn0 (mul_nonneg (Real.exp_pos _).le hnn1), hIVω a b, hA, ← hB,
      ENNReal.ofReal_mul (Real.exp_pos _).le]
  intro x y
  have hL := (hDω ((R : ℂ) * x) ((R : ℂ) * y)).2
  have hdil' : weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) ((R : ℂ) * x) ((R : ℂ) * y) =
      weylScaling (fun a b => 𝔇 (hC ω) (Homeomorph.mulLeft₀ (R : ℂ) hRc a) (Homeomorph.mulLeft₀ (R : ℂ) hRc b))
        ξ ((fun z => -α * Real.log ‖z‖) ∘ Homeomorph.mulLeft₀ (R : ℂ) hRc) x y :=
    (weylScaling_comp_homeomorph (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖)
      (Homeomorph.mulLeft₀ (R : ℂ) hRc) x y).symm
  have hfun : (fun a b => 𝔇 (hC ω) (Homeomorph.mulLeft₀ (R : ℂ) hRc a) (Homeomorph.mulLeft₀ (R : ℂ) hRc b)) =
      fun a b => Real.exp (ξ * (lqgQ γ * Real.log R + hcirc ω R 0)) * 𝔇 (normField R hC hcirc ω) a b :=
    funext fun a => funext fun b => hc a b
  have hcong : weylScaling (𝔇 (normField R hC hcirc ω)) ξ
      ((fun z => -α * Real.log ‖z‖) ∘ Homeomorph.mulLeft₀ (R : ℂ) hRc) x y =
      weylScaling (𝔇 (normField R hC hcirc ω)) ξ (fun z => -α * Real.log ‖z‖ + -α * Real.log R) x y := by
    refine weylScaling_congr_of_ne_zero hINω ξ _ _ (fun z hz => ?_) x y
    show -α * Real.log ‖(R : ℂ) * z‖ = -α * Real.log ‖z‖ + -α * Real.log R
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le,
      Real.log_mul hR.ne' (norm_ne_zero_iff.mpr hz)]
    ring
  have hexp : Real.exp (ξ * (lqgQ γ * Real.log R + hcirc ω R 0)) * Real.exp (ξ * (-α * Real.log R)) =
      Real.exp (ξ * (hcirc ω R 0 + (lqgQ γ - α) * Real.log R)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hL, hdil', hfun, IsEuclideanLengthMetric.weylScaling_const_mul hINω
    (Real.exp_pos (ξ * (lqgQ γ * Real.log R + hcirc ω R 0))), hcong,
    weylScaling_add_const, ← mul_assoc,
    ← ENNReal.ofReal_mul (Real.exp_pos (ξ * (lqgQ γ * Real.log R + hcirc ω R 0))).le, hexp]

/-- **`ZoomMetricNormAlphaFor`, proved.** For a whole-plane model and an LQG metric `D` of the insertion-`α` field, the zoom of
`D` at scale `2^k` is almost surely a positive constant times the metric `Dk` of the normalized field `normField (2^k)`, which
is again an insertion-`α` LQG metric (`IsLQGMetricOfField`). The constant is `e^{ξ C}` with `C = h_{2^k}(0) + (Q_γ - α) log 2^k`. -/
theorem zoomMetricNormAlpha_of_isLQGMetricOfField {Ω₀ : Type} [MeasurableSpace Ω₀] {P : Measure Ω₀} {γ ξ α : ℝ}
    {hC : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc : Ω₀ → ℝ → ℂ → ℝ} {D : Ω₀ → ℂ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) (hD : IsLQGMetricOfField P γ ξ α hC D) :
    ZoomMetricNormAlphaFor P γ ξ α hC hcirc D := by
  obtain ⟨𝔇, hM, hDae⟩ := hD
  intro k
  have hR : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hid := zoom_metric_alpha_identity hM hG hDae hR
  refine ⟨fun ω x y => (weylScaling (𝔇 (normField ((2 : ℝ) ^ k) hC hcirc ω)) ξ
      (fun x => -α * Real.log ‖x‖) x y).toReal, ⟨𝔇, hM, ?_⟩, ?_⟩
  · filter_upwards [hid] with ω hω
    intro u v
    have hfin : weylScaling (𝔇 (normField ((2 : ℝ) ^ k) hC hcirc ω)) ξ
        (fun x => -α * Real.log ‖x‖) u v ≠ ⊤ := by
      intro htop
      have h := hω u v
      rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'] at h
      exact ENNReal.ofReal_ne_top h
    exact ⟨ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin⟩
  · filter_upwards [hid, hDae] with ω hω hDω
    refine ⟨Real.exp (ξ * (hcirc ω ((2 : ℝ) ^ k) 0 + (lqgQ γ - α) * Real.log ((2 : ℝ) ^ k))),
      Real.exp_pos _, fun x y => ?_⟩
    have hfin : weylScaling (𝔇 (normField ((2 : ℝ) ^ k) hC hcirc ω)) ξ
        (fun x => -α * Real.log ‖x‖) x y ≠ ⊤ := by
      intro htop
      have h := hω x y
      rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'] at h
      exact ENNReal.ofReal_ne_top h
    have h := hω x y
    rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_mul (Real.exp_pos _).le] at h
    simp only [zoomMetric, one_mul]
    exact (ENNReal.ofReal_eq_ofReal_iff (hDω _ _).1
      (mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg)).mp h

/-- **`ZoomMetricNormAlpha0Stmt`, proved**. The insertion-`α₀` metric normalization for every whole-plane
model and every insertion `α₀`, over probability spaces in `Type` (`IsLQGMetric` quantifies over `Type`), that is, at `v = 0`. -/
theorem zoomMetricNormAlpha0_stmt : ZoomMetricNormAlpha0Stmt.{0} := by
  intro γ ξ α₀ Ω _ P hC hcirc D hG hD
  exact zoomMetricNormAlpha_of_isLQGMetricOfField hG hD

end HarmonicBalls.FirstPassS11iZoomMetricAlpha0

