import HarmonicBalls.Steps.Sec11.WeylPathSegments
import HarmonicBalls.Steps.Sec11.WeylPathReverse
import HarmonicBalls.Steps.Sec11.WeylPathConcatenation
import HarmonicBalls.Steps.Sec11.WeylLocalCurveLength
import HarmonicBalls.Steps.Sec11.MetricArcLength

/-!
# Weyl scaling by a continuous compactly supported weight is a Euclidean length metric

Deterministic replacement of the frozen Prop `LQGMetricAlphaWeylShiftLengthFrozen` (sections 2-3). For a Euclidean length metric `D`, a real `ξ` and a
continuous compactly supported `f`, the Weyl scaling `W = weylScaling D ξ f` is finite and `(W·).toReal` is again a
Euclidean length metric. Proof (Steps 1-7 of the note): the weight satisfies `m ≤ e^{ξ f} ≤ M` with `m = e^{-|ξ| C}`,
`M = e^{|ξ| C}`, `|f| ≤ C`; hence `m D ≤ W ≤ M D` (lower bound from `dist_le_of_lengthParametrized`, upper bound from
arclength reparametrization `exists_lengthParametrized_of_curveLength_lt_top`). The metric axioms and the length clause
then follow from `weylScaling_symm`, `weylScaling_triangle` and `weylScaling_internalMetric` (Steps 5 and 7, reused).
No external input.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric
open scoped ENNReal

/-- Deterministic statement of the Weyl-scaled length property (note section 3): for every Euclidean length metric `D`,
real `ξ`, and continuous compactly supported `f`, the Weyl scaling is finite and its real part is a Euclidean length metric. -/
def WeylScalingContinuousCompactSupportLengthStmt : Prop :=
  ∀ (D : ℂ → ℂ → ℝ) (ξ : ℝ) (f : ℂ → ℝ),
    IsEuclideanLengthMetric D → Continuous f → HasCompactSupport f →
    (∀ x y, weylScaling D ξ f x y < ∞) ∧
    IsEuclideanLengthMetric (fun x y => (weylScaling D ξ f x y).toReal)

/-- Upper comparison for a single length-parametrized competitor: if `e^{ξ f} ≤ M` then the cost of `p : [0, T] → ℂ`
is at most `M T`. -/
theorem weylScaling_le_cost_of_lengthParametrized_bound {D : ℂ → ℂ → ℝ} (ξ : ℝ) {f : ℂ → ℝ} {M : ℝ}
    (hfM : ∀ z, Real.exp (ξ * f z) ≤ M) {p : ℝ → ℂ} {T : ℝ} (u v : ℂ)
    (hp : IsLengthParametrized D p T) (h0 : p 0 = u) (hT' : p T = v) :
    weylScaling D ξ f u v ≤ ENNReal.ofReal M * ENNReal.ofReal T := by
  have hT : 0 ≤ T := hp.1
  have hcost : ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * f (p t))) ≤
      ∫⁻ _ in Icc 0 T, ENNReal.ofReal M :=
    setLIntegral_mono' measurableSet_Icc fun t _ => ENNReal.ofReal_le_ofReal (hfM (p t))
  rw [setLIntegral_const, Real.volume_Icc, sub_zero] at hcost
  unfold weylScaling
  exact iInf_le_of_le T (iInf_le_of_le p (iInf_le_of_le hp (iInf_le_of_le h0 (iInf_le_of_le hT' hcost))))

/-- Lower comparison for a single length-parametrized competitor: `m D(u,v) ≤ cost` when `m ≤ e^{ξ f}`. -/
theorem ofReal_mul_dist_le_of_lengthParametrized {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (ξ : ℝ)
    {f : ℂ → ℝ} {m : ℝ} (hm : 0 ≤ m) (hfm : ∀ z, m ≤ Real.exp (ξ * f z)) {p : ℝ → ℂ} {T : ℝ}
    (u v : ℂ) (hp : IsLengthParametrized D p T) (h0 : p 0 = u) (hT' : p T = v) :
    ENNReal.ofReal (m * D u v) ≤ ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * f (p t))) := by
  have hT : 0 ≤ T := hp.1
  have hdist : D (p 0) (p T) ≤ |T - 0| :=
    hD.dist_le_of_lengthParametrized hp ⟨le_refl 0, hT⟩ ⟨hT, le_refl T⟩
  rw [h0, hT', sub_zero, abs_of_nonneg hT] at hdist
  have hcost : ∫⁻ _ in Icc 0 T, ENNReal.ofReal m ≤
      ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * f (p t))) :=
    setLIntegral_mono' measurableSet_Icc fun t _ => ENNReal.ofReal_le_ofReal (hfm (p t))
  rw [setLIntegral_const, Real.volume_Icc, sub_zero, ← ENNReal.ofReal_mul hm] at hcost
  exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hdist hm)).trans hcost

/-- Upper comparison along a path: `W(u,v) ≤ M · len(P; D)` for every path `P` from `u` to `v`, by arclength
reparametrization of `P` (`exists_lengthParametrized_of_curveLength_lt_top`). -/
theorem IsEuclideanLengthMetric.weylScaling_le_mul_pathLength {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (ξ : ℝ) {f : ℂ → ℝ} {M : ℝ} (hM : 0 < M) (hfM : ∀ z, Real.exp (ξ * f z) ≤ M) {u v : ℂ} (P : Path u v) :
    weylScaling D ξ f u v ≤ ENNReal.ofReal M * pathLength D P := by
  by_cases hfin : pathLength D P = ⊤
  · rw [hfin, ENNReal.mul_top (ENNReal.ofReal_pos.2 hM).ne']
    exact le_top
  · have hlt : curveLength D P.extend 0 1 < ⊤ := lt_top_iff_ne_top.2 hfin
    obtain ⟨q, hq, hq0, hqT⟩ := hD.exists_lengthParametrized_of_curveLength_lt_top zero_le_one
      P.continuous_extend.continuousOn hlt
    have hL : ENNReal.ofReal (curveLength D P.extend 0 1).toReal = pathLength D P :=
      ENNReal.ofReal_toReal hfin
    have hbound := weylScaling_le_cost_of_lengthParametrized_bound ξ hfM u v hq
      (hq0.trans P.extend_zero) (hqT.trans P.extend_one)
    rw [hL] at hbound
    exact hbound

/-- The Weyl scaling by a weight with `e^{ξ f} ≤ M` is bounded by `M` times the metric. -/
theorem IsEuclideanLengthMetric.weylScaling_le_ofReal_mul {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (ξ : ℝ) {f : ℂ → ℝ} {M : ℝ} (hM : 0 < M) (hfM : ∀ z, Real.exp (ξ * f z) ≤ M) (u v : ℂ) :
    weylScaling D ξ f u v ≤ ENNReal.ofReal M * ENNReal.ofReal (D u v) := by
  have hint : ENNReal.ofReal (D u v) = ⨅ P : Path u v, pathLength D P := by
    rw [hD.ofReal_eq_internalMetric u v]
    unfold internalMetric
    simp
  rw [hint, ENNReal.mul_iInf_of_ne (ENNReal.ofReal_pos.2 hM).ne' ENNReal.ofReal_ne_top]
  exact le_iInf fun P => hD.weylScaling_le_mul_pathLength ξ hM hfM P

/-- Deterministic Weyl-scaled length property:
the Weyl scaling of a Euclidean length metric by a continuous compactly supported weight is finite and is again a
Euclidean length metric after taking real parts. -/
theorem weylScaling_continuous_compactSupport_length : WeylScalingContinuousCompactSupportLengthStmt := by
  intro D ξ f hD hf hc
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hc
  have hC' : ∀ z, |f z| ≤ C := fun z => by simpa [Real.norm_eq_abs] using hC z
  have hb : ∀ z, |ξ * f z| ≤ |ξ| * C := fun z => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hC' z) (abs_nonneg ξ)
  have hm : 0 < Real.exp (-(|ξ| * C)) := Real.exp_pos _
  have hM : 0 < Real.exp (|ξ| * C) := Real.exp_pos _
  have hfm : ∀ z, Real.exp (-(|ξ| * C)) ≤ Real.exp (ξ * f z) := fun z =>
    Real.exp_le_exp.2 (abs_le.1 (hb z)).1
  have hfM : ∀ z, Real.exp (ξ * f z) ≤ Real.exp (|ξ| * C) := fun z =>
    Real.exp_le_exp.2 (abs_le.1 (hb z)).2
  set m := Real.exp (-(|ξ| * C)) with hmdef
  set M := Real.exp (|ξ| * C) with hMdef
  have hnonneg : ∀ x y, 0 ≤ D x y := fun x y => by
    have h := hD.triangle x y x
    rw [hD.self_eq_zero, hD.symm y x] at h
    linarith
  have hup : ∀ x y, weylScaling D ξ f x y ≤ ENNReal.ofReal (M * D x y) := fun x y => by
    rw [ENNReal.ofReal_mul hM.le]
    exact hD.weylScaling_le_ofReal_mul ξ hM hfM x y
  have hfin : ∀ x y, weylScaling D ξ f x y ≠ ⊤ := fun x y =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hup x y)
  have hlow : ∀ x y, ENNReal.ofReal (m * D x y) ≤ weylScaling D ξ f x y := fun x y => by
    unfold weylScaling
    refine le_iInf fun T => le_iInf fun p => le_iInf fun hp => le_iInf fun h0 => le_iInf fun hT' => ?_
    exact ofReal_mul_dist_le_of_lengthParametrized hD ξ hm.le hfm x y hp h0 hT'
  have hsymm : ∀ x y, (weylScaling D ξ f x y).toReal = (weylScaling D ξ f y x).toReal := fun x y => by
    rw [hD.weylScaling_symm ξ f x y]
  have hEW : ∀ x y, ENNReal.ofReal ((weylScaling D ξ f x y).toReal) = weylScaling D ξ f x y :=
    fun x y => ENNReal.ofReal_toReal (hfin x y)
  have hlowR : ∀ x y, m * D x y ≤ (weylScaling D ξ f x y).toReal := fun x y => by
    have h := ENNReal.toReal_mono (hfin x y) (hlow x y)
    rwa [ENNReal.toReal_ofReal (mul_nonneg hm.le (hnonneg x y))] at h
  have hupR : ∀ x y, (weylScaling D ξ f x y).toReal ≤ M * D x y := fun x y =>
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg hM.le (hnonneg x y)) (hup x y)
  refine ⟨fun x y => lt_top_iff_ne_top.2 (hfin x y), ?_⟩
  refine
    { self_eq_zero := ?_, eq_of_eq_zero := ?_, symm := hsymm, triangle := ?_, isOpen_iff := ?_,
      ofReal_eq_internalMetric := ?_ }
  · intro z
    have h1 := hupR z z
    rw [hD.self_eq_zero, mul_zero] at h1
    exact le_antisymm h1 ENNReal.toReal_nonneg
  · intro x y h
    have h1 := hlowR x y
    rw [h] at h1
    have hDle : D x y ≤ 0 := by nlinarith
    exact hD.eq_of_eq_zero x y (le_antisymm hDle (hnonneg x y))
  · intro x y z
    have h := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin x y, hfin y z⟩)
      (hD.weylScaling_triangle ξ f x y z)
    rw [ENNReal.toReal_add (hfin x y) (hfin y z)] at h
    exact h
  · intro U
    constructor
    · intro hU z hz
      obtain ⟨ε, hε, hball⟩ := (hD.isOpen_iff U).1 hU z hz
      refine ⟨m * ε, mul_pos hm hε, fun w hw => hball w ?_⟩
      exact lt_of_mul_lt_mul_left (lt_of_le_of_lt (hlowR z w) hw) hm.le
    · intro hU
      refine (hD.isOpen_iff U).2 fun z hz => ?_
      obtain ⟨ε, hε, hball⟩ := hU z hz
      refine ⟨ε / M, div_pos hε hM, fun w hw => hball w ?_⟩
      have h2 : D z w * M < ε := (lt_div_iff₀ hM).1 hw
      exact lt_of_le_of_lt (hupR z w) (by linarith [mul_comm (D z w) M])
  · intro x y
    exact hD.weylScaling_internalMetric ξ f (E := fun a b => (weylScaling D ξ f a b).toReal) hEW hsymm x y

end HarmonicBalls
