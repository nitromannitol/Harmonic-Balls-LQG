import HarmonicBalls.FirstPass.S11r.RootedFinite
import HarmonicBalls.Steps.Sec11.WeylPathSegments
import HarmonicBalls.FirstPass.Frozen.S11d
import HarmonicBalls.FirstPass.Frozen.S11j

/-!
# Weyl scaling by a continuous function preserves Euclidean length metrics

Let `D` be a length metric on `ℂ` inducing the Euclidean topology (`IsEuclideanLengthMetric`) and let `f` be an
arbitrary continuous function (no boundedness or compact support). Then the Weyl scaling `e^{ξ f} · D`
(Gwynne-Miller, arXiv:1905.00383, (1.8), p. 6; paper Fact 2.2 III, line 445) is finite and is again a length metric
inducing the Euclidean topology.

Route: `f` is bounded on every compact set, so the weight is locally bounded above and below by positive constants.
A path parametrized by `D`-length from `x` spends at least `min(r, D(x, y))` units of time in the `D`-ball of radius `r`
about `x` (the `D`-distance to `x` at time `t` is at most `t`), which gives the local lower bound
`e^{-K} min(r, D(x, y)) ≤ e^{ξ f} · D (x, y)`. A path from `x` to `y` of `D`-length less than `s` stays in the `D`-ball
of radius `s`, which gives the local upper bound `e^{ξ f} · D (x, y) ≤ M s`. The two local bounds give separation,
`D(x, x) = 0` and the Euclidean topology; symmetry, the triangle inequality and the length property hold for every
weight (path reversal, concatenation and segment comparison).

Consequence: Fact 2.2 I for the field `h + g` with `g` continuous (`LQGMetricContinuousShiftFactI`,
`FirstPass/Frozen/S11d.lean:32`) follows from Fact 2.2 I and III for `h` (`LQGMetricFieldAxiomsUnivFrozen`,
`FirstPass/Frozen/S11j.lean:149`), at the same universe.
-/

open MeasureTheory Set Metric Filter
open scoped ENNReal

namespace HarmonicBalls

universe u

/-- The `D`-distance between the endpoints of a curve on `[a, b]` is at most its `D`-length. -/
theorem ofReal_endpoints_le_curveLength (D : ℂ → ℂ → ℝ) (p : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b) :
    ENNReal.ofReal (D (p b) (p a)) ≤ curveLength D p a b := by
  let u : ℕ → ℝ := fun n => if n = 0 then a else b
  have hu : Monotone u := by
    apply monotone_nat_of_le_succ
    intro n
    rcases n with _ | n <;> simp [u, hab]
  have humem : ∀ n, u n ∈ Icc a b := by
    intro n
    rcases n with _ | n <;> simp [u, hab]
  unfold curveLength
  refine le_iSup_of_le (⟨1, ⟨u, hu, humem⟩⟩ : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc a b}) ?_
  simp [u]

/-- **Local lower bound for a Weyl scaling.** If `-K ≤ ξ f` on the `D`-ball of radius `r` about `x`, then
`e^{-K} min(r, D(x, y)) ≤ (e^{ξ f} · D)(x, y)` for every `y`. -/
theorem IsEuclideanLengthMetric.weylScaling_ge_of_localLowerWeight {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {ξ K r : ℝ} {f : ℂ → ℝ} {x : ℂ} (hr : 0 ≤ r)
    (hw : ∀ z, D x z < r → -K ≤ ξ * f z) (y : ℂ) :
    ENNReal.ofReal (Real.exp (-K) * min r (D x y)) ≤ weylScaling D ξ f x y := by
  unfold weylScaling
  refine le_iInf fun T => le_iInf fun p => le_iInf fun hp => le_iInf fun hp0 => le_iInf fun hpT => ?_
  obtain ⟨hT0, -, hlen⟩ := hp
  have hDt : ∀ t, 0 ≤ t → t ≤ T → D x (p t) ≤ t := by
    intro t ht0 htT
    have h1 := ofReal_endpoints_le_curveLength D p ht0
    rw [hlen 0 t le_rfl ht0 htT, sub_zero, hp0, hD.symm (p t) x] at h1
    exact (ENNReal.ofReal_le_ofReal_iff ht0).mp h1
  have hDT : D x y ≤ T := by simpa [hpT] using hDt T hT0 le_rfl
  have hs0 : 0 ≤ min r T := le_min hr hT0
  calc ENNReal.ofReal (Real.exp (-K) * min r (D x y))
      ≤ ENNReal.ofReal (Real.exp (-K) * min r T) :=
        ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left (min_le_min_left r hDT) (Real.exp_pos _).le)
    _ = ∫⁻ _ in Ico 0 (min r T), ENNReal.ofReal (Real.exp (-K)) := by
        rw [setLIntegral_const, Real.volume_Ico, sub_zero, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    _ ≤ ∫⁻ t in Ico 0 (min r T), ENNReal.ofReal (Real.exp (ξ * f (p t))) := by
        refine setLIntegral_mono' measurableSet_Ico fun t ht => ?_
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (hw _ ?_))
        exact lt_of_le_of_lt (hDt t ht.1 (ht.2.le.trans (min_le_right _ _)))
          (ht.2.trans_le (min_le_left _ _))
    _ ≤ ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * f (p t))) :=
        lintegral_mono_set fun t ht => ⟨ht.1, ht.2.le.trans (min_le_right _ _)⟩

/-- **Local upper bound for a Weyl scaling.** If `e^{ξ f} ≤ M` on the `D`-ball of radius `r` about `x` and
`D(x, y) < s ≤ r`, then `(e^{ξ f} · D)(x, y) ≤ M s`. -/
theorem IsEuclideanLengthMetric.weylScaling_le_of_localUpperWeight {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {ξ M r s : ℝ} {f : ℂ → ℝ} {x y : ℂ} (hM : 0 < M)
    (hw : ∀ z, D x z < r → Real.exp (ξ * f z) ≤ M) (hs : D x y < s) (hsr : s ≤ r) :
    weylScaling D ξ f x y ≤ ENNReal.ofReal (M * s) := by
  have hDnn : 0 ≤ D x y := by
    have h1 := hD.triangle x y x
    rw [hD.self_eq_zero x, hD.symm y x] at h1
    linarith
  have hs0 : 0 < s := lt_of_le_of_lt hDnn hs
  have hlt : internalMetric D univ x y < ENNReal.ofReal s := by
    rw [← hD.ofReal_eq_internalMetric]
    exact (ENNReal.ofReal_lt_ofReal_iff hs0).2 hs
  unfold internalMetric at hlt
  obtain ⟨P, hP⟩ := iInf_lt_iff.1 hlt
  obtain ⟨-, hPlt⟩ := iInf_lt_iff.1 hP
  have hPlt' : curveLength D P.extend 0 1 < ENNReal.ofReal s := hPlt
  have hfin : curveLength D P.extend 0 1 < ⊤ := lt_trans hPlt' ENNReal.ofReal_lt_top
  have hsub : ∀ t ∈ Icc (0 : ℝ) 1, P.extend t ∈ {z | D x z < r} := by
    intro t ht
    have h1 := ofReal_endpoints_le_curveLength D P.extend ht.1
    have h2 : curveLength D P.extend 0 t ≤ curveLength D P.extend 0 1 :=
      curveLength_mono_interval D P.extend le_rfl ht.2
    rw [Path.extend_zero, hD.symm (P.extend t) x] at h1
    have h3 : ENNReal.ofReal (D x (P.extend t)) < ENNReal.ofReal s := lt_of_le_of_lt (h1.trans h2) hPlt'
    exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff hs0).1 h3) hsr
  have hW := weylScaling_le_mul_curveLength_of_subset hD ξ hM (fun z hz => hw z hz) zero_le_one
    P.continuous_extend.continuousOn hsub hfin
  rw [Path.extend_zero, Path.extend_one] at hW
  calc weylScaling D ξ f x y ≤ ENNReal.ofReal M * curveLength D P.extend 0 1 := hW
    _ ≤ ENNReal.ofReal M * ENNReal.ofReal s := by gcongr
    _ = ENNReal.ofReal (M * s) := (ENNReal.ofReal_mul hM.le).symm

/-- Local two-sided weight bounds: for continuous `f` and every `x`, the weight `e^{ξ f}` is bounded above and
below by positive constants on a small `D`-ball about `x` (this ball lies in the Euclidean unit ball about `x`). -/
theorem IsEuclideanLengthMetric.exists_localWeightBounds {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {f : ℂ → ℝ} (hf : Continuous f) (ξ : ℝ) (x : ℂ) :
    ∃ r : ℝ, 0 < r ∧ ∃ M : ℝ, 0 < M ∧ ∃ K : ℝ,
      ∀ z, D x z < r → Real.exp (ξ * f z) ≤ M ∧ -K ≤ ξ * f z := by
  obtain ⟨r, hr, hball⟩ := (hD.isOpen_iff (ball x 1)).1 isOpen_ball x (mem_ball_self one_pos)
  obtain ⟨C, hC⟩ := (isCompact_closedBall x 1).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨r, hr, Real.exp (|ξ| * C), Real.exp_pos _, |ξ| * C, fun z hz => ?_⟩
  have hfz : |f z| ≤ C := by
    simpa [Real.norm_eq_abs] using hC z (ball_subset_closedBall (hball z hz))
  have habs : |ξ * f z| ≤ |ξ| * C := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hfz (abs_nonneg ξ)
  exact ⟨Real.exp_le_exp.mpr ((le_abs_self _).trans habs), (abs_le.mp habs).1⟩

/-- **Weyl scaling by a continuous function.** For a Euclidean length metric `D` and an arbitrary continuous `f`,
the Weyl scaling `e^{ξ f} · D` is finite and `(e^{ξ f} · D).toReal` is a Euclidean length metric. -/
theorem IsEuclideanLengthMetric.weylScaling_continuous_isEuclideanLengthMetric {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) (ξ : ℝ) {f : ℂ → ℝ} (hf : Continuous f) :
    (∀ u v, weylScaling D ξ f u v < ⊤) ∧
      IsEuclideanLengthMetric (fun u v => (weylScaling D ξ f u v).toReal) := by
  -- finiteness along a path of finite `D`-length
  have hfin : ∀ x y, weylScaling D ξ f x y < ⊤ := by
    intro x y
    have hlt : internalMetric D univ x y < ⊤ := by
      rw [← hD.ofReal_eq_internalMetric]
      exact ENNReal.ofReal_lt_top
    unfold internalMetric at hlt
    obtain ⟨P, hP⟩ := iInf_lt_iff.1 hlt
    obtain ⟨-, hPlt⟩ := iInf_lt_iff.1 hP
    have hPlt' : curveLength D P.extend 0 1 < ⊤ := hPlt
    obtain ⟨M, hM, hfM⟩ := exists_expWeight_bound (isCompact_range P.continuous) hf.continuousOn ξ
    have hsub : ∀ t ∈ Icc (0 : ℝ) 1, P.extend t ∈ range P := fun t ht =>
      ⟨⟨t, ht⟩, (Path.extend_extends' P ⟨t, ht⟩).symm⟩
    have hW := weylScaling_le_mul_curveLength_of_subset hD ξ hM hfM zero_le_one
      P.continuous_extend.continuousOn hsub hPlt'
    rw [Path.extend_zero, Path.extend_one] at hW
    exact lt_of_le_of_lt hW (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hPlt')
  refine ⟨hfin, ?_⟩
  set E : ℂ → ℂ → ℝ := fun u v => (weylScaling D ξ f u v).toReal with hEdef
  have hE : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y :=
    fun x y => ENNReal.ofReal_toReal (hfin x y).ne
  have hEsymm : ∀ x y, E x y = E y x := fun x y => by
    show (weylScaling D ξ f x y).toReal = (weylScaling D ξ f y x).toReal
    rw [hD.weylScaling_symm ξ f x y]
  have hDnn : ∀ x y, 0 ≤ D x y := fun x y => by
    have h1 := hD.triangle x y x
    rw [hD.self_eq_zero x, hD.symm y x] at h1
    linarith
  -- real-valued local bounds
  have hlowR : ∀ z, ∃ r : ℝ, 0 < r ∧ ∃ K : ℝ, ∀ w, Real.exp (-K) * min r (D z w) ≤ E z w := by
    intro z
    obtain ⟨r, hr, M, -, K, hb⟩ := hD.exists_localWeightBounds hf ξ z
    refine ⟨r, hr, K, fun w => ?_⟩
    have h := hD.weylScaling_ge_of_localLowerWeight hr.le (fun y hy => (hb y hy).2) w
    rw [← hE z w] at h
    exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp h
  have hupR : ∀ z, ∃ r : ℝ, 0 < r ∧ ∃ M : ℝ, 0 < M ∧
      ∀ w s, D z w < s → s ≤ r → E z w ≤ M * s := by
    intro z
    obtain ⟨r, hr, M, hM, K, hb⟩ := hD.exists_localWeightBounds hf ξ z
    refine ⟨r, hr, M, hM, fun w s hs hsr => ?_⟩
    have h := hD.weylScaling_le_of_localUpperWeight hM (fun y hy => (hb y hy).1) hs hsr
    have hs0 : 0 ≤ s := (hDnn z w).trans hs.le
    exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hM.le hs0) h
  refine ⟨?_, ?_, hEsymm, ?_, ?_, fun z w => hD.weylScaling_internalMetric ξ f hE hEsymm z w⟩
  · -- `E z z = 0`
    intro z
    obtain ⟨r, hr, M, hM, hup⟩ := hupR z
    by_contra hne
    have hpos : 0 < E z z := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hne)
    set s : ℝ := min r (E z z / (2 * M)) with hsdef
    have hs : 0 < s := lt_min hr (div_pos hpos (mul_pos two_pos hM))
    have h1 : E z z ≤ M * s := hup z s (by rw [hD.self_eq_zero z]; exact hs) (min_le_left _ _)
    have h2 : M * s ≤ M * (E z z / (2 * M)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hM.le
    have h3 : M * (E z z / (2 * M)) = E z z / 2 := by field_simp
    linarith
  · -- separation
    intro z w hzw
    obtain ⟨r, hr, K, hlow⟩ := hlowR z
    have h := hlow w
    rw [hzw] at h
    by_contra hne
    have hDpos : 0 < D z w := lt_of_le_of_ne (hDnn z w) (fun h0 => hne (hD.eq_of_eq_zero z w h0.symm))
    have : 0 < Real.exp (-K) * min r (D z w) := mul_pos (Real.exp_pos _) (lt_min hr hDpos)
    linarith
  · -- triangle inequality
    intro x y z
    have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨(hfin x y).ne, (hfin y z).ne⟩)
      (hD.weylScaling_triangle ξ f x y z)
    rw [ENNReal.toReal_add (hfin x y).ne (hfin y z).ne] at h
    exact h
  · -- the topology
    intro U
    constructor
    · intro hU z hz
      obtain ⟨ε, hε, hball⟩ := (hD.isOpen_iff U).mp hU z hz
      obtain ⟨r, hr, K, hlow⟩ := hlowR z
      refine ⟨Real.exp (-K) * min r ε, mul_pos (Real.exp_pos _) (lt_min hr hε), fun w hw => hball w ?_⟩
      by_contra hge
      rw [not_lt] at hge
      have h1 : Real.exp (-K) * min r ε ≤ Real.exp (-K) * min r (D z w) :=
        mul_le_mul_of_nonneg_left (min_le_min_left r hge) (Real.exp_pos _).le
      have h2 := hlow w
      linarith
    · intro h
      refine (hD.isOpen_iff U).mpr fun z hz => ?_
      obtain ⟨ε, hε, hEU⟩ := h z hz
      obtain ⟨r, hr, M, hM, hup⟩ := hupR z
      refine ⟨min r (ε / (2 * M)), lt_min hr (div_pos hε (mul_pos two_pos hM)), fun w hw => hEU w ?_⟩
      have h1 := hup w (min r (ε / (2 * M))) hw (min_le_left _ _)
      have h2 : M * min r (ε / (2 * M)) ≤ M * (ε / (2 * M)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hM.le
      have h3 : M * (ε / (2 * M)) = ε / 2 := by field_simp
      linarith

/-- **Derived: Fact 2.2 I for a continuous shift** (`LQGMetricContinuousShiftFactI`,
`FirstPass/Frozen/S11d.lean:32`) from the field axioms (`LQGMetricFieldAxiomsUnivFrozen`,
`FirstPass/Frozen/S11j.lean:149`) at the same universe. Fact 2.2 III identifies
`e^{ξ (g - α₀ log |·|)} · D_{h^ℂ}` with `e^{ξ g} · D_h` simultaneously for all continuous `g`, almost surely; Fact 2.2 I
makes `D_h` a Euclidean length metric; the deterministic theorem
`IsEuclideanLengthMetric.weylScaling_continuous_isEuclideanLengthMetric` concludes. -/
theorem lqgMetricContinuousShiftFactI_of_fieldAxioms (hAx : LQGMetricFieldAxiomsUnivFrozen.{u}) :
    LQGMetricContinuousShiftFactI.{u} := by
  intro γ ξ α₀ Ω _ P hC hcirc hh hγ hγ2 hα 𝔇 h𝔇 g hg
  have hA := hAx Ω P γ ξ α₀ hC hcirc hh hγ hγ2 hα 𝔇 h𝔇
  filter_upwards [hA.1, hA.2.2.1] with ω h1 h3
  have heq : ∀ u v, weylScaling (𝔇 (hC ω)) ξ (fun x => g x - α₀ * Real.log ‖x‖) u v =
      weylScaling (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal) ξ g u v :=
    h3 g hg
  have hD : IsEuclideanLengthMetric
      (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal) := h1.2
  simp only [heq]
  exact hD.weylScaling_continuous_isEuclideanLengthMetric ξ hg

end HarmonicBalls
