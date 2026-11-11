import HarmonicBalls.FirstPass.Frozen.S11j
import HarmonicBalls.Steps.Sec11.WeylPathSegments
import HarmonicBalls.Steps.Sec11.WeylPathConcatenation
import HarmonicBalls.Steps.Sec11.WeylPathReverse
import HarmonicBalls.Steps.Sec11.WeylLocalEdges
import HarmonicBalls.Steps.Sec11.ArcLengthInterval

/-! # Weyl composition for the outer scaling (Frozen statement `WeylMetricCompositionContinuousOuterFrozen`)

Derivation of `WeylMetricCompositionContinuousOuterFrozen` (`FirstPass/Frozen/S11j.lean:117`; source: Bou-Rabee-Gwynne arXiv:2208.11795, Fact 2.2 III, and Gwynne-Miller
(1.8)). For `ξ > 0`, a Euclidean length metric `D`, a weight `g` continuous on `ℂ ∖ {0}` with finite Weyl scaling and a
continuous weight `f`, the Weyl scaling of the inner metric `d = (weylScaling D ξ g).toReal` by `f` equals the Weyl
scaling of `D` by `g + f`.

Proof structure (no hypothesis beyond the frozen ones; no literature input):
* `innerDist` is a metric; its topology is one-way (`weylScaling_nhds`: inner balls are Euclidean neighbourhoods),
  which is all the argument needs: `d`-small points are Euclidean-close (an exit-time argument on the annulus
  `{r ≤ |z - x| ≤ R}`, which avoids `0`), and `innerDist_eq_zero` separates points.
* `weylScaling_le_iterated`: a `d`-length-parametrized curve gives a `D`-admissible competitor for `g + f`
  (concatenation of near-optimal `D`-curves over a uniform partition, uniform multiplicative continuity of `e^{ξ f}`).
* `weylScaling_innerDist_le_direct`: a `D`-length-parametrized curve for `g + f` is reparametrized by inner arc length
  (`exists_arclength_innerDist`, a copy of the tracking lemma with the one-way topology); a Riemann comparison
  (`riemann_arc`) gives the cost bound, and `ρ ↓ 1` removes the factor.
-/

namespace HarmonicBalls

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal NNReal

theorem IsEuclideanLengthMetric.nonneg' {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (x y : ℂ) :
    0 ≤ D x y := by
  have h1 := hD.triangle x y x
  have h2 := hD.symm y x
  have h3 := hD.self_eq_zero x
  linarith

theorem IsEuclideanLengthMetric.exists_near_lt {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (x : ℂ) {c : ℝ} (hc : 0 < c) : ∃ r > 0, ∀ z, dist z x < r → D x z < c := by
  have hopen : IsOpen {w | D x w < c} := by
    rw [hD.isOpen_iff]
    intro w hw
    have hw' : D x w < c := hw
    refine ⟨c - D x w, by linarith, fun v hv => ?_⟩
    show D x v < c
    have := hD.triangle x w v
    linarith
  have hx : x ∈ {w | D x w < c} := by
    show D x x < c
    rw [hD.self_eq_zero x]
    exact hc
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen x hx
  exact ⟨r, hr, fun z hz => hball (Metric.mem_ball.mpr hz)⟩

theorem IsEuclideanLengthMetric.continuous_dist_fix_left {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (x : ℂ) : Continuous (fun w => D x w) := by
  rw [Metric.continuous_iff]
  intro b ε hε
  obtain ⟨δ, hδ, h⟩ := hD.exists_near_lt b hε
  refine ⟨δ, hδ, fun a ha => ?_⟩
  have h1 := h a ha
  have h2 := hD.triangle x b a
  have h3 := hD.triangle x a b
  have h4 := hD.symm a b
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith


theorem two_point_le_curveLength {D : ℂ → ℂ → ℝ} (p : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b) :
    ENNReal.ofReal (D (p b) (p a)) ≤ curveLength D p a b := by
  have hmono : Monotone (fun i : ℕ => if i = 0 then a else b) := by
    intro i j hij
    by_cases hi : i = 0
    · subst hi
      by_cases hj : j = 0
      · simp [hj]
      · simp [hj, hab]
    · have hj : j ≠ 0 := by omega
      simp [hi, hj]
  have hmem : ∀ i : ℕ, (if i = 0 then a else b) ∈ Icc a b := by
    intro i
    by_cases hi : i = 0
    · simp only [hi, ite_true]; exact ⟨le_rfl, hab⟩
    · simp only [hi, ite_false]; exact ⟨hab, le_rfl⟩
  unfold curveLength
  refine le_iSup_of_le ((1 : ℕ), ⟨fun i => if i = 0 then a else b, hmono, hmem⟩) ?_
  simp

theorem IsEuclideanLengthMetric.cost_ge_of_exit {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {ξ : ℝ} {g : ℂ → ℝ} {x : ℂ} {R r c m : ℝ} (hm0 : 0 < m) (hr : 0 < r) (hrR : r < R)
    (hm : ∀ z : ℂ, r < dist z x → dist z x ≤ R → m ≤ Real.exp (ξ * g z))
    (hc : ∀ w : ℂ, dist w x = R → c ≤ D x w)
    (hnear : ∀ z : ℂ, dist z x ≤ r → D x z < c / 2)
    {p : ℝ → ℂ} {T : ℝ} (hp : IsLengthParametrized D p T) (h0 : p 0 = x) {w : ℂ} (hT : p T = w)
    (hw : R < dist w x) :
    ENNReal.ofReal (m * (c / 2)) ≤ ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * g (p t))) := by
  obtain ⟨hT0, hcont, hlen⟩ := hp
  set h : ℝ → ℝ := fun t => dist (p t) x with hh
  have hhc : ContinuousOn h (Icc 0 T) :=
    (continuous_id.dist continuous_const).comp_continuousOn hcont
  have hh0 : h 0 = 0 := by simp [hh, h0]
  have hT_mem : T ∈ Icc 0 T := ⟨hT0, le_rfl⟩
  set S : Set ℝ := Icc 0 T ∩ h ⁻¹' Ici R with hS
  have hSc : IsClosed S := hhc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hSne : S.Nonempty := ⟨T, hT_mem, by show R ≤ h T; simp only [hh, hT]; exact hw.le⟩
  have hSb : BddBelow S := ⟨0, fun t ht => ht.1.1⟩
  have ht2S : sInf S ∈ S := hSc.csInf_mem hSne hSb
  set t2 := sInf S with ht2
  have ht2_T : t2 ≤ T := ht2S.1.2
  have ht2_0 : 0 ≤ t2 := ht2S.1.1
  have ht2_le : ∀ t ∈ Icc 0 T, t < t2 → h t < R := by
    intro t ht hlt
    by_contra hcon
    have : t2 ≤ t := csInf_le hSb ⟨ht, not_lt.mp hcon⟩
    linarith
  have hh2 : h t2 = R := by
    have hcont2 : ContinuousOn h (Icc 0 t2) := hhc.mono (Icc_subset_Icc le_rfl ht2_T)
    have hR_mem : R ∈ Icc (h 0) (h t2) := ⟨by rw [hh0]; exact (hr.trans hrR).le, ht2S.2⟩
    obtain ⟨t', ht'mem, ht'eq⟩ := intermediate_value_Icc ht2_0 hcont2 hR_mem
    have hle : t2 ≤ t' := csInf_le hSb ⟨⟨ht'mem.1, ht'mem.2.trans ht2_T⟩, by show R ≤ h t'; rw [ht'eq]⟩
    have heq : t' = t2 := le_antisymm ht'mem.2 hle
    rw [← heq]; exact ht'eq
  -- last time in [0, t2] with h ≤ r
  set S1 : Set ℝ := Icc 0 t2 ∩ h ⁻¹' Iic r with hS1
  have hS1c : IsClosed S1 :=
    (hhc.mono (Icc_subset_Icc le_rfl ht2_T)).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hS1ne : S1.Nonempty := ⟨0, ⟨le_rfl, ht2_0⟩, by show h 0 ≤ r; rw [hh0]; exact hr.le⟩
  have hS1b : BddAbove S1 := ⟨t2, fun t ht => ht.1.2⟩
  have ht1S : sSup S1 ∈ S1 := hS1c.csSup_mem hS1ne hS1b
  set t1 := sSup S1 with ht1
  have ht1_0 : 0 ≤ t1 := ht1S.1.1
  have ht1_le : t1 ≤ t2 := ht1S.1.2
  have hh1 : h t1 ≤ r := ht1S.2
  have ht1_lt : t1 < t2 := by
    refine lt_of_le_of_ne ht1_le (fun heq => ?_)
    have : h t1 = R := by rw [heq, hh2]
    linarith
  have hmid : ∀ t ∈ Ioc t1 t2, r < h t ∧ h t ≤ R := by
    intro t ht
    have htT : t ≤ T := ht.2.trans ht2_T
    have ht0 : 0 ≤ t := ht1_0.trans ht.1.le
    constructor
    · by_contra hcon
      have hmem : t ∈ S1 := ⟨⟨ht0, ht.2⟩, not_lt.mp hcon⟩
      have : t ≤ t1 := le_csSup hS1b hmem
      linarith [ht.1]
    · rcases lt_or_eq_of_le ht.2 with hlt | heq
      · exact (ht2_le t ⟨ht0, htT⟩ hlt).le
      · rw [heq, hh2]
  have hd : c / 2 ≤ t2 - t1 := by
    have hcurve := hlen t1 t2 ht1_0 ht1_le ht2_T
    have hpt := two_point_le_curveLength (D := D) p ht1_le
    rw [hcurve] at hpt
    have hnn : 0 ≤ t2 - t1 := by linarith
    have hDd : D (p t2) (p t1) ≤ t2 - t1 := (ENNReal.ofReal_le_ofReal_iff hnn).mp hpt
    have hw2 : c ≤ D x (p t2) := hc (p t2) hh2
    have hw1 : D x (p t1) < c / 2 := hnear (p t1) hh1
    have htri := hD.triangle x (p t1) (p t2)
    have hsymm := hD.symm (p t1) (p t2)
    linarith
  have hsub : Ioc t1 t2 ⊆ Icc 0 T := fun t ht => ⟨ht1_0.trans ht.1.le, ht.2.trans ht2_T⟩
  have hconst : ∫⁻ _ in Ioc t1 t2, ENNReal.ofReal m = ENNReal.ofReal m * ENNReal.ofReal (t2 - t1) := by
    rw [setLIntegral_const, Real.volume_Ioc]
  calc ENNReal.ofReal (m * (c / 2)) = ENNReal.ofReal m * ENNReal.ofReal (c / 2) :=
        ENNReal.ofReal_mul hm0.le
    _ ≤ ENNReal.ofReal m * ENNReal.ofReal (t2 - t1) :=
        mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hd) (by positivity)
    _ = ∫⁻ _ in Ioc t1 t2, ENNReal.ofReal m := hconst.symm
    _ ≤ ∫⁻ t in Ioc t1 t2, ENNReal.ofReal (Real.exp (ξ * g (p t))) :=
        setLIntegral_mono' measurableSet_Ioc
          (fun t ht => ENNReal.ofReal_le_ofReal (hm (p t) (hmid t ht).1 (hmid t ht).2))
    _ ≤ ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * g (p t))) := lintegral_mono_set hsub

/-- One-way topology of the inner Weyl distance: a Euclidean neighbourhood of `x` contains a
`ε`-ball of the inner distance `D_ξ g (x, ·)`. -/
theorem IsEuclideanLengthMetric.weylScaling_nhds {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {ξ : ℝ} {g : ℂ → ℝ} (hg : ContinuousOn g {z | z ≠ 0}) (hfin : ∀ x y, weylScaling D ξ g x y ≠ ⊤)
    (x : ℂ) {U : Set ℂ} (hU : IsOpen U) (hx : x ∈ U) :
    ∃ ε > 0, ∀ w, (weylScaling D ξ g x w).toReal < ε → w ∈ U := by
  obtain ⟨ε0, hε0, hball⟩ := Metric.isOpen_iff.mp hU x hx
  obtain ⟨R, hR, hRU, hRx⟩ : ∃ R > 0, closedBall x R ⊆ U ∧ (x = 0 ∨ R < dist x 0) := by
    by_cases h0 : x = 0
    · refine ⟨ε0 / 2, by linarith, fun z hz => hball (mem_ball.mpr ?_), Or.inl h0⟩
      have := mem_closedBall.mp hz
      linarith
    · have hpos : 0 < dist x 0 := dist_pos.mpr h0
      refine ⟨min (ε0 / 2) (dist x 0 / 2), lt_min (by linarith) (by linarith),
        fun z hz => hball (mem_ball.mpr ?_), Or.inr ?_⟩
      · have := mem_closedBall.mp hz
        have := min_le_left (ε0 / 2) (dist x 0 / 2)
        linarith
      · have := min_le_right (ε0 / 2) (dist x 0 / 2)
        linarith
  have hcont : Continuous (fun w => D x w) := hD.continuous_dist_fix_left x
  obtain ⟨w1, hw1, hmin1⟩ := (isCompact_sphere x R).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hR.le) hcont.continuousOn
  have hw1x : dist w1 x = R := mem_sphere.mp hw1
  have hc : 0 < D x w1 := by
    rcases (hD.nonneg' x w1).lt_or_eq with h | h
    · exact h
    · exfalso
      have heq : x = w1 := hD.eq_of_eq_zero x w1 h.symm
      rw [heq, dist_self] at hw1x
      linarith
  obtain ⟨r0, hr0, hnear0⟩ := hD.exists_near_lt x (half_pos hc)
  set r : ℝ := min (R / 2) (r0 / 2) with hr_def
  have hr : 0 < r := lt_min (by linarith) (by linarith)
  have hrR : r < R := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hrr0 : r < r0 := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  set A : Set ℂ := closedBall x R ∩ {z | r ≤ dist z x} with hA
  have hAc : IsCompact A := (isCompact_closedBall x R).inter_right
    (isClosed_le continuous_const (continuous_id.dist continuous_const))
  have hA0 : ∀ z ∈ A, z ≠ 0 := by
    rintro z ⟨hz1, hz2⟩ hz0
    have h1 : dist z x ≤ R := mem_closedBall.mp hz1
    have h2 : r ≤ dist z x := hz2
    subst hz0
    rcases hRx with h0 | h0
    · subst h0
      rw [dist_self] at h2
      linarith
    · rw [dist_comm] at h1
      linarith
  have hAne : A.Nonempty :=
    ⟨w1, mem_closedBall.mpr hw1x.le, by show r ≤ dist w1 x; rw [hw1x]; exact hrR.le⟩
  have hgA : ContinuousOn (fun z => Real.exp (ξ * g z)) A :=
    Real.continuous_exp.comp_continuousOn (continuousOn_const.mul (hg.mono (fun z hz => hA0 z hz)))
  obtain ⟨z0, hz0A, hz0min⟩ := hAc.exists_isMinOn hAne hgA
  set m : ℝ := Real.exp (ξ * g z0) with hm_def
  have hm0 : 0 < m := Real.exp_pos _
  have hm : ∀ z : ℂ, r < dist z x → dist z x ≤ R → m ≤ Real.exp (ξ * g z) := by
    intro z hz1 hz2
    have hzA : z ∈ A := ⟨mem_closedBall.mpr hz2, hz1.le⟩
    exact isMinOn_iff.mp hz0min z hzA
  have hc' : ∀ w : ℂ, dist w x = R → D x w1 ≤ D x w :=
    fun w hw => isMinOn_iff.mp hmin1 w (mem_sphere.mpr hw)
  have hnear : ∀ z : ℂ, dist z x ≤ r → D x z < D x w1 / 2 :=
    fun z hz => hnear0 z (lt_of_le_of_lt hz hrr0)
  refine ⟨m * (D x w1 / 2), mul_pos hm0 (half_pos hc), fun w hw => ?_⟩
  by_contra hwU
  have hwR : R < dist w x := by
    by_contra hle
    exact hwU (hRU (mem_closedBall.mpr (not_lt.mp hle)))
  have key : ENNReal.ofReal (m * (D x w1 / 2)) ≤ weylScaling D ξ g x w := by
    unfold weylScaling
    refine le_iInf fun T => le_iInf fun p => le_iInf fun hp => le_iInf fun h0 => le_iInf fun hT => ?_
    exact hD.cost_ge_of_exit hm0 hr hrR hm hc' hnear hp h0 hT hwR
  have hle := (ENNReal.ofReal_le_iff_le_toReal (hfin x w)).mp key
  linarith

/-- The inner Weyl distance `(u, v) ↦ (weylScaling D ξ g u v).toReal`, the metric of the inner scaling. -/
noncomputable def innerDist (D : ℂ → ℂ → ℝ) (ξ : ℝ) (g : ℂ → ℝ) (x y : ℂ) : ℝ :=
  (weylScaling D ξ g x y).toReal

theorem IsEuclideanLengthMetric.weylScaling_self_eq_zero {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (ξ : ℝ) (g : ℂ → ℝ) (x : ℂ) : weylScaling D ξ g x x = 0 := by
  have hp : IsLengthParametrized D (fun _ => x) 0 := by
    refine ⟨le_rfl, continuousOn_const, fun s t hs hst ht => ?_⟩
    have hs0 : s = 0 := le_antisymm (hst.trans ht) hs
    have ht0 : t = 0 := le_antisymm ht (hs0 ▸ hst)
    subst hs0; subst ht0
    simp only [sub_self, ENNReal.ofReal_zero]
    unfold curveLength
    refine le_antisymm (iSup_le fun q => ?_) (by positivity)
    simp [hD.self_eq_zero x]
  have h := weylScaling_le_of_lengthParametrized D ξ g hp rfl rfl
    (B := ξ * g x) (fun t _ => le_refl _)
  simpa using h

theorem innerDist_symm {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (ξ : ℝ) (g : ℂ → ℝ) (x y : ℂ) :
    innerDist D ξ g x y = innerDist D ξ g y x := by
  unfold innerDist
  rw [hD.weylScaling_symm ξ g x y]

theorem innerDist_self {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (ξ : ℝ) (g : ℂ → ℝ) (x : ℂ) :
    innerDist D ξ g x x = 0 := by
  unfold innerDist
  rw [hD.weylScaling_self_eq_zero ξ g x]
  simp

theorem innerDist_nonneg {D : ℂ → ℂ → ℝ} (ξ : ℝ) (g : ℂ → ℝ) (x y : ℂ) : 0 ≤ innerDist D ξ g x y :=
  ENNReal.toReal_nonneg

theorem innerDist_triangle {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {ξ : ℝ} {g : ℂ → ℝ}
    (hfin : ∀ x y, weylScaling D ξ g x y ≠ ⊤) (x y z : ℂ) :
    innerDist D ξ g x z ≤ innerDist D ξ g x y + innerDist D ξ g y z := by
  unfold innerDist
  have h := hD.weylScaling_triangle ξ g x y z
  have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin x y, hfin y z⟩) h
  rw [ENNReal.toReal_add (hfin x y) (hfin y z)] at h2
  exact h2

theorem innerDist_ofReal {D : ℂ → ℂ → ℝ} {ξ : ℝ} {g : ℂ → ℝ}
    (hfin : ∀ x y, weylScaling D ξ g x y ≠ ⊤) (x y : ℂ) :
    ENNReal.ofReal (innerDist D ξ g x y) = weylScaling D ξ g x y :=
  ENNReal.ofReal_toReal (hfin x y)

/-- The inner distance separates points, by the one-way topology `weylScaling_nhds`. -/
theorem IsEuclideanLengthMetric.innerDist_eq_zero {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {ξ : ℝ} {g : ℂ → ℝ} (hg : ContinuousOn g {z | z ≠ 0}) (hfin : ∀ x y, weylScaling D ξ g x y ≠ ⊤)
    {x y : ℂ} (h : innerDist D ξ g x y = 0) : x = y := by
  by_contra hne
  have hpos : 0 < dist x y := dist_pos.mpr hne
  obtain ⟨ε, hε, hU⟩ := hD.weylScaling_nhds hg hfin x
    (isOpen_ball (x := x) (ε := dist x y / 2)) (mem_ball_self (half_pos hpos))
  have hy := hU y (by change innerDist D ξ g x y < ε; rw [h]; exact hε)
  rw [mem_ball, dist_comm] at hy
  linarith

theorem IsEuclideanLengthMetric.isLengthParametrized_const {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (x : ℂ) : IsLengthParametrized D (fun _ => x) 0 := by
  refine ⟨le_rfl, continuousOn_const, fun s t hs hst ht => ?_⟩
  have hs0 : s = 0 := le_antisymm (hst.trans ht) hs
  have ht0 : t = 0 := le_antisymm ht (hs0 ▸ hst)
  subst hs0; subst ht0
  simp only [sub_self, ENNReal.ofReal_zero]
  unfold curveLength
  refine le_antisymm (iSup_le fun q => ?_) (by positivity)
  simp [hD.self_eq_zero x]

theorem innerDist_le_of_lp {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {ξ : ℝ} {g : ℂ → ℝ}
    {q : ℝ → ℂ} {L : ℝ} (hq : IsLengthParametrized (innerDist D ξ g) q L) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : b ≤ L) : innerDist D ξ g (q a) (q b) ≤ b - a := by
  have h := two_point_le_curveLength (D := innerDist D ξ g) q hab
  rw [hq.2.2 a b ha hab hb] at h
  rw [innerDist_symm hD ξ g (q a) (q b)]
  exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).mp h

theorem exists_lp_lt {D : ℂ → ℂ → ℝ} {ξ : ℝ} {g : ℂ → ℝ} (hfin : ∀ x y, weylScaling D ξ g x y ≠ ⊤)
    (z w : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ T : ℝ, ∃ p : ℝ → ℂ, IsLengthParametrized D p T ∧ p 0 = z ∧ p T = w ∧
      ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * g (p t))) <
        weylScaling D ξ g z w + ENNReal.ofReal δ := by
  have key : ∀ a : ENNReal, weylScaling D ξ g z w < a → ∃ T : ℝ, ∃ p : ℝ → ℂ, IsLengthParametrized D p T ∧
      p 0 = z ∧ p T = w ∧ ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * g (p t))) < a := by
    intro a ha
    unfold weylScaling at ha
    simpa only [iInf_lt_iff, exists_prop] using ha
  exact key _ (ENNReal.lt_add_right (hfin z w) (by simpa using hδ))

theorem IsEuclideanLengthMetric.exists_chain {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (F : ℂ → ENNReal) :
    ∀ (n : ℕ) (z : ℕ → ℂ) (T : ℕ → ℝ) (P : ℕ → ℝ → ℂ),
      (∀ i < n, 0 ≤ T i ∧ IsLengthParametrized D (P i) (T i) ∧ P i 0 = z i ∧ P i (T i) = z (i + 1)) →
      ∃ R : ℝ → ℂ, IsLengthParametrized D R (∑ i ∈ Finset.range n, T i) ∧ R 0 = z 0 ∧
        R (∑ i ∈ Finset.range n, T i) = z n ∧
        ∫⁻ t in Icc 0 (∑ i ∈ Finset.range n, T i), F (R t) ≤
          ∑ i ∈ Finset.range n, ∫⁻ t in Icc 0 (T i), F (P i t) := by
  intro n
  induction n with
  | zero =>
    intro z T P _
    refine ⟨fun _ => z 0, by simpa using hD.isLengthParametrized_const (z 0), rfl, rfl, ?_⟩
    simp
  | succ n ih =>
    intro z T P h
    obtain ⟨R, hR, hR0, hRn, hRint⟩ := ih z T P (fun i hi => h i (by omega))
    obtain ⟨hTn, hPn, hP0, hPT⟩ := h n (by omega)
    set S := ∑ i ∈ Finset.range n, T i with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun i hi => (h i (by simp at hi; omega)).1
    have hjoin : R S = P n 0 := by rw [hRn, hP0]
    refine ⟨fun t => if t ≤ S then R t else P n (t - S), ?_, ?_, ?_, ?_⟩
    · rw [Finset.sum_range_succ]
      exact hD.isLengthParametrized_piecewise_concat hR hPn hjoin
    · simp [hR0, hS0]
    · have hT_succ : ∑ i ∈ Finset.range (n + 1), T i = S + T n := Finset.sum_range_succ T n
      rw [hT_succ]
      by_cases hz0 : T n = 0
      · have hle : S + T n ≤ S := by linarith
        have hz : z n = z (n + 1) := by rw [← hPT, hz0, hP0]
        simp only [hle, ↓reduceIte]
        rw [hz0, add_zero, hRn, hz]
      · have hlt : 0 < T n := lt_of_le_of_ne hTn (Ne.symm hz0)
        have hnle : ¬ (S + T n ≤ S) := by intro h'; linarith
        simp only [hnle, ↓reduceIte]
        rw [show S + T n - S = T n by ring, hPT]
    · have hT_succ : ∑ i ∈ Finset.range (n + 1), T i = S + T n := Finset.sum_range_succ T n
      have hI_succ : ∑ i ∈ Finset.range (n + 1), ∫⁻ t in Icc 0 (T i), F (P i t) =
          (∑ i ∈ Finset.range n, ∫⁻ t in Icc 0 (T i), F (P i t)) + ∫⁻ t in Icc 0 (T n), F (P n t) :=
        Finset.sum_range_succ _ _
      rw [hT_succ, hI_succ]
      have hc := lintegral_length_concat_le F R (P n) hS0 hTn hjoin
      exact le_trans hc (add_le_add hRint le_rfl)

theorem innerDist_lip_abs {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {ξ : ℝ} {g : ℂ → ℝ}
    {q : ℝ → ℂ} {L : ℝ} (hq : IsLengthParametrized (innerDist D ξ g) q L) {a b : ℝ}
    (ha : a ∈ Icc 0 L) (hb : b ∈ Icc 0 L) :
    innerDist D ξ g (q a) (q b) ≤ |a - b| := by
  rcases le_total a b with hab | hab
  · have h := innerDist_le_of_lp hD hq ha.1 hab hb.2
    exact h.trans (by rw [abs_sub_comm]; exact le_abs_self _)
  · have h := innerDist_le_of_lp hD hq hb.1 hab ha.2
    rw [innerDist_symm hD ξ g]
    exact h.trans (le_abs_self _)

/-- Claim U (uniform multiplicative continuity along an inner-length-parametrized curve): the weight
`exp(ξ f)` at points inner-close to `q t`, `t ∈ [0, L]`, is at most `(1 + ε)` times its value at `q t`.
Proof by sequences: a limit point of the parameters, the one-way topology `weylScaling_nhds`, and continuity. -/
theorem IsEuclideanLengthMetric.exists_near_mul {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {ξ : ℝ} {g : ℂ → ℝ} (hg : ContinuousOn g {z | z ≠ 0}) (hfin : ∀ x y, weylScaling D ξ g x y ≠ ⊤)
    {f : ℂ → ℝ} (hf : Continuous f) {q : ℝ → ℂ} {L : ℝ}
    (hq : IsLengthParametrized (innerDist D ξ g) q L) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ t ∈ Icc 0 L, ∀ w : ℂ, innerDist D ξ g (q t) w < η →
      Real.exp (ξ * f w) ≤ (1 + ε) * Real.exp (ξ * f (q t)) := by
  by_contra H
  have H' : ∀ n : ℕ, ∃ t ∈ Icc 0 L, ∃ w : ℂ, innerDist D ξ g (q t) w < 1 / ((n : ℝ) + 1) ∧
      (1 + ε) * Real.exp (ξ * f (q t)) < Real.exp (ξ * f w) := by
    intro n
    by_contra H2
    apply H
    refine ⟨1 / ((n : ℝ) + 1), by positivity, fun t ht w hw => ?_⟩
    by_contra H3
    exact H2 ⟨t, ht, w, hw, lt_of_not_ge H3⟩
  choose t ht w hw1 hw2 using H'
  obtain ⟨tstar, htstar, φ, hφ, htend⟩ := isCompact_Icc.tendsto_subseq ht
  have hd : Tendsto (fun n => innerDist D ξ g (q tstar) (w (φ n))) atTop (𝓝 0) := by
    have hA : Tendsto (fun n => |t (φ n) - tstar|) atTop (𝓝 0) := by
      have := (htend.sub_const tstar).abs
      simpa using this
    have hB : Tendsto (fun n : ℕ => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    have hup := (hA.add hB)
    rw [zero_add] at hup
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun n => innerDist_nonneg ξ g _ _) (fun n => ?_)
    have h1 := innerDist_lip_abs hD hq htstar (ht (φ n))
    have h2 := hw1 (φ n)
    have h4 : |tstar - t (φ n)| = |t (φ n) - tstar| := abs_sub_comm _ _
    have htri := innerDist_triangle hD hfin (q tstar) (q (t (φ n))) (w (φ n))
    show innerDist D ξ g (q tstar) (w (φ n)) ≤ |t (φ n) - tstar| + 1 / ((φ n : ℝ) + 1)
    linarith
  have hw_lim : Tendsto (fun n => w (φ n)) atTop (𝓝 (q tstar)) := by
    rw [_root_.tendsto_nhds]
    intro U hU hzU
    obtain ⟨ε', hε', hT1⟩ := hD.weylScaling_nhds hg hfin (q tstar) hU hzU
    filter_upwards [(tendsto_order.1 hd).2 ε' hε'] with n hn
    exact hT1 _ hn
  have hq_lim : Tendsto (fun n => q (t (φ n))) atTop (𝓝 (q tstar)) :=
    (hq.2.1 tstar htstar).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨htend, Eventually.of_forall fun n => ht (φ n)⟩)
  have hBc : Continuous fun z => Real.exp (ξ * f z) := by fun_prop
  have hB1 : Tendsto (fun n => Real.exp (ξ * f (w (φ n)))) atTop
      (𝓝 (Real.exp (ξ * f (q tstar)))) := (hBc.tendsto _).comp hw_lim
  have hB2 : Tendsto (fun n => (1 + ε) * Real.exp (ξ * f (q (t (φ n))))) atTop
      (𝓝 ((1 + ε) * Real.exp (ξ * f (q tstar)))) :=
    ((hBc.tendsto _).comp hq_lim).const_mul _
  have hle := le_of_tendsto_of_tendsto' hB2 hB1 (fun n => (hw2 (φ n)).le)
  have hpos : 0 < Real.exp (ξ * f (q tstar)) := Real.exp_pos _
  nlinarith

/-- Partition of `[0, L]` into `n` equal pieces: the points `t i = i * (L / n)`. -/
theorem IsEuclideanLengthMetric.weylScaling_le_iterated_key {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {ξ : ℝ} {g : ℂ → ℝ} (hg : ContinuousOn g {z | z ≠ 0}) (hfin : ∀ x y, weylScaling D ξ g x y ≠ ⊤)
    {f : ℂ → ℝ} (hf : Continuous f) {q : ℝ → ℂ} {L : ℝ}
    (hq : IsLengthParametrized (innerDist D ξ g) q L) {x y : ℂ} (h0 : q 0 = x) (hL : q L = y)
    {ρ ε1 : ℝ} (hρ : 1 < ρ) (hε1 : 0 < ε1) :
    weylScaling D ξ (fun z => g z + f z) x y ≤
      ENNReal.ofReal (ρ * ρ) * (∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (q t)))) +
        ENNReal.ofReal (ρ * ε1) := by
  set J := ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (q t))) with hJdef
  have hL0 : 0 ≤ L := hq.1
  have hlogpos : 0 < Real.log ρ := Real.log_pos hρ
  obtain ⟨η, hη, hU⟩ := hD.exists_near_mul hg hfin hf hq (ε := ρ - 1) (by linarith)
  have hU' : ∀ t ∈ Icc 0 L, ∀ w : ℂ, innerDist D ξ g (q t) w < η →
      Real.exp (ξ * f w) ≤ ρ * Real.exp (ξ * f (q t)) := by
    intro t ht w hw
    have h := hU t ht w hw
    rwa [show 1 + (ρ - 1) = ρ by ring] at h
  have hℓc : ContinuousOn (fun t => ξ * f (q t)) (Icc 0 L) :=
    ((continuous_const.mul hf).comp_continuousOn hq.2.1)
  obtain ⟨κ, hκ, hκU⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hℓc) (Real.log ρ) hlogpos
  have hexp : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L, |s - t| < κ →
      Real.exp (ξ * f (q s)) ≤ ρ * Real.exp (ξ * f (q t)) := by
    intro s hs t ht hst
    have h1 : dist (ξ * f (q s)) (ξ * f (q t)) < Real.log ρ :=
      hκU s hs t ht (by rw [Real.dist_eq]; exact hst)
    rw [Real.dist_eq, abs_lt] at h1
    rw [show ρ * Real.exp (ξ * f (q t)) = Real.exp (ξ * f (q t) + Real.log ρ) by
      rw [Real.exp_add, Real.exp_log (by linarith), mul_comm]]
    exact Real.exp_le_exp.mpr (by linarith [h1.2])
  -- the partition
  set m := min κ η with hm_def
  have hm : 0 < m := lt_min hκ hη
  set n : ℕ := ⌈L / m⌉₊ + 1 with hn_def
  have hnpos : (0 : ℝ) < n := by positivity
  set Δ := L / n with hΔ_def
  have hΔ0 : 0 ≤ Δ := div_nonneg hL0 hnpos.le
  have hΔm : Δ < m := by
    have h1 : L / m ≤ (⌈L / m⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈L / m⌉₊ : ℝ) < (n : ℝ) := by rw [hn_def]; push_cast; linarith
    rw [hΔ_def, div_lt_iff₀ hnpos]
    rw [div_le_iff₀ hm] at h1
    nlinarith
  have hΔκ : Δ < κ := lt_of_lt_of_le hΔm (min_le_left _ _)
  have hΔη : Δ < η := lt_of_lt_of_le hΔm (min_le_right _ _)
  have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
  have hρ0 : 0 < ρ := by linarith
  set t : ℕ → ℝ := fun i => (i : ℝ) * Δ with ht_def
  have ht0 : t 0 = 0 := by simp [ht_def]
  have htn : t n = L := by
    have : (n : ℝ) * (L / n) = L := by field_simp
    exact this
  have htmono : Monotone t := fun i j hij => by
    simp only [ht_def]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hΔ0
  have htmem : ∀ i ≤ n, t i ∈ Icc 0 L := by
    intro i hi
    exact ⟨mul_nonneg (Nat.cast_nonneg i) hΔ0, htn ▸ htmono hi⟩
  set z : ℕ → ℂ := fun i => q (t i) with hz_def
  set S : ℝ := ∑ i ∈ Finset.range n, Real.exp (ξ * f (z i)) with hS_def
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => (Real.exp_pos _).le
  set δ : ℝ := min ((η - Δ) / 2) (ε1 / (S + 1)) with hδ_def
  have hδ0 : 0 < δ := lt_min (by linarith) (by positivity)
  have hδη : Δ + δ < η := by
    have := min_le_left ((η - Δ) / 2) (ε1 / (S + 1))
    linarith
  have hδS : δ * S ≤ ε1 := by
    have h1 := min_le_right ((η - Δ) / 2) (ε1 / (S + 1))
    rw [← hδ_def] at h1
    have h2 : δ * (S + 1) ≤ ε1 := by
      rw [le_div_iff₀ (by positivity)] at h1
      linarith
    nlinarith
  -- near-optimal inner-length pieces
  have hpair : ∀ i : ℕ, ∃ T : ℝ, ∃ p : ℝ → ℂ, IsLengthParametrized D p T ∧ p 0 = z i ∧ p T = z (i + 1) ∧
      ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * g (p t))) <
        weylScaling D ξ g (z i) (z (i + 1)) + ENNReal.ofReal δ :=
    fun i => exists_lp_lt hfin (z i) (z (i + 1)) hδ0
  choose T P hP h0P hTP hcost using hpair
  have hdist_i : ∀ i < n, innerDist D ξ g (z i) (z (i + 1)) ≤ Δ := by
    intro i hi
    have h := innerDist_lip_abs hD hq (a := t i) (b := t (i + 1))
      (htmem i (by omega)) (htmem (i + 1) (by omega))
    have e : |t i - t (i + 1)| = Δ := by
      simp only [ht_def]
      rw [show (i : ℝ) * Δ - ((i + 1 : ℕ) : ℝ) * Δ = -Δ by push_cast; ring, abs_neg,
        abs_of_nonneg hΔ0]
    rw [e] at h
    exact h
  have hcost_le : ∀ i < n, ∫⁻ t in Icc 0 (T i), ENNReal.ofReal (Real.exp (ξ * g (P i t))) <
      ENNReal.ofReal (Δ + δ) := by
    intro i hi
    have hW : weylScaling D ξ g (z i) (z (i + 1)) ≤ ENNReal.ofReal Δ := by
      rw [← innerDist_ofReal hfin (z i) (z (i + 1))]
      exact ENNReal.ofReal_le_ofReal (hdist_i i hi)
    refine lt_of_lt_of_le (hcost i) ?_
    rw [ENNReal.ofReal_add hΔ0 hδ0.le]
    exact add_le_add hW le_rfl
  -- piece bound for the near-optimal curves
  have hpiece : ∀ i < n, ∀ s ∈ Icc 0 (T i),
      ENNReal.ofReal (Real.exp (ξ * f (P i s))) ≤
        ENNReal.ofReal ρ * ENNReal.ofReal (Real.exp (ξ * f (z i))) := by
    intro i hi s hs
    have hseg := hD.weylScaling_le_segment_cost ξ g (hP i) le_rfl hs.1 hs.2
    rw [h0P i] at hseg
    have hsub : ∫⁻ t in Icc 0 s, ENNReal.ofReal (Real.exp (ξ * g (P i t))) ≤
        ∫⁻ t in Icc 0 (T i), ENNReal.ofReal (Real.exp (ξ * g (P i t))) :=
      lintegral_mono_set (Icc_subset_Icc le_rfl hs.2)
    have hW2 : weylScaling D ξ g (z i) (P i s) ≤ ENNReal.ofReal (Δ + δ) :=
      hseg.trans (hsub.trans (hcost_le i hi).le)
    have hin : innerDist D ξ g (z i) (P i s) < η := by
      have := ENNReal.toReal_le_of_le_ofReal (by linarith) hW2
      unfold innerDist
      linarith
    have hb := hU' (t i) (htmem i (by omega)) (P i s) hin
    rw [← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hb
  -- the concatenation
  have hchain_hyp : ∀ i < n, 0 ≤ T i ∧ IsLengthParametrized D (P i) (T i) ∧ P i 0 = z i ∧
      P i (T i) = z (i + 1) :=
    fun i _ => ⟨(hP i).1, hP i, h0P i, hTP i⟩
  obtain ⟨R, hR, hR0, hRn, hRint⟩ :=
    hD.exists_chain (fun w => ENNReal.ofReal (Real.exp (ξ * (g w + f w)))) n z T P hchain_hyp
  have hz0 : z 0 = x := by
    show q (t 0) = x
    rw [ht0, h0]
  have hzn : z n = y := by
    show q (t n) = y
    rw [htn, hL]
  have hW : weylScaling D ξ (fun z => g z + f z) x y ≤
      ∫⁻ t in Icc 0 (∑ i ∈ Finset.range n, T i), ENNReal.ofReal (Real.exp (ξ * (g (R t) + f (R t)))) := by
    have hR0x : R 0 = x := hR0.trans hz0
    have hRny : R (∑ i ∈ Finset.range n, T i) = y := hRn.trans hzn
    unfold weylScaling
    exact (iInf₂_le _ R).trans ((iInf₂_le hR hR0x).trans (iInf_le _ hRny))
  -- splitting the integrand
  have hsplit : ∀ w : ℂ, ENNReal.ofReal (Real.exp (ξ * (g w + f w))) =
      ENNReal.ofReal (Real.exp (ξ * g w)) * ENNReal.ofReal (Real.exp (ξ * f w)) := by
    intro w
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  have hpieceint : ∀ i < n, ∫⁻ t in Icc 0 (T i), ENNReal.ofReal (Real.exp (ξ * (g (P i t) + f (P i t)))) ≤
      ENNReal.ofReal ρ * ENNReal.ofReal (Real.exp (ξ * f (z i))) * ENNReal.ofReal (Δ + δ) := by
    intro i hi
    calc ∫⁻ t in Icc 0 (T i), ENNReal.ofReal (Real.exp (ξ * (g (P i t) + f (P i t))))
        = ∫⁻ t in Icc 0 (T i), ENNReal.ofReal (Real.exp (ξ * g (P i t))) *
            ENNReal.ofReal (Real.exp (ξ * f (P i t))) :=
          setLIntegral_congr_fun measurableSet_Icc (fun t _ => hsplit (P i t))
      _ ≤ ∫⁻ t in Icc 0 (T i), ENNReal.ofReal (Real.exp (ξ * g (P i t))) *
            (ENNReal.ofReal ρ * ENNReal.ofReal (Real.exp (ξ * f (z i)))) :=
          setLIntegral_mono' measurableSet_Icc (fun s hs =>
            mul_le_mul_of_nonneg_left (hpiece i hi s hs) (by positivity))
      _ = (∫⁻ t in Icc 0 (T i), ENNReal.ofReal (Real.exp (ξ * g (P i t)))) *
            (ENNReal.ofReal ρ * ENNReal.ofReal (Real.exp (ξ * f (z i)))) :=
          lintegral_mul_const' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      _ ≤ ENNReal.ofReal (Δ + δ) * (ENNReal.ofReal ρ * ENNReal.ofReal (Real.exp (ξ * f (z i)))) :=
          mul_le_mul_of_nonneg_right (hcost_le i hi).le (by positivity)
      _ = ENNReal.ofReal ρ * ENNReal.ofReal (Real.exp (ξ * f (z i))) * ENNReal.ofReal (Δ + δ) := by ring
  -- Riemann comparison on the outer parameter
  have hA1 : ∑ i ∈ Finset.range n, ENNReal.ofReal (Real.exp (ξ * f (z i))) * ENNReal.ofReal Δ ≤
      ENNReal.ofReal ρ * J := by
    have hadj := sum_lintegral_Icc_adjacent (fun τ => ENNReal.ofReal (Real.exp (ξ * f (q τ)))) t htmono n
    rw [ht0, htn] at hadj
    rw [hJdef, ← hadj, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' : i < n := Finset.mem_range.mp hi
    have e2 : t (i + 1) - t i = Δ := by
      simp only [ht_def]
      push_cast
      ring
    have hpc : ∫⁻ τ in Icc (t i) (t (i + 1)), ENNReal.ofReal (Real.exp (ξ * f (z i))) =
        ENNReal.ofReal (Real.exp (ξ * f (z i))) * ENNReal.ofReal Δ := by
      rw [setLIntegral_const, Real.volume_Icc, e2]
    rw [← hpc, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Icc (fun τ hτ => ?_)
    have hτL : τ ∈ Icc 0 L := ⟨(htmem i (by omega)).1.trans hτ.1, hτ.2.trans (htmem (i + 1) (by omega)).2⟩
    have hdiff : |t i - τ| < κ := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith [hτ.1])]
      linarith [hτ.2, e2, hΔκ]
    have hb := hexp (t i) (htmem i (by omega)) τ hτL hdiff
    rw [← ENNReal.ofReal_mul hρ0.le]
    exact ENNReal.ofReal_le_ofReal hb
  have hA2 : ∑ i ∈ Finset.range n, ENNReal.ofReal (Real.exp (ξ * f (z i))) * ENNReal.ofReal δ =
      ENNReal.ofReal (S * δ) := by
    rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => (Real.exp_pos _).le),
      ← ENNReal.ofReal_mul hS0]
  have hSδ : S * δ ≤ ε1 := by
    rw [mul_comm]
    exact hδS
  have e1 : ENNReal.ofReal ρ * (ENNReal.ofReal ρ * J) = ENNReal.ofReal (ρ * ρ) * J := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul hρ0.le]
  have e3 : ENNReal.ofReal ρ * ENNReal.ofReal (S * δ) ≤ ENNReal.ofReal (ρ * ε1) := by
    rw [← ENNReal.ofReal_mul hρ0.le]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hSδ hρ0.le)
  calc weylScaling D ξ (fun z => g z + f z) x y
      ≤ ∫⁻ t in Icc 0 (∑ i ∈ Finset.range n, T i), ENNReal.ofReal (Real.exp (ξ * (g (R t) + f (R t)))) := hW
    _ ≤ ∑ i ∈ Finset.range n, ∫⁻ t in Icc 0 (T i), ENNReal.ofReal (Real.exp (ξ * (g (P i t) + f (P i t)))) :=
        hRint
    _ ≤ ∑ i ∈ Finset.range n, ENNReal.ofReal ρ * ENNReal.ofReal (Real.exp (ξ * f (z i))) * ENNReal.ofReal (Δ + δ) :=
        Finset.sum_le_sum fun i hi => hpieceint i (Finset.mem_range.mp hi)
    _ = ENNReal.ofReal ρ * (∑ i ∈ Finset.range n, ENNReal.ofReal (Real.exp (ξ * f (z i))) * ENNReal.ofReal Δ) +
        ENNReal.ofReal ρ * (∑ i ∈ Finset.range n, ENNReal.ofReal (Real.exp (ξ * f (z i))) * ENNReal.ofReal δ) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ENNReal.ofReal_add hΔ0 hδ0.le]
        ring
    _ ≤ ENNReal.ofReal ρ * (ENNReal.ofReal ρ * J) + ENNReal.ofReal ρ * ENNReal.ofReal (S * δ) := by
        rw [hA2]
        exact add_le_add (mul_le_mul_of_nonneg_left hA1 (by positivity)) le_rfl
    _ ≤ ENNReal.ofReal (ρ * ρ) * J + ENNReal.ofReal (ρ * ε1) := by
        rw [e1]
        exact add_le_add le_rfl e3

/-- Direction `W_D(g+f) ≤ W_d(f)` (the direct scaling is at most the iterated one): for an inner-length-parametrized
curve `q` from `x` to `y`, the direct Weyl scaling by `g + f` is at most the cost of `q` for the weight `e^{ξ f}`. -/
theorem IsEuclideanLengthMetric.weylScaling_le_iterated {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {ξ : ℝ} {g : ℂ → ℝ} (hg : ContinuousOn g {z | z ≠ 0}) (hfin : ∀ x y, weylScaling D ξ g x y ≠ ⊤)
    {f : ℂ → ℝ} (hf : Continuous f) {q : ℝ → ℂ} {L : ℝ}
    (hq : IsLengthParametrized (innerDist D ξ g) q L) {x y : ℂ} (h0 : q 0 = x) (hL : q L = y) :
    weylScaling D ξ (fun z => g z + f z) x y ≤
      ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (q t))) := by
  by_cases hJ : (∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (q t)))) = ⊤
  · rw [hJ]
    exact le_top
  set J := ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (q t))) with hJdef
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hJr : J = ENNReal.ofReal J.toReal := (ENNReal.ofReal_toReal hJ).symm
  have hJr0 : 0 ≤ J.toReal := ENNReal.toReal_nonneg
  have he : (0 : ℝ) < ε := by exact_mod_cast hε
  set t : ℝ := min 1 ((ε : ℝ) / (6 * (J.toReal + 1))) with ht_def
  have ht0 : 0 < t := lt_min one_pos (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht2 : t ≤ (ε : ℝ) / (6 * (J.toReal + 1)) := min_le_right _ _
  have ht3 : t * (6 * (J.toReal + 1)) ≤ (ε : ℝ) := by
    rw [le_div_iff₀ (by positivity)] at ht2
    linarith
  have hkey := hD.weylScaling_le_iterated_key hg hfin hf hq h0 hL (ρ := 1 + t) (ε1 := (ε : ℝ) / 4)
    (by linarith) (by positivity)
  have h1 : ENNReal.ofReal ((1 + t) * (1 + t)) * J ≤ J + ENNReal.ofReal ((ε : ℝ) / 2) := by
    rw [hJr, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add hJr0 (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h_tt : t * t ≤ t := by nlinarith
    have h_tt2 : t * t * J.toReal ≤ t * J.toReal := mul_le_mul_of_nonneg_right h_tt hJr0
    nlinarith
  have h2 : ENNReal.ofReal ((1 + t) * ((ε : ℝ) / 4)) ≤ ENNReal.ofReal ((ε : ℝ) / 2) :=
    ENNReal.ofReal_le_ofReal (by nlinarith)
  calc weylScaling D ξ (fun z => g z + f z) x y
      ≤ ENNReal.ofReal ((1 + t) * (1 + t)) * J + ENNReal.ofReal ((1 + t) * ((ε : ℝ) / 4)) := hkey
    _ ≤ (J + ENNReal.ofReal ((ε : ℝ) / 2)) + ENNReal.ofReal ((ε : ℝ) / 2) := add_le_add h1 h2
    _ = J + ENNReal.ofReal (ε : ℝ) := by
        rw [add_assoc, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 2
        ring
    _ = J + (ε : ENNReal) := by rw [ENNReal.ofReal_coe_nnreal]

/-- Finiteness of the outer-free cost: a `D`-length-parametrized curve of finite cost for the weight `e^{ξ(g+f)}`
has finite cost for the weight `e^{ξ g}`, since `e^{ξ f}` is bounded below on its compact image. -/
theorem IsEuclideanLengthMetric.cost_g_ne_top {D : ℂ → ℂ → ℝ} {ξ : ℝ} {g f : ℂ → ℝ} (hf : Continuous f)
    {p : ℝ → ℂ} {T : ℝ} (hp : IsLengthParametrized D p T)
    (hC : ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * (g (p t) + f (p t)))) ≠ ⊤) :
    ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * g (p t))) ≠ ⊤ := by
  have hcont : ContinuousOn (fun t => Real.exp (ξ * f (p t))) (Icc 0 T) :=
    (Real.continuous_exp.comp (continuous_const.mul hf)).comp_continuousOn hp.2.1
  obtain ⟨t0, ht0, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_isMinOn
    ⟨0, ⟨le_rfl, hp.1⟩⟩ hcont
  set c : ℝ := Real.exp (ξ * f (p t0)) with hc_def
  have hc0 : 0 < c := Real.exp_pos _
  have hle : (∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * g (p t)))) * ENNReal.ofReal c ≤
      ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * (g (p t) + f (p t)))) := by
    rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Icc (fun t ht => ?_)
    have hm : c ≤ Real.exp (ξ * f (p t)) := isMinOn_iff.mp hmin t ht
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    have : Real.exp (ξ * (g (p t) + f (p t))) = Real.exp (ξ * g (p t)) * Real.exp (ξ * f (p t)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le
  intro hA
  rw [hA, ENNReal.top_mul (ENNReal.ofReal_pos.mpr hc0).ne'] at hle
  exact hC (top_le_iff.mp hle)

/-- Cost bound for the inner length: the inner length of a sub-arc is at most its `e^{ξ g}`-cost. -/
theorem IsEuclideanLengthMetric.curveLength_innerDist_le_cost {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {ξ : ℝ} {g : ℂ → ℝ} (hfin : ∀ x y, weylScaling D ξ g x y ≠ ⊤) {p : ℝ → ℂ} {T : ℝ}
    (hp : IsLengthParametrized D p T) {u v : ℝ} (hu : 0 ≤ u) (hv : v ≤ T) :
    curveLength (innerDist D ξ g) p u v ≤
      ∫⁻ t in Icc u v, ENNReal.ofReal (Real.exp (ξ * g (p t))) := by
  unfold curveLength
  refine iSup_le ?_
  rintro ⟨n, w, hwmono, hwmem⟩
  have hterm : ∀ i ∈ Finset.range n, ENNReal.ofReal (innerDist D ξ g (p (w (i + 1))) (p (w i))) ≤
      ∫⁻ t in Icc (w i) (w (i + 1)), ENNReal.ofReal (Real.exp (ξ * g (p t))) := by
    intro i _
    have hi1 : w i ≤ w (i + 1) := hwmono (Nat.le_succ i)
    rw [innerDist_ofReal hfin, hD.weylScaling_symm ξ g (p (w (i + 1))) (p (w i))]
    exact hD.weylScaling_le_segment_cost ξ g hp (hu.trans (hwmem i).1) hi1
      (((hwmem (i + 1)).2).trans hv)
  calc ∑ i ∈ Finset.range n, ENNReal.ofReal (innerDist D ξ g (p (w (i + 1))) (p (w i)))
      ≤ ∑ i ∈ Finset.range n, ∫⁻ t in Icc (w i) (w (i + 1)), ENNReal.ofReal (Real.exp (ξ * g (p t))) :=
        Finset.sum_le_sum hterm
    _ = ∫⁻ t in Icc (w 0) (w n), ENNReal.ofReal (Real.exp (ξ * g (p t))) :=
        sum_lintegral_Icc_adjacent (fun t => ENNReal.ofReal (Real.exp (ξ * g (p t)))) w hwmono n
    _ ≤ ∫⁻ t in Icc u v, ENNReal.ofReal (Real.exp (ξ * g (p t))) :=
        lintegral_mono_set (Icc_subset_Icc (hwmem 0).1 (hwmem n).2)

/-- Auxiliary point type carrying the inner distance, used for the arc-length parametrization. -/
private structure InnerLengthPt where
  val : ℂ

/-- The inner distance as a metric on `InnerLengthPt`. -/
noncomputable abbrev innerMetricSpace {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {ξ : ℝ} {g : ℂ → ℝ}
    (hg : ContinuousOn g {z | z ≠ 0}) (hfin : ∀ x y, weylScaling D ξ g x y ≠ ⊤) :
    MetricSpace InnerLengthPt where
  dist x y := innerDist D ξ g x.val y.val
  dist_self x := innerDist_self hD ξ g x.val
  dist_comm x y := innerDist_symm hD ξ g x.val y.val
  dist_triangle x y z := innerDist_triangle hD hfin x.val y.val z.val
  eq_of_dist_eq_zero {x y} h := by
    cases x
    cases y
    exact congrArg InnerLengthPt.mk (hD.innerDist_eq_zero hg hfin h)

/-- Additivity of the inner length along a curve (through `eVariationOn`). -/
theorem curveLength_innerDist_add {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {ξ : ℝ} {g : ℂ → ℝ}
    (hg : ContinuousOn g {z | z ≠ 0}) (hfin : ∀ x y, weylScaling D ξ g x y ≠ ⊤) (p : ℝ → ℂ)
    {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    curveLength (innerDist D ξ g) p a b + curveLength (innerDist D ξ g) p b c =
      curveLength (innerDist D ξ g) p a c := by
  let := innerMetricSpace hD hg hfin
  have hcurve : ∀ u v, curveLength (innerDist D ξ g) p u v =
      eVariationOn (fun t => (⟨p t⟩ : InnerLengthPt)) (Icc u v) := by
    intro u v
    simp only [curveLength, eVariationOn, edist_dist]
    rfl
  rw [hcurve, hcurve, hcurve]
  have h := eVariationOn.Icc_add_Icc (fun t => (⟨p t⟩ : InnerLengthPt)) (s := univ) hab hbc (mem_univ b)
  simpa only [univ_inter] using h

/-- Arc-length parametrization for the inner distance (copy of `exists_lengthParametrized_with_tracking`,
with the continuity of the curve in the inner metric supplied as the hypothesis `hdc`; the Euclidean continuity of
the reparametrized curve follows from the one-way topology `weylScaling_nhds`). -/
theorem IsEuclideanLengthMetric.exists_arclength_innerDist {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {ξ : ℝ} {g : ℂ → ℝ} (hg : ContinuousOn g {z | z ≠ 0}) (hfin : ∀ x y, weylScaling D ξ g x y ≠ ⊤)
    {p : ℝ → ℂ} {T : ℝ} (hT : 0 ≤ T)
    (hfinite : curveLength (innerDist D ξ g) p 0 T ≠ ⊤)
    (hdc : ∀ t ∈ Icc 0 T, Tendsto (fun v => innerDist D ξ g (p t) (p v)) (𝓝[Icc 0 T] t) (𝓝 0)) :
    ∃ q : ℝ → ℂ, IsLengthParametrized (innerDist D ξ g) q (curveLength (innerDist D ξ g) p 0 T).toReal ∧
      q 0 = p 0 ∧ q (curveLength (innerDist D ξ g) p 0 T).toReal = p T ∧
      ∀ t ∈ Icc 0 T, q (curveLength (innerDist D ξ g) p 0 t).toReal = p t := by
  let := innerMetricSpace hD hg hfin
  have hcurve (q : ℝ → ℂ) (a b : ℝ) :
      curveLength (innerDist D ξ g) q a b = eVariationOn (fun t => (⟨q t⟩ : InnerLengthPt)) (Icc a b) := by
    simp only [curveLength, eVariationOn, edist_dist]
    rfl
  have hrcont : ContinuousOn (fun t => (⟨p t⟩ : InnerLengthPt)) (Icc 0 T) := by
    intro t ht
    rw [ContinuousWithinAt, tendsto_iff_dist_tendsto_zero]
    refine (hdc t ht).congr (fun v => ?_)
    show innerDist D ξ g (p t) (p v) = innerDist D ξ g (p v) (p t)
    exact innerDist_symm hD ξ g _ _
  have hrvar : BoundedVariationOn (fun t => (⟨p t⟩ : InnerLengthPt)) (Icc 0 T) := by
    change eVariationOn (fun t => (⟨p t⟩ : InnerLengthPt)) (Icc 0 T) ≠ ⊤
    rw [← hcurve]
    exact hfinite
  obtain ⟨hspeed, hstart, hend⟩ := naturalParameterization_unitSpeed_Icc
    (fun t => (⟨p t⟩ : InnerLengthPt)) hT hrcont hrvar
  set R := (curveLength (innerDist D ξ g) p 0 T).toReal with hR_def
  have hs : HasUnitSpeedOn (naturalParameterization (fun t => (⟨p t⟩ : InnerLengthPt)) (Icc 0 T) 0)
      (Icc 0 R) := by
    simpa only [hR_def, hcurve] using hspeed
  have hval : Continuous (fun z : InnerLengthPt => z.val) := by
    rw [Metric.continuous_iff]
    intro b ε hε
    obtain ⟨δ, hδ, h⟩ := hD.weylScaling_nhds hg hfin b.val (isOpen_ball (x := b.val) (ε := ε))
      (mem_ball_self hε)
    refine ⟨δ, hδ, fun a ha => ?_⟩
    have ha' : innerDist D ξ g b.val a.val < δ := by
      rw [innerDist_symm hD ξ g]
      exact ha
    have hmem := h a.val ha'
    exact mem_ball.mp hmem
  refine ⟨fun t => (naturalParameterization (fun t => (⟨p t⟩ : InnerLengthPt)) (Icc 0 T) 0 t).val,
    ⟨ENNReal.toReal_nonneg, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact (hval.comp_continuousOn (HasUnitSpeedOn.lipschitzOnWith_Icc hs).continuousOn)
  · intro a b ha hab hb
    have ha' : a ∈ Icc 0 R := ⟨ha, hab.trans hb⟩
    have hb' : b ∈ Icc 0 R := ⟨ha.trans hab, hb⟩
    have hinter : Icc 0 R ∩ Icc a b = Icc a b := by
      apply inter_eq_right.mpr
      exact Icc_subset_Icc ha hb
    have h := hs ha' hb'
    simp only [NNReal.coe_one, one_mul, hinter] at h
    rw [hcurve]
    exact h
  · exact congrArg InnerLengthPt.val hstart
  · have h := congrArg InnerLengthPt.val hend
    simpa only [hR_def, hcurve] using h
  · intro t ht
    have h := edist_naturalParameterization_eq_zero hrvar.locallyBoundedVariationOn
      (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩) ht
    rw [variationOnFromTo.eq_of_le _ (Icc 0 T) ht.1,
      inter_eq_right.mpr (Icc_subset_Icc le_rfl ht.2)] at h
    have heq := edist_eq_zero.mp h
    have hv := congrArg InnerLengthPt.val heq
    simpa only [hcurve] using hv

/-- Absolute continuity of a finite integral, pointwise along `[0, T]`. -/
theorem integral_small_near {F : ℝ → ENNReal} {T : ℝ} (hF : ∫⁻ t in Icc 0 T, F t ≠ ⊤) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    Tendsto (fun v => ∫⁻ s in Icc (min t v) (max t v), F s) (𝓝[Icc 0 T] t) (𝓝 0) := by
  have hvol : Tendsto (fun v => volume (Icc (min t v) (max t v))) (𝓝[Icc 0 T] t) (𝓝 0) := by
    have hc : Continuous fun v : ℝ => |v - t| := by fun_prop
    have h1 : Tendsto (fun v : ℝ => |v - t|) (𝓝[Icc 0 T] t) (𝓝 0) := by
      have := (hc.tendsto t).mono_left (nhdsWithin_le_nhds (s := Icc 0 T))
      simpa using this
    have h2 : Tendsto (fun v : ℝ => ENNReal.ofReal |v - t|) (𝓝[Icc 0 T] t) (𝓝 0) := by
      have := (ENNReal.continuous_ofReal.tendsto 0).comp h1
      simpa [Function.comp_def] using this
    refine h2.congr' ?_
    filter_upwards with v
    simp only [Real.volume_Icc]
    congr 1
    rw [max_sub_min_eq_abs', abs_sub_comm]
  have hlim := tendsto_setLIntegral_zero (μ := volume.restrict (Icc 0 T)) (f := F) hF
    (s := fun v => Icc (min t v) (max t v)) (l := 𝓝[Icc 0 T] t) (by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hvol (fun _ => zero_le) ?_
      intro v
      rw [Function.comp, Measure.restrict_apply measurableSet_Icc]
      exact measure_mono inter_subset_left)
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with v hv
  have hsub : Icc (min t v) (max t v) ⊆ Icc 0 T :=
    Icc_subset_Icc (le_min ht.1 hv.1) (max_le ht.2 hv.2)
  rw [Measure.restrict_restrict measurableSet_Icc, inter_eq_left.mpr hsub]

theorem IsEuclideanLengthMetric.innerDist_le_cost_minmax {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {ξ : ℝ} {g : ℂ → ℝ}
    (hfin : ∀ x y, weylScaling D ξ g x y ≠ ⊤) {p : ℝ → ℂ} {T : ℝ}
    (hp : IsLengthParametrized D p T)
    (hC : ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * g (p t))) ≠ ⊤) {u v : ℝ} (hu : u ∈ Icc 0 T)
    (hv : v ∈ Icc 0 T) :
    innerDist D ξ g (p u) (p v) ≤
      (∫⁻ t in Icc (min u v) (max u v), ENNReal.ofReal (Real.exp (ξ * g (p t)))).toReal := by
  have key : ∀ a b : ℝ, a ∈ Icc 0 T → b ∈ Icc 0 T → a ≤ b →
      innerDist D ξ g (p b) (p a) ≤
        (∫⁻ t in Icc a b, ENNReal.ofReal (Real.exp (ξ * g (p t)))).toReal := by
    intro a b ha hb hab
    have hI : ∫⁻ t in Icc a b, ENNReal.ofReal (Real.exp (ξ * g (p t))) ≠ ⊤ :=
      ne_top_of_le_ne_top hC (lintegral_mono_set (Icc_subset_Icc ha.1 hb.2))
    have h1 := hD.curveLength_innerDist_le_cost hfin hp (hu := ha.1) (hv := hb.2) (u := a) (v := b)
    have h2 := two_point_le_curveLength (D := innerDist D ξ g) p hab
    exact (ENNReal.ofReal_le_iff_le_toReal hI).mp (h2.trans h1)
  rcases le_total u v with huv | huv
  · rw [min_eq_left huv, max_eq_right huv]
    have := key u v hu hv huv
    rw [innerDist_symm hD ξ g]
    exact this
  · rw [min_eq_right huv, max_eq_left huv]
    exact key v u hv hu huv

theorem IsEuclideanLengthMetric.abs_sub_arc_le {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {ξ : ℝ}
    {g : ℂ → ℝ} (hg : ContinuousOn g {z | z ≠ 0}) (hfin : ∀ x y, weylScaling D ξ g x y ≠ ⊤)
    {p : ℝ → ℂ} {T : ℝ} (hp : IsLengthParametrized D p T)
    (hC : ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * g (p t))) ≠ ⊤) {u v : ℝ} (hu : u ∈ Icc 0 T)
    (hv : v ∈ Icc 0 T) :
    |(curveLength (innerDist D ξ g) p 0 u).toReal - (curveLength (innerDist D ξ g) p 0 v).toReal| ≤
      (∫⁻ t in Icc (min u v) (max u v), ENNReal.ofReal (Real.exp (ξ * g (p t)))).toReal := by
  have hfinw : ∀ w ∈ Icc 0 T, curveLength (innerDist D ξ g) p 0 w ≠ ⊤ := fun w hw =>
    ne_top_of_le_ne_top hC ((hD.curveLength_innerDist_le_cost hfin hp (hu := le_rfl) (hv := hw.2)).trans
      (lintegral_mono_set (Icc_subset_Icc le_rfl hw.2)))
  have hI : ∫⁻ t in Icc (min u v) (max u v), ENNReal.ofReal (Real.exp (ξ * g (p t))) ≠ ⊤ :=
    ne_top_of_le_ne_top hC (lintegral_mono_set (Icc_subset_Icc (le_min hu.1 hv.1) (max_le hu.2 hv.2)))
  -- for a ≤ b in [0, T]: |s b - s a| ≤ cost on [a, b]
  have key : ∀ a b : ℝ, a ∈ Icc 0 T → b ∈ Icc 0 T → a ≤ b →
      |(curveLength (innerDist D ξ g) p 0 b).toReal - (curveLength (innerDist D ξ g) p 0 a).toReal| ≤
        (∫⁻ t in Icc a b, ENNReal.ofReal (Real.exp (ξ * g (p t)))).toReal := by
    intro a b ha hb hab
    have hadd := curveLength_innerDist_add hD hg hfin p (a := 0) (b := a) (c := b) ha.1 hab
    have hXb := hD.curveLength_innerDist_le_cost hfin hp (hu := ha.1) (hv := hb.2) (u := a) (v := b)
    have hXI : ∫⁻ t in Icc a b, ENNReal.ofReal (Real.exp (ξ * g (p t))) ≠ ⊤ :=
      ne_top_of_le_ne_top hC (lintegral_mono_set (Icc_subset_Icc ha.1 hb.2))
    have hX : curveLength (innerDist D ξ g) p a b ≠ ⊤ := ne_top_of_le_ne_top hXI hXb
    have hsum := congrArg ENNReal.toReal hadd
    rw [ENNReal.toReal_add (hfinw a ha) hX] at hsum
    have hnn : 0 ≤ (curveLength (innerDist D ξ g) p a b).toReal := ENNReal.toReal_nonneg
    have hpos : 0 ≤ (curveLength (innerDist D ξ g) p 0 b).toReal -
        (curveLength (innerDist D ξ g) p 0 a).toReal := by linarith
    rw [abs_of_nonneg hpos]
    have hle := ENNReal.toReal_mono hXI hXb
    linarith
  rcases le_total u v with huv | huv
  · rw [min_eq_left huv, max_eq_right huv]
    rw [abs_sub_comm]
    exact key u v hu hv huv
  · rw [min_eq_right huv, max_eq_left huv]
    exact key v u hv hu huv

theorem IsEuclideanLengthMetric.innerDist_tendsto_of_cost {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {ξ : ℝ} {g : ℂ → ℝ} (hfin : ∀ x y, weylScaling D ξ g x y ≠ ⊤)
    {p : ℝ → ℂ} {T : ℝ} (hp : IsLengthParametrized D p T)
    (hC : ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * g (p t))) ≠ ⊤) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Tendsto (fun v => innerDist D ξ g (p t) (p v)) (𝓝[Icc 0 T] t) (𝓝 0) := by
  have hlim := (ENNReal.tendsto_toReal (ENNReal.zero_ne_top)).comp
    (integral_small_near (F := fun s => ENNReal.ofReal (Real.exp (ξ * g (p s)))) hC ht)
  rw [ENNReal.toReal_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · exact Eventually.of_forall fun v => innerDist_nonneg _ _ _ _
  · filter_upwards [self_mem_nhdsWithin] with v hv
    exact hD.innerDist_le_cost_minmax hfin hp hC ht hv

/-- Uniform multiplicative modulus of a continuous real function on a compact interval. -/
theorem exists_exp_modulus {φ : ℝ → ℝ} {a b : ℝ} (hφ : ContinuousOn φ (Icc a b)) {ρ : ℝ} (hρ : 1 < ρ) :
    ∃ κ > 0, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, |s - t| < κ →
      Real.exp (φ s) ≤ ρ * Real.exp (φ t) := by
  have hlog : 0 < Real.log ρ := Real.log_pos hρ
  obtain ⟨κ, hκ, hκU⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hφ) (Real.log ρ) hlog
  refine ⟨κ, hκ, fun s hs t ht hst => ?_⟩
  have h1 : dist (φ s) (φ t) < Real.log ρ := hκU s hs t ht (by rw [Real.dist_eq]; exact hst)
  rw [Real.dist_eq, abs_lt] at h1
  rw [show ρ * Real.exp (φ t) = Real.exp (φ t + Real.log ρ) by
    rw [Real.exp_add, Real.exp_log (by linarith), mul_comm]]
  exact Real.exp_le_exp.mpr (by linarith [h1.2])

/-- The Riemann comparison for the arc-length reparametrization: the cost of the reparametrized curve for the weight
`e^{ξ f}` is at most `ρ²` times the cost of the original curve for the weight `e^{ξ(g+f)}`. -/
theorem riemann_arc {ξ : ℝ} {f g : ℂ → ℝ} {φ q : ℝ → ℂ} {s : ℝ → ℝ} {T L : ℝ} (hT : 0 ≤ T)
    (hL : s T = L) (hs0 : s 0 = 0) (hqp : ∀ t ∈ Icc 0 T, q (s t) = φ t)
    (hscont : ContinuousOn s (Icc 0 T))
    (hsinc : ∀ a ∈ Icc 0 T, ∀ b ∈ Icc 0 T, a ≤ b → s a ≤ s b ∧
      ENNReal.ofReal (s b - s a) ≤ ∫⁻ t in Icc a b, ENNReal.ofReal (Real.exp (ξ * g (φ t))))
    (hφc : ContinuousOn (fun t => ξ * f (φ t)) (Icc 0 T)) {ρ : ℝ} (hρ : 1 < ρ) :
    ∫⁻ τ in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (q τ))) ≤
      ENNReal.ofReal (ρ * ρ) * ∫⁻ t in Icc 0 T,
        ENNReal.ofReal (Real.exp (ξ * f (φ t))) * ENNReal.ofReal (Real.exp (ξ * g (φ t))) := by
  have hρ0 : 0 < ρ := by linarith
  obtain ⟨κ, hκ, hmod⟩ := exists_exp_modulus hφc hρ
  -- the uniform partition of [0, T]
  set m := κ with hm_def
  set n : ℕ := ⌈T / m⌉₊ + 1 with hn_def
  have hnpos : (0 : ℝ) < n := by positivity
  set Δ := T / n with hΔ_def
  have hΔ0 : 0 ≤ Δ := div_nonneg hT hnpos.le
  have hΔκ : Δ < κ := by
    have h1 : T / m ≤ (⌈T / m⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈T / m⌉₊ : ℝ) < (n : ℝ) := by rw [hn_def]; push_cast; linarith
    rw [hΔ_def, div_lt_iff₀ hnpos]
    rw [div_le_iff₀ hκ] at h1
    nlinarith
  set t : ℕ → ℝ := fun i => (i : ℝ) * Δ with ht_def
  have ht0 : t 0 = 0 := by simp [ht_def]
  have htn : t n = T := by
    have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
    have : (n : ℝ) * (T / n) = T := by field_simp
    exact this
  have htmono : Monotone t := fun i j hij => by
    simp only [ht_def]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hΔ0
  have htmem : ∀ i ≤ n, t i ∈ Icc 0 T := fun i hi =>
    ⟨mul_nonneg (Nat.cast_nonneg i) hΔ0, htn ▸ htmono hi⟩
  have hte : ∀ i, t (i + 1) - t i = Δ := fun i => by
    simp only [ht_def]
    push_cast
    ring
  -- the arc-length points (clamped to [0, T])
  set τ : ℕ → ℝ := fun i => s (min (t i) T) with hτ_def
  have hmemT : ∀ i, min (t i) T ∈ Icc 0 T := fun i =>
    ⟨le_min (mul_nonneg (Nat.cast_nonneg i) hΔ0) hT, min_le_right _ _⟩
  have hτmono : Monotone τ := fun i j hij =>
    (hsinc _ (hmemT i) _ (hmemT j) (min_le_min_right _ (htmono hij))).1
  have hτt : ∀ i ≤ n, τ i = s (t i) := fun i hi => by
    simp only [hτ_def]
    rw [min_eq_left (htmem i hi).2]
  have hτ0 : τ 0 = 0 := by
    simp only [hτ_def, ht0, min_eq_left hT, hs0]
  have hτn : τ n = L := by
    simp only [hτ_def, htn, min_self, hL]
  -- one piece
  have hpiece : ∀ i < n, ∫⁻ τ' in Icc (τ i) (τ (i + 1)), ENNReal.ofReal (Real.exp (ξ * f (q τ'))) ≤
      ENNReal.ofReal (ρ * ρ) * ∫⁻ t' in Icc (t i) (t (i + 1)),
        ENNReal.ofReal (Real.exp (ξ * f (φ t'))) * ENNReal.ofReal (Real.exp (ξ * g (φ t'))) := by
    intro i hi
    have hti : t i ∈ Icc 0 T := htmem i (by omega)
    have hti1 : t (i + 1) ∈ Icc 0 T := htmem (i + 1) (by omega)
    have hle : t i ≤ t (i + 1) := htmono (Nat.le_succ i)
    have hτi : τ i = s (t i) := hτt i (by omega)
    have hτi1 : τ (i + 1) = s (t (i + 1)) := hτt (i + 1) (by omega)
    set bi : ℝ := Real.exp (ξ * f (φ (t i))) with hbi_def
    have hbi0 : 0 < bi := Real.exp_pos _
    have hq_le : ∀ τ' ∈ Icc (τ i) (τ (i + 1)), ENNReal.ofReal (Real.exp (ξ * f (q τ'))) ≤
        ENNReal.ofReal (ρ * bi) := by
      intro τ' hτ'
      rw [hτi, hτi1] at hτ'
      obtain ⟨t', ht', hst'⟩ := intermediate_value_Icc hle
        (hscont.mono (Icc_subset_Icc hti.1 hti1.2)) ⟨hτ'.1, hτ'.2⟩
      have ht'T : t' ∈ Icc 0 T := ⟨hti.1.trans ht'.1, ht'.2.trans hti1.2⟩
      have hqeq : q τ' = φ t' := by rw [← hst', hqp t' ht'T]
      rw [hqeq]
      apply ENNReal.ofReal_le_ofReal
      have hnn : 0 ≤ t' - t i := by linarith [ht'.1]
      have hdist : |t' - t i| < κ := by
        rw [abs_of_nonneg hnn]
        linarith [ht'.2, hte i]
      have hm : Real.exp (ξ * f (φ t')) ≤ ρ * Real.exp (ξ * f (φ (t i))) :=
        hmod t' ht'T (t i) hti hdist
      exact hm
    have hτint : ∫⁻ τ' in Icc (τ i) (τ (i + 1)), ENNReal.ofReal (Real.exp (ξ * f (q τ'))) ≤
        ENNReal.ofReal (ρ * bi) * ENNReal.ofReal (τ (i + 1) - τ i) := by
      calc _ ≤ ∫⁻ τ' in Icc (τ i) (τ (i + 1)), ENNReal.ofReal (ρ * bi) :=
            setLIntegral_mono' measurableSet_Icc hq_le
        _ = ENNReal.ofReal (ρ * bi) * ENNReal.ofReal (τ (i + 1) - τ i) := by
            rw [setLIntegral_const, Real.volume_Icc]
    have hI_le : ENNReal.ofReal (τ (i + 1) - τ i) ≤
        ∫⁻ t' in Icc (t i) (t (i + 1)), ENNReal.ofReal (Real.exp (ξ * g (φ t'))) := by
      rw [hτi, hτi1]
      exact (hsinc (t i) hti (t (i + 1)) hti1 hle).2
    have hstep : ENNReal.ofReal (ρ * bi) * ENNReal.ofReal (τ (i + 1) - τ i) ≤
        ∫⁻ t' in Icc (t i) (t (i + 1)), ENNReal.ofReal (ρ * bi) * ENNReal.ofReal (Real.exp (ξ * g (φ t'))) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact mul_le_mul_of_nonneg_left hI_le (by positivity)
    have hstep2 : ∫⁻ t' in Icc (t i) (t (i + 1)), ENNReal.ofReal (ρ * bi) * ENNReal.ofReal (Real.exp (ξ * g (φ t'))) ≤
        ENNReal.ofReal (ρ * ρ) * ∫⁻ t' in Icc (t i) (t (i + 1)),
          ENNReal.ofReal (Real.exp (ξ * f (φ t'))) * ENNReal.ofReal (Real.exp (ξ * g (φ t'))) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_mono' measurableSet_Icc (fun t' ht' => ?_)
      have ht'T : t' ∈ Icc 0 T := ⟨hti.1.trans ht'.1, ht'.2.trans hti1.2⟩
      have hdist : |t i - t'| < κ := by
        rw [abs_sub_comm, abs_of_nonneg (by linarith [ht'.1] : (0 : ℝ) ≤ t' - t i)]
        linarith [ht'.2, hte i]
      have hbi_le : bi ≤ ρ * Real.exp (ξ * f (φ t')) := hmod (t i) hti t' ht'T hdist
      have hA : ENNReal.ofReal (ρ * bi) ≤
          ENNReal.ofReal (ρ * ρ) * ENNReal.ofReal (Real.exp (ξ * f (φ t'))) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have := mul_le_mul_of_nonneg_left hbi_le hρ0.le
        nlinarith [this]
      calc ENNReal.ofReal (ρ * bi) * ENNReal.ofReal (Real.exp (ξ * g (φ t')))
          ≤ (ENNReal.ofReal (ρ * ρ) * ENNReal.ofReal (Real.exp (ξ * f (φ t')))) *
              ENNReal.ofReal (Real.exp (ξ * g (φ t'))) :=
            mul_le_mul_of_nonneg_right hA (by positivity)
        _ = ENNReal.ofReal (ρ * ρ) * (ENNReal.ofReal (Real.exp (ξ * f (φ t'))) *
              ENNReal.ofReal (Real.exp (ξ * g (φ t')))) := by ring
    calc ∫⁻ τ' in Icc (τ i) (τ (i + 1)), ENNReal.ofReal (Real.exp (ξ * f (q τ')))
        ≤ ENNReal.ofReal (ρ * bi) * ENNReal.ofReal (τ (i + 1) - τ i) := hτint
      _ ≤ _ := hstep
      _ ≤ _ := hstep2
  -- summing the pieces
  have hadj := sum_lintegral_Icc_adjacent (fun τ' => ENNReal.ofReal (Real.exp (ξ * f (q τ')))) τ hτmono n
  have hadjt := sum_lintegral_Icc_adjacent
    (fun t' => ENNReal.ofReal (Real.exp (ξ * f (φ t'))) * ENNReal.ofReal (Real.exp (ξ * g (φ t')))) t htmono n
  rw [hτ0, hτn] at hadj
  rw [ht0, htn] at hadjt
  rw [← hadj, ← hadjt, Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi => hpiece i (Finset.mem_range.mp hi)

theorem IsEuclideanLengthMetric.curveLength_ne_top_of_mem {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {ξ : ℝ} {g : ℂ → ℝ} (hfin : ∀ x y, weylScaling D ξ g x y ≠ ⊤) {p : ℝ → ℂ} {T : ℝ}
    (hp : IsLengthParametrized D p T)
    (hC : ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * g (p t))) ≠ ⊤) {w : ℝ} (hw : w ∈ Icc 0 T) :
    curveLength (innerDist D ξ g) p 0 w ≠ ⊤ :=
  ne_top_of_le_ne_top hC ((hD.curveLength_innerDist_le_cost hfin hp (hu := le_rfl) (hv := hw.2)).trans
    (lintegral_mono_set (Icc_subset_Icc le_rfl hw.2)))

theorem IsEuclideanLengthMetric.arc_sinc {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {ξ : ℝ}
    {g : ℂ → ℝ} (hg : ContinuousOn g {z | z ≠ 0}) (hfin : ∀ x y, weylScaling D ξ g x y ≠ ⊤)
    {p : ℝ → ℂ} {T : ℝ} (hp : IsLengthParametrized D p T)
    (hC : ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * g (p t))) ≠ ⊤) {a b : ℝ} (ha : a ∈ Icc 0 T)
    (hb : b ∈ Icc 0 T) (hab : a ≤ b) :
    (curveLength (innerDist D ξ g) p 0 a).toReal ≤ (curveLength (innerDist D ξ g) p 0 b).toReal ∧
      ENNReal.ofReal ((curveLength (innerDist D ξ g) p 0 b).toReal -
        (curveLength (innerDist D ξ g) p 0 a).toReal) ≤
        ∫⁻ t in Icc a b, ENNReal.ofReal (Real.exp (ξ * g (p t))) := by
  have hadd := curveLength_innerDist_add hD hg hfin p (a := 0) (b := a) (c := b) ha.1 hab
  have hXI : ∫⁻ t in Icc a b, ENNReal.ofReal (Real.exp (ξ * g (p t))) ≠ ⊤ :=
    ne_top_of_le_ne_top hC (lintegral_mono_set (Icc_subset_Icc ha.1 hb.2))
  have hX : curveLength (innerDist D ξ g) p a b ≠ ⊤ :=
    ne_top_of_le_ne_top hXI (hD.curveLength_innerDist_le_cost hfin hp (hu := ha.1) (hv := hb.2))
  have hsum := congrArg ENNReal.toReal hadd
  rw [ENNReal.toReal_add (hD.curveLength_ne_top_of_mem hfin hp hC ha) hX] at hsum
  have hdiff : (curveLength (innerDist D ξ g) p 0 b).toReal -
      (curveLength (innerDist D ξ g) p 0 a).toReal = (curveLength (innerDist D ξ g) p a b).toReal := by
    linarith
  have hnn : 0 ≤ (curveLength (innerDist D ξ g) p a b).toReal := ENNReal.toReal_nonneg
  refine ⟨by linarith, ?_⟩
  rw [hdiff, ENNReal.ofReal_toReal hX]
  exact hD.curveLength_innerDist_le_cost hfin hp (hu := ha.1) (hv := hb.2)

theorem IsEuclideanLengthMetric.arc_continuousOn {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {ξ : ℝ}
    {g : ℂ → ℝ} (hg : ContinuousOn g {z | z ≠ 0}) (hfin : ∀ x y, weylScaling D ξ g x y ≠ ⊤)
    {p : ℝ → ℂ} {T : ℝ} (hp : IsLengthParametrized D p T)
    (hC : ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * g (p t))) ≠ ⊤) :
    ContinuousOn (fun t => (curveLength (innerDist D ξ g) p 0 t).toReal) (Icc 0 T) := by
  intro t ht
  rw [ContinuousWithinAt, tendsto_iff_dist_tendsto_zero]
  have hlim := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (integral_small_near (F := fun s => ENNReal.ofReal (Real.exp (ξ * g (p s)))) hC ht)
  rw [ENNReal.toReal_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · exact Eventually.of_forall fun v => dist_nonneg
  · filter_upwards [self_mem_nhdsWithin] with v hv
    rw [Real.dist_eq, abs_sub_comm]
    exact hD.abs_sub_arc_le hg hfin hp hC ht hv

theorem le_of_forall_ofReal_mul_le {W C : ENNReal} (hC : C ≠ ⊤)
    (h : ∀ ρ : ℝ, 1 < ρ → W ≤ ENNReal.ofReal (ρ * ρ) * C) : W ≤ C := by
  have hlim : Tendsto (fun ρ : ℝ => ENNReal.ofReal (ρ * ρ) * C) (𝓝[>] 1)
      (𝓝 (ENNReal.ofReal (1 * 1) * C)) := by
    have h1 : Tendsto (fun ρ : ℝ => ρ * ρ) (𝓝[>] 1) (𝓝 (1 * 1)) :=
      ((continuous_id.mul continuous_id).tendsto 1).mono_left nhdsWithin_le_nhds
    exact ENNReal.Tendsto.mul_const ((ENNReal.continuous_ofReal.tendsto _).comp h1) (Or.inr hC)
  have hge := ge_of_tendsto hlim (by
    filter_upwards [self_mem_nhdsWithin] with ρ hρ
    exact h ρ hρ)
  simpa using hge

theorem IsEuclideanLengthMetric.weylScaling_innerDist_le_direct {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {ξ : ℝ} {g : ℂ → ℝ} (hg : ContinuousOn g {z | z ≠ 0}) (hfin : ∀ x y, weylScaling D ξ g x y ≠ ⊤)
    {f : ℂ → ℝ} (hf : Continuous f) {p : ℝ → ℂ} {T : ℝ} (hp : IsLengthParametrized D p T) {x y : ℂ}
    (h0 : p 0 = x) (hT : p T = y)
    (hC : ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * (g (p t) + f (p t)))) ≠ ⊤) :
    weylScaling (innerDist D ξ g) ξ f x y ≤
      ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * (g (p t) + f (p t)))) := by
  have hGc := IsEuclideanLengthMetric.cost_g_ne_top hf hp hC
  have hfinite : curveLength (innerDist D ξ g) p 0 T ≠ ⊤ :=
    hD.curveLength_ne_top_of_mem hfin hp hGc ⟨hp.1, le_rfl⟩
  obtain ⟨q, hq, hq0, hqT, hqp⟩ := hD.exists_arclength_innerDist hg hfin hp.1 hfinite
    (fun t ht => hD.innerDist_tendsto_of_cost hfin hp hGc ht)
  have hs0 : (curveLength (innerDist D ξ g) p 0 0).toReal = 0 := by
    have h := hD.curveLength_innerDist_le_cost hfin hp (u := 0) (v := 0) (hu := le_rfl) (hv := hp.1)
    have hz : ∫⁻ t in Icc (0 : ℝ) 0, ENNReal.ofReal (Real.exp (ξ * g (p t))) = 0 := by
      simp
    rw [hz] at h
    rw [nonpos_iff_eq_zero.mp h, ENNReal.toReal_zero]
  have hφc : ContinuousOn (fun t => ξ * f (p t)) (Icc 0 T) :=
    (continuous_const.mul hf).comp_continuousOn hp.2.1
  have hρ : ∀ ρ : ℝ, 1 < ρ → weylScaling (innerDist D ξ g) ξ f x y ≤
      ENNReal.ofReal (ρ * ρ) * ∫⁻ t in Icc 0 T,
        ENNReal.ofReal (Real.exp (ξ * f (p t))) * ENNReal.ofReal (Real.exp (ξ * g (p t))) := by
    intro ρ hρ1
    have hR := riemann_arc (ξ := ξ) (f := f) (g := g) (φ := p) (q := q)
      (s := fun t => (curveLength (innerDist D ξ g) p 0 t).toReal) (T := T)
      (L := (curveLength (innerDist D ξ g) p 0 T).toReal) hp.1 rfl hs0 hqp
      (hD.arc_continuousOn hg hfin hp hGc)
      (fun a ha b hb hab => hD.arc_sinc hg hfin hp hGc ha hb hab) hφc hρ1
    have hW : weylScaling (innerDist D ξ g) ξ f x y ≤
        ∫⁻ τ in Icc 0 (curveLength (innerDist D ξ g) p 0 T).toReal,
          ENNReal.ofReal (Real.exp (ξ * f (q τ))) := by
      unfold weylScaling
      exact (iInf₂_le _ q).trans ((iInf₂_le hq (hq0.trans h0)).trans (iInf_le _ (hqT.trans hT)))
    exact hW.trans hR
  have hcongr : ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * f (p t))) *
      ENNReal.ofReal (Real.exp (ξ * g (p t))) =
      ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * (g (p t) + f (p t)))) :=
    setLIntegral_congr_fun measurableSet_Icc (fun t _ => by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      ring)
  have hCfin : ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * f (p t))) *
      ENNReal.ofReal (Real.exp (ξ * g (p t))) ≠ ⊤ := by
    rw [hcongr]
    exact hC
  rw [← hcongr]
  exact le_of_forall_ofReal_mul_le hCfin hρ


/-- Derivation of `WeylMetricCompositionContinuousOuterFrozen` (FirstPass/Frozen/S11j.lean:117). -/
theorem weylMetricCompositionContinuousOuter_derived : WeylMetricCompositionContinuousOuterFrozen := by
  intro ξ _ D g f hD hg hf hfin x y
  apply le_antisymm
  · show weylScaling (innerDist D ξ g) ξ f x y ≤ ⨅ (T : ℝ) (p : ℝ → ℂ) (_ : IsLengthParametrized D p T)
      (_ : p 0 = x) (_ : p T = y), ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * (g (p t) + f (p t))))
    refine le_iInf fun T => le_iInf fun p => le_iInf fun hp => le_iInf fun h0 => le_iInf fun hT => ?_
    by_cases hC : ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * (g (p t) + f (p t)))) = ⊤
    · rw [hC]
      exact le_top
    · exact hD.weylScaling_innerDist_le_direct hg hfin hf hp h0 hT hC
  · show weylScaling D ξ (fun z => g z + f z) x y ≤ ⨅ (L : ℝ) (q : ℝ → ℂ)
      (_ : IsLengthParametrized (innerDist D ξ g) q L) (_ : q 0 = x) (_ : q L = y),
        ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (q t)))
    refine le_iInf fun L => le_iInf fun q => le_iInf fun hq => le_iInf fun h0 => le_iInf fun hL => ?_
    exact hD.weylScaling_le_iterated hg hfin hf hq h0 hL

end HarmonicBalls
