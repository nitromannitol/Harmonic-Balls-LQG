import HarmonicBalls.Defs.LQGMetric
import HarmonicBalls.Draft.Section11
import HarmonicBalls.Steps.Sec11.WeylPathConcatenation

/-!
# Lemma 11.14: the pinch-point event forces a metric-ball consequence (deterministic part)

FIRST-PASS NEW (lemma:geometric-event-consequence, paper line 3264; proof lines 3266-3300). The printed proof uses
LQG geodesics. Here the same inequalities are obtained for arbitrary Euclidean-continuous paths: for a path `γ`
from `0` to `y`, its `D`-length dominates `D(0, q₁) + D(q₂, y)` with `q₁ ∈ ∂B_{5r}(z)` met before `q₂ ∈ ∂Q_r(z)`
(intermediate value theorem on `|γ - z|`, then additivity of the curve length). The argument is deterministic in
the realisation; its only metric input is the length-metric structure `IsEuclideanLengthMetric D` (Fact 2.2 I).
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace HarmonicBalls

namespace FirstPassS11

variable {D : ℂ → ℂ → ℝ}

/-- The `D`-balls of a length metric are Euclidean open (the `D`-open sets are the Euclidean open sets). -/
lemma isOpen_lqgBall (hD : IsEuclideanLengthMetric D) (x : ℂ) (s : ℝ) : IsOpen {w | D x w < s} := by
  refine (hD.isOpen_iff _).2 fun z hz => ⟨s - D x z, ?_, fun w hw => ?_⟩
  · have hz' : D x z < s := hz
    linarith
  · have hz' : D x z < s := hz
    have hw' : D z w < s - D x z := hw
    show D x w < s
    linarith [hD.triangle x z w]

/-- For a length metric, `w ↦ D x w` is Euclidean continuous. -/
lemma continuous_dist_right (hD : IsEuclideanLengthMetric D) (x : ℂ) : Continuous fun w => D x w := by
  rw [continuous_iff_continuousAt]
  intro w
  show Tendsto (fun v => D x v) (𝓝 w) (𝓝 (D x w))
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hw : w ∈ {v | D w v < ε} := by
    show D w w < ε
    rw [hD.self_eq_zero]
    exact hε
  filter_upwards [(isOpen_lqgBall hD w ε).mem_nhds hw] with v hv
  have hv' : D w v < ε := hv
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor
  · linarith [hD.triangle x w v, hD.symm w v]
  · linarith [hD.triangle x v w, hD.symm v w]

/-- A one-interval partition gives `ofReal (D (p a) (p b)) ≤ curveLength D p a b` for `a ≤ b`. -/
lemma ofReal_dist_le_curveLength (hD : IsEuclideanLengthMetric D) (p : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b) :
    ENNReal.ofReal (D (p a) (p b)) ≤ curveLength D p a b := by
  unfold curveLength
  rw [show D (p a) (p b) = D (p b) (p a) from hD.symm _ _]
  have hmono : Monotone (fun i : ℕ => if i = 0 then a else b) := by
    intro i j hij
    dsimp only
    split_ifs <;> first | exact le_rfl | exact hab | omega
  have hmem : ∀ i : ℕ, (fun i : ℕ => if i = 0 then a else b) i ∈ Icc a b := by
    intro i
    dsimp only
    split_ifs <;> simp [Set.mem_Icc, hab]
  refine le_iSup_of_le (1, ⟨fun i : ℕ => if i = 0 then a else b, hmono, hmem⟩) ?_
  simp

/-- Splitting a curve length at `s₁ ≤ s` with `s ≤ 1`. -/
lemma curveLength_split_le (hD : IsEuclideanLengthMetric D) (p : ℝ → ℂ) {s1 s : ℝ}
    (h1 : 0 ≤ s1) (hs : s1 ≤ s) (h2 : s ≤ 1) :
    curveLength D p 0 s1 + curveLength D p s 1 ≤ curveLength D p 0 1 := by
  have e1 := hD.curveLength_add p h1 hs
  have e2 := hD.curveLength_add p (h1.trans hs) h2
  rw [← e2, ← e1]
  exact add_le_add (le_self_add : curveLength D p 0 s1 ≤ curveLength D p 0 s1 + curveLength D p s1 s) le_rfl

/-- `(r x + z)`-distance to the centre. -/
lemma dist_rescale_centre {r : ℝ} (hr : 0 < r) (x z : ℂ) : dist ((r : ℂ) * x + z) z = r * dist x 0 := by
  simp [dist_eq_norm, abs_of_pos hr]

lemma mem_rescaledSet_iff' {A : Set ℂ} {r : ℝ} (hr : (r : ℂ) ≠ 0) (z y : ℂ) :
    y ∈ rescaledSet A r z ↔ (r : ℂ)⁻¹ * (y - z) ∈ A := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    have : (r : ℂ)⁻¹ * ((r : ℂ) * x + z - z) = x := by
      field_simp
      ring
    rw [this]
    exact hx
  · intro h
    exact ⟨_, h, by field_simp; ring⟩

/-- Lower bound along a path from `0` to `y ∈ Q'_r(z)`: any such path has length at least `u` whenever
`z` lies on the frontier of `𝓑_u(0)` (proof of the first clause of Lemma 11.14, lines 3272-3280). -/
lemma length_lower_bound_Q' (hD : IsEuclideanLengthMetric D) {Q Q' : Set ℂ} {r u : ℝ} {z y : ℂ}
    (hr : 0 < r) (hz10 : 10 * r ≤ dist (0 : ℂ) z)
    (hQr_open : IsOpen (rescaledSet Q r z))
    (hclQr : closure (rescaledSet Q r z) ⊆ closedBall z (5 * r))
    (hyQ' : y ∈ rescaledSet Q' r z) (hyQr : y ∈ rescaledSet Q r z)
    (hev1 : (⨆ x ∈ sphere z (5 * r), ENNReal.ofReal (D z x)) <
      ENNReal.ofReal (setDist D (rescaledSet Q' r z) (frontier (rescaledSet Q r z))))
    (hu : u ≤ D 0 z) :
    ∀ γ : ℝ → ℂ, Continuous γ → γ 0 = 0 → γ 1 = y → ENNReal.ofReal u < curveLength D γ 0 1 := by
  intro γ hγc hγ0 hγ1
  have hyQcl : y ∈ closure (rescaledSet Q r z) := subset_closure hyQr
  -- the closed set of times at which `γ` is in the closure of `𝒬_r(z)`
  have hKc : IsClosed (Icc (0 : ℝ) 1 ∩ γ ⁻¹' closure (rescaledSet Q r z)) :=
    isClosed_Icc.inter (isClosed_closure.preimage hγc)
  have hKne : (Icc (0 : ℝ) 1 ∩ γ ⁻¹' closure (rescaledSet Q r z)).Nonempty := by
    refine ⟨1, ⟨⟨zero_le_one, le_rfl⟩, ?_⟩⟩
    show γ 1 ∈ closure (rescaledSet Q r z)
    rw [hγ1]
    exact hyQcl
  have hKbdd : BddBelow (Icc (0 : ℝ) 1 ∩ γ ⁻¹' closure (rescaledSet Q r z)) := ⟨0, fun s hs => hs.1.1⟩
  have hsmin := hKc.csInf_mem hKne hKbdd
  obtain ⟨⟨hs0_0, hs0_1⟩, hγs0⟩ := hsmin
  have hγs0' : γ (sInf (Icc (0 : ℝ) 1 ∩ γ ⁻¹' closure (rescaledSet Q r z))) ∈
      closure (rescaledSet Q r z) := hγs0
  set s0 := sInf (Icc (0 : ℝ) 1 ∩ γ ⁻¹' closure (rescaledSet Q r z)) with hs0def
  have hclosed_ball : closure (rescaledSet Q r z) ⊆ closedBall z (5 * r) := hclQr
  have hs0pos : 0 < s0 := by
    rcases hs0_0.lt_or_eq with h | h
    · exact h
    · exfalso
      have h0 : γ 0 ∈ closure (rescaledSet Q r z) := by
        rw [← h] at hγs0'
        exact hγs0'
      have := mem_closedBall.1 (hclosed_ball h0)
      rw [hγ0] at this
      linarith
  -- `γ s0` is not in the open set `𝒬_r(z)`, hence lies on its frontier
  have hq2fr : γ s0 ∈ frontier (rescaledSet Q r z) := by
    refine ⟨hγs0', ?_⟩
    intro hin
    rw [hQr_open.interior_eq] at hin
    have hev : ∀ᶠ s in 𝓝 s0, γ s ∈ rescaledSet Q r z :=
      hγc.continuousAt.eventually_mem (hQr_open.mem_nhds hin)
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
    have hmpos : 0 < min (ε / 2) s0 := lt_min (by linarith) hs0pos
    have hmle : min (ε / 2) s0 ≤ s0 := min_le_right _ _
    have hmle' : min (ε / 2) s0 ≤ ε / 2 := min_le_left _ _
    have hsub : s0 - min (ε / 2) s0 / 2 ∈ Icc (0 : ℝ) 1 ∩ γ ⁻¹' closure (rescaledSet Q r z) := by
      refine ⟨⟨by linarith, by linarith⟩, ?_⟩
      show γ (s0 - min (ε / 2) s0 / 2) ∈ closure (rescaledSet Q r z)
      apply subset_closure
      apply hball
      rw [Real.dist_eq, abs_sub_lt_iff]
      constructor <;> linarith
    have hle := csInf_le hKbdd hsub
    linarith
  -- intermediate value theorem for `|γ - z|` on `[0, s0]`
  have hgc : Continuous fun s => dist (γ s) z := hγc.dist continuous_const
  have hgs0 : dist (γ s0) z ≤ 5 * r := mem_closedBall.1 (hclosed_ball hγs0')
  have hg0 : 10 * r ≤ dist (γ 0) z := by rw [hγ0]; exact hz10
  obtain ⟨s1, hs1, hgs1⟩ : ∃ s1 ∈ Icc (0 : ℝ) s0, dist (γ s1) z = 5 * r := by
    obtain ⟨s1, hs1, h⟩ := intermediate_value_Icc' hs0_0 hgc.continuousOn
      (show 5 * r ∈ Icc (dist (γ s0) z) (dist (γ 0) z) from ⟨hgs0, by linarith⟩)
    exact ⟨s1, hs1, h⟩
  have hq1sph : γ s1 ∈ sphere z (5 * r) := mem_sphere.2 hgs1
  have hs1le : s1 ≤ s0 := hs1.2
  have hs1nn : 0 ≤ s1 := hs1.1
  -- length of `γ` dominates `D(0, q₁) + D(q₂, y)`
  have hlen : ENNReal.ofReal (D 0 (γ s1)) + ENNReal.ofReal (D (γ s0) y) ≤ curveLength D γ 0 1 := by
    have ha := ofReal_dist_le_curveLength hD γ hs1nn
    have hb := ofReal_dist_le_curveLength hD γ hs0_1
    rw [hγ0] at ha
    rw [hγ1] at hb
    exact (add_le_add ha hb).trans (curveLength_split_le hD γ hs1nn hs1le hs0_1)
  -- the first-event inequality
  have hkey : ENNReal.ofReal (D z (γ s1)) < ENNReal.ofReal (D (γ s0) y) := by
    have h1 : ENNReal.ofReal (D z (γ s1)) ≤ ⨆ x ∈ sphere z (5 * r), ENNReal.ofReal (D z x) :=
      le_iSup₂ (f := fun x (_ : x ∈ sphere z (5 * r)) => ENNReal.ofReal (D z x)) (γ s1) hq1sph
    have hbdd : BddBelow (image2 D (rescaledSet Q' r z) (frontier (rescaledSet Q r z))) := by
      by_contra hnb
      rw [setDist, Real.sInf_of_not_bddBelow hnb] at hev1
      simp at hev1
    have h2 : setDist D (rescaledSet Q' r z) (frontier (rescaledSet Q r z)) ≤ D y (γ s0) :=
      csInf_le hbdd ⟨y, hyQ', γ s0, hq2fr, rfl⟩
    calc ENNReal.ofReal (D z (γ s1)) ≤ ⨆ x ∈ sphere z (5 * r), ENNReal.ofReal (D z x) := h1
      _ < ENNReal.ofReal (setDist D (rescaledSet Q' r z) (frontier (rescaledSet Q r z))) := hev1
      _ ≤ ENNReal.ofReal (D y (γ s0)) := ENNReal.ofReal_le_ofReal h2
      _ = ENNReal.ofReal (D (γ s0) y) := by rw [hD.symm]
  -- conclusion
  calc ENNReal.ofReal u ≤ ENNReal.ofReal (D 0 z) := ENNReal.ofReal_le_ofReal hu
    _ ≤ ENNReal.ofReal (D 0 (γ s1) + D (γ s1) z) :=
        ENNReal.ofReal_le_ofReal (hD.triangle 0 (γ s1) z)
    _ ≤ ENNReal.ofReal (D 0 (γ s1)) + ENNReal.ofReal (D (γ s1) z) := ENNReal.ofReal_add_le
    _ = ENNReal.ofReal (D 0 (γ s1)) + ENNReal.ofReal (D z (γ s1)) := by rw [hD.symm (γ s1) z]
    _ < ENNReal.ofReal (D 0 (γ s1)) + ENNReal.ofReal (D (γ s0) y) :=
        ENNReal.add_lt_add_left ENNReal.ofReal_ne_top hkey
    _ ≤ curveLength D γ 0 1 := hlen

/-- Gap for paths from `0` to `z`: `D(0, y) + δ ≤` length, for `y ∈ 𝒯_r(z)` (second clause of Lemma 11.14,
lines 3283-3292). The `δ > 0` comes from the strict inequality of the second event. -/
lemma length_gap_T (hD : IsEuclideanLengthMetric D) {T : Set ℂ} {r : ℝ} {z y : ℂ} (hr : 0 < r)
    (hz10 : 10 * r ≤ dist (0 : ℂ) z)
    (hSph : sphere z (5 * r) ⊆ closure (rescaledSet T r z))
    (hyT : y ∈ rescaledSet T r z)
    (hev2 : (⨆ x ∈ rescaledSet T r z, ⨆ y' ∈ rescaledSet T r z, ENNReal.ofReal (D x y')) <
      ENNReal.ofReal (setDist D {z} (sphere z (5 * r)))) :
    ∃ δ : NNReal, 0 < δ ∧ ∀ γ : ℝ → ℂ, Continuous γ → γ 0 = 0 → γ 1 = z →
      ENNReal.ofReal (D 0 y) + δ ≤ curveLength D γ 0 1 := by
  obtain ⟨δ, hδpos, hδ⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 hev2
  refine ⟨δ, hδpos, fun γ hγc hγ0 hγ1 => ?_⟩
  have hgc : Continuous fun s => dist (γ s) z := hγc.dist continuous_const
  have hg0 : 10 * r ≤ dist (γ 0) z := by rw [hγ0]; exact hz10
  have hg1 : dist (γ 1) z = 0 := by rw [hγ1, dist_self]
  obtain ⟨s1, hs1, hgs1⟩ : ∃ s1 ∈ Icc (0 : ℝ) 1, dist (γ s1) z = 5 * r := by
    obtain ⟨s1, hs1, h⟩ := intermediate_value_Icc' zero_le_one hgc.continuousOn
      (show 5 * r ∈ Icc (dist (γ 1) z) (dist (γ 0) z) from ⟨by rw [hg1]; linarith, by linarith⟩)
    exact ⟨s1, hs1, h⟩
  have hq1 : γ s1 ∈ sphere z (5 * r) := mem_sphere.2 hgs1
  -- `y ∈ 𝒯_r(z)` and the bound on the closure of `𝒯_r(z)`
  set S := ⨆ x ∈ rescaledSet T r z, ⨆ y' ∈ rescaledSet T r z, ENNReal.ofReal (D x y') with hSdef
  have hcy : Continuous fun x => D x y := (continuous_dist_right hD y).congr fun x => hD.symm y x
  have hclosed : IsClosed {x : ℂ | ENNReal.ofReal (D x y) ≤ S} :=
    isClosed_le (ENNReal.continuous_ofReal.comp hcy) continuous_const
  have hTle : closure (rescaledSet T r z) ⊆ {x : ℂ | ENNReal.ofReal (D x y) ≤ S} := by
    apply closure_minimal _ hclosed
    intro x hx
    show ENNReal.ofReal (D x y) ≤ S
    exact (le_iSup₂ (f := fun y' (_ : y' ∈ rescaledSet T r z) => ENNReal.ofReal (D x y')) y hyT).trans
      (le_iSup₂ (f := fun x' (_ : x' ∈ rescaledSet T r z) =>
        ⨆ y' ∈ rescaledSet T r z, ENNReal.ofReal (D x' y')) x hx)
  have hq1S : ENNReal.ofReal (D (γ s1) y) ≤ S := hTle (hSph hq1)
  have hbdd2 : BddBelow (image2 D {z} (sphere z (5 * r))) := by
    by_contra hnb
    have h0 := hev2
    rw [setDist, Real.sInf_of_not_bddBelow hnb] at h0
    simp at h0
  have hq1L : ENNReal.ofReal (setDist D {z} (sphere z (5 * r))) ≤ ENNReal.ofReal (D z (γ s1)) :=
    ENNReal.ofReal_le_ofReal (csInf_le hbdd2 ⟨z, mem_singleton z, γ s1, hq1, rfl⟩)
  -- the length bound through `γ(s₁)`
  have hs1nn : (0 : ℝ) ≤ s1 := hs1.1
  have hs1le : s1 ≤ 1 := hs1.2
  have ha := ofReal_dist_le_curveLength hD γ hs1nn
  have hb := ofReal_dist_le_curveLength hD γ hs1le
  rw [hγ0] at ha
  rw [hγ1] at hb
  have hlen : ENNReal.ofReal (D 0 (γ s1)) + ENNReal.ofReal (D (γ s1) z) ≤ curveLength D γ 0 1 :=
    (add_le_add ha hb).trans (curveLength_split_le hD γ hs1nn le_rfl hs1le)
  have hdy : ENNReal.ofReal (D 0 y) ≤ ENNReal.ofReal (D 0 (γ s1)) + ENNReal.ofReal (D (γ s1) y) :=
    (ENNReal.ofReal_le_ofReal (hD.triangle 0 (γ s1) y)).trans ENNReal.ofReal_add_le
  have h1 : ENNReal.ofReal (D 0 y) ≤ ENNReal.ofReal (D 0 (γ s1)) + S :=
    hdy.trans (add_le_add le_rfl hq1S)
  have h2 : ENNReal.ofReal (D 0 y) + δ ≤ ENNReal.ofReal (D 0 (γ s1)) + S + δ := add_le_add h1 le_rfl
  have h3 : (S + δ) ≤ ENNReal.ofReal (D z (γ s1)) := hδ.le.trans hq1L
  calc ENNReal.ofReal (D 0 y) + δ ≤ ENNReal.ofReal (D 0 (γ s1)) + S + δ := h2
    _ = ENNReal.ofReal (D 0 (γ s1)) + (S + δ) := add_assoc _ _ _
    _ ≤ ENNReal.ofReal (D 0 (γ s1)) + ENNReal.ofReal (D z (γ s1)) := add_le_add le_rfl h3
    _ = ENNReal.ofReal (D 0 (γ s1)) + ENNReal.ofReal (D (γ s1) z) := by rw [hD.symm z (γ s1)]
    _ ≤ curveLength D γ 0 1 := hlen

/-- Deterministic core of Lemma 11.14 (lemma:geometric-event-consequence, line 3264): for a length metric `D` and a
pinch-point configuration, the two geometric clauses of `Ĝ_r(z)` and `z ∈ ∂𝓑_u(0)` force `Q'_r(z) ⊆ 𝓑_u(0)ᶜ` and
`T_r(z) ⊆ 𝓑_u(0)`. -/
theorem metricBall_of_pinch_event (hD : IsEuclideanLengthMetric D) {U T Q' Q : Set ℂ}
    (hc : IsPinchPointConfiguration U T Q' Q) {z : ℂ} {r u : ℝ} (hr : 0 < r)
    (hz0 : (0 : ℂ) ∉ ball z (10 * r)) (hu : 0 < u)
    (hev1 : (⨆ x ∈ sphere z (5 * r), ENNReal.ofReal (D z x)) <
      ENNReal.ofReal (setDist D (rescaledSet Q' r z) (frontier (rescaledSet Q r z))))
    (hev2 : (⨆ x ∈ rescaledSet T r z, ⨆ y ∈ rescaledSet T r z, ENNReal.ofReal (D x y)) <
      ENNReal.ofReal (setDist D {z} (sphere z (5 * r))))
    (hfr : z ∈ frontier (lqgMetricBall D 0 u)) :
    rescaledSet Q' r z ⊆ (lqgMetricBall D 0 u)ᶜ ∧ rescaledSet T r z ⊆ lqgMetricBall D 0 u := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hz10 : 10 * r ≤ dist (0 : ℂ) z := not_lt.mp fun h => hz0 (mem_ball.2 h)
  have hBd_open : IsOpen (lqgMetricBall D 0 u) := isOpen_lqgBall hD 0 u
  -- `D(0, z) = u` (only `u ≤ D(0,z)` from the frontier point not lying in the open ball is needed for `Q'`)
  have hu_le : u ≤ D 0 z := by
    have hnot : ¬ (D 0 z < u) := fun h => hfr.2 (by rw [hBd_open.interior_eq]; exact h)
    exact not_lt.mp hnot
  have hz_cl : D 0 z ≤ u := by
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨w, hwV, hwB⟩ := mem_closure_iff.1 hfr.1 {v | D z v < ε} (isOpen_lqgBall hD z ε)
      (by show D z z < ε; rw [hD.self_eq_zero]; exact hε)
    have hwV' : D z w < ε := hwV
    have hwB' : D 0 w < u := hwB
    linarith [hD.triangle 0 w z, hD.symm w z]
  -- the open set `𝒬_r(z)` and its closure inside `B_{5r}(z)`
  have hQball : ∀ x ∈ Q, dist x 0 < 5 := fun x hx => by
    have h := hc.Q_subset hx
    unfold annulus at h
    exact mem_ball.1 h.1.1
  have hQr_open : IsOpen (rescaledSet Q r z) := by
    have heq : rescaledSet Q r z = (fun y : ℂ => (r : ℂ)⁻¹ * (y - z)) ⁻¹' Q :=
      Set.ext fun y => mem_rescaledSet_iff' hr0 z y
    rw [heq]
    exact hc.isOpen_Q.preimage (by fun_prop)
  have hclQr : closure (rescaledSet Q r z) ⊆ closedBall z (5 * r) := by
    apply closure_minimal _ isClosed_closedBall
    rintro _ ⟨x, hx, rfl⟩
    show dist ((r : ℂ) * x + z) z ≤ 5 * r
    rw [dist_rescale_centre hr]
    have := hQball x hx
    nlinarith
  -- the sphere `∂B_{5r}(z)` lies in the closure of `𝒯_r(z)`
  have hTsph : sphere z (5 * r) ⊆ closure (rescaledSet T r z) := by
    intro y hy
    have hy' : dist y z = 5 * r := mem_sphere.1 hy
    have hnorm : ‖(r : ℂ)⁻¹ * (y - z)‖ = 5 := by
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hr.le, ← dist_eq_norm, hy']
      field_simp
    have hxs : (r : ℂ)⁻¹ * (y - z) ∈ sphere (0 : ℂ) 5 := mem_sphere_zero_iff_norm.2 hnorm
    have hxcl : (r : ℂ)⁻¹ * (y - z) ∈ closure T := (hc.sphere_subset_frontier hxs).1
    have hy_eq : (r : ℂ) * ((r : ℂ)⁻¹ * (y - z)) + z = y := by
      rw [mul_inv_cancel_left₀ hr0, sub_add_cancel]
    have hcont : Continuous fun x : ℂ => (r : ℂ) * x + z := by fun_prop
    have h' : y ∈ closure ((fun x : ℂ => (r : ℂ) * x + z) '' T) := by
      rw [← hy_eq]
      exact image_closure_subset_closure_image hcont ⟨_, hxcl, rfl⟩
    exact h'
  refine ⟨?_, ?_⟩
  · intro y hy
    have hyQ : y ∈ rescaledSet Q r z := by
      obtain ⟨x, hx, hxy⟩ := hy
      exact ⟨x, hc.closure_Q'_subset (subset_closure hx), hxy⟩
    have hlow := length_lower_bound_Q' hD hr hz10 hQr_open hclQr hy hyQ hev1 hu_le
    have hle : ENNReal.ofReal u ≤ ENNReal.ofReal (D 0 y) := by
      rw [hD.ofReal_eq_internalMetric 0 y]
      unfold internalMetric
      exact le_iInf fun P => le_iInf fun _ =>
        (hlow P.extend P.continuous_extend P.extend_zero P.extend_one).le
    have hu' : u ≤ D 0 y := by
      rcases ENNReal.ofReal_le_ofReal_iff'.1 hle with h | h
      · exact h
      · linarith
    exact not_lt.mpr hu'
  · intro y hy
    show D 0 y < u
    obtain ⟨δ, hδ, hgap⟩ := length_gap_T hD hr hz10 hTsph hy hev2
    have hle : ENNReal.ofReal (D 0 y) + δ ≤ ENNReal.ofReal (D 0 z) := by
      rw [hD.ofReal_eq_internalMetric 0 z]
      unfold internalMetric
      exact le_iInf fun P => le_iInf fun _ =>
        hgap P.extend P.continuous_extend P.extend_zero P.extend_one
    have hlt : ENNReal.ofReal (D 0 y) < ENNReal.ofReal (D 0 z) :=
      lt_of_lt_of_le (ENNReal.lt_add_right ENNReal.ofReal_ne_top (ENNReal.coe_ne_zero.2 hδ.ne')) hle
    have hDlt : D 0 y < D 0 z := (ENNReal.ofReal_lt_ofReal_iff'.1 hlt).1
    linarith [hz_cl]

end FirstPassS11

end HarmonicBalls
