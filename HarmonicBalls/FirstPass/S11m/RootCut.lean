import HarmonicBalls.Steps.Sec11.LocalPathLength
import HarmonicBalls.Steps.Sec11.InternalMetricPaths

/-!
# Root recovery from punctured distances (write-up Step 3.5, first display (8))

Source: Step 3.4 of the written proof. For an open set `O` with `0 ∈ O`,
`0 < s`, and a point `x` with `s < ‖x‖`, the root distance `D(0, x; O)` is squeezed between punctured distances to the
circle `∂B_s`:

* lower bound: `inf_{y ∈ ∂B_s} D(y, x; O \ {0}) ≤ D(0, x; O)` (cut an almost minimizing path after its last visit to
  `closedBall 0 s`; the rest lies outside `closedBall 0 s`, hence avoids `0`);
* upper bound: `D(0, x; O) ≤ sup_{y ∈ ∂B_s} D(0, y; O) + inf_{y ∈ ∂B_s} D(y, x; O \ {0})` (triangle inequality for the
  internal metric of a Euclidean length metric, plus `D(·; O) ≤ D(·; O \ {0})`).

The limit `sup_{y ∈ ∂B_s} D(0, y; O) → 0` as `s → 0` is a continuity input and is not proved here.
-/

namespace HarmonicBalls.S11m

open Set Metric Topology unitInterval

/-- Exit point of a path from `0` to `x` through the circle `∂B_s`: the last visit to `closedBall 0 s`. The rest of
the path is a path from a point of the circle to `x`, it stays outside `closedBall 0 s` (so it avoids `0`), and it is
not longer. -/
theorem exists_sphere_subpath (D : ℂ → ℂ → ℝ) {O : Set ℂ} {s : ℝ} (hs : 0 < s) {x : ℂ} (hx : s < ‖x‖)
    (p : Path (0 : ℂ) x) (hp : ∀ t, p t ∈ O) :
    ∃ y : ℂ, ‖y‖ = s ∧ ∃ q : Path y x, (∀ u, q u ∈ O ∧ s ≤ ‖q u‖) ∧ pathLength D q ≤ pathLength D p := by
  set K : Set unitInterval := {t | ‖p t‖ ≤ s} with hK
  have hKc : IsCompact K := (isClosed_le p.continuous.norm continuous_const).isCompact
  have hne : K.Nonempty := ⟨0, by simp [hK, hs.le]⟩
  obtain ⟨t, htK, htmax⟩ := hKc.exists_isGreatest hne
  have hle : ∀ w : unitInterval, t < w → s < ‖p w‖ := by
    intro w hw
    by_contra h
    exact absurd (htmax (show w ∈ K from not_lt.1 h)) (not_le.2 hw)
  -- real-variable version for the intermediate value theorem
  set f : ℝ → ℝ := fun u => ‖p.extend u‖ with hf
  have hfc : Continuous f := p.continuous_extend.norm
  have hfp : ∀ w : unitInterval, f (w : ℝ) = ‖p w‖ := fun w => by
    simp only [hf]
    rw [p.extend_extends' w]
  have hf1 : f 1 = ‖x‖ := by
    have h := hfp 1
    rw [p.target] at h
    exact h
  have hft : f (t : ℝ) = s := by
    have ht_le : (t : ℝ) ≤ 1 := t.2.2
    have hfs : f (t : ℝ) ≤ s := by
      rw [hfp]
      exact htK
    have hfs1 : s ≤ f 1 := by
      rw [hf1]
      exact hx.le
    obtain ⟨u, ⟨hu1, hu2⟩, hfu⟩ := intermediate_value_Icc ht_le hfc.continuousOn ⟨hfs, hfs1⟩
    by_cases hut : u = (t : ℝ)
    · rw [← hut]
      exact hfu
    · exfalso
      have hu0 : (0 : ℝ) ≤ u := le_trans t.2.1 hu1
      have htu : (t : ℝ) < u := lt_of_le_of_ne hu1 (Ne.symm hut)
      have hgt : s < ‖p ⟨u, hu0, hu2⟩‖ := hle _ (Subtype.coe_lt_coe.mp htu)
      have e : f u = ‖p ⟨u, hu0, hu2⟩‖ := hfp ⟨u, hu0, hu2⟩
      linarith
  refine ⟨p t, ?_, ?_⟩
  · rw [← hfp t, hft]
  · let q : Path (p t) x := (p.subpath t 1).cast rfl p.target.symm
    refine ⟨q, ?_, ?_⟩
    · intro u
      have hu : (p.subpath t 1) u ∈ Set.range (p.subpath t 1) := Set.mem_range_self u
      rw [Path.range_subpath_of_le p t 1 (show t ≤ 1 from t.2.2)] at hu
      obtain ⟨w, hw, hwu⟩ := hu
      have hO : (p.subpath t 1) u ∈ O := by
        rw [← hwu]
        exact hp w
      refine ⟨hO, ?_⟩
      have key : s ≤ ‖p w‖ := by
        by_cases hwt : w = t
        · rw [hwt]
          have h0 : ‖p t‖ = s := by rw [← hfp t, hft]
          exact h0.ge
        · exact (hle w (lt_of_le_of_ne hw.1 (Ne.symm hwt))).le
      rw [hwu] at key
      exact key
    · exact pathLength_subpath_le D p t 1 (show t ≤ 1 from t.2.2)

/-- Lower bound of display (8): the infimum over the circle `∂B_s` of the punctured distances to `x` is at most the root
distance `D(0, x; O)`. No metric hypothesis is needed. -/
theorem iInf_sphere_internalMetric_le (D : ℂ → ℂ → ℝ) {O : Set ℂ} {s : ℝ} (hs : 0 < s) {x : ℂ} (hx : s < ‖x‖) :
    (⨅ y ∈ sphere (0 : ℂ) s, internalMetric D (O \ {0}) y x) ≤ internalMetric D O 0 x := by
  unfold internalMetric
  refine le_iInf₂ fun P hP => ?_
  obtain ⟨y, hy, q, hq, hqle⟩ := exists_sphere_subpath D hs hx P hP
  have hqO : ∀ u, q u ∈ O \ {0} := fun u => ⟨(hq u).1, fun h0 => by
    have h1 := (hq u).2
    rw [Set.mem_singleton_iff.mp h0, norm_zero] at h1
    linarith⟩
  exact le_trans (iInf₂_le y (mem_sphere_zero_iff_norm.mpr hy)) (le_trans (iInf₂_le q hqO) hqle)

/-- Upper bound of display (8), pointwise in the circle point `y`: `D(0, x; O) ≤ D(0, y; O) + D(y, x; O \ {0})`. Uses the
triangle inequality for the internal metric and `D(·; O) ≤ D(·; O \ {0})`. -/
theorem internalMetric_root_le_add (D : ℂ → ℂ → ℝ) (hD : IsEuclideanLengthMetric D) (O : Set ℂ) (y x : ℂ) :
    internalMetric D O 0 x ≤ internalMetric D O 0 y + internalMetric D (O \ {0}) y x :=
  le_trans (IsEuclideanLengthMetric.internalMetric_triangle hD O 0 y x)
    (add_le_add_right (internalMetric_anti D sdiff_subset y x) _)

/-- Display (8), upper bound, in the form used by the limit: `D(0, x; O) ≤ sup_{y ∈ ∂B_s} D(0, y; O) +
inf_{y ∈ ∂B_s} D(y, x; O \ {0})`. The limit `s → 0` of the supremum is a separate continuity input. -/
theorem internalMetric_root_le_sup_add_iInf (D : ℂ → ℂ → ℝ) (hD : IsEuclideanLengthMetric D) (O : Set ℂ)
    (s : ℝ) (x : ℂ) :
    internalMetric D O 0 x ≤
      (⨆ y ∈ sphere (0 : ℂ) s, internalMetric D O 0 y) + ⨅ y ∈ sphere (0 : ℂ) s, internalMetric D (O \ {0}) y x := by
  have key : ∀ y ∈ sphere (0 : ℂ) s, internalMetric D O 0 x ≤
      (⨆ z ∈ sphere (0 : ℂ) s, internalMetric D O 0 z) + internalMetric D (O \ {0}) y x := fun y hy =>
    le_trans (internalMetric_root_le_add D hD O y x)
      (add_le_add_left (le_iSup₂ (f := fun z (_ : z ∈ sphere (0 : ℂ) s) => internalMetric D O 0 z) y hy) _)
  calc internalMetric D O 0 x
      ≤ ⨅ y ∈ sphere (0 : ℂ) s, ((⨆ z ∈ sphere (0 : ℂ) s, internalMetric D O 0 z) +
          internalMetric D (O \ {0}) y x) := le_iInf₂ key
    _ = (⨆ y ∈ sphere (0 : ℂ) s, internalMetric D O 0 y) + ⨅ y ∈ sphere (0 : ℂ) s,
          internalMetric D (O \ {0}) y x := by
      simp only [ENNReal.add_iInf]

end HarmonicBalls.S11m

