import HarmonicBalls.Steps.Sec11.PuncturedPathLength
import HarmonicBalls.Steps.Sec11.InternalMetricContinuity

/-! # A path crossing a puncture

The first and last visits to a point are separated from nonzero endpoints.
Continuity allows the visits to be bracketed by nonzero points arbitrarily
near the puncture.
-/

namespace HarmonicBalls

open Set Metric Filter Topology
open scoped ENNReal NNReal

/-- A path with nonzero endpoints which visits the origin can be cut before
its first visit and after its last visit, with both cut points arbitrarily
close to the origin and the retained pieces avoiding the origin. -/
theorem Path.exists_bracketing_origin {x y : ℂ} (p : Path x y)
    (hx : x ≠ 0) (hy : y ≠ 0) (hhit : ∃ u, p u = 0)
    {r : ℝ} (hr : 0 < r) :
    ∃ s t : unitInterval, s ≤ t ∧ ‖p s‖ < r ∧ ‖p t‖ < r ∧
      (∀ u : unitInterval, u ≤ s → p u ≠ 0) ∧
      (∀ u : unitInterval, t ≤ u → p u ≠ 0) := by
  let S : Set ℝ := Icc 0 1 ∩ p.extend ⁻¹' {0}
  have hcompact : IsCompact S := isCompact_Icc.of_isClosed_subset
    (isClosed_Icc.inter (isClosed_singleton.preimage p.continuous_extend)) inter_subset_left
  have hne : S.Nonempty := by
    obtain ⟨u, hu⟩ := hhit
    refine ⟨u, u.property, ?_⟩
    simpa only [mem_preimage, mem_singleton_iff, Path.extend_apply _ u.property] using hu
  obtain ⟨a, ha⟩ := hcompact.exists_isLeast hne
  obtain ⟨b, hb⟩ := hcompact.exists_isGreatest hne
  have ha0 : p.extend a = 0 := ha.1.2
  have hb0 : p.extend b = 0 := hb.1.2
  have ha_pos : 0 < a := by
    have h : a ≠ 0 := by
      intro h
      apply hx
      simpa only [h, p.extend_zero] using ha0
    exact lt_of_le_of_ne ha.1.1.1 (Ne.symm h)
  have hb_lt : b < 1 := by
    have h : b ≠ 1 := by
      intro h
      apply hy
      simpa only [h, p.extend_one] using hb0
    exact lt_of_le_of_ne hb.1.1.2 h
  have hab : a ≤ b := ha.2 hb.1
  have hcont : Continuous (fun u : ℝ => ‖p.extend u‖) := continuous_norm.comp p.continuous_extend
  obtain ⟨δa, hδa, hclosea⟩ := Metric.continuousAt_iff.mp hcont.continuousAt r hr
  obtain ⟨δb, hδb, hcloseb⟩ := Metric.continuousAt_iff.mp hcont.continuousAt r hr
  let da : ℝ := min (a / 2) (δa / 2)
  let db : ℝ := min ((1 - b) / 2) (δb / 2)
  have hda : 0 < da := lt_min (by linarith) (by linarith)
  have hdb : 0 < db := lt_min (by linarith) (by linarith)
  have hda_a : da ≤ a / 2 := min_le_left _ _
  have hda_δ : da ≤ δa / 2 := min_le_right _ _
  have hdb_b : db ≤ (1 - b) / 2 := min_le_left _ _
  have hdb_δ : db ≤ δb / 2 := min_le_right _ _
  let s : unitInterval := ⟨a - da, by constructor <;> linarith [ha.1.1.2]⟩
  let t : unitInterval := ⟨b + db, by constructor <;> linarith [hb.1.1.1]⟩
  have hsa : (s : ℝ) < a := by dsimp [s]; linarith
  have hbt : b < (t : ℝ) := by dsimp [t]; linarith
  refine ⟨s, t, ?_, ?_, ?_, ?_, ?_⟩
  · change (s : ℝ) ≤ t
    linarith
  · have hd : dist (s : ℝ) a < δa := by
      rw [Real.dist_eq, abs_of_neg (by linarith : (s : ℝ) - a < 0)]
      dsimp [s]
      linarith
    have hc := hclosea hd
    simpa only [ha0, norm_zero, Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _),
      Path.extend_apply _ s.property] using hc
  · have hd : dist (t : ℝ) b < δb := by
      rw [Real.dist_eq, abs_of_pos (by linarith : 0 < (t : ℝ) - b)]
      dsimp [t]
      linarith
    have hc := hcloseb hd
    simpa only [hb0, norm_zero, Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _),
      Path.extend_apply _ t.property] using hc
  · intro u hu hu0
    have huS : (u : ℝ) ∈ S := by
      refine ⟨u.property, ?_⟩
      simpa only [mem_preimage, mem_singleton_iff, Path.extend_apply _ u.property] using hu0
    have h := ha.2 huS
    have hu' : (u : ℝ) ≤ s := hu
    linarith
  · intro u hu hu0
    have huS : (u : ℝ) ∈ S := by
      refine ⟨u.property, ?_⟩
      simpa only [mem_preimage, mem_singleton_iff, Path.extend_apply _ u.property] using hu0
    have h := hb.2 huS
    have hu' : (t : ℝ) ≤ u := hu
    linarith

/-- Small punctured neighborhoods with vanishing internal diameter allow
all paths to bypass the origin without changing internal distance. -/
theorem IsEuclideanLengthMetric.internalMetric_sdiff_zero_eq_of_small_detours
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {V : Set ℂ}
    {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0)
    (hcheap : ∀ ε : ℝ≥0, 0 < ε → ∃ r : ℝ, 0 < r ∧
      ∀ a b : ℂ, a ∈ V → b ∈ V → a ≠ 0 → b ≠ 0 → ‖a‖ < r → ‖b‖ < r →
        internalMetric D (V \ {0}) a b < ε) :
    internalMetric D (V \ {0}) x y = internalMetric D V x y := by
  apply le_antisymm
  · change internalMetric D (V \ {0}) x y ≤
      ⨅ (p : Path x y) (_ : ∀ u, p u ∈ V), pathLength D p
    refine le_iInf fun p => le_iInf fun hp => ?_
    by_cases hhit : ∃ u, p u = 0
    · apply ENNReal.le_of_forall_pos_le_add
      intro ε hε _
      obtain ⟨r, hr, hbound⟩ := hcheap ε hε
      obtain ⟨s, t, hst, hs, ht, hfirst, hlast⟩ := Path.exists_bracketing_origin p hx hy hhit hr
      have hs0 : p s ≠ 0 := hfirst s le_rfl
      have ht0 : p t ≠ 0 := hlast t le_rfl
      have hshort := hbound (p s) (p t) (hp s) (hp t) hs0 ht0 hs ht
      obtain ⟨q, hq, hlen⟩ : ∃ q : Path (p s) (p t),
          (∀ u, q u ∈ V \ {0}) ∧ pathLength D q < ε := by
        unfold internalMetric at hshort
        simpa only [iInf_lt_iff, exists_prop] using hshort
      have hfirst' : ∀ u, (p.subpath 0 s) u ∈ V \ {0} := by
        intro u
        have hm : (p.subpath 0 s) u ∈ p '' Icc (0 : unitInterval) s := by
          rw [← p.range_subpath_of_le 0 s (show (0 : unitInterval) ≤ s from s.property.1)]
          exact mem_range_self u
        obtain ⟨v, hv, heq⟩ := hm
        rw [← heq]
        exact ⟨hp v, by simpa only [mem_singleton_iff] using hfirst v hv.2⟩
      have hlast' : ∀ u, (p.subpath t 1) u ∈ V \ {0} := by
        intro u
        have hm : (p.subpath t 1) u ∈ p '' Icc t (1 : unitInterval) := by
          rw [← p.range_subpath_of_le t 1 (show t ≤ (1 : unitInterval) from t.property.2)]
          exact mem_range_self u
        obtain ⟨v, hv, heq⟩ := hm
        rw [← heq]
        exact ⟨hp v, by simpa only [mem_singleton_iff] using hlast v hv.1⟩
      exact (hD.internalMetric_le_of_middle_detour p s t hst q hfirst' hlast' hq).trans
        (add_le_add le_rfl hlen.le)
    · have hp' : ∀ u, p u ∈ V \ {0} := by
        intro u
        refine ⟨hp u, ?_⟩
        simp only [mem_singleton_iff]
        intro hu
        exact hhit ⟨u, hu⟩
      exact iInf_le_of_le p (iInf_le _ hp')
  · exact internalMetric_anti D sdiff_subset x y

/-- Conversely, point removal on a neighborhood of the origin forces the
punctured internal distances between pairs approaching the origin to vanish
uniformly. -/
theorem IsEuclideanLengthMetric.small_detours_of_internalMetric_sdiff_zero_eq
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {V : Set ℂ}
    (hV : IsOpen V) (hzero : (0 : ℂ) ∈ V)
    (hremove : ∀ a ∈ V \ {0}, ∀ b ∈ V \ {0},
      internalMetric D (V \ {0}) a b = internalMetric D V a b) :
    ∀ ε : ℝ≥0, 0 < ε → ∃ r : ℝ, 0 < r ∧
      ∀ a b : ℂ, a ∈ V → b ∈ V → a ≠ 0 → b ≠ 0 → ‖a‖ < r → ‖b‖ < r →
        internalMetric D (V \ {0}) a b < ε := by
  have hnonneg (x y : ℂ) : 0 ≤ D x y := by
    have ht := hD.triangle x y x
    rw [hD.self_eq_zero, hD.symm y x] at ht
    linarith
  intro ε hε
  have hzero' : internalMetric D V 0 0 = 0 :=
    hD.internalMetric_self_of_mem_open hnonneg hV hzero
  have hcont := (hD.continuousAt_internalMetric_pair hnonneg hV hzero hzero).tendsto
  rw [hzero'] at hcont
  have hε' : (0 : ℝ≥0∞) < ε := by exact_mod_cast hε
  have hevent : ∀ᶠ p : ℂ × ℂ in 𝓝 ((0 : ℂ), (0 : ℂ)),
      internalMetric D V p.1 p.2 < ε := hcont.eventually_lt_const hε'
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨r, hr, ?_⟩
  intro a b ha hb ha0 hb0 har hbr
  have hd : dist (a, b) ((0 : ℂ), (0 : ℂ)) < r := by
    simpa only [Prod.dist_eq, dist_zero_right, max_lt_iff] using And.intro har hbr
  have hlt := hrsub hd
  rw [hremove a ⟨ha, by simpa only [mem_singleton_iff] using ha0⟩
    b ⟨hb, by simpa only [mem_singleton_iff] using hb0⟩]
  exact hlt


end HarmonicBalls
