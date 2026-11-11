import HarmonicBalls.Proofs.Sec5.BoundaryJumpModel

/-! # An open connected model with a macroscopic boundary jump

This deterministic model is not an obstacle cluster. It tests which geometric
properties alone can exclude a jump at the boundary of the unit disc.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped Topology

private def modelOpenBefore : Set ℂ := ball 0 1 ∩ {z : ℂ | 0 < z.re}

private def modelOpenFamily (t : ℝ) : Set ℂ :=
  ball 0 1 ∩ {z : ℂ | 0 < z.re ∨ max 0 (2 - t) < ‖z‖}

private theorem modelOpenBefore_connected : IsConnected modelOpenBefore := by
  apply ((convex_ball (0 : ℂ) 1).inter (convex_halfSpace_re_gt 0)).isConnected
  refine ⟨(1 / 2 : ℂ), ?_⟩
  norm_num [modelOpenBefore, mem_ball_zero_iff]

private theorem modelOpenFamily_open (t : ℝ) : IsOpen (modelOpenFamily t) := by
  apply isOpen_ball.inter
  exact (isOpen_lt continuous_const Complex.continuous_re).union
    (isOpen_lt continuous_const continuous_norm)

private theorem modelOpenFamily_mono : Monotone modelOpenFamily := by
  intro s t hst x hx
  refine ⟨hx.1, ?_⟩
  rcases hx.2 with hx | hx
  · exact Or.inl hx
  · right
    exact lt_of_le_of_lt (max_le_max le_rfl (sub_le_sub_left hst 2)) hx

private theorem modelOpenFamily_connected (t : ℝ) : IsConnected (modelOpenFamily t) := by
  have hbefore : modelOpenBefore ⊆ modelOpenFamily t := by
    intro x hx
    exact ⟨hx.1, Or.inl hx.2⟩
  refine ⟨modelOpenBefore_connected.nonempty.mono hbefore, ?_⟩
  apply isPreconnected_of_forall (1 / 2 : ℂ)
  intro x hx
  rcases hx.2 with hxbase | hxann
  · refine ⟨modelOpenBefore, hbefore, ?_, ⟨hx.1, hxbase⟩,
      modelOpenBefore_connected.isPreconnected⟩
    norm_num [modelOpenBefore, mem_ball_zero_iff]
  · have hnorm : 0 < ‖x‖ := lt_of_le_of_lt (le_max_left 0 (2 - t)) hxann
    have hxnorm : ‖x‖ < 1 := by simpa [mem_ball_zero_iff] using hx.1
    let y : ℂ := (‖x‖ : ℂ)
    have hybase : y ∈ modelOpenBefore := by
      simp only [modelOpenBefore, mem_inter_iff, mem_ofPred_eq, mem_ball_zero_iff,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hnorm, Complex.ofReal_re, y]
      exact ⟨hxnorm, hnorm⟩
    have hysphere : y ∈ sphere (0 : ℂ) ‖x‖ := by
      simp [y]
    have hxsphere : x ∈ sphere (0 : ℂ) ‖x‖ := by simp
    have hsphere : sphere (0 : ℂ) ‖x‖ ⊆ modelOpenFamily t := by
      intro w hw
      have hnormw : ‖w‖ = ‖x‖ := by simpa [mem_sphere, dist_zero_right] using hw
      refine ⟨?_, Or.inr ?_⟩
      · simpa [mem_ball_zero_iff, hnormw] using hxnorm
      · rwa [hnormw]
    refine ⟨modelOpenBefore ∪ sphere 0 ‖x‖, union_subset hbefore hsphere,
      Or.inl ?_, Or.inr hxsphere, ?_⟩
    · norm_num [modelOpenBefore, mem_ball_zero_iff]
    · exact (modelOpenBefore_connected.union ⟨y, hybase, hysphere⟩
        (isConnected_sphere (by simp) 0 (norm_nonneg x))).isPreconnected

private theorem modelOpenFamily_one : modelOpenFamily 1 = modelOpenBefore := by
  ext x
  simp only [modelOpenFamily, modelOpenBefore, mem_inter_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨hx, h | h⟩
    · exact ⟨hx, h⟩
    · have hxnorm : ‖x‖ < 1 := by simpa [mem_ball_zero_iff] using hx
      have : (1 : ℝ) < ‖x‖ := by norm_num at h ⊢; exact h
      linarith
  · rintro ⟨hx, h⟩
    exact ⟨hx, Or.inl h⟩

private theorem modelOpenFamily_boundary_mem {t : ℝ} (ht : 1 < t) :
    sphere (0 : ℂ) 1 ⊆ closure (modelOpenFamily t) := by
  intro x hx
  have hxnorm : ‖x‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hx
  let a := max 0 (2 - t)
  have ha0 : 0 ≤ a := le_max_left _ _
  have ha1 : a < 1 := max_lt (by norm_num) (by linarith)
  let f : ℝ → ℂ := fun r => (r : ℂ) * x
  have hf : Continuous f := Complex.continuous_ofReal.mul continuous_const
  have hsub : f '' Ioo a 1 ⊆ modelOpenFamily t := by
    rintro _ ⟨r, hr, rfl⟩
    have hr0 : 0 < r := lt_of_le_of_lt ha0 hr.1
    refine ⟨?_, Or.inr ?_⟩
    · simpa [mem_ball_zero_iff, f, norm_mul, hxnorm, abs_of_pos hr0] using hr.2
    · simpa [f, a, norm_mul, hxnorm, abs_of_pos hr0] using hr.1
  have h1 : (1 : ℝ) ∈ closure (Ioo a 1) := by
    rw [closure_Ioo ha1.ne]
    exact right_mem_Icc.mpr ha1.le
  have h := (image_closure_subset_closure_image hf) (mem_image_of_mem f h1)
  have h' : f 1 ∈ closure (modelOpenFamily t) := closure_mono hsub h
  simpa [f] using h'

private theorem modelOpenFamily_increment_iInter :
    (⋂ n : ℕ, (modelOpenFamily (1 + (2 : ℝ)⁻¹ ^ n) \ modelOpenFamily 1)) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hx0 := mem_iInter.mp hx 0
  have hxball := hx0.1.1
  have hxnorm : ‖x‖ < 1 := by simpa [mem_ball_zero_iff] using hxball
  have hxre : ¬ 0 < x.re := fun h => hx0.2 (by rw [modelOpenFamily_one]; exact ⟨hxball, h⟩)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (sub_pos.mpr hxnorm)
    (by norm_num : (2 : ℝ)⁻¹ < 1)
  have hxann := (mem_iInter.mp hx n).1.2.resolve_left hxre
  have hlow : 2 - (1 + (2 : ℝ)⁻¹ ^ n) < ‖x‖ :=
    lt_of_le_of_lt (le_max_right 0 _) hxann
  linarith

private theorem modelOpenFamily_increment_tendsto :
    Tendsto (fun n : ℕ => volume (modelOpenFamily (1 + (2 : ℝ)⁻¹ ^ n) \
      modelOpenFamily 1)) atTop (𝓝 0) := by
  let E : ℕ → Set ℂ := fun n => modelOpenFamily (1 + (2 : ℝ)⁻¹ ^ n) \ modelOpenFamily 1
  have hmeas : ∀ n, NullMeasurableSet (E n) volume := by
    intro n
    have ha : MeasurableSet (modelOpenFamily (1 + (2 : ℝ)⁻¹ ^ n)) :=
      (modelOpenFamily_open _).measurableSet
    have hb : MeasurableSet (modelOpenFamily 1) := (modelOpenFamily_open _).measurableSet
    exact (ha.diff hb).nullMeasurableSet
  have hanti : Antitone E := by
    intro n m hnm
    apply sdiff_subset_sdiff_left
    apply modelOpenFamily_mono
    have hp := pow_le_pow_of_le_one (a := (2 : ℝ)⁻¹) (by norm_num) (by norm_num) hnm
    linarith
  have hfinite : ∃ n, volume (E n) ≠ ⊤ := by
    refine ⟨0, ne_top_of_le_ne_top
      (measure_ball_lt_top (μ := (volume : Measure ℂ)) (x := 0) (r := 1)).ne ?_⟩
    exact measure_mono (sdiff_subset.trans inter_subset_left)
  have h := tendsto_measure_iInter_atTop hmeas hanti hfinite
  have hzero : (⋂ n, E n) = ∅ := modelOpenFamily_increment_iInter
  rw [hzero, measure_empty] at h
  simpa only [E, Function.comp_def] using h

private theorem modelOpenFamily_future_interior :
    rightClosedEnvelope modelOpenFamily 1 ∩ ball 0 1 ⊆ closure (modelOpenFamily 1) := by
  intro x hx
  by_contra hxnot
  rw [modelOpenFamily_one] at hxnot
  have hxnorm : ‖x‖ < 1 := by simpa [mem_ball_zero_iff] using hx.2
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (sub_pos.mpr hxnorm)
    (by norm_num : (2 : ℝ)⁻¹ < 1)
  let a : ℝ := 2 - (1 + (2 : ℝ)⁻¹ ^ n)
  have hclosed : IsClosed (closure modelOpenBefore ∪ {z : ℂ | a ≤ ‖z‖}) :=
    isClosed_closure.union (isClosed_le continuous_const continuous_norm)
  have hsub : modelOpenFamily (1 + (2 : ℝ)⁻¹ ^ n) ⊆
      closure modelOpenBefore ∪ {z : ℂ | a ≤ ‖z‖} := by
    intro y hy
    rcases hy.2 with hpos | hnorm
    · exact Or.inl (subset_closure ⟨hy.1, hpos⟩)
    · exact Or.inr (le_of_lt (lt_of_le_of_lt (le_max_right 0 a) hnorm))
  have h := (closure_minimal hsub hclosed) (mem_iInter.mp hx.1 n)
  have hxlow := h.resolve_left hxnot
  change a ≤ ‖x‖ at hxlow
  dsimp [a] at hxlow
  linarith

private theorem modelOpenFamily_jump_subset_sphere :
    rightClosedEnvelope modelOpenFamily 1 \ closure (modelOpenFamily 1) ⊆ sphere 0 1 := by
  intro x hx
  have hbounded : ∀ s, closure (modelOpenFamily s) ⊆ closedBall 0 1 := fun _ =>
    closure_minimal (inter_subset_left.trans ball_subset_closedBall) isClosed_closedBall
  have hxle := hbounded _ (mem_iInter.mp hx.1 0)
  have hxnot : x ∉ ball 0 1 := fun h => hx.2 (modelOpenFamily_future_interior ⟨hx.1, h⟩)
  rw [mem_closedBall, dist_zero_right] at hxle
  rw [mem_ball, dist_zero_right, not_lt] at hxnot
  rw [mem_sphere, dist_zero_right]
  exact le_antisymm hxle hxnot

private theorem modelOpenFamily_cap_jump :
    sphere (0 : ℂ) 1 ∩ {z : ℂ | z.re < 0} ⊆
      rightClosedEnvelope modelOpenFamily 1 \ closure (modelOpenFamily 1) := by
  intro x hx
  refine ⟨?_, ?_⟩
  · apply mem_iInter.mpr
    intro n
    exact modelOpenFamily_boundary_mem (lt_add_of_pos_right 1 (pow_pos (by norm_num) n)) hx.1
  · rw [modelOpenFamily_one]
    have hsub : closure modelOpenBefore ⊆ {z : ℂ | 0 ≤ z.re} :=
      closure_minimal (by intro y hy; change 0 ≤ y.re; exact hy.2.le)
        (isClosed_le continuous_const Complex.continuous_re)
    intro h
    have hre : 0 ≤ x.re := hsub h
    exact (not_lt_of_ge hre) hx.2

/-- Open connected sets can have vanishing area increments and no new interior
right-limit points while their right envelope gains an entire semicircular arc. -/
theorem exists_open_connected_arc_boundary_jump :
    ∃ F : ℝ → Set ℂ,
      (∀ t, IsOpen (F t) ∧ IsConnected (F t) ∧ F t ⊆ ball (0 : ℂ) 1) ∧
      Monotone F ∧
      Tendsto (fun n : ℕ => volume (F (1 + (2 : ℝ)⁻¹ ^ n) \ F 1)) atTop (𝓝 0) ∧
      rightClosedEnvelope F 1 ∩ ball 0 1 ⊆ closure (F 1) ∧
      rightClosedEnvelope F 1 \ closure (F 1) ⊆ sphere 0 1 ∧
      sphere (0 : ℂ) 1 ∩ {z : ℂ | z.re < 0} ⊆
        rightClosedEnvelope F 1 \ closure (F 1) := by
  refine ⟨modelOpenFamily, ?_, modelOpenFamily_mono, modelOpenFamily_increment_tendsto,
    modelOpenFamily_future_interior, modelOpenFamily_jump_subset_sphere,
    modelOpenFamily_cap_jump⟩
  · intro t
    exact ⟨modelOpenFamily_open t, modelOpenFamily_connected t, inter_subset_left⟩

end HarmonicBalls
