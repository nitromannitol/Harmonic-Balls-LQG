import HarmonicBalls.Proofs.Sec5.BoundaryJumpModel

/-! # An open connected-set model for boundary jumps

This deterministic model has the geometric regularity of open connected
clusters, but does not satisfy or represent the LQG obstacle problem.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped Topology ENNReal

private def base : Set ℂ := ball 0 1 ∩ {z : ℂ | 0 < z.re}
private noncomputable def width (t : ℝ) : ℝ := max 0 (min (t - 1) (1 / 2))
private noncomputable def collar (t : ℝ) : Set ℂ := ball 0 1 ∩ {z : ℂ | 1 - width t < ‖z‖}
private noncomputable def family (t : ℝ) : Set ℂ := base ∪ collar t

private theorem width_nonneg (t : ℝ) : 0 ≤ width t := le_max_left _ _
private theorem width_le_half (t : ℝ) : width t ≤ 1 / 2 := by
  unfold width
  exact max_le (by norm_num) (min_le_right _ _)
private theorem width_mono : Monotone width := by
  intro s t hst
  unfold width
  exact max_le_max le_rfl (min_le_min (sub_le_sub_right hst 1) le_rfl)
private theorem width_le_sub {t : ℝ} (ht : 1 ≤ t) : width t ≤ t - 1 := by
  unfold width
  exact max_le (sub_nonneg.mpr ht) (min_le_left _ _)
private theorem width_pos {t : ℝ} (ht : 1 < t) : 0 < width t := by
  unfold width
  exact lt_of_lt_of_le (lt_min (sub_pos.mpr ht) (by norm_num)) (le_max_right _ _)
private theorem width_one : width 1 = 0 := by simp [width]

private theorem base_open : IsOpen base := isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
private theorem base_connected : IsConnected base := by
  apply ((convex_ball (0 : ℂ) 1).inter (convex_halfSpace_re_gt 0)).isConnected
  refine ⟨(1 / 2 : ℂ), ?_⟩
  norm_num [base, mem_ball, dist_zero_right, Complex.norm_def]

private theorem family_open (t : ℝ) : IsOpen (family t) :=
  base_open.union (isOpen_ball.inter (isOpen_lt continuous_const continuous_norm))

private theorem family_connected (t : ℝ) : IsConnected (family t) := by
  have hb : base ⊆ family t := subset_union_left
  have hpoint : (1 / 2 : ℂ) ∈ base := by
    norm_num [base, mem_ball, dist_zero_right, Complex.norm_def]
  refine ⟨⟨1 / 2, hb hpoint⟩, isPreconnected_of_forall (1 / 2 : ℂ) ?_⟩
  intro y hy
  rcases hy with hy | hy
  · exact ⟨base, hb, hpoint, hy, base_connected.isPreconnected⟩
  · have hyball := hy.1
    have hybound : 1 - width t < ‖y‖ := hy.2
    have hnorm : 0 < ‖y‖ := by
      have hw := width_le_half t
      linarith [norm_nonneg y]
    have hnorm1 : ‖y‖ < 1 := by simpa [mem_ball, dist_zero_right] using hyball
    let S := sphere (0 : ℂ) ‖y‖
    have hys : y ∈ S := by simp [S]
    have hsub : S ⊆ family t := by
      intro v hv
      have hvnorm : ‖v‖ = ‖y‖ := by simpa [S, mem_sphere, dist_zero_right] using hv
      right
      constructor
      · simpa [mem_ball, dist_zero_right, hvnorm] using hnorm1
      · simpa [hvnorm] using hybound
    have hinter : (base ∩ S).Nonempty := by
      refine ⟨(‖y‖ : ℂ), ?_, ?_⟩
      · constructor
        · simpa [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hnorm] using hnorm1
        · simpa using hnorm
      · simp [S]
    refine ⟨base ∪ S, union_subset hb hsub, mem_union_left _ hpoint,
      mem_union_right _ hys, ?_⟩
    exact (base_connected.union hinter (isConnected_sphere (by simp) 0 (norm_nonneg y))).isPreconnected

private theorem family_mono : Monotone family := by
  intro s t hst z hz
  rcases hz with hz | hz
  · exact Or.inl hz
  · exact Or.inr ⟨hz.1, lt_of_le_of_lt (sub_le_sub_left (width_mono hst) 1) hz.2⟩

private theorem family_one : family 1 = base := by
  unfold family collar
  rw [width_one]
  apply union_eq_left.mpr
  intro z hz
  have hnorm : ‖z‖ < 1 := by simpa [mem_ball, dist_zero_right] using hz.1
  have hlt : 1 - 0 < ‖z‖ := hz.2
  linarith

private theorem closure_family_subset (t : ℝ) :
    closure (family t) ⊆ closure base ∪ {z : ℂ | 1 - width t ≤ ‖z‖} := by
  apply closure_minimal _ (isClosed_closure.union (isClosed_le continuous_const continuous_norm))
  intro z hz
  rcases hz with hz | hz
  · exact Or.inl (subset_closure hz)
  · exact Or.inr (le_of_lt (show 1 - width t < ‖z‖ from hz.2))

private theorem envelope_sdiff_subset_sphere :
    rightClosedEnvelope family 1 \ closure (family 1) ⊆ sphere (0 : ℂ) 1 := by
  intro z hz
  rw [family_one] at hz
  have hclosed : z ∈ closedBall (0 : ℂ) 1 := by
    apply closure_minimal (s := family (1 + (2 : ℝ)⁻¹ ^ 0)) ?_ isClosed_closedBall
      (mem_iInter.mp hz.1 0)
    intro x hx
    rcases hx with hx | hx <;> exact ball_subset_closedBall hx.1
  have hbound : 1 ≤ ‖z‖ := by
    by_contra h
    have hδ : 0 < 1 - ‖z‖ := sub_pos.mpr (lt_of_not_ge h)
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (2 : ℝ)⁻¹ < 1)
    have hmem := closure_family_subset (1 + (2 : ℝ)⁻¹ ^ n) (mem_iInter.mp hz.1 n)
    rcases hmem with hc | hc
    · exact hz.2 hc
    · change 1 - width (1 + (2 : ℝ)⁻¹ ^ n) ≤ ‖z‖ at hc
      have hw := width_le_sub (t := 1 + (2 : ℝ)⁻¹ ^ n) (le_add_of_nonneg_right (by positivity))
      linarith
  apply mem_sphere.mpr
  have hupper : ‖z‖ ≤ 1 := by simpa [mem_closedBall, dist_zero_right] using hclosed
  simpa [dist_zero_right] using le_antisymm hupper hbound

private theorem neg_one_mem_closure_family {t : ℝ} (ht : 1 < t) :
    (-1 : ℂ) ∈ closure (family t) := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let q := min (width t) ε / 2
  have hq : 0 < q := by
    dsimp [q]
    exact div_pos (lt_min (width_pos ht) hε) (by norm_num)
  have hqw : q < width t := by
    have h := min_le_left (width t) ε
    dsimp [q]
    linarith [width_pos ht]
  have hqε : q < ε := by
    have h := min_le_right (width t) ε
    dsimp [q]
    linarith
  have hq1 : q < 1 := by linarith [hqw, width_le_half t]
  let z : ℂ := ((q - 1 : ℝ) : ℂ)
  have hznorm : ‖z‖ = 1 - q := by
    dsimp [z]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith : q - 1 < 0)]
    ring
  have hdist : dist (-1 : ℂ) z = q := by
    rw [dist_comm, dist_eq_norm]
    have heq : z - (-1 : ℂ) = (q : ℂ) := by dsimp [z]; push_cast; ring
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq]
  refine ⟨z, ?_, hdist.trans_lt hqε⟩
  right
  constructor
  · rw [mem_ball, dist_zero_right, hznorm]
    linarith
  · change 1 - width t < ‖z‖
    rw [hznorm]
    linarith

private theorem neg_one_not_mem_closure_base : (-1 : ℂ) ∉ closure base := by
  have hsub : closure base ⊆ {z : ℂ | 0 ≤ z.re} :=
    closure_minimal (by
      intro z hz
      change 0 ≤ z.re
      exact le_of_lt (show 0 < z.re from hz.2))
      (isClosed_le continuous_const Complex.continuous_re)
  intro h
  have hh := hsub h
  norm_num at hh

private theorem future_increment_iInter_eq_empty :
    (⋂ n : ℕ, (family (1 + (2 : ℝ)⁻¹ ^ n) \ family 1)) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hbase : z ∉ base := by
    have h := (mem_iInter.mp hz 0).2
    simpa [family_one] using h
  have hc (n : ℕ) : z ∈ collar (1 + (2 : ℝ)⁻¹ ^ n) := by
    rcases (mem_iInter.mp hz n).1 with h | h
    · exact (hbase h).elim
    · exact h
  have hzball : ‖z‖ < 1 := by
    simpa [mem_ball, dist_zero_right] using (hc 0).1
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (sub_pos.mpr hzball)
    (by norm_num : (2 : ℝ)⁻¹ < 1)
  have hzlower : 1 - width (1 + (2 : ℝ)⁻¹ ^ n) < ‖z‖ := (hc n).2
  have hw := width_le_sub (t := 1 + (2 : ℝ)⁻¹ ^ n) (le_add_of_nonneg_right (by positivity))
  linarith

private theorem tendsto_future_increment_zero :
    Tendsto (fun n : ℕ => volume (family (1 + (2 : ℝ)⁻¹ ^ n) \ family 1)) atTop (𝓝 0) := by
  have ha : Antitone (fun n : ℕ => family (1 + (2 : ℝ)⁻¹ ^ n) \ family 1) := by
    intro i j hij
    apply sdiff_subset_sdiff_left
    apply family_mono
    simpa only [add_comm] using add_le_add_left (pow_le_pow_of_le_one (by norm_num : 0 ≤ (2 : ℝ)⁻¹)
      (by norm_num : (2 : ℝ)⁻¹ ≤ 1) hij) 1
  have hf : volume (family (1 + (2 : ℝ)⁻¹ ^ 0) \ family 1) ≠ ∞ := by
    apply ne_top_of_le_ne_top (ne_of_lt (measure_ball_lt_top (μ := volume) (x := (0 : ℂ)) (r := (1 : ℝ))))
    apply measure_mono
    intro z hz
    rcases hz.1 with h | h <;> exact h.1
  have hlim := tendsto_measure_iInter_atTop (μ := volume)
    (s := fun n : ℕ => family (1 + (2 : ℝ)⁻¹ ^ n) \ family 1)
    (fun n => ((family_open _).measurableSet.diff (family_open _).measurableSet).nullMeasurableSet)
    ha ⟨0, hf⟩
  rw [future_increment_iInter_eq_empty, measure_empty] at hlim
  exact hlim

/-- An increasing family of open connected subsets of the unit disc can have a
nonempty, boundary-only right-limit jump of zero planar area. The family is a
geometric model and is not asserted to solve the LQG obstacle problem. -/
theorem exists_open_connected_zero_area_boundary_jump :
    ∃ F : ℝ → Set ℂ,
      (∀ t, IsOpen (F t) ∧ IsConnected (F t) ∧ F t ⊆ ball (0 : ℂ) 1) ∧
      Monotone F ∧
      Tendsto (fun n : ℕ => volume (F (1 + (2 : ℝ)⁻¹ ^ n) \ F 1)) atTop (𝓝 0) ∧
      (rightClosedEnvelope F 1 \ closure (F 1) ⊆ sphere (0 : ℂ) 1) ∧
      volume (rightClosedEnvelope F 1 \ closure (F 1)) = 0 ∧
      (rightClosedEnvelope F 1 \ closure (F 1)).Nonempty := by
  refine ⟨family, ?_, family_mono, tendsto_future_increment_zero,
    envelope_sdiff_subset_sphere, ?_, ?_⟩
  · intro t
    refine ⟨family_open t, family_connected t, ?_⟩
    intro z hz
    rcases hz with hz | hz <;> exact hz.1
  · exact measure_mono_null envelope_sdiff_subset_sphere (Measure.addHaar_sphere volume 0 1)
  · refine ⟨-1, ?_, ?_⟩
    · apply mem_iInter.mpr
      intro n
      exact neg_one_mem_closure_family (lt_add_of_pos_right _ (by positivity))
    · simpa [family_one] using neg_one_not_mem_closure_base

end HarmonicBalls
