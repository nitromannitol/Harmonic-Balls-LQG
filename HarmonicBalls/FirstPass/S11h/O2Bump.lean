import HarmonicBalls.FirstPass.S11h.Faithful
import HarmonicBalls.FirstPass.S11c.ShiftBump
import HarmonicBalls.FirstPass.S11d.ShiftBound

/-!
# First pass, Section 11: the corrected set `O₂` and the final bump of Lemma 11.17 (fp-S11h, owner n2)

Deterministic geometry of the faithful Lemma 11.17 (`notes/fp-gaps/CHATGPT-11-15-17-faithful.md`, section 2.2, repaired
inclusion (2.1)-(2.2); operator notes 21:14 UTC ([C44] amended) and 21:22 UTC). For an `IsBufferedPinchGeometry U V W T Q' Q δ`
(buffer conditions `buffer_U`, `buffer_W` and the open sets `V`, `W`), put `O₂ = B_δ(closure (B_{3δ}(W) \ V))`. Then

* `closure O₂ ⊆ B_{4δ}`-neighbourhood of `W`, hence `closure O₂ ⊆ B_{5δ}(W)`;
* `closure O₂` lies at distance at least `9δ` from `closure U` (`disjoint_closure_pinchO2_closure_U`);
* there is a smooth `φ`, equal to `1` on `closure O₂`, `0` on `closure U` and on the unit circle, with
  `tsupport φ ⊆ B_{5δ}(W)` and `0 ≤ φ ≤ 1` (`exists_pinch_bump`).

Only the buffers are used. Nonemptiness of `U` is not used (the faithful statements need it separately; see `Faithful.lean`).
-/

namespace HarmonicBalls

open MeasureTheory Set Metric Filter

/-- The corrected set `O₂ = B_δ(closure (B_{3δ}(W) \ V))` (faithful note section 2.2; paper `O_2`, [C44] amended). -/
def pinchO2 (δ : ℝ) (V W : Set ℂ) : Set ℂ :=
  thickening δ (closure (thickening (3 * δ) W \ V))

theorem isOpen_pinchO2 (δ : ℝ) (V W : Set ℂ) : IsOpen (pinchO2 δ V W) :=
  isOpen_thickening

/-- Every point of `O₂` lies within `4δ` of `W` (upper bound by distance to `W`). -/
theorem pinchO2_subset_infDist_le {δ : ℝ} (V W : Set ℂ) :
    pinchO2 δ V W ⊆ {z | infDist z W ≤ 4 * δ} := by
  have hX : thickening (3 * δ) W \ V ⊆ {k | infDist k W ≤ 3 * δ} := by
    intro k hk
    obtain ⟨w, hw, hkw⟩ := mem_thickening_iff.mp hk.1
    exact le_trans (infDist_le_dist_of_mem hw) hkw.le
  have hcl : closure (thickening (3 * δ) W \ V) ⊆ {k | infDist k W ≤ 3 * δ} :=
    closure_minimal hX (isClosed_le (continuous_infDist_pt W) continuous_const)
  intro z hz
  obtain ⟨k, hk, hzk⟩ := mem_thickening_iff.mp hz
  have h1 : infDist z W ≤ infDist k W + dist z k := infDist_le_infDist_add_dist
  have h2 : infDist k W ≤ 3 * δ := hcl hk
  show infDist z W ≤ 4 * δ
  linarith

theorem closure_pinchO2_infDist_le {δ : ℝ} (V W : Set ℂ) :
    closure (pinchO2 δ V W) ⊆ {z | infDist z W ≤ 4 * δ} :=
  closure_minimal (pinchO2_subset_infDist_le V W) (isClosed_le (continuous_infDist_pt W) continuous_const)

/-- `closure O₂ ⊆ B_{5δ}(W)` (the open `5δ`-neighbourhood of `W`, corrected paper `[C44]`). -/
theorem closure_pinchO2_subset_thickening {δ : ℝ} {U V W T Q' Q : Set ℂ}
    (h : IsBufferedPinchGeometry U V W T Q' Q δ) :
    closure (pinchO2 δ V W) ⊆ thickening (5 * δ) W := by
  rcases W.eq_empty_or_nonempty with hW | hW
  · subst hW
    simp [pinchO2]
  · intro z hz
    have hz4 : infDist z W ≤ 4 * δ := closure_pinchO2_infDist_le V W hz
    have h5 : infDist z W < 5 * δ := by linarith [h.delta_pos]
    exact mem_thickening_iff.mpr ((infDist_lt_iff hW).mp h5)

/-- Points of `closure O₂` lie within `δ` of the complement of `V`. -/
theorem closure_pinchO2_infDist_compl_le {δ : ℝ} {V W : Set ℂ} (hV : IsOpen V) :
    closure (pinchO2 δ V W) ⊆ {z | infDist z Vᶜ ≤ δ} := by
  have hX : thickening (3 * δ) W \ V ⊆ Vᶜ := fun k hk => hk.2
  have hcl : closure (thickening (3 * δ) W \ V) ⊆ Vᶜ := closure_minimal hX hV.isClosed_compl
  have hsub : pinchO2 δ V W ⊆ {z | infDist z Vᶜ ≤ δ} := by
    intro z hz
    obtain ⟨k, hk, hzk⟩ := mem_thickening_iff.mp hz
    exact le_trans (infDist_le_dist_of_mem (hcl hk)) hzk.le
  exact closure_minimal hsub (isClosed_le (continuous_infDist_pt _) continuous_const)

/-- Points of `closure U` lie at distance at least `10δ` from the complement of `V` (buffer of `U`). -/
theorem tenDelta_le_infDist_compl_of_mem_closure {δ : ℝ} {U V : Set ℂ}
    (hbU : closure (thickening (10 * δ) (closure U)) ⊆ V) (hVc : Vᶜ.Nonempty) {u : ℂ} (hu : u ∈ closure U) :
    10 * δ ≤ infDist u Vᶜ := by
  by_contra hlt
  have hlt' : infDist u Vᶜ < 10 * δ := not_le.mp hlt
  obtain ⟨y, hy, hdy⟩ := (infDist_lt_iff hVc).mp hlt'
  have hyT : y ∈ thickening (10 * δ) (closure U) :=
    mem_thickening_iff.mpr ⟨u, hu, by rw [dist_comm]; exact hdy⟩
  exact hy (hbU (subset_closure hyT))

/-- `closure O₂` and `closure U` are disjoint: their distance is at least `9δ > 0`. -/
theorem disjoint_closure_pinchO2_closure_U {δ : ℝ} {U V W T Q' Q : Set ℂ}
    (h : IsBufferedPinchGeometry U V W T Q' Q δ) :
    Disjoint (closure (pinchO2 δ V W)) (closure U) := by
  have hVc : Vᶜ.Nonempty := ⟨0, fun h0 => (h.V_subset h0).2 (mem_closedBall_self zero_le_one)⟩
  refine Set.disjoint_left.mpr fun z hz1 hz2 => ?_
  have a : infDist z Vᶜ ≤ δ := closure_pinchO2_infDist_compl_le h.isOpen_V hz1
  have b : 10 * δ ≤ infDist z Vᶜ := tenDelta_le_infDist_compl_of_mem_closure h.buffer_U hVc hz2
  linarith [h.delta_pos]

/-- The unit circle does not meet `B_{5δ}(W)` (buffer of `W`, corrected paper `[C42]`). -/
theorem not_mem_thickening_of_mem_sphere {δ : ℝ} {U V W T Q' Q : Set ℂ}
    (h : IsBufferedPinchGeometry U V W T Q' Q δ) {z : ℂ} (hz : z ∈ sphere (0 : ℂ) 1) :
    z ∉ thickening (5 * δ) W := by
  intro hzW
  obtain ⟨w, hw, hzw⟩ := mem_thickening_iff.mp hzW
  have hδ := h.delta_pos
  have hzT : z ∈ thickening (10 * δ) (closure W) :=
    mem_thickening_iff.mpr ⟨w, subset_closure hw, by linarith⟩
  have hA := (h.buffer_W (subset_closure hzT)).2
  exact hA.2 (mem_closedBall.mpr (mem_sphere.mp hz).le)

/-- The smooth bump of Lemma 11.17 (faithful note 17.4): `φ = 1` on `closure O₂`, `φ = 0` on `closure U`, `tsupport φ ⊆ B_{5δ}(W)`,
`φ = 0` on the unit circle, `0 ≤ φ ≤ 1`. -/
theorem exists_pinch_bump {δ : ℝ} {U V W T Q' Q : Set ℂ} (h : IsBufferedPinchGeometry U V W T Q' Q δ) :
    ∃ φ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      tsupport φ ⊆ thickening (5 * δ) W ∧
      (∀ z ∈ closure (pinchO2 δ V W), φ z = 1) ∧ (∀ z ∈ closure U, φ z = 0) ∧
      (∀ z ∈ sphere (0 : ℂ) 1, φ z = 0) ∧ ∀ z, 0 ≤ φ z ∧ φ z ≤ 1 := by
  have hδ := h.delta_pos
  have hball : Bornology.IsBounded (ball (0 : ℂ) (2 + 5 * δ)) := Metric.isBounded_ball
  have hWb : Bornology.IsBounded (thickening (5 * δ) W) := by
    refine hball.subset ?_
    intro z hz
    obtain ⟨w, hw, hzw⟩ := mem_thickening_iff.mp hz
    have hw2 : w ∈ ball (0 : ℂ) 2 := (h.W_subset hw).1
    rw [mem_ball] at hw2 ⊢
    linarith [dist_triangle z w (0 : ℂ)]
  have hKG := closure_pinchO2_subset_thickening h
  have hK : IsCompact (closure (pinchO2 δ V W)) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure (hWb.subset hKG)
  obtain ⟨G, hG, hKG', hGcl⟩ := exists_open_between_of_compact hK isOpen_thickening hKG
  have hF : IsClosed (closure U ∪ Gᶜ) := isClosed_closure.union hG.isClosed_compl
  have hdisj : Disjoint (closure (pinchO2 δ V W)) (closure U ∪ Gᶜ) :=
    Set.disjoint_union_right.mpr ⟨disjoint_closure_pinchO2_closure_U h,
      Set.disjoint_compl_right_iff_subset.mpr hKG'⟩
  obtain ⟨φ, hφs, hφc, hφ0, hφ1, hφ01⟩ := exists_bump_one_zero hK hF hdisj
  have hsupp : Function.support φ ⊆ G := fun z hz => by
    by_contra hzG
    exact hz (hφ0 z (Or.inr hzG))
  have htsupp : tsupport φ ⊆ thickening (5 * δ) W := (closure_mono hsupp).trans hGcl
  refine ⟨φ, hφs, hφc, htsupp, fun z hz => hφ1 z hz, fun z hz => hφ0 z (Or.inl hz), ?_, hφ01⟩
  intro z hz
  by_contra hne
  exact not_mem_thickening_of_mem_sphere h hz (htsupp (subset_tsupport φ hne))

end HarmonicBalls
