import HarmonicBalls.Proofs.Sec5.CountableContinuityExceptions

/-! # The right-continuous envelope of an increasing cluster family

This construction does not identify the envelope with the original clusters
at every time. That equality is the outstanding boundary-contact issue.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped Pointwise

/-- The intersection of the closures of a family at dyadic future times. -/
def rightClosedEnvelope (F : ℝ → Set ℂ) (t : ℝ) : Set ℂ :=
  ⋂ n : ℕ, closure (F (t + (2 : ℝ)⁻¹ ^ n))

/-- The right envelope is closed. -/
theorem isClosed_rightClosedEnvelope (F : ℝ → Set ℂ) (t : ℝ) :
    IsClosed (rightClosedEnvelope F t) := isClosed_iInter fun _ => isClosed_closure

/-- An increasing family is contained in its right envelope, even after
closing the set at the present time. -/
theorem closure_subset_rightClosedEnvelope {F : ℝ → Set ℂ} {t : ℝ} (ht : 0 < t)
    (hmono : ∀ s s', 0 < s → s ≤ s' → F s ⊆ F s') :
    closure (F t) ⊆ rightClosedEnvelope F t := by
  intro x hx
  apply mem_iInter.mpr
  intro n
  exact closure_mono (hmono t _ ht (le_add_of_nonneg_right (by positivity))) hx

/-- The right envelope at `t` is contained in every later closed set. -/
theorem rightClosedEnvelope_subset_closure_of_lt {F : ℝ → Set ℂ} {t s : ℝ}
    (ht : 0 < t) (hts : t < s)
    (hmono : ∀ a b, 0 < a → a ≤ b → F a ⊆ F b) :
    rightClosedEnvelope F t ⊆ closure (F s) := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (sub_pos.mpr hts) (by norm_num : (2 : ℝ)⁻¹ < 1)
  intro x hx
  exact closure_mono (hmono _ s (by positivity) (by linarith)) (mem_iInter.mp hx n)

/-- The right envelope is increasing. -/
theorem rightClosedEnvelope_mono {F : ℝ → Set ℂ}
    (hmono : ∀ s s', 0 < s → s ≤ s' → F s ⊆ F s') :
    ∀ s s', 0 < s → s ≤ s' → rightClosedEnvelope F s ⊆ rightClosedEnvelope F s' := by
  intro s s' hs hss' x hx
  apply mem_iInter.mpr
  intro n
  exact closure_mono (hmono (s + (2 : ℝ)⁻¹ ^ n) (s' + (2 : ℝ)⁻¹ ^ n)
      (by positivity) (add_le_add hss' le_rfl))
    (mem_iInter.mp hx n)

/-- Every increasing family in the unit disc has a right-continuous closed
envelope, including at times when the original family meets the boundary. -/
theorem rightClosedEnvelope_right_continuous {F : ℝ → Set ℂ} {t : ℝ} (ht : 0 < t)
    (hmono : ∀ s s', 0 < s → s ≤ s' → F s ⊆ F s')
    (hbound : ∀ s, 0 < s → F s ⊆ ball (0 : ℂ) 1) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
      rightClosedEnvelope F s ⊆ rightClosedEnvelope F t + ball (0 : ℂ) ε := by
  intro ε hε
  obtain ⟨δ, hδ, hδsub⟩ := eventually_closure_subset_open_of_iInter_subset ht hmono hbound
    (U := thickening ε (rightClosedEnvelope F t)) isOpen_thickening
    (show rightClosedEnvelope F t ⊆ thickening ε (rightClosedEnvelope F t) from
      subset_closure.trans (closure_subset_thickening hε _))
  refine ⟨δ / 2, by positivity, ?_⟩
  intro s hs x hx
  have hst : s < t + δ := by linarith [hs.2]
  have hxs : x ∈ closure (F (t + δ)) :=
    rightClosedEnvelope_subset_closure_of_lt (lt_of_lt_of_le ht hs.1) hst hmono hx
  have hx' := hδsub (t + δ) ⟨by linarith, le_rfl⟩ hxs
  obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.mp hx'
  refine ⟨y, hy, x - y, ?_, by abel⟩
  simpa [mem_ball, dist_eq_norm] using hxy

/-- The right envelope is the least closed right-continuous enlargement:
any closed family containing `F` and satisfying the dyadic intersection
identity contains the envelope. -/
theorem rightClosedEnvelope_subset_of_dyadic_identity {F G : ℝ → Set ℂ} {t : ℝ}
    (ht : 0 < t) (hsub : ∀ s, 0 < s → F s ⊆ G s)
    (hclosed : ∀ s, 0 < s → IsClosed (G s))
    (hG : (⋂ n : ℕ, G (t + (2 : ℝ)⁻¹ ^ n)) = G t) :
    rightClosedEnvelope F t ⊆ G t := by
  rw [← hG]
  intro x hx
  apply mem_iInter.mpr
  intro n
  have hp : 0 < t + (2 : ℝ)⁻¹ ^ n := by positivity
  exact (hclosed _ hp).closure_subset_iff.mpr (hsub _ hp) (mem_iInter.mp hx n)

/-- A closed, right-continuous family containing `F` contains its right
envelope. No boundedness of the comparison family is needed. -/
theorem rightClosedEnvelope_subset_of_right_continuity {F G : ℝ → Set ℂ} {t : ℝ}
    (ht : 0 < t) (hsub : ∀ s, 0 < s → F s ⊆ G s) (hclosed : IsClosed (G t))
    (hcont : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
      closure (G s) ⊆ G t + ball (0 : ℂ) ε) :
    rightClosedEnvelope F t ⊆ G t := by
  intro x hx
  have hxcl : x ∈ closure (G t) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨δ, hδ, hδsub⟩ := hcont ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (2 : ℝ)⁻¹ < 1)
    have hp : 0 < t + (2 : ℝ)⁻¹ ^ n := by positivity
    have hmem : x ∈ closure (G (t + (2 : ℝ)⁻¹ ^ n)) :=
      closure_mono (hsub _ hp) (mem_iInter.mp hx n)
    obtain ⟨y, hy, z, hz, rfl⟩ := hδsub _ ⟨le_add_of_nonneg_right (by positivity), by linarith⟩ hmem
    refine ⟨y, hy, ?_⟩
    simpa [mem_ball, dist_eq_norm] using hz
  rwa [hclosed.closure_eq] at hxcl

/-- Taking the right envelope twice has no effect. -/
theorem rightClosedEnvelope_idempotent {F : ℝ → Set ℂ} {t : ℝ} (ht : 0 < t)
    (hmono : ∀ s s', 0 < s → s ≤ s' → F s ⊆ F s')
    (hbound : ∀ s, 0 < s → F s ⊆ ball (0 : ℂ) 1) :
    rightClosedEnvelope (rightClosedEnvelope F) t = rightClosedEnvelope F t := by
  apply Set.Subset.antisymm
  · apply rightClosedEnvelope_subset_of_right_continuity ht (fun _ _ => subset_rfl)
      (isClosed_rightClosedEnvelope F t)
    intro ε hε
    obtain ⟨δ, hδ, hδsub⟩ := rightClosedEnvelope_right_continuous ht hmono hbound ε hε
    refine ⟨δ, hδ, ?_⟩
    intro s hs
    rw [(isClosed_rightClosedEnvelope F s).closure_eq]
    exact hδsub s hs
  · simpa only [(isClosed_rightClosedEnvelope F t).closure_eq] using
      closure_subset_rightClosedEnvelope ht (rightClosedEnvelope_mono hmono)

/-- The envelope differs from the closed original family at only countably
many positive times. -/
theorem countable_rightClosedEnvelope_ne {F : ℝ → Set ℂ}
    (hmono : ∀ s s', 0 < s → s ≤ s' → F s ⊆ F s')
    (hbound : ∀ s, 0 < s → F s ⊆ ball (0 : ℂ) 1) :
    {t : ℝ | 0 < t ∧ rightClosedEnvelope F t ≠ closure (F t)}.Countable := by
  apply (countable_not_rightContinuous_of_monotone hmono hbound).mono
  intro t ht
  refine ⟨ht.1, ?_⟩
  intro hcont
  apply ht.2
  apply Set.Subset.antisymm
  · exact (closure_dyadic_iInter_subset_iff_right_continuous ht.1 hmono hbound).mpr hcont
  · exact closure_subset_rightClosedEnvelope ht.1 hmono

universe u

/-- For every centre simultaneously, LQG clusters have a right-continuous
closed envelope agreeing with their closures outside a countable time set. -/
theorem ae_cluster_rightClosedEnvelope_properties
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1,
      (∀ t : ℝ, 0 < t → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s ∈ Icc t (t + δ),
          rightClosedEnvelope (fun r => cluster (μ ω) 1 z r) s ⊆
            rightClosedEnvelope (fun r => cluster (μ ω) 1 z r) t + ball (0 : ℂ) ε) ∧
      {t : ℝ | 0 < t ∧ rightClosedEnvelope (fun r => cluster (μ ω) 1 z r) t ≠
        closure (cluster (μ ω) 1 z t)}.Countable := by
  filter_upwards [clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ]
    with ω hmono
  intro z hz
  have hm : ∀ s s', 0 < s → s ≤ s' → cluster (μ ω) 1 z s ⊆ cluster (μ ω) 1 z s' :=
    fun s s' hs hss' => hmono s s' 1 hs hss' zero_lt_one z hz
  exact ⟨fun _ ht => rightClosedEnvelope_right_continuous ht hm (fun _ _ => cluster_subset_ball),
    countable_rightClosedEnvelope_ne hm (fun _ _ => cluster_subset_ball)⟩

end HarmonicBalls
