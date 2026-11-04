import HarmonicBalls.Draft.Section5

/-!
# Gluing compatible local cluster families

The local time horizons in the proof of Theorem 5.5 need not increase
(GRAPH G6). Agreement on overlaps and coverage of all positive times are
sufficient to define a global family and preserve monotonicity.
-/

namespace HarmonicBalls

open Set Filter Topology MeasureTheory

/-- Choose any local family whose time horizon exceeds `t`. Values outside
all local time intervals are irrelevant to the positive-time construction. -/
noncomputable def glueLocalClusterFamilies (T : ℕ → ℝ) (Λ : ℕ → ℝ → Set ℂ) (t : ℝ) : Set ℂ :=
  by
    classical
    exact if h : ∃ n, t < T n then Λ (Classical.choose h) t else ∅

/-- Agreement of local families on every overlap of their positive-time intervals. -/
def LocalClusterFamiliesAgree (T : ℕ → ℝ) (Λ : ℕ → ℝ → Set ℂ) : Prop :=
  ∀ m n : ℕ, ∀ t : ℝ, 0 < t → t < T m → t < T n → Λ m t = Λ n t

/-- A glued family agrees with every local family wherever that family is defined. -/
theorem glueLocalClusterFamilies_eq (T : ℕ → ℝ) (Λ : ℕ → ℝ → Set ℂ)
    (hag : LocalClusterFamiliesAgree T Λ) (n : ℕ) {t : ℝ} (ht : 0 < t) (htn : t < T n) :
    glueLocalClusterFamilies T Λ t = Λ n t := by
  unfold glueLocalClusterFamilies
  split
  · exact hag _ n t ht (Classical.choose_spec ‹∃ n, t < T n›) htn
  · rename_i h
    exact (h ⟨n, htn⟩).elim

/-- If the local time intervals cover `(0,∞)`, a glued family of monotone
local families is monotone. No ordering of the horizons is required. -/
theorem glueLocalClusterFamilies_monotoneOn (T : ℕ → ℝ) (Λ : ℕ → ℝ → Set ℂ)
    (hag : LocalClusterFamiliesAgree T Λ) (hcover : ∀ t : ℝ, 0 < t → ∃ n, t < T n)
    (hmono : ∀ n, MonotoneOn (Λ n) (Ioo 0 (T n))) :
    MonotoneOn (glueLocalClusterFamilies T Λ) (Ioi 0) := by
  intro s hs t ht hst
  obtain ⟨n, htn⟩ := hcover t ht
  have hsn : s < T n := hst.trans_lt htn
  rw [glueLocalClusterFamilies_eq T Λ hag n hs hsn,
    glueLocalClusterFamilies_eq T Λ hag n ht htn]
  exact hmono n ⟨hs, hsn⟩ ⟨ht, htn⟩ hst

/-- Compatible local families satisfying the conditions of Theorem 1.1
on their respective intervals give a global family satisfying them for all
positive times. In particular, neither nesting nor monotonicity of the time
horizons is assumed. -/
theorem glueLocalClusterFamilies_satisfiesConditions (μ : Measure ℂ) (z : ℂ)
    (T : ℕ → ℝ) (Λ : ℕ → ℝ → Set ℂ) (hag : LocalClusterFamiliesAgree T Λ)
    (hcover : ∀ t : ℝ, 0 < t → ∃ n, t < T n)
    (hloc : ∀ n, SatisfiesHarmonicBallConditionsOn μ (Λ n) z (T n)) :
    SatisfiesHarmonicBallConditions μ (glueLocalClusterFamilies T Λ) z where
  measure_eq t ht := by
    obtain ⟨n, hn⟩ := hcover t ht
    rw [glueLocalClusterFamilies_eq T Λ hag n ht hn]
    exact (hloc n).measure_eq t ⟨ht, hn⟩
  measure_frontier t ht := by
    obtain ⟨n, hn⟩ := hcover t ht
    rw [glueLocalClusterFamilies_eq T Λ hag n ht hn]
    exact (hloc n).measure_frontier t ⟨ht, hn⟩
  isRegularOpen t ht := by
    obtain ⟨n, hn⟩ := hcover t ht
    rw [glueLocalClusterFamilies_eq T Λ hag n ht hn]
    exact (hloc n).isRegularOpen t ⟨ht, hn⟩
  isBounded t ht := by
    obtain ⟨n, hn⟩ := hcover t ht
    rw [glueLocalClusterFamilies_eq T Λ hag n ht hn]
    exact (hloc n).isBounded t ⟨ht, hn⟩
  isConnected t ht := by
    obtain ⟨n, hn⟩ := hcover t ht
    rw [glueLocalClusterFamilies_eq T Λ hag n ht hn]
    exact (hloc n).isConnected t ⟨ht, hn⟩
  mem t ht := by
    obtain ⟨n, hn⟩ := hcover t ht
    rw [glueLocalClusterFamilies_eq T Λ hag n ht hn]
    exact (hloc n).mem t ⟨ht, hn⟩
  monotoneOn := glueLocalClusterFamilies_monotoneOn T Λ hag hcover fun n => (hloc n).monotoneOn
  hausdorffContinuousOn t ht ε hε := by
    obtain ⟨n, hn⟩ := hcover t ht
    have hnear := (hloc n).hausdorffContinuousOn t ⟨ht, hn⟩ ε hε
    rw [nhdsWithin_eq_nhds.2 (Ioo_mem_nhds ht hn)] at hnear
    rw [nhdsWithin_eq_nhds.2 (Ioi_mem_nhds ht)]
    filter_upwards [hnear, Ioo_mem_nhds ht hn] with s hs hst
    rw [glueLocalClusterFamilies_eq T Λ hag n hst.1 hst.2,
      glueLocalClusterFamilies_eq T Λ hag n ht hn]
    exact hs
  iInter_eq := by
    obtain ⟨n, _⟩ := hcover 1 (by norm_num)
    apply Subset.antisymm
    · intro x hx
      rw [← (hloc n).iInter_eq]
      simp only [mem_iInter] at hx ⊢
      intro t ht
      rw [← glueLocalClusterFamilies_eq T Λ hag n ht.1 ht.2]
      exact hx t ht.1
    · intro x hx
      rw [mem_singleton_iff] at hx
      subst x
      simp only [mem_iInter, mem_Ioi]
      intro t ht
      obtain ⟨m, hm⟩ := hcover t ht
      rw [glueLocalClusterFamilies_eq T Λ hag m ht hm]
      exact (hloc m).mem t ⟨ht, hm⟩

end HarmonicBalls
