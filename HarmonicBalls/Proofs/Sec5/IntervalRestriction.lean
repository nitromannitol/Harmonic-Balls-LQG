import HarmonicBalls.Steps.Sec5.StrongCompatibility

/-! # Restricting regularized cluster intervals before exit -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

/-- A harmonic-ball flow restricted to a shorter positive time interval
still satisfies all the interval conditions. -/
theorem SatisfiesHarmonicBallConditionsOn.restrict_time
    {μ : Measure ℂ} {Λ : ℝ → Set ℂ} {z : ℂ} {S T : ℝ}
    (h : SatisfiesHarmonicBallConditionsOn μ Λ z T) (hS : 0 < S) (hST : S ≤ T) :
    SatisfiesHarmonicBallConditionsOn μ Λ z S := by
  have hsub : Ioo (0 : ℝ) S ⊆ Ioo 0 T := fun _ ht => ⟨ht.1, lt_of_lt_of_le ht.2 hST⟩
  refine ⟨fun t ht => h.measure_eq t (hsub ht),
    fun t ht => h.measure_frontier t (hsub ht),
    fun t ht => h.isRegularOpen t (hsub ht),
    fun t ht => h.isBounded t (hsub ht),
    fun t ht => h.isConnected t (hsub ht),
    fun t ht => h.mem t (hsub ht),
    h.monotoneOn.mono hsub, ?_, ?_⟩
  · intro t ht ε hε
    exact (h.hausdorffContinuousOn t (hsub ht) ε hε).filter_mono (nhdsWithin_mono t hsub)
  · apply Subset.antisymm
    · intro x hx
      have hx' : x ∈ ⋂ t ∈ Ioo (0 : ℝ) T, Λ t := by
        simp only [mem_iInter, mem_Ioo] at hx ⊢
        intro t ht
        by_cases htS : t < S
        · exact hx t ⟨ht.1, htS⟩
        · have hh : S / 2 ∈ Ioo (0 : ℝ) S := ⟨half_pos hS, half_lt_self hS⟩
          have hle : S / 2 ≤ t := le_trans hh.2.le (le_of_not_gt htS)
          exact h.monotoneOn (hsub hh) ht hle (hx (S / 2) hh)
      rw [h.iInter_eq] at hx'
      exact hx'
    · intro x hx
      rw [mem_singleton_iff] at hx
      subst x
      simp only [mem_iInter]
      intro t ht
      exact h.mem t (hsub ht)

/-- A compact-containment horizon precedes any time at which the closure of
the regularized cluster touches the boundary of the ambient ball. -/
theorem horizon_le_regularizedCluster_boundaryTime
    {μ : Measure ℂ} {R T H : ℝ} {z : ℂ} (hT : 0 < T)
    (hopen : IsOpen (cluster μ R z T))
    (hbefore : ∀ t ∈ Ioo (0 : ℝ) H, closure (cluster μ R z t) ⊆ ball 0 R)
    (htouch : (closure (regularizedCluster μ R z T) ∩ sphere (0 : ℂ) R).Nonempty) :
    H ≤ T := by
  by_contra h
  have hlt : T < H := lt_of_not_ge h
  obtain ⟨x, hx, hxs⟩ := htouch
  have hx' : x ∈ closure (cluster μ R z T) :=
    (closure_regularizedCluster_eq_of_isOpen hopen) ▸ hx
  have hxb := hbefore T ⟨hT, hlt⟩ hx'
  simp only [mem_ball, mem_sphere] at hxb hxs
  linarith

/-- The regularized cluster conditions hold throughout every positive
compact-containment horizon preceding boundary contact. -/
theorem regularizedClusterConditionsOn_of_horizon
    {μ : Measure ℂ} {R T H : ℝ} {z : ℂ} (hT : 0 < T) (hH : 0 < H)
    (hopen : IsOpen (cluster μ R z T))
    (hbefore : ∀ t ∈ Ioo (0 : ℝ) H, closure (cluster μ R z t) ⊆ ball 0 R)
    (htouch : (closure (regularizedCluster μ R z T) ∩ sphere (0 : ℂ) R).Nonempty)
    (hconditions : SatisfiesHarmonicBallConditionsOn μ (regularizedCluster μ R z) z T) :
    SatisfiesHarmonicBallConditionsOn μ (regularizedCluster μ R z) z H :=
  hconditions.restrict_time hH (horizon_le_regularizedCluster_boundaryTime hT hopen hbefore htouch)

end HarmonicBalls
