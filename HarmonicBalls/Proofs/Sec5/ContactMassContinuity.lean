import HarmonicBalls.Proofs.Sec5.InteriorClusterBoundary
import HarmonicBalls.Proofs.Sec7.ClusterIncrementMass

/-!
# Cluster mass at first boundary contact

Conservation of mass up to contact and the global upper bound imply mass
conservation at the contact time. They also control later increments in
measure, although this alone does not give Hausdorff continuity.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped ENNReal Topology

/-- Upper mass control and conservation at all earlier positive times imply
conservation at the limiting time for an increasing cluster family. -/
theorem cluster_measure_eq_of_earlier_mass_eq
    (μ : Measure ℂ) (r : ℝ) (z : ℂ) {t : ℝ} (ht : 0 < t)
    (hmono : ∀ s ∈ Ioo (0 : ℝ) t, cluster μ r z s ⊆ cluster μ r z t)
    (hupper : μ (cluster μ r z t) ≤ ENNReal.ofReal t)
    (hearlier : ∀ s ∈ Ioo (0 : ℝ) t,
      μ (cluster μ r z s) = ENNReal.ofReal s) :
    μ (cluster μ r z t) = ENNReal.ofReal t := by
  have hfin : μ (cluster μ r z t) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hupper
  have hlower : t ≤ (μ (cluster μ r z t)).toReal := by
    by_contra h
    have hlt : (μ (cluster μ r z t)).toReal < t := lt_of_not_ge h
    let s := ((μ (cluster μ r z t)).toReal + t) / 2
    have hs0 : 0 < s := by
      dsimp [s]
      have hnonneg : 0 ≤ (μ (cluster μ r z t)).toReal := ENNReal.toReal_nonneg
      linarith
    have hst : s < t := by dsimp [s]; linarith
    have hle := measure_mono (μ := μ) (hmono s ⟨hs0, hst⟩)
    rw [hearlier s ⟨hs0, hst⟩] at hle
    have hreal := ENNReal.toReal_mono hfin hle
    rw [ENNReal.toReal_ofReal hs0.le] at hreal
    dsimp [s] at hreal
    linarith
  apply le_antisymm hupper
  simpa [ENNReal.ofReal_toReal hfin] using ENNReal.ofReal_le_ofReal hlower

/-- Once a cluster has the prescribed mass, the mass of its later increment
is bounded by the elapsed time, without any compact-containment assumption. -/
theorem measure_cluster_sdiff_le_of_mass_eq
    (μ : Measure ℂ) (r : ℝ) (z : ℂ) {t s : ℝ} (ht : 0 ≤ t) (hts : t ≤ s)
    (hopen : IsOpen (cluster μ r z t))
    (hmono : cluster μ r z t ⊆ cluster μ r z s)
    (heq : μ (cluster μ r z t) = ENNReal.ofReal t)
    (hupper : μ (cluster μ r z s) ≤ ENNReal.ofReal s) :
    μ (cluster μ r z s \ cluster μ r z t) ≤ ENNReal.ofReal (s - t) := by
  apply measure_sdiff_le_of_measure_le_add hmono hopen.measurableSet.nullMeasurableSet
    (by rw [heq]; exact ENNReal.ofReal_ne_top)
  calc
    μ (cluster μ r z s) ≤ ENNReal.ofReal s := hupper
    _ = μ (cluster μ r z t) + ENNReal.ofReal (s - t) := by
      rw [heq, ← ENNReal.ofReal_add ht (sub_nonneg.mpr hts)]
      congr 1
      ring

/-- If later increments have vanishing mass and every later interior boundary
is null, the limiting future closures introduce no mass inside the disc. -/
theorem measure_dyadic_future_closure_sdiff_eq_zero
    (μ : Measure ℂ) (z : ℂ) (t : ℝ)
    (hopen : ∀ n : ℕ, IsOpen (cluster μ 1 z (t + dyadicScale n)))
    (hboundary : ∀ n : ℕ,
      μ (frontier (cluster μ 1 z (t + dyadicScale n)) ∩ ball 0 1) = 0)
    (hmass : ∀ n : ℕ,
      μ (cluster μ 1 z (t + dyadicScale n) \ cluster μ 1 z t) ≤
        ENNReal.ofReal (dyadicScale n)) :
    μ (((⋂ n : ℕ, closure (cluster μ 1 z (t + dyadicScale n))) ∩ ball 0 1) \ cluster μ 1 z t) = 0 := by
  have hbound : ∀ n : ℕ,
      μ (((⋂ n : ℕ, closure (cluster μ 1 z (t + dyadicScale n))) ∩ ball 0 1) \ cluster μ 1 z t) ≤ ENNReal.ofReal (dyadicScale n) := by
    intro n
    calc
      _ ≤ μ ((cluster μ 1 z (t + dyadicScale n) \ cluster μ 1 z t) ∪
          (frontier (cluster μ 1 z (t + dyadicScale n)) ∩ ball 0 1)) := by
        apply measure_mono
        intro x hx
        by_cases hmem : x ∈ cluster μ 1 z (t + dyadicScale n)
        · exact Or.inl ⟨hmem, hx.2⟩
        · apply Or.inr
          refine ⟨?_, hx.1.2⟩
          rw [frontier, (hopen n).interior_eq]
          exact ⟨Set.mem_iInter.mp hx.1.1 n, hmem⟩
      _ ≤ μ (cluster μ 1 z (t + dyadicScale n) \ cluster μ 1 z t) +
          μ (frontier (cluster μ 1 z (t + dyadicScale n)) ∩ ball 0 1) := measure_union_le _ _
      _ ≤ ENNReal.ofReal (dyadicScale n) := by rw [hboundary n, add_zero]; exact hmass n
  have hlim : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (dyadicScale n))
      Filter.atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal
      (tendsto_dyadicScale_nhdsGT.mono_right nhdsWithin_le_nhds)
  exact le_antisymm (ge_of_tendsto' hlim hbound) bot_le

universe u

/-- Almost surely, conservation persists at any time approached by compactly
contained clusters. Later increments have mass at most the elapsed time. -/
theorem ae_cluster_contact_mass_and_increment_of_steps
    (h32 : ClusterOpenLaplacianStmt.{u})
    (h33 : ClusterMonotoneStmt.{u})
    (h34 : ClusterConservationOfMassStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα₀ : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      (∀ s ∈ Ioo (0 : ℝ) t, closure (cluster (μ ω) 1 z s) ⊆ ball 0 1) →
      μ ω (cluster (μ ω) 1 z t) = ENNReal.ofReal t ∧
      ∀ s : ℝ, t ≤ s →
        μ ω (cluster (μ ω) 1 z s \ cluster (μ ω) 1 z t) ≤ ENNReal.ofReal (s - t) := by
  filter_upwards [h32 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    h33 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    h34 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_measure_frontier_cluster_inter_ball_eq_zero_of_steps h32 h611 h82
      γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ]
    with ω hopen hmono hmass hboundary
  intro t ht z hz hcompact
  have heq : μ ω (cluster (μ ω) 1 z t) = ENNReal.ofReal t := by
    apply cluster_measure_eq_of_earlier_mass_eq (μ ω) 1 z ht
    · intro s hs
      exact hmono s t 1 hs.1 hs.2.le zero_lt_one z hz
    · exact (hmass 1 t zero_lt_one ht z hz).1
    · intro s hs
      have hfront : μ ω (frontier (cluster (μ ω) 1 z s)) = 0 := by
        apply measure_mono_null _ (hboundary s hs.1 z hz)
        intro x hx
        exact ⟨hx, hcompact s hs (frontier_subset_closure hx)⟩
      exact (hmass 1 s zero_lt_one hs.1 z hz).2.2 (hcompact s hs) hfront
  refine ⟨heq, ?_⟩
  intro s hts
  exact measure_cluster_sdiff_le_of_mass_eq (μ ω) 1 z ht.le hts
    (hopen t 1 ht zero_lt_one z hz).1 (hmono t s 1 ht hts zero_lt_one z hz) heq
    (hmass 1 s zero_lt_one (lt_of_lt_of_le ht hts) z hz).1

/-- At a first-contact time, the interior part of the intersection of future
cluster closures differs from the present cluster by a null set. -/
theorem ae_measure_dyadic_future_closure_sdiff_eq_zero_of_steps
    (h32 : ClusterOpenLaplacianStmt.{u})
    (h33 : ClusterMonotoneStmt.{u})
    (h34 : ClusterConservationOfMassStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα₀ : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      (∀ s ∈ Ioo (0 : ℝ) t, closure (cluster (μ ω) 1 z s) ⊆ ball 0 1) →
      μ ω (((⋂ n : ℕ, closure (cluster (μ ω) 1 z (t + dyadicScale n))) ∩ ball 0 1) \ 
        cluster (μ ω) 1 z t) = 0 := by
  filter_upwards [h32 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_measure_frontier_cluster_inter_ball_eq_zero_of_steps h32 h611 h82
      γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_cluster_contact_mass_and_increment_of_steps h32 h33 h34 h611 h82
      γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hopen hboundary hmass
  intro t ht z hz hcompact
  apply measure_dyadic_future_closure_sdiff_eq_zero (μ ω) z t
  · intro n
    exact (hopen (t + dyadicScale n) 1 (add_pos ht (dyadicScale_pos n)) zero_lt_one z hz).1
  · intro n
    exact hboundary (t + dyadicScale n) (add_pos ht (dyadicScale_pos n)) z hz
  · intro n
    simpa using (hmass t ht z hz hcompact).2 (t + dyadicScale n)
      (le_add_of_nonneg_right (dyadicScale_pos n).le)

end HarmonicBalls
