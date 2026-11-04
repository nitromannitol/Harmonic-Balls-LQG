import HarmonicBalls.Proofs.Sec5.NoEntryPropagation
import HarmonicBalls.Steps.Sec5.RegularizedCluster
import HarmonicBalls.Steps.Sec5.CompactContinuity

/-!
# Density of earlier sets

An increasing open family whose measure equals its time parameter has no
open region that first appears at a positive time. This gives the density
input for left Hausdorff continuity of regularized clusters.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology Pointwise

/-- With full support, earlier sets in a mass-continuous increasing open
family are dense in the current set. -/
theorem subset_closure_iUnion_of_mass_continuity
    {μ : Measure ℂ} [μ.IsOpenPosMeasure] {A : ℝ → Set ℂ} {T t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) T) (hopen : IsOpen (A t)) (hmono : MonotoneOn A (Ioo 0 T))
    (hmass : ∀ s ∈ Ioo (0 : ℝ) T, μ (A s) = ENNReal.ofReal s) :
    A t ⊆ closure (⋃ s ∈ Ioo (0 : ℝ) t, A s) := by
  intro x hx
  by_contra hxcl
  have hU : IsOpen (A t \ closure (⋃ s ∈ Ioo (0 : ℝ) t, A s)) :=
    hopen.sdiff isClosed_closure
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.1 hU x ⟨hx, hxcl⟩
  have hBpos : 0 < μ (ball x r) := isOpen_ball.measure_pos μ ⟨x, mem_ball_self hr⟩
  have hBsub : ball x r ⊆ A t := fun y hy => (hrsub hy).1
  have hfinA : μ (A t) ≠ ⊤ := by rw [hmass t ht]; exact ENNReal.ofReal_ne_top
  have hfin : μ (ball x r) ≠ ⊤ := ne_top_of_le_ne_top hfinA (measure_mono hBsub)
  let d : ℝ := (μ (ball x r)).toReal
  have hd : 0 < d := ENNReal.toReal_pos hBpos.ne' hfin
  let s : ℝ := t - min t d / 2
  have hs : 0 < s := by dsimp [s]; have := min_le_left t d; linarith [ht.1]
  have hst : s < t := by dsimp [s]; have := lt_min ht.1 hd; linarith
  have hsT : s ∈ Ioo (0 : ℝ) T := ⟨hs, lt_trans hst ht.2⟩
  have hdis : Disjoint (A s) (ball x r) := by
    apply Set.disjoint_left.2
    intro y hy hyB
    have hyunion : y ∈ ⋃ s ∈ Ioo (0 : ℝ) t, A s := by
      simp only [mem_iUnion]
      exact ⟨s, ⟨hs, hst⟩, hy⟩
    exact (hrsub hyB).2 (subset_closure hyunion)
  have hle := measure_add_le_of_disjoint_entry (μ := μ) isOpen_ball.measurableSet hdis
    (hmono hsT ht hst.le) hBsub
  rw [hmass s hsT, hmass t ht] at hle
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top hfin,
    ENNReal.toReal_ofReal hs.le, ENNReal.toReal_ofReal ht.1.le] at hreal
  change s + d ≤ t at hreal
  have hmin := min_le_right t d
  dsimp [s] at hreal
  linarith

/-- Compactness makes the density of earlier sets uniform in space: the
current closure lies in an arbitrarily small neighborhood of one earlier
set. -/
theorem exists_earlier_uniform_approximation
    {μ : Measure ℂ} [μ.IsOpenPosMeasure] {A : ℝ → Set ℂ} {T t ε : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) T) (hε : 0 < ε) (hopen : IsOpen (A t))
    (hcompact : IsCompact (closure (A t))) (hmono : MonotoneOn A (Ioo 0 T))
    (hmass : ∀ s ∈ Ioo (0 : ℝ) T, μ (A s) = ENNReal.ofReal s) :
    ∃ s ∈ Ioo (0 : ℝ) t, closure (A t) ⊆ ⋃ y ∈ A s, ball y ε := by
  let U : Ioo (0 : ℝ) t → Set ℂ := fun s => ⋃ y ∈ A s, ball y ε
  have hclosure : closure (A t) ⊆ closure (⋃ s ∈ Ioo (0 : ℝ) t, A s) :=
    closure_minimal (subset_closure_iUnion_of_mass_continuity ht hopen hmono hmass)
      isClosed_closure
  have hopenU : ∀ s, IsOpen (U s) := by
    intro s
    exact isOpen_iUnion fun y => isOpen_iUnion fun _ => isOpen_ball
  have hcover : closure (A t) ⊆ ⋃ s, U s := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 (hclosure hx) ε hε
    change x ∈ ⋃ s : Ioo (0 : ℝ) t, ⋃ y ∈ A s, ball y ε
    simp only [mem_iUnion] at hy ⊢
    obtain ⟨s, hs, hys⟩ := hy
    exact ⟨⟨s, hs⟩, y, hys, hxy⟩
  have hdirected : Directed (· ⊆ ·) U := by
    intro s₁ s₂
    let s₃ : Ioo (0 : ℝ) t := ⟨max s₁ s₂,
      ⟨lt_of_lt_of_le s₁.property.1 (le_max_left _ _), max_lt s₁.property.2 s₂.property.2⟩⟩
    refine ⟨s₃, ?_, ?_⟩
    · intro x hx
      simp only [U, mem_iUnion] at hx ⊢
      obtain ⟨y, hy, hxy⟩ := hx
      exact ⟨y, hmono ⟨s₁.property.1, lt_trans s₁.property.2 ht.2⟩ ⟨s₃.property.1, lt_trans s₃.property.2 ht.2⟩ (le_max_left _ _) hy, hxy⟩
    · intro x hx
      simp only [U, mem_iUnion] at hx ⊢
      obtain ⟨y, hy, hxy⟩ := hx
      exact ⟨y, hmono ⟨s₂.property.1, lt_trans s₂.property.2 ht.2⟩ ⟨s₃.property.1, lt_trans s₃.property.2 ht.2⟩ (le_max_right _ _) hy, hxy⟩
  let _ : Nonempty (Ioo (0 : ℝ) t) := ⟨⟨t / 2, half_pos ht.1, half_lt_self ht.1⟩⟩
  obtain ⟨s, hs⟩ := hcompact.elim_directed_cover U hopenU hcover hdirected
  exact ⟨s, s.property, hs⟩

/-- A compact mass-continuous increasing open family is left-continuous in
Hausdorff edistance, expressed with a real error bound. -/
theorem exists_earlier_hausdorff_bound
    {μ : Measure ℂ} [μ.IsOpenPosMeasure] {A : ℝ → Set ℂ} {T t ε : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) T) (hε : 0 < ε) (hopen : IsOpen (A t))
    (hcompact : IsCompact (closure (A t))) (hmono : MonotoneOn A (Ioo 0 T))
    (hmass : ∀ s ∈ Ioo (0 : ℝ) T, μ (A s) = ENNReal.ofReal s) :
    ∃ s ∈ Ioo (0 : ℝ) t, ∀ s' ∈ Icc s t,
      hausdorffEDist (A s') (A t) ≤ ENNReal.ofReal ε := by
  obtain ⟨s, hs, hcover⟩ := exists_earlier_uniform_approximation ht hε hopen hcompact hmono hmass
  refine ⟨s, hs, ?_⟩
  intro s' hs'
  have hs'pos : 0 < s' := lt_of_lt_of_le hs.1 hs'.1
  have hsT : s ∈ Ioo (0 : ℝ) T := ⟨hs.1, lt_trans hs.2 ht.2⟩
  have hs'T : s' ∈ Ioo (0 : ℝ) T := ⟨hs'pos, lt_of_le_of_lt hs'.2 ht.2⟩
  have hss : A s ⊆ A s' := hmono hsT hs'T hs'.1
  have hst : A s' ⊆ A t := hmono hs'T ht hs'.2
  apply hausdorffEDist_le_of_mem_edist
  · intro x hx
    exact ⟨x, hst hx, by simp⟩
  · intro x hx
    have hxcover := hcover (subset_closure hx)
    simp only [mem_iUnion] at hxcover
    obtain ⟨y, hy, hxy⟩ := hxcover
    refine ⟨y, hss hy, ?_⟩
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal (le_of_lt hxy)

/-- Left Hausdorff continuity follows from mass continuity and full
support; a right-hand bound then gives two-sided continuity. -/
theorem hausdorffContinuousOn_of_right_bounds
    {μ : Measure ℂ} [μ.IsOpenPosMeasure] {A : ℝ → Set ℂ} {T : ℝ}
    (hopen : ∀ t ∈ Ioo (0 : ℝ) T, IsOpen (A t))
    (hcompact : ∀ t ∈ Ioo (0 : ℝ) T, IsCompact (closure (A t)))
    (hmono : MonotoneOn A (Ioo 0 T))
    (hmass : ∀ s ∈ Ioo (0 : ℝ) T, μ (A s) = ENNReal.ofReal s)
    (hright : ∀ t ∈ Ioo (0 : ℝ) T, ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
        hausdorffEDist (A s) (A t) ≤ ENNReal.ofReal ε) :
    HausdorffContinuousOn A (Ioo 0 T) := by
  intro t ht ε hε
  let e : ℝ≥0∞ := min ε 1
  have hepos : 0 < e := lt_min hε (by norm_num)
  have hefin : e ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  let η : ℝ := e.toReal / 2
  have hη : 0 < η := half_pos (ENNReal.toReal_pos hepos.ne' hefin)
  have hηε : ENNReal.ofReal η < ε := by
    calc
      ENNReal.ofReal η < ENNReal.ofReal e.toReal := (ENNReal.ofReal_lt_ofReal_iff (ENNReal.toReal_pos hepos.ne' hefin)).2
        (by dsimp [η]; linarith [ENNReal.toReal_pos hepos.ne' hefin])
      _ = e := ENNReal.ofReal_toReal hefin
      _ ≤ ε := min_le_left _ _
  obtain ⟨s, hs, hleft⟩ := exists_earlier_hausdorff_bound ht hη (hopen t ht)
    (hcompact t ht) hmono hmass
  obtain ⟨δ, hδ, hright'⟩ := hright t ht η hη
  have hneigh : Ioo s (t + δ) ∈ 𝓝 t := Ioo_mem_nhds hs.2 (lt_add_of_pos_right _ hδ)
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds hneigh] with s' hs'
  by_cases hst : s' ≤ t
  · exact lt_of_le_of_lt (hleft s' ⟨hs'.1.le, hst⟩) hηε
  · exact lt_of_le_of_lt (hright' s' ⟨(le_of_not_ge hst), hs'.2.le⟩) hηε

universe u

/-- The Hausdorff-continuity step for Proposition 5.4 follows from compact
right continuity, conservation of mass, null boundaries, and full support. -/
theorem regularizedClusterHausdorffContinuity_of_steps
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h34 : ClusterConservationOfMassStmt.{u}) (h53 : ClusterBoundaryMeasureZeroStmt.{u})
    (hfull : LQGMeasureFullSupportStmt.{u}) (hright : ClusterCompactRightContinuityStmt.{u}) :
    RegularizedClusterHausdorffContinuityStep.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [h32 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    h33 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    h34 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    h53 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    hfull γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    hright γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hop hmono hmass hnull hsupport hcont
  let _ : (μ ω).IsOpenPosMeasure := ⟨fun U hU hne => (hsupport U hU hne).ne'⟩
  intro z hz T hT hcompact
  have hz1 : z ∈ ball (0 : ℂ) 1 := ball_subset_ball (by norm_num : (1 : ℝ) / 2 ≤ 1) hz
  have hclusterOpen : ∀ t ∈ Ioo (0 : ℝ) T, IsOpen (cluster (μ ω) 1 z t) :=
    fun t ht => (hop t 1 ht.1 (by norm_num) z hz1).1
  apply hausdorffContinuousOn_of_right_bounds (μ := μ ω)
  · intro t ht
    exact isOpen_regularizedCluster _ _ _ _
  · intro t ht
    apply Metric.isCompact_of_isClosed_isBounded
    · exact isClosed_closure
    · apply Bornology.IsBounded.closure
      apply isBounded_regularizedCluster
      exact isBounded_ball.subset (fun x hx => hcompact t ht (subset_closure hx))
  · intro s hs t ht hst
    exact regularizedCluster_subset_of_cluster_subset (hmono s t 1 hs.1 hst (by norm_num) z hz1)
  · intro t ht
    have hb := hnull z hz1 t ht.1 (hcompact t ht)
    rw [measure_regularizedCluster_eq (hclusterOpen t ht) hb]
    exact (hmass 1 t (by norm_num) ht.1 z hz1).2.2 (hcompact t ht) hb
  · intro t ht ε hε
    obtain ⟨δ, hδ, hδbound⟩ := hcont z hz t ht.1 (hcompact t ht) ε hε
    refine ⟨δ, hδ, ?_⟩
    intro s hs
    have hspos : 0 < s := lt_of_lt_of_le ht.1 hs.1
    have hsub : regularizedCluster (μ ω) 1 z t ⊆ regularizedCluster (μ ω) 1 z s :=
      regularizedCluster_subset_of_cluster_subset (hmono t s 1 ht.1 hs.1 (by norm_num) z hz1)
    apply hausdorffEDist_le_of_mem_edist
    · intro x hx
      have hxcl : x ∈ closure (cluster (μ ω) 1 z s) := interior_subset hx
      have hxsum := hδbound s hs hxcl
      obtain ⟨y, hy, w, hw, rfl⟩ := hxsum
      refine ⟨y, cluster_subset_regularizedCluster (hclusterOpen t ht) hy, ?_⟩
      rw [edist_dist]
      apply ENNReal.ofReal_le_ofReal
      simp only [mem_ball, dist_zero_right] at hw
      simpa only [dist_eq_norm, add_sub_cancel_left] using hw.le
    · intro x hx
      exact ⟨x, hsub hx, by simp⟩

/-- Proposition 5.4 from the exit-time step, Proposition 7.2, and the
Section 3 and Section 5 inputs. -/
theorem regularizedClusterHarmonicBalls_of_exit
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h34 : ClusterConservationOfMassStmt.{u}) (hshrink : ClusterShrinksToCenterStmt.{u})
    (h53 : ClusterBoundaryMeasureZeroStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    (h72 : ClusterTimeContinuityStmt.{u}) (hexit : RegularizedClusterExitTimeStep.{u}) :
    RegularizedClusterHarmonicBallsStmt.{u} :=
  regularizedClusterHarmonicBalls_of_steps h32 h33 h34 hshrink h53 hexit
    (regularizedClusterHausdorffContinuity_of_steps h32 h33 h34 h53 hfull
      (clusterCompactRightContinuity_of_steps h33 h72))

end HarmonicBalls
