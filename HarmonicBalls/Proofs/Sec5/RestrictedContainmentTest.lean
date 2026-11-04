import HarmonicBalls.Proofs.Sec5.LocalCompactFamilyRepresentative
import HarmonicBalls.Proofs.Sec5.CompactStrongCompatibility

/-! # Compact containment via restricted measures -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter TopologicalSpace

/-- A compactly contained disc cluster has the same closure as a regularized
cluster family, provided the disc least supersolution is admissible. -/
theorem regularizedFamily_closure_eq_discCluster_of_compact_containment
    {μ : Measure ℂ} {r t : ℝ} {z : ℂ} (hr : 0 < r) (hz : z ∈ ball 0 r)
    (ht : 0 < t) {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hopen : ∀ R : ℝ, 0 < R → z ∈ ball 0 R → IsOpen (cluster μ R z t))
    (hv : leastSupersolution μ r z t ∈ supersolutions μ r z t)
    (hcl : closure (cluster μ r z t) ⊆ ball 0 r) :
    closure (Λ t) = closure (cluster μ r z t) := by
  have hv' : leastSupersolutionOn μ (ball 0 r) z t ∈
      supersolutionsOn μ (ball 0 r) z t := by
    have heq : leastSupersolutionOn μ (ball 0 r) z t = leastSupersolution μ r z t := by
      funext x
      simp only [leastSupersolutionOn, leastSupersolution, supersolutionsOn_ball μ hr.ne']
    rw [heq, supersolutionsOn_ball μ hr.ne']
    exact hv
  have hcl' : closure (clusterOn μ (ball 0 r) z t) ⊆ ball 0 r := by
    rwa [clusterOn_ball μ hr.ne']
  obtain ⟨s, hs⟩ := ((hΛ.1.isBounded t ht).closure).subset_ball (0 : ℂ)
  let R := max r s + 1
  have hrR : r ≤ R := by dsimp [R]; linarith [le_max_left r s]
  have hsR : s ≤ R := by dsimp [R]; linarith [le_max_right r s]
  have hR : 0 < R := lt_of_lt_of_le hr hrR
  have hΛR : closure (Λ t) ⊆ ball (0 : ℂ) R := hs.trans (ball_subset_ball hsR)
  have hzR : z ∈ ball (0 : ℂ) R := ball_subset_ball hrR hz
  have heq := hΛ.2.2 t ht R hR hΛR R le_rfl
  rw [heq, closure_regularizedCluster_eq_of_isOpen (hopen R hR hzR),
    ← clusterOn_eq_cluster_of_compact_containment isOpen_ball
      (ball_subset_ball hrR) hz ht hv' hcl', clusterOn_ball μ hr.ne']

/-- Compact containment of the regularized family is equivalent to compact
containment of the disc cluster for the restricted measure, in any disc
containing the open set. -/
theorem regularizedFamily_compact_containment_iff_restricted_cluster
    {μ : Measure ℂ} {U : Set ℂ} (hU : IsOpen U) {r t : ℝ} {z : ℂ}
    (hr : 0 < r) (hUr : U ⊆ ball 0 r) (hz : z ∈ U) (ht : 0 < t)
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hopen : ∀ R : ℝ, 0 < R → z ∈ ball 0 R → IsOpen (cluster μ R z t))
    (hv : leastSupersolution μ r z t ∈ supersolutions μ r z t) :
    closure (Λ t) ⊆ U ↔ closure (cluster (μ.restrict U) r z t) ⊆ U := by
  have hzr : z ∈ ball (0 : ℂ) r := hUr hz
  constructor
  · intro hΛU
    have hΛr := hΛU.trans hUr
    have hΛeq := hΛ.2.2 t ht r hr hΛr r le_rfl
    have hclosure : closure (Λ t) = closure (cluster μ r z t) := by
      rw [hΛeq, closure_regularizedCluster_eq_of_isOpen (hopen r hr hzr)]
    have heq := cluster_restrict_eq_of_closure_subset hU hzr ht.le hv
      (hclosure ▸ hΛU) (hclosure ▸ hΛr)
    rw [← heq, ← hclosure]
    exact hΛU
  · intro hrest
    have hcl : closure (cluster μ r z t) ⊆ U :=
      (closure_mono (cluster_antitone_measure Measure.restrict_le_self ht.le)).trans hrest
    have heq := regularizedFamily_closure_eq_discCluster_of_compact_containment
      hr hzr ht hΛ hopen hv (hcl.trans hUr)
    rw [heq]
    exact hcl

/-- The same test only needs the restricted cluster at a countable dense
sequence, even though the restricted cluster is not assumed open. -/
theorem regularizedFamily_compact_containment_iff_dense_restricted_cluster
    {μ : Measure ℂ} {U : Set ℂ} (hU : IsOpen U) {r t : ℝ} {z : ℂ}
    (hr : 0 < r) (hUr : U ⊆ ball 0 r) (hz : z ∈ U) (ht : 0 < t)
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hopen : ∀ R : ℝ, 0 < R → z ∈ ball 0 R → IsOpen (cluster μ R z t))
    (hv : leastSupersolution μ r z t ∈ supersolutions μ r z t) :
    closure (Λ t) ⊆ U ↔ denseSequenceClosure (cluster (μ.restrict U) r z t) ⊆ U := by
  have hzr : z ∈ ball (0 : ℂ) r := hUr hz
  have hsub : closure (cluster μ r z t) ⊆
      denseSequenceClosure (cluster (μ.restrict U) r z t) := by
    rw [denseSequenceClosure, closure_eq_closure_inter_denseSeq (hopen r hr hzr)]
    exact closure_mono (inter_subset_inter_left _
      (cluster_antitone_measure Measure.restrict_le_self ht.le))
  constructor
  · intro hΛU
    have hΛr := hΛU.trans hUr
    have hΛeq := hΛ.2.2 t ht r hr hΛr r le_rfl
    have hclosure : closure (Λ t) = closure (cluster μ r z t) := by
      rw [hΛeq, closure_regularizedCluster_eq_of_isOpen (hopen r hr hzr)]
    have heq := cluster_restrict_eq_of_closure_subset hU hzr ht.le hv
      (hclosure ▸ hΛU) (hclosure ▸ hΛr)
    rw [← heq, denseSequenceClosure, ← closure_eq_closure_inter_denseSeq (hopen r hr hzr), ← hclosure]
    exact hΛU
  · intro hrest
    have hcl := hsub.trans hrest
    have heq := regularizedFamily_closure_eq_discCluster_of_compact_containment
      hr hzr ht hΛ hopen hv (hcl.trans hUr)
    rw [heq]
    exact hcl

/-- A compact countable-sequence closure lies in an open set exactly when
its sequence points have a common positive distance from the complement. -/
theorem denseSequenceClosure_subset_open_iff
    {V U : Set ℂ} (hU : IsOpen U) (hUc : Uᶜ.Nonempty)
    (hK : IsCompact (denseSequenceClosure V)) :
    denseSequenceClosure V ⊆ U ↔ ∃ n : ℕ, ∀ m : ℕ,
      denseSeq ℂ m ∈ V → 1 / ((n : ℝ) + 1) ≤ infDist (denseSeq ℂ m) Uᶜ := by
  constructor
  · intro hsub
    by_cases hne : (denseSequenceClosure V).Nonempty
    · obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hne (continuous_infDist_pt Uᶜ).continuousOn
      have hpos : 0 < infDist x Uᶜ :=
        (hU.isClosed_compl.notMem_iff_infDist_pos hUc).mp (by simpa using hsub hx)
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
      refine ⟨n, fun m hm => ?_⟩
      have hmem : denseSeq ℂ m ∈ denseSequenceClosure V :=
        subset_closure ⟨hm, ⟨m, rfl⟩⟩
      exact (le_of_lt hn).trans (hmin hmem)
    · refine ⟨0, fun m hm => False.elim (hne ?_)⟩
      exact ⟨denseSeq ℂ m, subset_closure ⟨hm, ⟨m, rfl⟩⟩⟩
  · rintro ⟨n, hn⟩
    have hclosed : IsClosed {x : ℂ | 1 / ((n : ℝ) + 1) ≤ infDist x Uᶜ} :=
      isClosed_le continuous_const (continuous_infDist_pt Uᶜ)
    have hbound : denseSequenceClosure V ⊆
        {x : ℂ | 1 / ((n : ℝ) + 1) ≤ infDist x Uᶜ} := by
      apply closure_minimal _ hclosed
      rintro x ⟨hx, m, rfl⟩
      exact hn m hx
    intro x hx
    have hpos : 0 < infDist x Uᶜ := lt_of_lt_of_le (by positivity) (hbound hx)
    simpa using (hU.isClosed_compl.notMem_iff_infDist_pos hUc).mpr hpos

universe u

/-- On a bounded open domain the compact-containment predicates of an
existing regularized family have a field-local measurable representative.
The locality input is proposed and awaits source review. -/
theorem exists_local_lqg_bounded_compactContainmentFamily_representative
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {Λ : Ω → ℂ → ℝ → Set ℂ}
    (hΛ : ∀ᵐ ω ∂P, ∀ z, IsRegularizedClusterFamily (μ ω) (Λ ω z) z) :
    ∃ F : Ω → (U × Ioi (0 : ℝ) → Prop),
      Measurable[fieldSigmaAlgebra α₀ hC U] F ∧
      ∀ᵐ ω ∂P, ∀ p, F ω p ↔ closure (Λ ω p.1 p.2) ⊆ U := by
  classical
  obtain ⟨r, hr⟩ := hUb.subset_ball (0 : ℂ)
  let R := max 1 r + 1
  have hR : 0 < R := by
    have h := le_max_left (1 : ℝ) r
    dsimp [R]
    linarith
  have hrR : r ≤ R := by
    have h := le_max_right (1 : ℝ) r
    dsimp [R]
    linarith
  have hUR : U ⊆ ball (0 : ℂ) R := hr.trans (ball_subset_ball hrR)
  have hUc : Uᶜ.Nonempty := by
    refine ⟨(R : ℂ), ?_⟩
    intro hmem
    have h := hUR hmem
    simp only [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, lt_self_iff_false] at h
  obtain ⟨G, hG, hGeq⟩ := exists_local_lqg_restricted_clusterFamily_representative
    hI2 hγ hγ2 hα hGFF hμ hloc hU hR
  let J := U × Ioi (0 : ℝ)
  let F : Ω → J → Prop := fun ω p => ∃ n : ℕ, ∀ m : ℕ,
    denseSeq ℂ m ∈ G ω (⟨p.1, hUR p.1.property⟩, p.2) →
      1 / ((n : ℝ) + 1) ≤ infDist (denseSeq ℂ m) Uᶜ
  have hF : Measurable[fieldSigmaAlgebra α₀ hC U] F := by
    let : MeasurableSpace Ω := fieldSigmaAlgebra α₀ hC U
    apply Measurable.of_eval
    intro p
    apply Measurable.exists
    intro n
    apply Measurable.forall
    intro m
    have hm : Measurable (fun ω => denseSeq ℂ m ∈
        G ω (⟨p.1, hUR p.1.property⟩, p.2)) :=
      (measurable_pi_apply (denseSeq ℂ m)).comp
        ((measurable_pi_apply ((⟨p.1, hUR p.1.property⟩ : ball (0 : ℂ) R), p.2)).comp hG)
    exact hm.imp measurable_const
  obtain ⟨βm, βp, hae⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  refine ⟨F, hF, ?_⟩
  filter_upwards [hGeq, hae, hΛ] with ω hGω hω hΛω
  intro p
  have hopen : ∀ s : ℝ, 0 < s → (p.1 : ℂ) ∈ ball (0 : ℂ) s →
      IsOpen (cluster (μ ω) s p.1 p.2) := by
    intro s hs hz
    rw [(obstacleCompatibilityShiftStep_holds (μ ω) hω.1 s βm βp hs
      (hω.2 s hs) p.1 hz p.2 p.2.property).2.2.1]
    exact isOpen_nonCoincidenceSet_of obstacleLeastSuperharmonicMajorantGeneral_holds
      hω.1 hs (hω.2 s hs) hz p.2.property
  have hv := (leastSupersolution_mem_of_general obstacleLeastSuperharmonicMajorantGeneral_holds
    obstacleCompatibilityShiftStep_holds hω.1 hR (hω.2 R hR) (hUR p.1.property) p.2.property).2.2
  have hK : IsCompact (denseSequenceClosure (cluster ((μ ω).restrict U) R p.1 p.2)) := by
    apply (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset isClosed_closure
    apply closure_minimal _ isClosed_closedBall
    exact inter_subset_left.trans (cluster_subset_ball.trans ball_subset_closedBall)
  have htest := denseSequenceClosure_subset_open_iff hU hUc hK
  have heq := regularizedFamily_compact_containment_iff_dense_restricted_cluster
    hU hR hUR p.1.property p.2.property (hΛω p.1) hopen hv
  simpa only [F, hGω] using (htest.symm.trans heq.symm)

/-- The containment predicates and the corresponding regularized family
members have simultaneous field-local representatives on a bounded open
set. The family representative agrees whenever containment holds. -/
theorem exists_local_lqg_bounded_stoppedFamily_representative
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {Λ : Ω → ℂ → ℝ → Set ℂ}
    (hΛ : ∀ᵐ ω ∂P, ∀ z, IsRegularizedClusterFamily (μ ω) (Λ ω z) z) :
    ∃ E : Ω → (U × Ioi (0 : ℝ) → Prop),
      ∃ G : Ω → (U × Ioi (0 : ℝ) → Set ℂ),
        Measurable[fieldSigmaAlgebra α₀ hC U] E ∧
        Measurable[fieldSigmaAlgebra α₀ hC U] G ∧
        ∀ᵐ ω ∂P, ∀ p, (E ω p ↔ closure (Λ ω p.1 p.2) ⊆ U) ∧
          (E ω p → G ω p = Λ ω p.1 p.2) := by
  obtain ⟨E, hE, hEeq⟩ := exists_local_lqg_bounded_compactContainmentFamily_representative
    hI2 hγ hγ2 hα hGFF hμ hloc hU hUb hΛ
  obtain ⟨F, hF, hFeq⟩ := exists_local_lqg_bounded_compact_regularizedFamily_representative
    hI2 hγ hγ2 hα hGFF hμ hloc hU hUb hΛ
  let G : Ω → (U × Ioi (0 : ℝ) → Set ℂ) := fun ω p => F ω (p.1, p.2)
  have hG : Measurable[fieldSigmaAlgebra α₀ hC U] G := by
    let : MeasurableSpace Ω := fieldSigmaAlgebra α₀ hC U
    apply Measurable.of_eval
    intro p
    exact (measurable_pi_apply ((p.1 : ℂ), p.2)).comp hF
  refine ⟨E, G, hE, hG, ?_⟩
  filter_upwards [hEeq, hFeq] with ω hEω hFω
  intro p
  exact ⟨hEω p, fun hp => hFω p.1 p.2 ((hEω p).mp hp)⟩

end HarmonicBalls
