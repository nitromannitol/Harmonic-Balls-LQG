import HarmonicBalls.Proofs.Sec5.FiniteRankBarrierCover

/-! # Locally finite accumulation rank -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Laplacian

/-- A set has locally finite accumulation rank when each compact part has
some finite rank, possibly depending on the compact set. -/
def LocallyFiniteRankOn (U K : Set ℂ) : Prop :=
  ∀ C : Set ℂ, IsCompact C → C ⊆ U → ∃ n : ℕ, LocallyFiniteRank U n (K ∩ C)

/-- A finite-rank set has locally finite accumulation rank. -/
theorem LocallyFiniteRank.locallyFiniteRankOn {U K : Set ℂ} {n : ℕ}
    (hK : LocallyFiniteRank U n K) : LocallyFiniteRankOn U K := by
  intro C _ _
  exact ⟨n, hK.mono inter_subset_left⟩

/-- Restricting the domain preserves finite accumulation rank. -/
theorem LocallyFiniteRank.mono_domain {U V K : Set ℂ} {n : ℕ}
    (hK : LocallyFiniteRank U n K) (hVU : V ⊆ U) : LocallyFiniteRank V n K := by
  induction n generalizing U V K with
  | zero =>
    intro C hC hCV
    exact hK C hC (hCV.trans hVU)
  | succ n ih =>
    obtain ⟨L, hLc, hL, hK⟩ := hK
    refine ⟨L, hLc, ih hL hVU, ?_⟩
    intro C hC hCV
    exact hK C hC (fun _ hx => ⟨hVU (hCV hx).1, (hCV hx).2⟩)

/-- A set of locally finite accumulation rank is countable inside the domain. -/
theorem countable_inter_open_of_locallyFiniteRankOn {U K : Set ℂ}
    (hU : IsOpen U) (hK : LocallyFiniteRankOn U K) : (K ∩ U).Countable := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  have hσ : IsSigmaCompact U := isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
  obtain ⟨C, hC, hcover⟩ := hσ
  have hCU : ∀ n, C n ⊆ U := by
    intro n x hx
    rw [← hcover]
    exact mem_iUnion.mpr ⟨n, hx⟩
  have hc : ∀ n, (K ∩ C n).Countable := by
    intro n
    obtain ⟨m, hm⟩ := hK (C n) (hC n) (hCU n)
    have ht : ((K ∩ C n) ∩ U).Countable :=
      countable_inter_open_of_locallyFiniteRank hU hm
    apply ht.mono
    intro x hx
    exact ⟨hx, hCU n hx.2⟩
  apply (Set.countable_iUnion hc).mono
  intro x hx
  have hxU : x ∈ ⋃ n, C n := hcover.symm ▸ hx.2
  obtain ⟨n, hn⟩ := mem_iUnion.mp hxU
  exact mem_iUnion.mpr ⟨n, hx.1, hn⟩

/-- Continuous weak supersolutions extend across sets of locally finite
accumulation rank. -/
theorem laplacianLE_zero_of_locallyFiniteRankOn_removal {U K : Set ℂ}
    (hU : IsOpen U) (hK : LocallyFiniteRankOn U K)
    {w : ℂ → ℝ} (hwc : ContinuousOn w U) (hw : LaplacianLE w 0 (U \ K)) :
    LaplacianLE w 0 U := by
  refine ⟨hwc.locallyIntegrableOn hU.measurableSet, ?_⟩
  intro φ hφ hφ0 hφμ
  obtain ⟨V, hVo, hφV, hVU, hVc⟩ :=
    exists_open_between_and_isCompact_closure hφ.2.1 hU hφ.2.2
  obtain ⟨n, hn⟩ := hK (closure V) hVc hVU
  have hVU' : V ⊆ U := subset_closure.trans hVU
  have hsub : V \ (K ∩ closure V) ⊆ U \ K := by
    intro x hx
    refine ⟨hVU' hx.1, ?_⟩
    intro hxK
    exact hx.2 ⟨hxK, subset_closure hx.1⟩
  have hlocal : LaplacianLE w 0 V :=
    laplacianLE_zero_of_locallyFiniteRank_removal hVo (hn.mono_domain hVU')
      (hwc.mono hVU') (hw.mono_set hsub)
  exact hlocal.2 φ ⟨hφ.1, hφ.2.1, hφV⟩ hφ0 hφμ

/-- Measure-valued weak supersolutions extend when the measure has a
continuous potential. -/
theorem laplacianLE_of_locallyFiniteRankOn_removal {μ : Measure ℂ}
    (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ} (hU : IsOpen U)
    (hK : LocallyFiniteRankOn U K) {w q : ℂ → ℝ}
    (hwc : ContinuousOn w U) (hqc : ContinuousOn q U)
    (hq : HasLaplacian q 0 μ U) (hw : LaplacianLE w μ (U \ K)) :
    LaplacianLE w μ U := by
  have hp := (laplacianLE_iff_add_potential hμ (hq.mono_domain sdiff_subset)).mp hw
  exact (laplacianLE_iff_add_potential hμ hq).mpr
    (laplacianLE_zero_of_locallyFiniteRankOn_removal hU hK (hwc.add hqc) hp)

/-- Compact parts of a closed set of locally finite accumulation rank have
small continuous nonnegative capped barriers. -/
theorem exists_capped_barrier_of_locallyFiniteRankOn
    {R M ε : ℝ} {K C : Set ℂ} {x : ℂ}
    (hKc : IsClosed K) (hK : LocallyFiniteRankOn (ball (0 : ℂ) R) K)
    (hC : IsCompact C) (hCU : C ⊆ ball (0 : ℂ) R)
    (hxK : x ∉ K) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ b : ℂ → ℝ, ContinuousOn b (closedBall (0 : ℂ) R) ∧
      LaplacianLE b 0 (ball (0 : ℂ) R) ∧ (∀ y, 0 ≤ b y) ∧ b x < ε ∧
      ∀ y ∈ K ∩ C, M < b y := by
  obtain ⟨n, hn⟩ := hK C hC hCU
  obtain ⟨b, hbc, hbΔ, hbn, hbx, hcover⟩ :=
    exists_capped_barrier_of_locallyFiniteRank (hKc.inter hC.isClosed) hn hC hCU
      (fun hx => hxK hx.1) hM hε
  exact ⟨b, hbc, hbΔ, hbn, hbx, fun y hy => hcover y ⟨hy, hy.2⟩⟩

/-- A supersolution on a bounded open domain minus a set of locally finite
accumulation rank extends to the whole domain. -/
theorem locallyFiniteRankOn_punctured_supersolution_mem_domain
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hK : LocallyFiniteRankOn U K)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    {z : ℂ} {t : ℝ} (ht : 0 ≤ t) {w : ℂ → ℝ}
    (hw : w ∈ supersolutionsOn μ (U \ K) z t) : w ∈ supersolutionsOn μ U z t := by
  have hcl : closure (U \ K) = closure U :=
    closure_sdiff_countable_inter hU (countable_inter_open_of_locallyFiniteRankOn hU hK)
  refine ⟨by simpa only [hcl] using hw.1, ?_, ?_⟩
  · exact laplacianLE_of_locallyFiniteRankOn_removal hμ hU hK
      (hw.1.mono (by rw [hcl]; exact subset_closure)) hqc hq hw.2.1
  · intro x hx hxz
    have hwx := hw.2.2 x (hcl ▸ hx) hxz
    have hG := Section6.greenFunction_le_of_subset (show U \ K ⊆ U from sdiff_subset) hUb z x
    nlinarith

/-- The original-domain infimum bounds the punctured-domain infimum from
below, away from the pole. -/
theorem leastSupersolutionOn_le_locallyFiniteRankOn_punctured
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hK : LocallyFiniteRankOn U K)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    {z x : ℂ} {t : ℝ} (ht : 0 ≤ t) (hx : x ∈ closure U) (hxz : x ≠ z) :
    leastSupersolutionOn μ U z t x ≤ leastSupersolutionOn μ (U \ K) z t x := by
  apply le_csInf
  · exact ⟨_, ⟨0, zero_mem_supersolutionsOn (hUb.subset sdiff_subset) ht, rfl⟩⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact leastSupersolutionOn_le_of_mem
      (locallyFiniteRankOn_punctured_supersolution_mem_domain hμ hU hUb hK hqc hq ht hw) hx hxz

end HarmonicBalls
