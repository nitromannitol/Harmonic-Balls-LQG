import HarmonicBalls.Proofs.Sec5.GeneralDomainHarmonicExtension
import HarmonicBalls.Proofs.Sec5.GeneralDomainInteriorGreen
import HarmonicBalls.Proofs.Sec5.GeneralDomainDeletionComparison

/-! # Green corrections across locally finite-rank deletions -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Laplacian InnerProductSpace

/-- The Green correction of a punctured bounded domain extends harmonically
across a closed locally finite-rank deletion. -/
theorem exists_harmonic_green_correction_of_locallyFiniteRankOn
    {U K : Set ℂ} {R : ℝ} {z : ℂ}
    (hU : IsOpen U) (hUR : U ⊆ ball (0 : ℂ) R)
    (hKc : IsClosed K) (hK : LocallyFiniteRankOn (ball (0 : ℂ) R) K)
    (hz : z ∈ U \ K) :
    ∃ H : ℂ → ℝ, HarmonicOnNhd H U ∧
      ∀ x ∈ U \ K, x ≠ z →
        greenFunction (U \ K) z x - greenFunction (ball 0 R) z x = H x := by
  have hD : IsOpen (U \ K) := hU.sdiff hKc
  have hDR : U \ K ⊆ ball (0 : ℂ) R := sdiff_subset.trans hUR
  obtain ⟨h, hh, heq⟩ := exists_harmonicOnNhd_greenFunction_difference hD
    (isBounded_ball.subset hDR) hDR hz
  have hbounded : ∀ a ∈ U, ∃ ε M : ℝ, 0 < ε ∧
      ∀ y ∈ ball a ε \ K, |h y| ≤ M := by
    intro a ha
    by_cases haK : a ∈ K
    · have haz : a ≠ z := fun h => hz.2 (h ▸ haK)
      have hcont : ContinuousAt (greenFunction (ball (0 : ℂ) R) z) a :=
        (continuousOn_greenFunction_ball (hUR hz.1)).continuousAt
          (isOpen_compl_singleton.mem_nhds haz)
      have hnear : ∀ᶠ y in 𝓝 a,
          y ∈ U ∧ y ≠ z ∧ greenFunction (ball (0 : ℂ) R) z y <
            greenFunction (ball (0 : ℂ) R) z a + 1 :=
        (show ∀ᶠ y in 𝓝 a, y ∈ U from hU.mem_nhds ha).and
          ((show ∀ᶠ y in 𝓝 a, y ≠ z from isOpen_compl_singleton.mem_nhds haz).and
          (hcont.eventually (Iio_mem_nhds (by linarith))))
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
      refine ⟨ε, greenFunction (ball (0 : ℂ) R) z a + 1, hε, ?_⟩
      intro y hy
      have hy' := hball hy.1
      have hg0 := greenFunction_nonneg (isBounded_ball.subset hDR) z y
      have hgle := Section6.greenFunction_le_of_subset hDR isBounded_ball z y
      have hhval := heq y ⟨hy'.1, hy.2⟩ hy'.2.1
      rw [abs_le]
      constructor <;> linarith [hy'.2.2]
    · have haD : a ∈ U \ K := ⟨ha, haK⟩
      have hcont : ContinuousAt h a := hh.continuousOn.continuousAt (hD.mem_nhds haD)
      have hnear : ∀ᶠ y in 𝓝 a, |h y| < |h a| + 1 :=
        hcont.norm.eventually (Iio_mem_nhds (by simp))
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
      exact ⟨ε, |h a| + 1, hε, fun y hy => le_of_lt (hball hy.1)⟩
  obtain ⟨H, hH, hHeq⟩ :=
    exists_harmonic_extension_of_locallyFiniteRankOn hU hUR hKc hK hh hbounded
  exact ⟨H, hH, fun x hx hxz => (heq x hx hxz).trans (hHeq hx).symm⟩

/-- Removing a closed locally finite-rank set preserves the Green function
at undeleted points distinct from the pole. -/
theorem greenFunction_sdiff_of_locallyFiniteRankOn
    {U K : Set ℂ} {R : ℝ} {z x : ℂ}
    (hU : IsOpen U) (hUR : U ⊆ ball (0 : ℂ) R)
    (hKc : IsClosed K) (hK : LocallyFiniteRankOn (ball (0 : ℂ) R) K)
    (hz : z ∈ U \ K) (hx : x ∈ U \ K) (hxz : x ≠ z) :
    greenFunction (U \ K) z x = greenFunction U z x := by
  obtain ⟨H, hH, hG⟩ :=
    exists_harmonic_green_correction_of_locallyFiniteRankOn hU hUR hKc hK hz
  let q : ℂ → ℝ := fun y => greatestHarmonicMinorantBall R z y - H y
  have hq : HarmonicOnNhd q U :=
    ((isHarmonicMinorant_greatestHarmonicMinorantBall (hUR hz.1)).1.mono hUR).sub hH
  have hqle : ∀ y ∈ U \ K, y ≠ z → q y ≤ newtonKernel z y := by
    intro y hy hyz
    have hg0 := greenFunction_nonneg (isBounded_ball.subset ((show U \ K ⊆ U from sdiff_subset).trans hUR)) z y
    have hgy := hG y hy hyz
    have hgdisc : greenFunction (ball 0 R) z y =
        newtonKernel z y - greatestHarmonicMinorantBall R z y := by
      rw [greenFunction, ite_eq_left ⟨hUR hz.1, hUR hy.1, Ne.symm hyz⟩,
        greatestHarmonicMinorant_ball (hUR hz.1) (hUR hy.1), EReal.toReal_coe]
    dsimp [q]
    linarith
  let V : Set ℂ := U \ {z}
  have hVo : IsOpen V := hU.sdiff isClosed_singleton
  have hcount : (K ∩ V).Countable :=
    (countable_inter_open_of_locallyFiniteRankOn hU (hK.mono_domain hUR)).mono
      (show K ∩ V ⊆ K ∩ U from fun _ hy => ⟨hy.1, hy.2.1⟩)
  have hcl : closure (V \ K) = closure V := closure_sdiff_countable_inter hVo hcount
  have hqleV : ∀ y ∈ V, q y ≤ newtonKernel z y := by
    intro y hy
    have hycl : y ∈ closure (V \ K) := by rw [hcl]; exact subset_closure hy
    let : (𝓝[V \ K] y).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hycl
    have hcq : ContinuousAt q y := (hq y hy.1).1.continuousAt
    have hcn : ContinuousAt (newtonKernel z) y :=
      (harmonicAt_newtonKernel (by simpa using hy.2)).1.continuousAt
    apply le_of_tendsto_of_tendsto (b := 𝓝[V \ K] y) (hcq.tendsto.mono_left nhdsWithin_le_nhds)
      (hcn.tendsto.mono_left nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact hqle w ⟨hw.1.1, hw.2⟩ (by simpa using hw.1.2)
  have hminor : IsHarmonicMinorant U (newtonKernelEReal z) q := by
    refine ⟨hq, ?_⟩
    intro y hy
    by_cases hyz : y = z
    · simp [newtonKernelEReal, hyz]
    · simpa [newtonKernelEReal, hyz] using hqleV y ⟨hy, by simpa using hyz⟩
  have hlow := hminor.le_greatestHarmonicMinorant x
  have hupp : greatestHarmonicMinorant U (newtonKernelEReal z) x ≤
      (newtonKernel z x : EReal) := by
    simpa [newtonKernelEReal, hxz] using greatestHarmonicMinorant_le
      (u := newtonKernelEReal z) hx.1
  have hqbound : q x ≤ (greatestHarmonicMinorant U (newtonKernelEReal z) x).toReal := by
    have := EReal.toReal_le_toReal hlow (EReal.coe_ne_bot _)
      (ne_top_of_le_ne_top (EReal.coe_ne_top _) hupp)
    simpa only [EReal.toReal_coe] using this
  have hdisc : greenFunction (ball 0 R) z x =
      newtonKernel z x - greatestHarmonicMinorantBall R z x := by
    rw [greenFunction, ite_eq_left ⟨hUR hz.1, hUR hx.1, Ne.symm hxz⟩,
      greatestHarmonicMinorant_ball (hUR hz.1) (hUR hx.1), EReal.toReal_coe]
  have hfull : greenFunction U z x =
      newtonKernel z x - (greatestHarmonicMinorant U (newtonKernelEReal z) x).toReal := by
    rw [greenFunction, ite_eq_left ⟨hz.1, hx.1, Ne.symm hxz⟩]
  have hmono := Section6.greenFunction_le_of_subset (show U \ K ⊆ U from sdiff_subset)
    (isBounded_ball.subset hUR) z x
  have hpunct := hG x hx hxz
  dsimp [q] at hqbound
  rw [hdisc] at hpunct
  rw [hfull]
  linarith

/-- A full-domain supersolution that vanishes at the interior deleted points
is also a supersolution after deletion. -/
theorem supersolution_mem_sdiff_of_locallyFiniteRankOn_interior_zero
    {μ : Measure ℂ} {U K : Set ℂ} {R t : ℝ} {z : ℂ} {w : ℂ → ℝ}
    (hU : IsOpen U) (hUR : U ⊆ ball (0 : ℂ) R)
    (hKc : IsClosed K) (hK : LocallyFiniteRankOn (ball (0 : ℂ) R) K)
    (hz : z ∈ U \ K) (hw : w ∈ supersolutionsOn μ U z t)
    (hzero : ∀ a ∈ K, a ∈ U → w a = 0) :
    w ∈ supersolutionsOn μ (U \ K) z t := by
  have hcl : closure (U \ K) ⊆ closure U := closure_mono sdiff_subset
  refine ⟨hw.1.mono hcl, hw.2.1.mono_set sdiff_subset, ?_⟩
  intro y hy hyz
  by_cases hyK : y ∈ K
  · have hynot : y ∉ U \ K := fun h => h.2 hyK
    rw [greenFunction_of_notMem_right hynot, mul_zero]
    by_cases hyU : y ∈ U
    · rw [hzero y hyK hyU]
    · have h := hw.2.2 y (hcl hy) hyz
      rwa [greenFunction_of_notMem_right hyU, mul_zero] at h
  · by_cases hyU : y ∈ U
    · rw [greenFunction_sdiff_of_locallyFiniteRankOn hU hUR hKc hK hz ⟨hyU, hyK⟩ hyz]
      exact hw.2.2 y (hcl hy) hyz
    · have hynot : y ∉ U \ K := fun h => hyU h.1
      have h := hw.2.2 y (hcl hy) hyz
      rw [greenFunction_of_notMem_right hyU, mul_zero] at h
      rwa [greenFunction_of_notMem_right hynot, mul_zero]


/-- With an admissible full-domain least supersolution, deleting a closed
locally finite-rank set deletes exactly its points from the cluster. -/
theorem clusterOn_sdiff_of_locallyFiniteRankOn
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ}
    {R t : ℝ} {z : ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUR : closure U ⊆ ball (0 : ℂ) R) (hKc : IsClosed K)
    (hK : LocallyFiniteRankOn (ball (0 : ℂ) R) K) (hz : z ∈ U \ K)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 ≤ t)
    (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t) :
    clusterOn μ (U \ K) z t = clusterOn μ U z t \ K := by
  apply clusterOn_locallyFiniteRankOn_punctured_eq_sdiff_of_green_eq
    hμ hU hUb hUR hKc hK hqc hq ht ?_ hw
  intro y hy hyz
  exact greenFunction_sdiff_of_locallyFiniteRankOn hU (subset_closure.trans hUR)
    hKc hK hz hy hyz

/-- Under the same hypotheses, openness of the full-domain cluster implies
that deleting the set does not change its closure. -/
theorem closure_clusterOn_sdiff_of_locallyFiniteRankOn
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ}
    {R t : ℝ} {z : ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUR : closure U ⊆ ball (0 : ℂ) R) (hKc : IsClosed K)
    (hK : LocallyFiniteRankOn (ball (0 : ℂ) R) K) (hz : z ∈ U \ K)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 ≤ t)
    (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hopen : IsOpen (clusterOn μ U z t)) :
    closure (clusterOn μ (U \ K) z t) = closure (clusterOn μ U z t) := by
  apply closure_clusterOn_locallyFiniteRankOn_punctured_eq_of_green_eq
    hμ hU hUb hUR hKc hK hqc hq ht ?_ hw hopen
  intro y hy hyz
  exact greenFunction_sdiff_of_locallyFiniteRankOn hU (subset_closure.trans hUR)
    hKc hK hz hy hyz

/-- Admissibility of the punctured least supersolution forces the full-domain
least supersolution to vanish at every deleted interior point. -/
theorem leastSupersolutionOn_eq_zero_of_sdiff_admissible
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ}
    {R t : ℝ} {z : ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUR : closure U ⊆ ball (0 : ℂ) R) (hKc : IsClosed K)
    (hK : LocallyFiniteRankOn (ball (0 : ℂ) R) K) (hz : z ∈ U \ K)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 ≤ t)
    (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hadm : leastSupersolutionOn μ (U \ K) z t ∈ supersolutionsOn μ (U \ K) z t)
    {a : ℂ} (haK : a ∈ K) (haU : a ∈ U) :
    leastSupersolutionOn μ U z t a = 0 := by
  have haz : a ≠ z := fun h => hz.2 (h ▸ haK)
  let V : Set ℂ := U \ {z}
  have hVo : IsOpen V := hU.sdiff isClosed_singleton
  have hcount : (K ∩ V).Countable :=
    (countable_inter_open_of_locallyFiniteRankOn hU
      (hK.mono_domain (subset_closure.trans hUR))).mono
      (show K ∩ V ⊆ K ∩ U from fun _ hy => ⟨hy.1, hy.2.1⟩)
  have hclV : closure (V \ K) = closure V := closure_sdiff_countable_inter hVo hcount
  have hclU : closure (U \ K) = closure U := closure_sdiff_countable_inter hU
    (countable_inter_open_of_locallyFiniteRankOn hU
      (hK.mono_domain (subset_closure.trans hUR)))
  have heq : EqOn (leastSupersolutionOn μ (U \ K) z t)
      (leastSupersolutionOn μ U z t) (V \ K) := by
    intro y hy
    exact leastSupersolutionOn_locallyFiniteRankOn_punctured_eq_of_green_eq
      hμ hU hUb hUR hKc hK hqc hq ht
      (fun w hw hwz => greenFunction_sdiff_of_locallyFiniteRankOn hU
        (subset_closure.trans hUR) hKc hK hz hw hwz)
      hw ⟨hy.1.1, hy.2⟩ (by simpa using hy.1.2)
  have heqV := heq.of_subset_closure
    (hadm.1.mono (by rw [hclU]; exact sdiff_subset.trans subset_closure))
    (hw.1.mono (sdiff_subset.trans subset_closure)) sdiff_subset
    (by rw [hclV]; exact subset_closure)
  have haV : a ∈ V := ⟨haU, by simpa using haz⟩
  have haCl : a ∈ closure (U \ K) := by rw [hclU]; exact subset_closure haU
  have hzero := leastSupersolutionOn_eq_zero_of_boundary (μ := μ)
    (hUb.subset (show U \ K ⊆ U from sdiff_subset)) ht haCl
    (show a ∉ U \ K from fun ha => ha.2 haK) haz
  exact (heqV haV).symm.trans hzero

/-- Vanishing of the full-domain least supersolution on the deleted interior
points is sufficient for admissibility after deletion. -/
theorem leastSupersolutionOn_mem_sdiff_of_interior_zero
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ}
    {R t : ℝ} {z : ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUR : U ⊆ ball (0 : ℂ) R) (hKc : IsClosed K)
    (hK : LocallyFiniteRankOn (ball (0 : ℂ) R) K) (hz : z ∈ U \ K)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 ≤ t)
    (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hzero : ∀ a ∈ K, a ∈ U → leastSupersolutionOn μ U z t a = 0) :
    leastSupersolutionOn μ (U \ K) z t ∈ supersolutionsOn μ (U \ K) z t := by
  have hv := supersolution_mem_sdiff_of_locallyFiniteRankOn_interior_zero
    hU hUR hKc hK hz hw hzero
  have hcl : closure (U \ K) = closure U := closure_sdiff_countable_inter hU
    (countable_inter_open_of_locallyFiniteRankOn hU (hK.mono_domain hUR))
  have hbound : ∀ x ∈ closure U, ∀ w ∈ supersolutionsOn μ (U \ K) z t,
      leastSupersolutionOn μ U z t x ≤ w x := by
    intro x hx w hw'
    have hwU := locallyFiniteRankOn_punctured_supersolution_mem_domain hμ hU hUb
      (hK.mono_domain hUR) hqc hq ht hw'
    by_cases hxz : x = z
    · subst x
      have hcv : ContinuousAt (leastSupersolutionOn μ U z t) z :=
        (hw.1.mono subset_closure).continuousAt (hU.mem_nhds hz.1)
      have hcw : ContinuousAt w z :=
        (hwU.1.mono subset_closure).continuousAt (hU.mem_nhds hz.1)
      have : (𝓝[{z}ᶜ] z).NeBot := by
        apply mem_closure_iff_nhdsWithin_neBot.mp
        exact (dense_compl_singleton z) z
      apply le_of_tendsto_of_tendsto (b := 𝓝[{z}ᶜ] z)
        (hcv.tendsto.mono_left nhdsWithin_le_nhds)
        (hcw.tendsto.mono_left nhdsWithin_le_nhds)
      filter_upwards [(show ∀ᶠ y in 𝓝 z, y ∈ U from hU.mem_nhds hz.1).filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with y hyU hyz
      exact leastSupersolutionOn_le_of_mem hwU (subset_closure hyU) (by simpa using hyz)
    · exact leastSupersolutionOn_le_of_mem hwU hx hxz
  have heq : EqOn (leastSupersolutionOn μ (U \ K) z t)
      (leastSupersolutionOn μ U z t) (closure U) := by
    intro x hx
    have hbdd : BddBelow ((fun w : ℂ → ℝ => w x) '' supersolutionsOn μ (U \ K) z t) := by
      refine ⟨leastSupersolutionOn μ U z t x, ?_⟩
      rintro _ ⟨w, hw', rfl⟩
      exact hbound x hx w hw'
    apply le_antisymm
    · exact csInf_le hbdd ⟨_, hv, rfl⟩
    · apply le_csInf (show ((fun w : ℂ → ℝ => w x) '' supersolutionsOn μ (U \ K) z t).Nonempty from ⟨_, ⟨_, hv, rfl⟩⟩)
      rintro _ ⟨w, hw', rfl⟩
      exact hbound x hx w hw'
  have hD : IsOpen (U \ K) := hU.sdiff hKc
  refine ⟨hv.1.congr (heq.mono (by rw [hcl])), ?_, ?_⟩
  · exact hv.2.1.congr_eqOn hD.measurableSet
      (heq.symm.mono (sdiff_subset.trans subset_closure))
  · intro x hx hxz
    rw [heq (hcl ▸ hx)]
    exact hv.2.2 x hx hxz

/-- The punctured least supersolution is admissible exactly when the
full-domain least supersolution vanishes at all deleted interior points. -/
theorem leastSupersolutionOn_mem_sdiff_iff_interior_zero
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ}
    {R t : ℝ} {z : ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUR : closure U ⊆ ball (0 : ℂ) R) (hKc : IsClosed K)
    (hK : LocallyFiniteRankOn (ball (0 : ℂ) R) K) (hz : z ∈ U \ K)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 ≤ t)
    (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t) :
    leastSupersolutionOn μ (U \ K) z t ∈ supersolutionsOn μ (U \ K) z t ↔
      ∀ a ∈ K, a ∈ U → leastSupersolutionOn μ U z t a = 0 := by
  constructor
  · intro hadm a haK haU
    exact leastSupersolutionOn_eq_zero_of_sdiff_admissible
      hμ hU hUb hUR hKc hK hz hqc hq ht hw hadm haK haU
  · exact leastSupersolutionOn_mem_sdiff_of_interior_zero
      hμ hU hUb (subset_closure.trans hUR) hKc hK hz hqc hq ht hw







end HarmonicBalls
