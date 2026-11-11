import HarmonicBalls.Proofs.Sec5.CountableBarrierCover
import HarmonicBalls.Proofs.Sec5.RelativelyClosedDeletionLocality

/-! # Locally countable deletions -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Laplacian InnerProductSpace

/-- Locally bounded harmonic functions extend across a closed deletion with
countability inside the domain itself. -/
theorem exists_harmonic_extension_of_local_countable
    {U K : Set ℂ} {h : ℂ → ℝ}
    (hU : IsOpen U) (hKclosed : IsClosed K) (hK : (K ∩ U).Countable)
    (hh : HarmonicOnNhd h (U \ K))
    (hbounded : ∀ a ∈ U, ∃ ε M : ℝ, 0 < ε ∧
      ∀ y ∈ ball a ε \ K, |h y| ≤ M) :
    ∃ H : ℂ → ℝ, HarmonicOnNhd H U ∧ EqOn H h (U \ K) := by
  classical
  have hex : ∀ a : U, ∃ r : ℝ, 0 < r ∧ ∃ q : ℂ → ℝ,
      HarmonicOnNhd q (ball (a : ℂ) r) ∧ EqOn q h (ball (a : ℂ) r \ K) := by
    intro a
    obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp hU a a.property
    let r := δ / 2
    have hr : 0 < r := by dsimp [r]; linarith
    have hcl : closedBall (a : ℂ) r ⊆ U :=
      (closedBall_subset_ball (by dsimp [r]; linarith)).trans hδU
    have hcount' : (K ∩ closedBall (a : ℂ) r).Countable := hK.mono (by
      intro x hx
      exact ⟨hx.1, hcl hx.2⟩)
    have hsub : ball (a : ℂ) r ⊆ ball (0 : ℂ) (‖(a : ℂ)‖ + δ + 1) := by
      intro x hx
      rw [mem_ball, dist_zero_right]
      have hx' : dist x (a : ℂ) < r := hx
      have ht : ‖x‖ ≤ ‖x - (a : ℂ)‖ + ‖(a : ℂ)‖ := by
        simpa only [sub_add_cancel] using norm_add_le (x - (a : ℂ)) (a : ℂ)
      rw [dist_eq_norm] at hx'
      dsimp [r] at *
      linarith
    have heq : ball (a : ℂ) r \ (K ∩ closedBall (a : ℂ) r) =
        ball (a : ℂ) r \ K := by
      ext x
      simp only [Set.mem_sdiff, mem_inter_iff]
      constructor
      · rintro ⟨hx, hn⟩
        exact ⟨hx, fun hk => hn ⟨hk, ball_subset_closedBall hx⟩⟩
      · rintro ⟨hx, hn⟩
        exact ⟨hx, fun hk => hn hk.1⟩
    have hb : ∀ x ∈ ball (a : ℂ) r, ∃ ε M : ℝ, 0 < ε ∧
        ∀ y ∈ ball x ε \ (K ∩ closedBall (a : ℂ) r), |h y| ≤ M := by
      intro x hx
      obtain ⟨ε, M, hε, hb⟩ := hbounded x (hcl (ball_subset_closedBall hx))
      obtain ⟨η, hη, hηsub⟩ := Metric.isOpen_iff.mp isOpen_ball x hx
      refine ⟨min ε η, M, lt_min hε hη, ?_⟩
      intro y hy
      apply hb y
      refine ⟨(ball_subset_ball (min_le_left _ _)) hy.1, ?_⟩
      intro hyK
      exact hy.2 ⟨hyK, ball_subset_closedBall (hηsub ((ball_subset_ball (min_le_right _ _)) hy.1))⟩
    obtain ⟨q, hq, hqh⟩ := exists_harmonic_extension_of_countable
      isOpen_ball hsub (hKclosed.inter isClosed_closedBall) hcount'
      (by rw [heq]; exact hh.mono (fun _ hx => ⟨hcl (ball_subset_closedBall hx.1), hx.2⟩)) hb
    exact ⟨r, hr, q, hq, by simpa only [heq] using hqh⟩
  let r : U → ℝ := fun a => Classical.choose (hex a)
  have hr : ∀ a : U, 0 < r a := fun a => (Classical.choose_spec (hex a)).1
  let q : U → ℂ → ℝ := fun a => Classical.choose (Classical.choose_spec (hex a)).2
  have hq : ∀ a : U, HarmonicOnNhd (q a) (ball (a : ℂ) (r a)) ∧
      EqOn (q a) h (ball (a : ℂ) (r a) \ K) :=
    fun a => Classical.choose_spec (Classical.choose_spec (hex a)).2
  let H : ℂ → ℝ := fun x => if hx : x ∈ U then q ⟨x, hx⟩ x else 0
  have hcount : (K ∩ U).Countable := hK
  have hagree : ∀ a : U, ∀ x ∈ U ∩ ball (a : ℂ) (r a), H x = q a x := by
    intro a x hx
    let b : U := ⟨x, hx.1⟩
    let V : Set ℂ := U ∩ ball (a : ℂ) (r a) ∩ ball (b : ℂ) (r b)
    have hV : IsOpen V := (hU.inter isOpen_ball).inter isOpen_ball
    have hxV : x ∈ V := ⟨hx, mem_ball_self (hr b)⟩
    have hcountV : (K ∩ V).Countable := hcount.mono (by
      intro y hy; exact ⟨hy.1, hy.2.1.1⟩)
    have hcl : closure (V \ K) = closure V := closure_sdiff_countable_inter hV hcountV
    have heq : EqOn (q b) (q a) (V \ K) := by
      intro y hy
      exact ((hq b).2 ⟨hy.1.2, hy.2⟩).trans
        (((hq a).2 ⟨hy.1.1.2, hy.2⟩).symm)
    have heqV : EqOn (q b) (q a) V := heq.of_subset_closure
      ((hq b).1.continuousOn.mono (fun _ hy => hy.2))
      ((hq a).1.continuousOn.mono (fun _ hy => hy.1.2)) sdiff_subset
      (by rw [hcl]; exact subset_closure)
    simpa only [H, dite_eq_left hx.1] using heqV hxV
  refine ⟨H, ?_, ?_⟩
  · intro a ha
    let b : U := ⟨a, ha⟩
    apply (harmonicAt_congr_nhds (f₁ := q b) (f₂ := H) ?_).mp
      ((hq b).1 a (mem_ball_self (hr b)))
    filter_upwards [(hU.inter isOpen_ball).mem_nhds
      (show a ∈ U ∩ ball (b : ℂ) (r b) from ⟨ha, mem_ball_self (hr b)⟩)] with x hx
    exact (hagree b x hx).symm
  · intro x hx
    let b : U := ⟨x, hx.1⟩
    exact (hagree b x ⟨hx.1, mem_ball_self (hr b)⟩).trans
      ((hq b).2 ⟨mem_ball_self (hr b), hx.2⟩)

/-- The Green correction of a punctured bounded domain extends harmonically
across a deletion that is countable inside the domain. -/
theorem exists_harmonic_green_correction_of_local_countable
    {U K : Set ℂ} {R : ℝ} {z : ℂ}
    (hU : IsOpen U) (hUR : U ⊆ ball (0 : ℂ) R)
    (hKc : IsClosed K) (hK : (K ∩ U).Countable)
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
    exists_harmonic_extension_of_local_countable hU hKc hK hh hbounded
  exact ⟨H, hH, fun x hx hxz => (heq x hx hxz).trans (hHeq hx).symm⟩

/-- Removing a closed set that is countable inside the domain preserves its Green function
at undeleted points distinct from the pole. -/
theorem greenFunction_sdiff_of_local_countable
    {U K : Set ℂ} {R : ℝ} {z x : ℂ}
    (hU : IsOpen U) (hUR : U ⊆ ball (0 : ℂ) R)
    (hKc : IsClosed K) (hK : (K ∩ U).Countable)
    (hz : z ∈ U \ K) (hx : x ∈ U \ K) (hxz : x ≠ z) :
    greenFunction (U \ K) z x = greenFunction U z x := by
  obtain ⟨H, hH, hG⟩ :=
    exists_harmonic_green_correction_of_local_countable hU hUR hKc hK hz
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
    (hK).mono
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

/-- Continuous weak supersolutions extend across closed locally countable sets. -/
theorem laplacianLE_zero_of_local_countable_removal {U K : Set ℂ}
    (hU : IsOpen U) (hKc : IsClosed K) (hK : (K ∩ U).Countable)
    {w : ℂ → ℝ} (hwc : ContinuousOn w U) (hw : LaplacianLE w 0 (U \ K)) :
    LaplacianLE w 0 U := by
  refine ⟨hwc.locallyIntegrableOn hU.measurableSet, ?_⟩
  intro φ hφ hφ0 hφμ
  obtain ⟨V, hVo, hφV, hVU, hVc⟩ :=
    exists_open_between_and_isCompact_closure hφ.2.1 hU hφ.2.2
  have hcount : (K ∩ closure V).Countable := hK.mono (by
    intro x hx
    exact ⟨hx.1, hVU hx.2⟩)
  have hVU' : V ⊆ U := subset_closure.trans hVU
  have hsub : V \ (K ∩ closure V) ⊆ U \ K := by
    intro x hx
    refine ⟨hVU' hx.1, ?_⟩
    intro hxK
    exact hx.2 ⟨hxK, subset_closure hx.1⟩
  have hlocal : LaplacianLE w 0 V :=
    laplacianLE_zero_of_countable_removal hVo (hKc.inter isClosed_closure) hcount
      (hwc.mono hVU') (hw.mono_set hsub)
  exact hlocal.2 φ ⟨hφ.1, hφ.2.1, hφV⟩ hφ0 hφμ

/-- Measure-valued weak supersolutions extend when the measure has a
continuous potential. -/
theorem laplacianLE_of_local_countable_removal {μ : Measure ℂ}
    (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ} (hU : IsOpen U)
    (hKc : IsClosed K) (hK : (K ∩ U).Countable) {w q : ℂ → ℝ}
    (hwc : ContinuousOn w U) (hqc : ContinuousOn q U)
    (hq : HasLaplacian q 0 μ U) (hw : LaplacianLE w μ (U \ K)) :
    LaplacianLE w μ U := by
  have hp := (laplacianLE_iff_add_potential hμ (hq.mono_domain sdiff_subset)).mp hw
  exact (laplacianLE_iff_add_potential hμ hq).mpr
    (laplacianLE_zero_of_local_countable_removal hU hKc hK (hwc.add hqc) hp)

/-- A supersolution extends from a bounded open domain with a closed locally countable set removed. -/
theorem local_countable_punctured_supersolution_mem_domain
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hKc : IsClosed K) (hK : (K ∩ U).Countable)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    {z : ℂ} {t : ℝ} (ht : 0 ≤ t) {w : ℂ → ℝ}
    (hw : w ∈ supersolutionsOn μ (U \ K) z t) : w ∈ supersolutionsOn μ U z t := by
  have hcl : closure (U \ K) = closure U :=
    closure_sdiff_countable_inter hU (hK)
  refine ⟨by simpa only [hcl] using hw.1, ?_, ?_⟩
  · exact laplacianLE_of_local_countable_removal hμ hU hKc hK
      (hw.1.mono (by rw [hcl]; exact subset_closure)) hqc hq hw.2.1
  · intro x hx hxz
    have hwx := hw.2.2 x (hcl ▸ hx) hxz
    have hG := Section6.greenFunction_le_of_subset (show U \ K ⊆ U from sdiff_subset) hUb z x
    nlinarith

/-- The original-domain infimum bounds the punctured-domain infimum from
below, away from the pole. -/
theorem leastSupersolutionOn_le_local_countable_punctured
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hKc : IsClosed K) (hK : (K ∩ U).Countable)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    {z x : ℂ} {t : ℝ} (ht : 0 ≤ t) (hx : x ∈ closure U) (hxz : x ≠ z) :
    leastSupersolutionOn μ U z t x ≤ leastSupersolutionOn μ (U \ K) z t x := by
  apply le_csInf
  · exact ⟨_, ⟨0, zero_mem_supersolutionsOn (hUb.subset sdiff_subset) ht, rfl⟩⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact leastSupersolutionOn_le_of_mem
      (local_countable_punctured_supersolution_mem_domain hμ hU hUb hKc hK hqc hq ht hw) hx hxz


/-- A full-domain supersolution has arbitrarily close competitors after
removing a locally countable closed set. -/
theorem leastSupersolutionOn_sdiff_le_supersolution_of_local_countable
    {μ : Measure ℂ} {U K : Set ℂ} {R t : ℝ} {z x : ℂ} {w : ℂ → ℝ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUR : closure U ⊆ ball (0 : ℂ) R)
    (hKc : IsClosed K) (hK : (K ∩ U).Countable)
    (hz : z ∈ U \ K) (hx : x ∈ U \ K) (hxz : x ≠ z)
    (hw : w ∈ supersolutionsOn μ U z t) :
    leastSupersolutionOn μ (U \ K) z t x ≤ w x := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε / 2
  have hδ : 0 < δ := half_pos hε
  let C : Set ℂ := closure U ∩ w ⁻¹' Iic (-δ)
  have hCc : IsClosed C := hw.1.preimage_isClosed_of_isClosed isClosed_closure isClosed_Iic
  have hC : IsCompact C := hUb.isCompact_closure.of_isClosed_subset hCc inter_subset_left
  have hCU : C ⊆ U := by
    intro y hy
    by_contra hyU
    have hyz : y ≠ z := fun heq => hyU (heq ▸ hz.1)
    have hwbound := hw.2.2 y hy.1 hyz
    rw [greenFunction_of_notMem_right hyU, mul_zero] at hwbound
    have hyw : w y ≤ -δ := hy.2
    linarith
  have hcount' : (K ∩ C).Countable := hK.mono (by
    intro y hy
    exact ⟨hy.1, hCU hy.2⟩)
  obtain ⟨B, hB⟩ := hUb.isCompact_closure.exists_bound_of_continuousOn hw.1
  let M := max B 0
  have hM : 0 ≤ M := le_max_right B 0
  obtain ⟨b, hbc, hbΔ, hbn, hsmall, hcover⟩ :=
    exists_capped_barrier_of_countable (hKc.inter hCc) hcount'
      hC (hCU.trans (subset_closure.trans hUR)) (fun hy => hx.2 hy.1) hM hδ
  have hcl : closure (U \ K) ⊆ closure U := closure_mono sdiff_subset
  let v : ℂ → ℝ := fun y => w y + δ + b y
  have hv : v ∈ supersolutionsOn μ (U \ K) z t := by
    refine ⟨((hw.1.add continuousOn_const).add
      (hbc.mono (hUR.trans ball_subset_closedBall))).mono hcl, ?_, ?_⟩
    · have hc := hasLaplacian_zero_of_harmonicOnNhd (U := U) hU
        (harmonicOnNhd_const (1 : ℝ))
      have hwδ : LaplacianLE (fun y => w y + δ) μ U := by
        simpa only [mul_one] using hw.2.1.add_const_mul_of_hasLaplacian_zero hc δ
      exact (hwδ.add_of_nonpos (hbΔ.mono_set (subset_closure.trans hUR))).mono_set sdiff_subset
    · intro y hy hyz
      have hycl := hcl hy
      by_cases hyK : y ∈ K
      · have hynot : y ∉ U \ K := fun h => h.2 hyK
        rw [greenFunction_of_notMem_right hynot, mul_zero]
        by_cases hyC : y ∈ C
        · have hcov := hcover y ⟨⟨hyK, hyC⟩, hyC⟩
          have hbound : ‖w y‖ ≤ M := (hB y hycl).trans (le_max_left B 0)
          have habs : -‖w y‖ ≤ w y := by simpa only [Real.norm_eq_abs] using neg_abs_le (w y)
          dsimp [v]
          linarith
        · have htail : -δ < w y := by
            have : ¬ w y ≤ -δ := fun hyw => hyC ⟨hycl, hyw⟩
            exact lt_of_not_ge this
          dsimp [v]
          linarith [hbn y]
      · by_cases hyU : y ∈ U
        · rw [greenFunction_sdiff_of_local_countable hU (subset_closure.trans hUR) hKc hK
            hz ⟨hyU, hyK⟩ hyz]
          dsimp [v]
          linarith [hw.2.2 y hycl hyz, hbn y]
        · have hynot : y ∉ U \ K := fun h => hyU h.1
          have hwbound := hw.2.2 y hycl hyz
          rw [greenFunction_of_notMem_right hyU, mul_zero] at hwbound
          rw [greenFunction_of_notMem_right hynot, mul_zero]
          dsimp [v]
          linarith [hbn y]
  have hle := leastSupersolutionOn_le_of_mem hv (subset_closure hx) hxz
  dsimp [v, δ] at hle hsmall ⊢
  linarith

/-- The two least supersolutions agree away from a locally countable deletion
and the pole, provided the full-domain infimum is admissible. -/
theorem leastSupersolutionOn_sdiff_eq_of_local_countable
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ}
    {R t : ℝ} {z x : ℂ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUR : closure U ⊆ ball (0 : ℂ) R)
    (hKc : IsClosed K) (hK : (K ∩ U).Countable)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 ≤ t) (hz : z ∈ U \ K)
    (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hx : x ∈ U \ K) (hxz : x ≠ z) :
    leastSupersolutionOn μ (U \ K) z t x = leastSupersolutionOn μ U z t x := by
  exact le_antisymm
    (leastSupersolutionOn_sdiff_le_supersolution_of_local_countable hU hUb hUR hKc hK hz hx hxz hw)
    (leastSupersolutionOn_le_local_countable_punctured hμ hU hUb hKc hK hqc hq ht
      (subset_closure hx.1) hxz)

/-- Deleting a closed set that is countable inside the domain deletes
exactly those points from the cluster. -/
theorem clusterOn_sdiff_of_local_countable
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ}
    {R t : ℝ} {z : ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUR : closure U ⊆ ball (0 : ℂ) R)
    (hKc : IsClosed K) (hK : (K ∩ U).Countable)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 ≤ t) (hz : z ∈ U \ K)
    (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t) :
    clusterOn μ (U \ K) z t = clusterOn μ U z t \ K := by
  ext x
  constructor
  · rintro ⟨hx, hxz | hxpos⟩
    · exact ⟨⟨hx.1, Or.inl hxz⟩, hx.2⟩
    · refine ⟨⟨hx.1, ?_⟩, hx.2⟩
      by_cases hxz : x = z
      · exact Or.inl hxz
      · right
        rw [greenFunction_sdiff_of_local_countable hU (subset_closure.trans hUR) hKc hK hz hx hxz,
          leastSupersolutionOn_sdiff_eq_of_local_countable hμ hU hUb hUR hKc hK hqc hq ht hz hw hx hxz] at hxpos
        exact hxpos
  · rintro ⟨⟨hx, hxz | hxpos⟩, hxK⟩
    · exact ⟨⟨hx, hxK⟩, Or.inl hxz⟩
    · refine ⟨⟨hx, hxK⟩, ?_⟩
      by_cases hxz : x = z
      · exact Or.inl hxz
      · right
        rw [greenFunction_sdiff_of_local_countable hU (subset_closure.trans hUR) hKc hK hz ⟨hx, hxK⟩ hxz,
          leastSupersolutionOn_sdiff_eq_of_local_countable hμ hU hUb hUR hKc hK hqc hq ht hz hw ⟨hx, hxK⟩ hxz]
        exact hxpos

/-- If the full cluster is open, its closure is unchanged by a closed
locally countable deletion, including deletion sets accumulating at the boundary. -/
theorem closure_clusterOn_sdiff_of_local_countable
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ}
    {R t : ℝ} {z : ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUR : closure U ⊆ ball (0 : ℂ) R)
    (hKc : IsClosed K) (hK : (K ∩ U).Countable)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 ≤ t) (hz : z ∈ U \ K)
    (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hopen : IsOpen (clusterOn μ U z t)) :
    closure (clusterOn μ (U \ K) z t) = closure (clusterOn μ U z t) := by
  rw [clusterOn_sdiff_of_local_countable hμ hU hUb hUR hKc hK hqc hq ht hz hw]
  apply closure_sdiff_countable_inter hopen
  apply (hK).mono
  intro x hx
  exact ⟨hx.1, hx.2.1⟩


/-- Green functions are unchanged by relatively closed, locally countable
deletions at points remaining in the domain. -/
theorem greenFunction_sdiff_of_relative_countable
    {U K : Set ℂ} {R : ℝ} {z x : ℂ}
    (hU : IsOpen U) (hUR : U ⊆ ball (0 : ℂ) R)
    (hD : IsOpen (U \ K)) (hK : (K ∩ U).Countable)
    (hz : z ∈ U \ K) (hx : x ∈ U \ K) (hxz : x ≠ z) :
    greenFunction (U \ K) z x = greenFunction U z x := by
  have heq := sdiff_closure_inter_eq_of_isOpen_sdiff hD
  have hg := greenFunction_sdiff_of_local_countable hU hUR isClosed_closure
    (by simpa only [closure_inter_eq_inter_of_isOpen_sdiff hD] using hK)
    (heq ▸ hz) (heq ▸ hx) hxz
  simpa only [heq] using hg

/-- A relatively closed deletion that is countable inside the domain removes exactly its
points from the cluster, under full-domain obstacle admissibility. -/
theorem clusterOn_sdiff_of_relative_countable
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ}
    {R t : ℝ} {z : ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUR : closure U ⊆ ball (0 : ℂ) R)
    (hD : IsOpen (U \ K)) (hK : (K ∩ U).Countable)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 ≤ t) (hz : z ∈ U \ K)
    (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t) :
    clusterOn μ (U \ K) z t = clusterOn μ U z t \ K := by
  have heq := sdiff_closure_inter_eq_of_isOpen_sdiff hD
  have hc := clusterOn_sdiff_of_local_countable hμ hU hUb hUR isClosed_closure
    (by simpa only [closure_inter_eq_inter_of_isOpen_sdiff hD] using hK) hqc hq ht (heq ▸ hz) hw
  rw [heq] at hc
  rw [hc]
  ext x
  constructor
  · rintro ⟨hx, hxK⟩
    exact ⟨hx, fun hx' => hxK (subset_closure ⟨hx.1, hx'⟩)⟩
  · rintro ⟨hx, hxK⟩
    exact ⟨hx, fun hxcl => hxK
      ((Set.ext_iff.mp (closure_inter_eq_inter_of_isOpen_sdiff hD) x).mp ⟨hxcl, hx.1⟩).1⟩

/-- Under full-cluster openness, relatively closed countable deletions do
not change the cluster closure. -/
theorem closure_clusterOn_sdiff_of_relative_countable
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ}
    {R t : ℝ} {z : ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUR : closure U ⊆ ball (0 : ℂ) R)
    (hD : IsOpen (U \ K)) (hK : (K ∩ U).Countable)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 ≤ t) (hz : z ∈ U \ K)
    (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hopenU : IsOpen (clusterOn μ U z t)) :
    closure (clusterOn μ (U \ K) z t) = closure (clusterOn μ U z t) := by
  have heq := sdiff_closure_inter_eq_of_isOpen_sdiff hD
  have hc := closure_clusterOn_sdiff_of_local_countable hμ hU hUb hUR isClosed_closure
    (by simpa only [closure_inter_eq_inter_of_isOpen_sdiff hD] using hK) hqc hq ht (heq ▸ hz) hw hopenU
  simpa only [heq] using hc


/-- A compactly contained punctured-domain cluster determines the regularized
family, without requiring admissibility of the punctured-domain infimum. -/
theorem regularizedFamily_closure_eq_clusterOn_sdiff_of_local_countable
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ}
    {R t : ℝ} {z : ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUR : closure U ⊆ ball (0 : ℂ) R)
    (hKc : IsClosed K) (hK : (K ∩ U).Countable)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 < t) (hz : z ∈ U \ K)
    (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hopenU : IsOpen (clusterOn μ U z t))
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hopen : ∀ r : ℝ, 0 < r → z ∈ ball (0 : ℂ) r → IsOpen (cluster μ r z t))
    (hcl : closure (clusterOn μ (U \ K) z t) ⊆ U \ K) :
    closure (Λ t) = closure (clusterOn μ (U \ K) z t) := by
  have hc := closure_clusterOn_sdiff_of_local_countable hμ hU hUb hUR hKc hK
    hqc hq ht.le hz hw hopenU
  have hfull : closure (clusterOn μ U z t) ⊆ U := by
    rw [← hc]
    exact hcl.trans sdiff_subset
  obtain ⟨r₁, hr₁⟩ := hUb.subset_ball (0 : ℂ)
  obtain ⟨r₂, hr₂⟩ := ((hΛ.1.isBounded t ht).closure).subset_ball (0 : ℂ)
  let r := max 1 (max r₁ r₂) + 1
  have hr : 0 < r := by
    have h := le_max_left (1 : ℝ) (max r₁ r₂)
    dsimp [r]; linarith
  have hr₁r : r₁ ≤ r := by
    have h := (le_max_left r₁ r₂).trans (le_max_right (1 : ℝ) (max r₁ r₂))
    dsimp [r]; linarith
  have hr₂r : r₂ ≤ r := by
    have h := (le_max_right r₁ r₂).trans (le_max_right (1 : ℝ) (max r₁ r₂))
    dsimp [r]; linarith
  have hUr : U ⊆ ball (0 : ℂ) r := hr₁.trans (ball_subset_ball hr₁r)
  have hΛr : closure (Λ t) ⊆ ball (0 : ℂ) r := hr₂.trans (ball_subset_ball hr₂r)
  have heq := hΛ.2.2 t ht r hr hΛr r le_rfl
  rw [hc, heq, closure_regularizedCluster_eq_of_isOpen (hopen r hr (hUr hz.1)),
    ← clusterOn_eq_cluster_of_compact_containment hU hUr hz.1 ht hw hfull]

/-- If the full-domain Green function tends to zero at its boundary, the
regularized-family containment alternative also gives closure compatibility. -/
theorem regularizedFamily_closure_eq_clusterOn_sdiff_of_green_boundary_countable
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ}
    {R t : ℝ} {z : ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUR : closure U ⊆ ball (0 : ℂ) R)
    (hKc : IsClosed K) (hK : (K ∩ U).Countable)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 < t) (hz : z ∈ U \ K)
    (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hopenU : IsOpen (clusterOn μ U z t))
    (hboundary : ∀ y ∈ closure U, y ∉ U →
      Tendsto (greenFunction U z) (𝓝[U] y) (𝓝 0))
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hopen : ∀ r : ℝ, 0 < r → z ∈ ball (0 : ℂ) r → IsOpen (cluster μ r z t))
    (hcl : closure (Λ t) ⊆ U \ K) :
    closure (Λ t) = closure (clusterOn μ (U \ K) z t) := by
  have hc := closure_clusterOn_sdiff_of_local_countable hμ hU hUb hUR hKc hK
    hqc hq ht.le hz hw hopenU
  obtain ⟨r₁, hr₁⟩ := hUb.subset_ball (0 : ℂ)
  obtain ⟨r₂, hr₂⟩ := ((hΛ.1.isBounded t ht).closure).subset_ball (0 : ℂ)
  let r := max 1 (max r₁ r₂) + 1
  have hr : 0 < r := by
    have h := le_max_left (1 : ℝ) (max r₁ r₂)
    dsimp [r]; linarith
  have hr₁r : r₁ ≤ r := by
    have h := (le_max_left r₁ r₂).trans (le_max_right (1 : ℝ) (max r₁ r₂))
    dsimp [r]; linarith
  have hr₂r : r₂ ≤ r := by
    have h := (le_max_right r₁ r₂).trans (le_max_right (1 : ℝ) (max r₁ r₂))
    dsimp [r]; linarith
  have hUr : U ⊆ ball (0 : ℂ) r := hr₁.trans (ball_subset_ball hr₁r)
  have hΛr : closure (Λ t) ⊆ ball (0 : ℂ) r := hr₂.trans (ball_subset_ball hr₂r)
  have hrepr := hΛ.2.2 t ht r hr hΛr r le_rfl
  have hcluster : closure (Λ t) = closure (cluster μ r z t) := by
    rw [hrepr, closure_regularizedCluster_eq_of_isOpen (hopen r hr (hUr hz.1))]
  obtain ⟨h, hcont, hh, hG⟩ :=
    exists_continuousOn_green_difference_of_boundary_limits hU hUr hz.1 hboundary
  have heq := clusterOn_eq_cluster_of_green_difference_of_nonneg hU hUr hz.1 ht.le
    hw hcont hh hG (Or.inl (hcluster ▸ hcl.trans sdiff_subset))
  rw [hc, heq, ← hcluster]

/-- Both compact-containment alternatives give closure compatibility when
the full-domain Green function vanishes at the boundary. -/
theorem regularizedFamily_strongCompatibility_sdiff_of_local_countable
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ}
    {R t : ℝ} {z : ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUR : closure U ⊆ ball (0 : ℂ) R)
    (hKc : IsClosed K) (hK : (K ∩ U).Countable)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 < t) (hz : z ∈ U \ K)
    (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hopenU : IsOpen (clusterOn μ U z t))
    (hboundary : ∀ y ∈ closure U, y ∉ U →
      Tendsto (greenFunction U z) (𝓝[U] y) (𝓝 0))
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hopen : ∀ r : ℝ, 0 < r → z ∈ ball (0 : ℂ) r → IsOpen (cluster μ r z t))
    (hcl : closure (Λ t) ⊆ U \ K ∨
      closure (clusterOn μ (U \ K) z t) ⊆ U \ K) :
    closure (Λ t) = closure (clusterOn μ (U \ K) z t) := by
  rcases hcl with hcl | hcl
  · exact regularizedFamily_closure_eq_clusterOn_sdiff_of_green_boundary_countable
      hμ hU hUb hUR hKc hK hqc hq ht hz hw hopenU hboundary hΛ hopen hcl
  · exact regularizedFamily_closure_eq_clusterOn_sdiff_of_local_countable
      hμ hU hUb hUR hKc hK hqc hq ht hz hw hopenU hΛ hopen hcl

/-- Agreement of measures on a punctured domain identifies regularized
families when the first punctured-domain cluster is compactly contained. -/
theorem regularizedFamily_eq_of_restrict_eq_of_sdiff_local_countable
    {μ ν : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {U K : Set ℂ} {R t : ℝ} {z : ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUR : closure U ⊆ ball (0 : ℂ) R)
    (hKc : IsClosed K) (hK : (K ∩ U).Countable)
    (hμν : μ.restrict (U \ K) = ν.restrict (U \ K))
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 < t) (hz : z ∈ U \ K)
    (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hopenU : IsOpen (clusterOn μ U z t))
    {Λ Λ' : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hΛ' : IsRegularizedClusterFamily ν Λ' z)
    (hcl : closure (clusterOn μ (U \ K) z t) ⊆ U \ K) : Λ t = Λ' t := by
  have hopen : ∀ r : ℝ, 0 < r → z ∈ ball (0 : ℂ) r → IsOpen (cluster μ r z t) := by
    intro r hr hzr
    rw [(obstacleCompatibilityShiftStep_holds μ hμ r βm βp hr (hVμ r hr) z hzr t ht).2.2.1]
    exact isOpen_nonCoincidenceSet_of obstacleLeastSuperharmonicMajorantGeneral_holds
      hμ hr (hVμ r hr) hzr ht
  have heq := regularizedFamily_closure_eq_clusterOn_sdiff_of_local_countable
    hμ hU hUb hUR hKc hK hqc hq ht hz hw hopenU hΛ hopen hcl
  apply regularizedFamily_eq_of_restrict_eq_of_volumeGrowth hμ hν hVμ hVν
    (hU.sdiff hKc) hμν ht hΛ hΛ'
  rw [heq]
  exact hcl

/-- Local agreement of circle-average approximations on the punctured domain
implies the same compact-containment locality for their limiting measures. -/
theorem IsLQGLimit.regularizedFamily_eq_of_sdiff_local_countable
    {γ : ℝ} {hε hε' : ℝ → ℂ → ℝ} {μ ν : Measure ℂ}
    (hμlim : IsLQGLimit γ hε μ) (hνlim : IsLQGLimit γ hε' ν)
    (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {U K : Set ℂ} {R t : ℝ} {z : ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUR : closure U ⊆ ball (0 : ℂ) R)
    (hKc : IsClosed K) (hK : (K ∩ U).Countable)
    (hloc : ∀ C : Set ℂ, IsCompact C → C ⊆ U \ K →
      ∀ᶠ k : ℕ in atTop, ∀ y ∈ C, hε (dyadicScale k) y = hε' (dyadicScale k) y)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 < t) (hz : z ∈ U \ K)
    (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hopenU : IsOpen (clusterOn μ U z t))
    {Λ Λ' : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hΛ' : IsRegularizedClusterFamily ν Λ' z)
    (hcl : closure (clusterOn μ (U \ K) z t) ⊆ U \ K) : Λ t = Λ' t :=
  regularizedFamily_eq_of_restrict_eq_of_sdiff_local_countable hμ hν hVμ hVν hU hUb hUR
    hKc hK (hμlim.restrict_eq hνlim (hU.sdiff hKc) hloc)
    hqc hq ht hz hw hopenU hΛ hΛ' hcl

/-- Either compact-containment alternative gives measure locality after a
closed deletion of local countability in the original domain. -/
theorem regularizedFamily_eq_of_restrict_eq_of_sdiff_local_countable_or
    {μ ν : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {U K : Set ℂ} {R t : ℝ} {z : ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUR : closure U ⊆ ball (0 : ℂ) R)
    (hKc : IsClosed K) (hK : (K ∩ U).Countable)
    (hμν : μ.restrict (U \ K) = ν.restrict (U \ K))
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 < t) (hz : z ∈ U \ K)
    (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hopenU : IsOpen (clusterOn μ U z t))
    {Λ Λ' : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hΛ' : IsRegularizedClusterFamily ν Λ' z)
    (hcl : closure (Λ t) ⊆ U \ K ∨
      closure (clusterOn μ (U \ K) z t) ⊆ U \ K) : Λ t = Λ' t := by
  rcases hcl with hcl | hcl
  · exact regularizedFamily_eq_of_restrict_eq_of_volumeGrowth hμ hν hVμ hVν
      (hU.sdiff hKc) hμν ht hΛ hΛ' hcl
  · exact regularizedFamily_eq_of_restrict_eq_of_sdiff_local_countable hμ hν hVμ hVν
      hU hUb hUR hKc hK hμν hqc hq ht hz hw hopenU hΛ hΛ' hcl

/-- Local agreement of circle averages implies locality under either
compact-containment alternative. -/
theorem IsLQGLimit.regularizedFamily_eq_of_sdiff_local_countable_or
    {γ : ℝ} {hε hε' : ℝ → ℂ → ℝ} {μ ν : Measure ℂ}
    (hμlim : IsLQGLimit γ hε μ) (hνlim : IsLQGLimit γ hε' ν)
    (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {U K : Set ℂ} {R t : ℝ} {z : ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUR : closure U ⊆ ball (0 : ℂ) R)
    (hKc : IsClosed K) (hK : (K ∩ U).Countable)
    (hloc : ∀ C : Set ℂ, IsCompact C → C ⊆ U \ K →
      ∀ᶠ k : ℕ in atTop, ∀ y ∈ C, hε (dyadicScale k) y = hε' (dyadicScale k) y)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 < t) (hz : z ∈ U \ K)
    (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hopenU : IsOpen (clusterOn μ U z t))
    {Λ Λ' : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hΛ' : IsRegularizedClusterFamily ν Λ' z)
    (hcl : closure (Λ t) ⊆ U \ K ∨
      closure (clusterOn μ (U \ K) z t) ⊆ U \ K) : Λ t = Λ' t :=
  regularizedFamily_eq_of_restrict_eq_of_sdiff_local_countable_or hμ hν hVμ hVν hU hUb hUR
    hKc hK (hμlim.restrict_eq hνlim (hU.sdiff hKc) hloc)
    hqc hq ht hz hw hopenU hΛ hΛ' hcl


/-- Compact containment of the cluster after a relatively closed deletion
gives its closure as the closure of the regularized family. -/
theorem regularizedFamily_closure_eq_clusterOn_sdiff_of_relative_countable
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ}
    {R t : ℝ} {z : ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUR : closure U ⊆ ball (0 : ℂ) R)
    (hD : IsOpen (U \ K)) (hK : (K ∩ U).Countable)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 < t) (hz : z ∈ U \ K)
    (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hopenU : IsOpen (clusterOn μ U z t))
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hopen : ∀ r : ℝ, 0 < r → z ∈ ball (0 : ℂ) r → IsOpen (cluster μ r z t))
    (hcl : closure (clusterOn μ (U \ K) z t) ⊆ U \ K) :
    closure (Λ t) = closure (clusterOn μ (U \ K) z t) := by
  have heq := sdiff_closure_inter_eq_of_isOpen_sdiff hD
  have hc := regularizedFamily_closure_eq_clusterOn_sdiff_of_local_countable
    hμ hU hUb hUR isClosed_closure
    (by simpa only [closure_inter_eq_inter_of_isOpen_sdiff hD] using hK)
    hqc hq ht (heq ▸ hz) hw hopenU hΛ hopen (by simpa only [heq] using hcl)
  simpa only [heq] using hc

/-- Both compact-containment alternatives give closure compatibility after a
relatively closed deletion when the full-domain Green function vanishes at the boundary. -/
theorem regularizedFamily_strongCompatibility_sdiff_of_relative_countable
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ}
    {R t : ℝ} {z : ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUR : closure U ⊆ ball (0 : ℂ) R)
    (hD : IsOpen (U \ K)) (hK : (K ∩ U).Countable)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 < t) (hz : z ∈ U \ K)
    (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hopenU : IsOpen (clusterOn μ U z t))
    (hboundary : ∀ y ∈ closure U, y ∉ U →
      Tendsto (greenFunction U z) (𝓝[U] y) (𝓝 0))
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hopen : ∀ r : ℝ, 0 < r → z ∈ ball (0 : ℂ) r → IsOpen (cluster μ r z t))
    (hcl : closure (Λ t) ⊆ U \ K ∨
      closure (clusterOn μ (U \ K) z t) ⊆ U \ K) :
    closure (Λ t) = closure (clusterOn μ (U \ K) z t) := by
  have heq := sdiff_closure_inter_eq_of_isOpen_sdiff hD
  have hc := regularizedFamily_strongCompatibility_sdiff_of_local_countable
    hμ hU hUb hUR isClosed_closure
    (by simpa only [closure_inter_eq_inter_of_isOpen_sdiff hD] using hK)
    hqc hq ht (heq ▸ hz) hw hopenU hboundary hΛ hopen
    (by simpa only [heq] using hcl)
  simpa only [heq] using hc

/-- Agreement of measures after a relatively closed deletion identifies
regularized families under either compact-containment alternative. -/
theorem regularizedFamily_eq_of_restrict_eq_of_relative_countable
    {μ ν : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {U K : Set ℂ} {R t : ℝ} {z : ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUR : closure U ⊆ ball (0 : ℂ) R)
    (hD : IsOpen (U \ K)) (hK : (K ∩ U).Countable)
    (hμν : μ.restrict (U \ K) = ν.restrict (U \ K))
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 < t) (hz : z ∈ U \ K)
    (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hopenU : IsOpen (clusterOn μ U z t))
    {Λ Λ' : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hΛ' : IsRegularizedClusterFamily ν Λ' z)
    (hcl : closure (Λ t) ⊆ U \ K ∨
      closure (clusterOn μ (U \ K) z t) ⊆ U \ K) : Λ t = Λ' t := by
  have heq := sdiff_closure_inter_eq_of_isOpen_sdiff hD
  exact regularizedFamily_eq_of_restrict_eq_of_sdiff_local_countable_or hμ hν hVμ hVν
    hU hUb hUR isClosed_closure (by simpa only [closure_inter_eq_inter_of_isOpen_sdiff hD] using hK)
    (by simpa only [heq] using hμν) hqc hq ht (heq ▸ hz) hw hopenU hΛ hΛ'
    (by simpa only [heq] using hcl)

/-- Local agreement of circle averages after a relatively closed deletion
implies equality under either compact-containment alternative. -/
theorem IsLQGLimit.regularizedFamily_eq_of_relative_countable
    {γ : ℝ} {hε hε' : ℝ → ℂ → ℝ} {μ ν : Measure ℂ}
    (hμlim : IsLQGLimit γ hε μ) (hνlim : IsLQGLimit γ hε' ν)
    (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {U K : Set ℂ} {R t : ℝ} {z : ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUR : closure U ⊆ ball (0 : ℂ) R)
    (hD : IsOpen (U \ K)) (hK : (K ∩ U).Countable)
    (hloc : ∀ C : Set ℂ, IsCompact C → C ⊆ U \ K →
      ∀ᶠ k : ℕ in atTop, ∀ y ∈ C, hε (dyadicScale k) y = hε' (dyadicScale k) y)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 < t) (hz : z ∈ U \ K)
    (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hopenU : IsOpen (clusterOn μ U z t))
    {Λ Λ' : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hΛ' : IsRegularizedClusterFamily ν Λ' z)
    (hcl : closure (Λ t) ⊆ U \ K ∨
      closure (clusterOn μ (U \ K) z t) ⊆ U \ K) : Λ t = Λ' t :=
  regularizedFamily_eq_of_restrict_eq_of_relative_countable hμ hν hVμ hVν hU hUb hUR
    hD hK (hμlim.restrict_eq hνlim hD hloc) hqc hq ht hz hw hopenU hΛ hΛ' hcl


end HarmonicBalls
