import HarmonicBalls.Proofs.Sec5.FiniteRankBarrierCover
import HarmonicBalls.Proofs.Sec5.GeneralDomainHarmonicExtension
import HarmonicBalls.Proofs.Sec5.GeneralDomainInteriorGreen
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Barrier covers for countable point sets -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Laplacian InnerProductSpace

/-- A compact portion of a closed countable set admits a continuous,
nonnegative capped Green barrier which is arbitrarily small at a point outside
that set. -/
theorem exists_capped_barrier_of_countable
    {R M ε : ℝ} {K C : Set ℂ} {x : ℂ}
    (hKc : IsClosed K) (hK : K.Countable)
    (hC : IsCompact C) (hCU : C ⊆ ball (0 : ℂ) R)
    (hxK : x ∉ K) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ b : ℂ → ℝ, ContinuousOn b (closedBall (0 : ℂ) R) ∧
      LaplacianLE b 0 (ball (0 : ℂ) R) ∧ (∀ y, 0 ≤ b y) ∧ b x < ε ∧
      ∀ y ∈ K ∩ C, M < b y := by
  classical
  by_cases hne : (K ∩ C).Nonempty
  · obtain ⟨a, ha⟩ := (hK.mono inter_subset_left).exists_eq_range hne
    have haK (n : ℕ) : a n ∈ K ∩ C := by
      rw [ha]
      exact mem_range_self n
    have hsingle (n : ℕ) : ∃ b : ℂ → ℝ,
        ContinuousOn b (closedBall (0 : ℂ) R) ∧
        LaplacianLE b 0 (ball (0 : ℂ) R) ∧ (∀ y, 0 ≤ b y) ∧
        b x < (ε / 4) * ((1 / 2 : ℝ) ^ n) ∧ M < b (a n) := by
      have hJ : (({a n} : Finset ℂ) : Set ℂ) ⊆ ball (0 : ℂ) R := by
        simpa using hCU (haK n).2
      have hxJ : x ∉ ({a n} : Finset ℂ) := by
        simp only [Finset.mem_singleton]
        intro h
        exact hxK (h ▸ (haK n).1)
      obtain ⟨b, hbc, hbΔ, hbn, hbx, hba⟩ :=
        exists_capped_barrier_of_finite (ε := (ε / 4) * ((1 / 2 : ℝ) ^ n))
          hJ hxJ hM (by positivity)
      exact ⟨b, hbc, hbΔ, hbn, hbx, hba _ (by simp)⟩
    choose b hb using hsingle
    let W : ℕ → Set ℂ := fun n => ball (0 : ℂ) R ∩ b n ⁻¹' Ioi M
    have hWo (n : ℕ) : IsOpen (W n) :=
      ((hb n).1.mono ball_subset_closedBall).isOpen_inter_preimage isOpen_ball isOpen_Ioi
    have hcover : K ∩ C ⊆ ⋃ n, W n := by
      intro y hy
      have hy' : y ∈ range a := ha ▸ hy
      obtain ⟨n, rfl⟩ := hy'
      exact mem_iUnion.mpr ⟨n, hCU (haK n).2, (hb n).2.2.2.2⟩
    have hcompact : IsCompact (K ∩ C) :=
      hC.of_isClosed_subset (hKc.inter hC.isClosed) inter_subset_right
    obtain ⟨J, hJ⟩ := hcompact.elim_finite_subcover W hWo hcover
    have hgeom : Summable (fun n : ℕ => (ε / 4) * ((1 / 2 : ℝ) ^ n)) :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    have htsum : (∑' n : ℕ, (ε / 4) * ((1 / 2 : ℝ) ^ n)) = ε / 2 := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      ring
    have hsum := hgeom.sum_le_tsum J (fun n _ => by positivity)
    rw [htsum] at hsum
    refine ⟨fun y => ∑ n ∈ J, b n y,
      continuousOn_finsetSum J (fun n _ => (hb n).1), ?_,
      fun y => Finset.sum_nonneg (fun n _ => (hb n).2.2.1 y), ?_, ?_⟩
    · have h := (laplacianLE_zero (0 : Measure ℂ) (ball (0 : ℂ) R)).add_finset_of_nonpos J
        (b := fun n => b n) (fun n _ => (hb n).2.1)
      simpa using h
    · have hle : (∑ n ∈ J, b n x) ≤ ∑ n ∈ J, (ε / 4) * ((1 / 2 : ℝ) ^ n) :=
        Finset.sum_le_sum (fun n _ => (hb n).2.2.2.1.le)
      linarith
    · intro y hy
      obtain ⟨n, hn, hyn⟩ := mem_iUnion₂.mp (hJ hy)
      have hle : b n y ≤ ∑ i ∈ J, b i y :=
        Finset.single_le_sum (fun i _ => (hb i).2.2.1 y) hn
      exact lt_of_lt_of_le hyn.2 hle
  · refine ⟨fun _ => 0, continuousOn_const, laplacianLE_zero _ _, fun _ => le_rfl, hε, ?_⟩
    intro y hy
    exact (hne ⟨y, hy⟩).elim

/-- A closed countable set is removable for harmonic comparison when the
harmonic excess has a uniform local upper bound at the deleted points. -/
theorem harmonic_sub_le_of_countable
    {R ρ C M : ℝ} {K : Set ℂ} {h q : ℂ → ℝ} {x : ℂ}
    (hρR : ρ < R) (hKclosed : IsClosed K)
    (hK : K.Countable)
    (hh : HarmonicOnNhd h (closedBall (0 : ℂ) ρ \ K))
    (hq : HarmonicOnNhd q (closedBall (0 : ℂ) ρ)) (hM : 0 ≤ M)
    (hnear : ∀ a ∈ K, ∀ᶠ y in 𝓝[ball (0 : ℂ) ρ \ K] a, h y - q y ≤ C + M)
    (hbd : ∀ y ∈ sphere (0 : ℂ) ρ, y ∉ K → h y - q y ≤ C)
    (hx : x ∈ ball (0 : ℂ) ρ \ K) : h x - q x ≤ C := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨b, hbc, hbΔ, hbn, hbx, hbar⟩ :=
    exists_capped_barrier_of_countable hKclosed hK
      (isCompact_closedBall _ _) (closedBall_subset_ball hρR) hx.2 hM hε
  have hbcρ : ContinuousOn b (closedBall (0 : ℂ) ρ) :=
    hbc.mono ((closedBall_subset_ball hρR).trans ball_subset_closedBall)
  have hDopen : IsOpen (ball (0 : ℂ) ρ \ K) := isOpen_ball.sdiff hKclosed
  have hDR : ball (0 : ℂ) ρ \ K ⊆ ball (0 : ℂ) R :=
    sdiff_subset.trans (ball_subset_ball (le_of_lt hρR))
  have hbs : IsSuperharmonicOn (ball (0 : ℂ) ρ \ K) b :=
    superharmonicOfLaplacianLEStep_holds _ b hDopen
      (hbcρ.mono (sdiff_subset.trans ball_subset_closedBall)) (hbΔ.mono_set hDR)
  have hcmp := harmonic_sub_le_of_superharmonic_barrier hKclosed hh hq hbcρ hbs hnear
    hbar (fun y _ => hbn y) hbd x hx
  linarith

/-- Every Newtonian harmonic minorant on the punctured disc is bounded by the
full-disc minorant at every undeleted point. -/
theorem IsHarmonicMinorant.le_greatestHarmonicMinorantBall_of_countable
    {R : ℝ} {z x : ℂ} {K : Set ℂ} (hKclosed : IsClosed K)
    (hK : K.Countable)
    (hz : z ∈ ball (0 : ℂ) R \ K)
    {h : ℂ → ℝ} (hh : IsHarmonicMinorant (ball 0 R \ K) (newtonKernelEReal z) h)
    (hx : x ∈ ball (0 : ℂ) R \ K) :
    h x ≤ greatestHarmonicMinorantBall R z x := by
  have hzn : ‖z‖ < R := mem_ball_zero_iff.mp hz.1
  have hxn : ‖x‖ < R := mem_ball_zero_iff.mp hx.1
  have hR : 0 < R := (norm_nonneg z).trans_lt hzn
  let m := max ‖z‖ ‖x‖
  have hmR : m < R := max_lt hzn hxn
  have hzm : ‖z‖ ≤ m := le_max_left _ _
  have hxm : ‖x‖ ≤ m := le_max_right _ _
  let B : ℝ → ℝ := fun ρ =>
    (4 * Real.pi)⁻¹ * ((R ^ 2 - ‖z‖ ^ 2) * (R ^ 2 - ρ ^ 2) / (R ^ 2 * (ρ - ‖z‖) ^ 2))
  have hgB : ∀ ρ ∈ Ioo m R, h x - greatestHarmonicMinorantBall R z x ≤ B ρ := by
    rintro ρ ⟨hmρ, hρR⟩
    have hzρ : ‖z‖ < ρ := hzm.trans_lt hmρ
    have hxρ : ‖x‖ < ρ := hxm.trans_lt hmρ
    have hq : HarmonicOnNhd (greatestHarmonicMinorantBall R z) (closedBall 0 ρ) :=
      (isHarmonicMinorant_greatestHarmonicMinorantBall hz.1).1.mono
        (closedBall_subset_ball hρR)
    obtain ⟨M, hM, hnear⟩ :=
      hh.exists_uniform_excess_near_closed_deletion hρR hKclosed hz.2 (C := B ρ) hq
    have hhρ : HarmonicOnNhd h (closedBall (0 : ℂ) ρ \ K) :=
      hh.1.mono (fun _ hy => ⟨closedBall_subset_ball hρR hy.1, hy.2⟩)
    apply harmonic_sub_le_of_countable hρR hKclosed hK hhρ hq hM hnear
      (x := x) ?_ ⟨mem_ball_zero_iff.mpr hxρ, hx.2⟩
    intro y hy hyK
    have hyn : ‖y‖ = ρ := mem_sphere_zero_iff_norm.mp hy
    have hyz : y ≠ z := by rintro rfl; exact hzρ.ne hyn
    have hyR : ‖y‖ < R := hyn ▸ hρR
    have hpos := norm_sub_conj_mul_pos hR hzn hyR.le
    have h1 : h y ≤ newtonKernel z y := by
      have h := hh.2 y ⟨mem_ball_zero_iff.mpr hyR, hyK⟩
      simpa [newtonKernelEReal, hyz] using h
    have h2 := newtonKernel_sub_greenBall hR (Ne.symm hyz) hpos.ne'
    have h3 := greenBall_le_of_norm_eq hR hzρ hyn hρR.le
    dsimp only [B]
    linarith
  have hB : Tendsto B (𝓝[<] R) (𝓝 0) := by
    have hden : R ^ 2 * (R - ‖z‖) ^ 2 ≠ 0 :=
      mul_ne_zero (pow_ne_zero 2 hR.ne') (pow_ne_zero 2 (sub_ne_zero.2 hzn.ne'))
    have hc : ContinuousAt B R :=
      continuousAt_const.mul (ContinuousAt.div (by fun_prop) (by fun_prop) hden)
    have h0 : B R = 0 := by simp [B]
    rw [← h0]
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have := ge_of_tendsto hB (eventually_of_mem (Ioo_mem_nhdsLT hmR) hgB)
  linarith

theorem greatestHarmonicMinorant_ball_sdiff_of_countable
    {R : ℝ} {z x : ℂ} {K : Set ℂ} (hKclosed : IsClosed K)
    (hK : K.Countable)
    (hz : z ∈ ball (0 : ℂ) R \ K) (hx : x ∈ ball (0 : ℂ) R \ K) :
    greatestHarmonicMinorant (ball 0 R \ K) (newtonKernelEReal z) x =
      greatestHarmonicMinorantBall R z x := by
  apply le_antisymm
  · exact iSup₂_le fun _ hh => EReal.coe_le_coe_iff.mpr
      (hh.le_greatestHarmonicMinorantBall_of_countable hKclosed hK hz hx)
  · have hq := isHarmonicMinorant_greatestHarmonicMinorantBall hz.1
    have hq' : IsHarmonicMinorant (ball 0 R \ K) (newtonKernelEReal z)
        (greatestHarmonicMinorantBall R z) :=
      ⟨fun y hy => hq.1 y hy.1, fun y hy => hq.2 y hy.1⟩
    exact hq'.le_greatestHarmonicMinorant x

/-- The disc Green function is preserved away from a closed countable deletion and away from the pole. -/
theorem greenFunction_ball_sdiff_of_countable
    {R : ℝ} {z x : ℂ} {K : Set ℂ} (hKclosed : IsClosed K)
    (hK : K.Countable)
    (hz : z ∈ ball (0 : ℂ) R \ K) (hx : x ∈ ball (0 : ℂ) R \ K) (hxz : x ≠ z) :
    greenFunction (ball 0 R \ K) z x = greenFunction (ball 0 R) z x := by
  rw [greenFunction, ite_eq_left ⟨hz, hx, Ne.symm hxz⟩,
    greatestHarmonicMinorant_ball_sdiff_of_countable hKclosed hK hz hx,
    EReal.toReal_coe, greenFunction, ite_eq_left ⟨hz.1, hx.1, Ne.symm hxz⟩,
    greatestHarmonicMinorant_ball hz.1 hx.1, EReal.toReal_coe]


/-- If deletion preserves the Green function, capped barriers turn any
full-domain supersolution into an arbitrarily close punctured competitor. -/
theorem leastSupersolutionOn_countable_punctured_le_supersolution
    {μ : Measure ℂ} {U K : Set ℂ} {R t : ℝ} {z x : ℂ} {w : ℂ → ℝ}
    (hUb : Bornology.IsBounded U)
    (hUR : closure U ⊆ ball (0 : ℂ) R)
    (hKc : IsClosed K) (hK : K.Countable)
    (hG : ∀ y ∈ U \ K, y ≠ z → greenFunction (U \ K) z y = greenFunction U z y)
    (hx : x ∈ U \ K) (hxz : x ≠ z) (hw : w ∈ supersolutionsOn μ U z t) :
    leastSupersolutionOn μ (U \ K) z t x ≤ w x := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨B, hB⟩ := hUb.isCompact_closure.exists_bound_of_continuousOn hw.1
  let M := max B 0
  have hM : 0 ≤ M := le_max_right B 0
  obtain ⟨b, hbc, hbΔ, hbn, hsmall, hcover⟩ :=
    exists_capped_barrier_of_countable hKc hK hUb.isCompact_closure hUR hx.2 hM hε
  have hcl : closure (U \ K) ⊆ closure U := closure_mono sdiff_subset
  let v : ℂ → ℝ := fun y => w y + b y
  have hv : v ∈ supersolutionsOn μ (U \ K) z t := by
    refine ⟨(hw.1.add (hbc.mono (hUR.trans ball_subset_closedBall))).mono hcl, ?_, ?_⟩
    · exact (hw.2.1.add_of_nonpos (hbΔ.mono_set (subset_closure.trans hUR))).mono_set sdiff_subset
    · intro y hy hyz
      have hycl := hcl hy
      by_cases hyK : y ∈ K
      · have hynot : y ∉ U \ K := fun h => h.2 hyK
        rw [greenFunction_of_notMem_right hynot, mul_zero]
        have hcov := hcover y ⟨hyK, hycl⟩
        have hbound : ‖w y‖ ≤ M := (hB y hycl).trans (le_max_left B 0)
        have habs : -‖w y‖ ≤ w y := by simpa only [Real.norm_eq_abs] using neg_abs_le (w y)
        dsimp [v]
        linarith
      · by_cases hyU : y ∈ U
        · rw [hG y ⟨hyU, hyK⟩ hyz]
          dsimp [v]
          linarith [hw.2.2 y hycl hyz, hbn y]
        · have hynot : y ∉ U \ K := fun h => hyU h.1
          have hwbound := hw.2.2 y hycl hyz
          rw [greenFunction_of_notMem_right hyU, mul_zero] at hwbound
          rw [greenFunction_of_notMem_right hynot, mul_zero]
          dsimp [v]
          linarith [hbn y]
  have hle := leastSupersolutionOn_le_of_mem hv (subset_closure hx) hxz
  dsimp [v] at hle
  linarith


/-- Harmonic comparison across a thin deletion with boundary-continuous data.
The harmonicity hypotheses are only needed in the open disc. -/
theorem harmonic_sub_le_of_countable_ball_of_continuous_boundary
    {R r C M : ℝ} {c x : ℂ} {K : Set ℂ} {h q : ℂ → ℝ}
    (hball : closedBall c r ⊆ ball (0 : ℂ) R) (hKclosed : IsClosed K)
    (hK : K.Countable)
    (hhc : ContinuousOn h (closedBall c r \ K))
    (hh : HarmonicOnNhd h (ball c r \ K))
    (hqc : ContinuousOn q (closedBall c r)) (hq : HarmonicOnNhd q (ball c r))
    (hM : 0 ≤ M)
    (hnear : ∀ a ∈ K, ∀ᶠ y in 𝓝[ball c r \ K] a, h y - q y ≤ C + M)
    (hbd : ∀ y ∈ sphere c r, y ∉ K → h y - q y ≤ C)
    (hx : x ∈ ball c r \ K) : h x - q x ≤ C := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨b, hbc, hbΔ, hbn, hbx, hbar⟩ :=
    exists_capped_barrier_of_countable hKclosed hK
      (isCompact_closedBall _ _) hball hx.2 hM hε
  have hbc' : ContinuousOn b (closedBall c r) := hbc.mono (hball.trans ball_subset_closedBall)
  let D := ball c r \ K
  let f : ℂ → ℝ := fun y => (h y - q y) - b y
  have hdc : D ⊆ closedBall c r \ K :=
    fun _ hy => ⟨ball_subset_closedBall hy.1, hy.2⟩
  have hDopen : IsOpen D := isOpen_ball.sdiff hKclosed
  have hDR : D ⊆ ball (0 : ℂ) R := hdc.trans (sdiff_subset.trans hball)
  have hbs : IsSuperharmonicOn D b :=
    superharmonicOfLaplacianLEStep_holds _ b hDopen
      (hbc'.mono (hdc.trans sdiff_subset)) (hbΔ.mono_set hDR)
  have hfc : ContinuousOn f (closedBall c r \ K) :=
    (hhc.sub (hqc.mono sdiff_subset)).sub (hbc'.mono sdiff_subset)
  have hsub : IsSubharmonicOn D f := by
    have hhq := hh.sub (hq.mono sdiff_subset)
    have hhqb := HarmonicOnNhd.sub_superharmonic hhq (hbc'.mono (hdc.trans sdiff_subset)) hbs
    convert hhqb using 1
  have hne : ∀ a ∈ K, ∀ᶠ y in 𝓝[D] a, f y < C := by
    intro a ha
    by_cases haρ : a ∈ closedBall c r
    · have hba := hbar a ⟨ha, haρ⟩
      have hba' : ∀ᶠ y in 𝓝[closedBall c r] a, M < b y :=
        (hbc' a haρ).eventually (Ioi_mem_nhds hba)
      filter_upwards [hnear a ha, hba'.filter_mono
        (nhdsWithin_mono a (hdc.trans sdiff_subset))] with y hy hyb
      dsimp [f]
      linarith
    · have haway : ∀ᶠ y in 𝓝 a, y ∉ closedBall c r :=
        isClosed_closedBall.isOpen_compl.mem_nhds haρ
      filter_upwards [haway.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with y hy hyD
      exact (hy (ball_subset_closedBall hyD.1)).elim
  have hle := isSubharmonicOn_ball_sdiff_le_of_eventually_lt hKclosed hfc hsub hne
    (fun y hy hyK => by dsimp [f]; linarith [hbd y hy hyK, hbn y]) x hx
  dsimp [f] at hle
  linarith

/-- A bounded punctured harmonic function agrees with a boundary-continuous
harmonic replacement having the same undeleted boundary values. -/
theorem harmonic_eq_of_countable_ball_of_continuous_boundary
    {R r M : ℝ} {c : ℂ} {K : Set ℂ} {h q : ℂ → ℝ}
    (hball : closedBall c r ⊆ ball (0 : ℂ) R) (hKclosed : IsClosed K)
    (hK : K.Countable)
    (hhc : ContinuousOn h (closedBall c r \ K))
    (hh : HarmonicOnNhd h (ball c r \ K))
    (hqc : ContinuousOn q (closedBall c r)) (hq : HarmonicOnNhd q (ball c r))
    (hM : 0 ≤ M) (hbound : ∀ y ∈ ball c r \ K, |h y - q y| ≤ M)
    (hbd : ∀ y ∈ sphere c r, y ∉ K → h y = q y)
    {x : ℂ} (hx : x ∈ ball c r \ K) : h x = q x := by
  have hnear : ∀ a ∈ K, ∀ᶠ y in 𝓝[ball c r \ K] a, h y - q y ≤ 0 + M := by
    intro a ha
    filter_upwards [self_mem_nhdsWithin] with y hy
    simpa using (le_abs_self (h y - q y)).trans (hbound y hy)
  have hnear' : ∀ a ∈ K, ∀ᶠ y in 𝓝[ball c r \ K] a, (-h) y - (-q) y ≤ 0 + M := by
    intro a ha
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hb := (neg_le_abs (h y - q y)).trans (hbound y hy)
    simp only [Pi.neg_apply]
    linarith
  have hle := harmonic_sub_le_of_countable_ball_of_continuous_boundary
    hball hKclosed hK hhc hh hqc hq hM hnear
    (fun y hy hyK => by rw [hbd y hy hyK]; simp) hx
  have hge := harmonic_sub_le_of_countable_ball_of_continuous_boundary
    hball hKclosed hK hhc.neg hh.neg hqc.neg hq.neg hM hnear'
    (fun y hy hyK => by simp [hbd y hy hyK]) hx
  simp only [Pi.neg_apply] at hge
  linarith

/-- A bounded harmonic function on a punctured disc has a harmonic replacement
when the boundary circle avoids the deletion. -/
theorem exists_harmonic_replacement_of_countable_ball
    {R r M : ℝ} {c : ℂ} {K : Set ℂ} {h : ℂ → ℝ}
    (hr : 0 < r) (hball : closedBall c r ⊆ ball (0 : ℂ) R)
    (hKclosed : IsClosed K) (hK : K.Countable)
    (hdis : Disjoint (sphere c r) K)
    (hh : HarmonicOnNhd h (closedBall c r \ K))
    (hbound : ∀ y ∈ ball c r \ K, |h y| ≤ M) :
    ∃ q : ℂ → ℝ, HarmonicOnNhd q (ball c r) ∧
      ContinuousOn q (closedBall c r) ∧ EqOn q h (ball c r \ K) := by
  have hsphere : sphere c r ⊆ closedBall c r \ K := by
    intro y hy
    exact ⟨sphere_subset_closedBall hy, fun hyK => Set.disjoint_left.mp hdis hy hyK⟩
  have hhc : ContinuousOn h (sphere c r) := hh.continuousOn.mono hsphere
  let f : C(sphere c r, ℝ) := ⟨fun y => h y, hhc.domRestrict⟩
  obtain ⟨g, hg⟩ := ContinuousMap.exists_restrict_eq isClosed_sphere f
  have hg' : ∀ y ∈ sphere c r, g y = h y := by
    intro y hy
    exact congrFun (congrArg DFunLike.coe hg) ⟨y, hy⟩
  let q : ℂ → ℝ := discSweep univ c r g
  have hD : IsSweepDisc (univ : Set ℂ) c r := ⟨hr, subset_univ _⟩
  have hqc : ContinuousOn q (closedBall c r) :=
    (continuousOn_discSweep isOpen_univ g.continuous.continuousOn).mono (subset_univ _)
  have hq : HarmonicOnNhd q (ball c r) := by
    intro y hy
    apply (harmonicAt_congr_nhds (f₁ := discPoissonIntegral g c r) (f₂ := q) ?_).mp
      (harmonicOnNhd_discPoissonIntegral (hD.circleIntegrable g.continuous.continuousOn) y hy)
    filter_upwards [isOpen_ball.mem_nhds hy] with w hw
    exact (discSweep_of_mem hD hw).symm
  have hbd : ∀ y ∈ sphere c r, y ∉ K → h y = q y := by
    intro y hy _
    have hynot : y ∉ ball c r := by
      rw [mem_sphere] at hy
      exact fun hyb => (mem_ball.mp hyb).ne hy
    dsimp [q]
    rw [discSweep_of_not (fun h => hynot h.2), hg' y hy]
  obtain ⟨B, hB⟩ := (isCompact_closedBall c r).exists_bound_of_continuousOn hqc
  let A := max (M + B) 0
  have hA : 0 ≤ A := le_max_right _ _
  have hbound' : ∀ y ∈ ball c r \ K, |h y - q y| ≤ A := by
    intro y hy
    have hqbound : |q y| ≤ B := by simpa only [Real.norm_eq_abs] using hB y (ball_subset_closedBall hy.1)
    exact (abs_sub _ _).trans ((add_le_add (hbound y hy) hqbound).trans (le_max_left _ _))
  refine ⟨q, hq, hqc, ?_⟩
  intro x hx
  exact (harmonic_eq_of_countable_ball_of_continuous_boundary
    hball hKclosed hK hh.continuousOn (hh.mono (fun _ hy => ⟨ball_subset_closedBall hy.1, hy.2⟩))
    hqc hq hA hbound' hbd hx).symm

/-- Locally bounded harmonic functions have local harmonic replacements across a
closed countable deletion. -/
theorem exists_local_harmonic_replacement_of_countable
    {U K : Set ℂ} {R ε M : ℝ} {a : ℂ} {h : ℂ → ℝ}
    (hU : IsOpen U) (hUR : U ⊆ ball (0 : ℂ) R) (ha : a ∈ U)
    (hKclosed : IsClosed K) (hK : K.Countable)
    (hh : HarmonicOnNhd h (U \ K)) (hε : 0 < ε)
    (hbound : ∀ y ∈ ball a ε \ K, |h y| ≤ M) :
    ∃ r : ℝ, 0 < r ∧ ∃ q : ℂ → ℝ,
      HarmonicOnNhd q (ball a r) ∧ EqOn q h (ball a r \ K) := by
  let V := U ∩ ball a ε
  have hV : IsOpen V := hU.inter isOpen_ball
  have hVR : V ⊆ ball (0 : ℂ) R := inter_subset_left.trans hUR
  have haV : a ∈ V := ⟨ha, mem_ball_self hε⟩
  obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.mp hV a haV
  obtain ⟨r, hr, hdis⟩ := exists_radius_sphere_disjoint_of_countable
    hK a (lt_min hε hδ)
  have hcl : closedBall a r ⊆ V :=
    (closedBall_subset_ball (hr.2.trans_le (min_le_right _ _))).trans hδV
  have hball : closedBall a r ⊆ ball (0 : ℂ) R := hcl.trans hVR
  have hh' : HarmonicOnNhd h (closedBall a r \ K) :=
    hh.mono (fun _ hy => ⟨(hcl hy.1).1, hy.2⟩)
  have hbound' : ∀ y ∈ ball a r \ K, |h y| ≤ M := by
    intro y hy
    exact hbound y ⟨(hcl (ball_subset_closedBall hy.1)).2, hy.2⟩
  obtain ⟨q, hq, _, heq⟩ := exists_harmonic_replacement_of_countable_ball
    hr.1 hball hKclosed hK hdis hh' hbound'
  exact ⟨r, hr.1, q, hq, heq⟩


/-- A locally bounded harmonic function on the complement of a closed,
countable set extends harmonically across it. -/
theorem exists_harmonic_extension_of_countable
    {U K : Set ℂ} {R : ℝ} {h : ℂ → ℝ}
    (hU : IsOpen U) (hUR : U ⊆ ball (0 : ℂ) R)
    (hKclosed : IsClosed K) (hK : K.Countable)
    (hh : HarmonicOnNhd h (U \ K))
    (hbounded : ∀ a ∈ U, ∃ ε M : ℝ, 0 < ε ∧
      ∀ y ∈ ball a ε \ K, |h y| ≤ M) :
    ∃ H : ℂ → ℝ, HarmonicOnNhd H U ∧ EqOn H h (U \ K) := by
  classical
  have hex : ∀ a : U, ∃ r : ℝ, 0 < r ∧ ∃ q : ℂ → ℝ,
      HarmonicOnNhd q (ball (a : ℂ) r) ∧ EqOn q h (ball (a : ℂ) r \ K) := by
    intro a
    obtain ⟨ε, M, hε, hb⟩ := hbounded a a.property
    exact exists_local_harmonic_replacement_of_countable hU hUR a.property
      hKclosed hK hh hε hb
  let r : U → ℝ := fun a => Classical.choose (hex a)
  have hr : ∀ a : U, 0 < r a := fun a => (Classical.choose_spec (hex a)).1
  let q : U → ℂ → ℝ := fun a => Classical.choose (Classical.choose_spec (hex a)).2
  have hq : ∀ a : U, HarmonicOnNhd (q a) (ball (a : ℂ) (r a)) ∧
      EqOn (q a) h (ball (a : ℂ) (r a) \ K) :=
    fun a => Classical.choose_spec (Classical.choose_spec (hex a)).2
  let H : ℂ → ℝ := fun x => if hx : x ∈ U then q ⟨x, hx⟩ x else 0
  have hcount : (K ∩ U).Countable :=
    hK.mono inter_subset_left
  have hagree : ∀ a : U, ∀ x ∈ U ∩ ball (a : ℂ) (r a), H x = q a x := by
    intro a x hx
    let b : U := ⟨x, hx.1⟩
    let V : Set ℂ := U ∩ ball (a : ℂ) (r a) ∩ ball (b : ℂ) (r b)
    have hV : IsOpen V := (hU.inter isOpen_ball).inter isOpen_ball
    have hxV : x ∈ V := ⟨hx, mem_ball_self (hr b)⟩
    have hcountV : (K ∩ V).Countable := hcount.mono (by
      intro y hy
      exact ⟨hy.1, hy.2.1.1⟩)
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

/-- Harmonic extensions across a countable set are unique. -/
theorem harmonic_extension_unique_of_countable
    {U K : Set ℂ} {f g : ℂ → ℝ} (hU : IsOpen U)
    (hK : K.Countable) (hf : HarmonicOnNhd f U)
    (hg : HarmonicOnNhd g U) (heq : EqOn f g (U \ K)) : EqOn f g U := by
  have hcl : closure (U \ K) = closure U :=
    closure_sdiff_countable_inter hU (hK.mono inter_subset_left)
  exact heq.of_subset_closure hf.continuousOn hg.continuousOn sdiff_subset
    (by rw [hcl]; exact subset_closure)


/-- The Green correction of a punctured bounded domain extends harmonically
across a closed countable deletion. -/
theorem exists_harmonic_green_correction_of_countable
    {U K : Set ℂ} {R : ℝ} {z : ℂ}
    (hU : IsOpen U) (hUR : U ⊆ ball (0 : ℂ) R)
    (hKc : IsClosed K) (hK : K.Countable)
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
    exists_harmonic_extension_of_countable hU hUR hKc hK hh hbounded
  exact ⟨H, hH, fun x hx hxz => (heq x hx hxz).trans (hHeq hx).symm⟩

/-- Removing a closed countable set preserves the Green function
at undeleted points distinct from the pole. -/
theorem greenFunction_sdiff_of_countable
    {U K : Set ℂ} {R : ℝ} {z x : ℂ}
    (hU : IsOpen U) (hUR : U ⊆ ball (0 : ℂ) R)
    (hKc : IsClosed K) (hK : K.Countable)
    (hz : z ∈ U \ K) (hx : x ∈ U \ K) (hxz : x ≠ z) :
    greenFunction (U \ K) z x = greenFunction U z x := by
  obtain ⟨H, hH, hG⟩ :=
    exists_harmonic_green_correction_of_countable hU hUR hKc hK hz
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
    hK.mono inter_subset_left
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
theorem supersolution_mem_sdiff_of_countable_interior_zero
    {μ : Measure ℂ} {U K : Set ℂ} {R t : ℝ} {z : ℂ} {w : ℂ → ℝ}
    (hU : IsOpen U) (hUR : U ⊆ ball (0 : ℂ) R)
    (hKc : IsClosed K) (hK : K.Countable)
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
    · rw [greenFunction_sdiff_of_countable hU hUR hKc hK hz ⟨hyU, hyK⟩ hyz]
      exact hw.2.2 y (hcl hy) hyz
    · have hynot : y ∉ U \ K := fun h => hyU h.1
      have h := hw.2.2 y (hcl hy) hyz
      rw [greenFunction_of_notMem_right hyU, mul_zero] at h
      rwa [greenFunction_of_notMem_right hynot, mul_zero]


/-- Under a closed countable deletion, a full-domain supersolution gives
an upper bound for the punctured least supersolution at every remaining point. -/
theorem leastSupersolutionOn_countable_sdiff_le_supersolution
    {μ : Measure ℂ} {U K : Set ℂ} {R t : ℝ} {z x : ℂ} {w : ℂ → ℝ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUR : closure U ⊆ ball (0 : ℂ) R)
    (hKc : IsClosed K) (hK : K.Countable) (hz : z ∈ U \ K)
    (hx : x ∈ U \ K) (hxz : x ≠ z) (hw : w ∈ supersolutionsOn μ U z t) :
    leastSupersolutionOn μ (U \ K) z t x ≤ w x := by
  apply leastSupersolutionOn_countable_punctured_le_supersolution hUb hUR hKc hK _ hx hxz hw
  intro y hy hyz
  exact greenFunction_sdiff_of_countable hU (subset_closure.trans hUR) hKc hK hz hy hyz

/-- The cluster of the punctured domain is contained in the undeleted part
of the full-domain cluster. -/
theorem clusterOn_countable_sdiff_subset_clusterOn_sdiff
    {μ : Measure ℂ} {U K : Set ℂ} {R t : ℝ} {z : ℂ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUR : closure U ⊆ ball (0 : ℂ) R)
    (hKc : IsClosed K) (hK : K.Countable) (hz : z ∈ U \ K)
    (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t) :
    clusterOn μ (U \ K) z t ⊆ clusterOn μ U z t \ K := by
  rintro x ⟨⟨hx, hxK⟩, hxz | hxpos⟩
  · exact ⟨⟨hx, Or.inl hxz⟩, hxK⟩
  · refine ⟨⟨hx, ?_⟩, hxK⟩
    by_cases hxz : x = z
    · exact Or.inl hxz
    · right
      rw [greenFunction_sdiff_of_countable hU (subset_closure.trans hUR) hKc hK
        hz ⟨hx, hxK⟩ hxz] at hxpos
      have hle := leastSupersolutionOn_countable_sdiff_le_supersolution
        hU hUb hUR hKc hK hz ⟨hx, hxK⟩ hxz hw
      linarith

/-- A continuous function satisfying the subharmonic maximum principle away
from a closed countable set obeys the maximum principle on the whole disc. -/
theorem isSubharmonicOn_ball_sdiff_le_of_countable
    {R r : ℝ} {c : ℂ} {K : Set ℂ} {f : ℂ → ℝ}
    (hball : closedBall c r ⊆ ball (0 : ℂ) R)
    (hKc : IsClosed K) (hK : K.Countable)
    (hfc : ContinuousOn f (closedBall c r))
    (hf : IsSubharmonicOn (ball c r \ K) f)
    (hbd : ∀ y ∈ sphere c r, f y ≤ 0)
    {x : ℂ} (hx : x ∈ ball c r) : f x ≤ 0 := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall c r).exists_bound_of_continuousOn hfc
  let M := max B 0
  have hM : 0 ≤ M := le_max_right B 0
  have hbound : ∀ y ∈ closedBall c r, f y ≤ M := by
    intro y hy
    have h := (hB y hy).trans (le_max_left B 0)
    exact (le_abs_self (f y)).trans (by simpa only [Real.norm_eq_abs] using h)
  have hinside : ∀ y ∈ ball c r \ K, f y ≤ 0 := by
    intro y hy
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨b, hbc, hbΔ, hbn, hbx, hbar⟩ :=
      exists_capped_barrier_of_countable hKc hK (isCompact_closedBall _ _) hball
        hy.2 hM hε
    have hbc' : ContinuousOn b (closedBall c r) := hbc.mono (hball.trans ball_subset_closedBall)
    let D := ball c r \ K
    have hdc : D ⊆ closedBall c r \ K :=
      fun _ hz => ⟨ball_subset_closedBall hz.1, hz.2⟩
    have hDopen : IsOpen D := isOpen_ball.sdiff hKc
    have hDR : D ⊆ ball (0 : ℂ) R := hdc.trans (sdiff_subset.trans hball)
    have hbs : IsSuperharmonicOn D b :=
      superharmonicOfLaplacianLEStep_holds _ b hDopen
        (hbc'.mono (hdc.trans sdiff_subset)) (hbΔ.mono_set hDR)
    have hfcD : ContinuousOn f D := hfc.mono (hdc.trans sdiff_subset)
    have hbD : ContinuousOn b D := hbc'.mono (hdc.trans sdiff_subset)
    have hfΔ : LaplacianLE (-f) 0 D :=
      laplacianLEOfSuperharmonicStep_holds D (-f) hDopen hfcD.neg hf
    have hsum := superharmonicOfLaplacianLEStep_holds D ((-f) + b) hDopen
      (hfcD.neg.add hbD) (hfΔ.add_of_nonpos (hbΔ.mono_set hDR))
    have hsub : IsSubharmonicOn D (fun z => f z - b z) := by
      change IsSuperharmonicOn D (-(fun z => f z - b z))
      convert hsum using 1
      ext z
      simp only [Pi.neg_apply, Pi.add_apply]
      ring
    have hne : ∀ a ∈ K, ∀ᶠ z in 𝓝[D] a, f z - b z < 0 := by
      intro a ha
      by_cases haρ : a ∈ closedBall c r
      · have hba := hbar a ⟨ha, haρ⟩
        have hba' : ∀ᶠ z in 𝓝[closedBall c r] a, M < b z :=
          (hbc' a haρ).eventually (Ioi_mem_nhds hba)
        filter_upwards [hba'.filter_mono (nhdsWithin_mono a (hdc.trans sdiff_subset)),
          self_mem_nhdsWithin] with z hzb hzD
        linarith [hbound z (hdc hzD).1]
      · have haway : ∀ᶠ z in 𝓝 a, z ∉ closedBall c r :=
          isClosed_closedBall.isOpen_compl.mem_nhds haρ
        filter_upwards [haway.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hzD
        exact (hz (ball_subset_closedBall hzD.1)).elim
    have hle := isSubharmonicOn_ball_sdiff_le_of_eventually_lt hKc
      ((hfc.sub hbc').mono sdiff_subset) hsub hne
      (fun z hz _ => by simp only [Pi.sub_apply]; linarith [hbd z hz, hbn z]) y hy
    simp only [Pi.sub_apply] at hle
    linarith
  have hcl : closure (ball c r \ K) = closure (ball c r) :=
    closure_sdiff_countable_inter isOpen_ball (hK.mono inter_subset_left)
  have hxcl : x ∈ closure (ball c r \ K) := by rw [hcl]; exact subset_closure hx
  let : (𝓝[ball c r \ K] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hxcl
  have hcont : ContinuousAt f x := hfc.continuousAt
    (mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall)
  apply le_of_tendsto_of_tendsto (b := 𝓝[ball c r \ K] x)
    (hcont.tendsto.mono_left nhdsWithin_le_nhds) tendsto_const_nhds
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact hinside z hz

/-- A continuous superharmonic function extends across a closed countable set. -/
theorem isSuperharmonicOn_of_countable_removal {U K : Set ℂ} {v : ℂ → ℝ}
    (hU : IsOpen U) (hKc : IsClosed K) (hK : K.Countable)
    (hvc : ContinuousOn v U) (hs : IsSuperharmonicOn (U \ K) v) :
    IsSuperharmonicOn U v := by
  have hlocal : HasLocalSuperMean U v := by
    intro x hx
    obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp hU x hx
    refine ⟨δ / 2, half_pos hδ, fun r hr => ?_⟩
    have hr0 : 0 < r := hr.1
    have hball : closedBall x r ⊆ U :=
      (closedBall_subset_ball (lt_trans hr.2 (half_lt_self hδ))).trans hδU
    have hD : IsSweepDisc U x r := ⟨hr0, hball⟩
    have hvi : CircleIntegrable v x r := hD.circleIntegrable hvc
    let p := discSweep U x r v
    have hpc : ContinuousOn p U := continuousOn_discSweep hU hvc
    have hp : HarmonicOnNhd p (ball x r) := by
      intro y hy
      apply (harmonicAt_congr_nhds (f₁ := discPoissonIntegral v x r) (f₂ := p) ?_).mp
        (harmonicOnNhd_discPoissonIntegral hvi y hy)
      filter_upwards [isOpen_ball.mem_nhds hy] with z hz
      exact (discSweep_of_mem hD hz).symm
    let D := ball x r \ K
    have hDU : D ⊆ U \ K := fun _ hy => ⟨hball (ball_subset_closedBall hy.1), hy.2⟩
    have hsD : IsSuperharmonicOn D v :=
      ⟨hs.1.mono hDU, fun y hy s hsr hsb => hs.2 y (hDU hy) s hsr (hsb.trans hDU)⟩
    have hneg : IsSubharmonicOn D (-v) := by simpa [IsSubharmonicOn] using hsD
    have hf : ContinuousOn (-v) D := (hvc.mono (hDU.trans sdiff_subset)).neg
    have hsub := hneg.add_harmonicOnNhd hf (hp.mono sdiff_subset)
    obtain ⟨R, hballR⟩ := (isBounded_closedBall : Bornology.IsBounded (closedBall x r)).subset_ball (0 : ℂ)
    have hcomp := isSubharmonicOn_ball_sdiff_le_of_countable hballR hKc hK
      (((hvc.neg).add hpc).mono hball) hsub (by
        intro y hy
        have hyb : y ∉ ball x r := by
          rw [mem_ball, mem_sphere] at *
          linarith
        change -v y + discSweep U x r v y ≤ 0
        rw [discSweep_of_not (fun h => hyb h.2)]
        simp) (mem_ball_self hr0)
    have heq := discSweep_of_mem (f := v) hD (mem_ball_self hr0)
    change -v x + p x ≤ 0 at hcomp
    dsimp [p] at hcomp
    rw [heq, discPoissonIntegral_center hr0.ne'] at hcomp
    exact ⟨hvi, by linarith⟩
  refine ⟨hvc.lowerSemicontinuousOn, fun x hx r hr hball => ?_⟩
  have hi : CircleIntegrable v x r :=
    (hvc.mono (sphere_subset_closedBall.trans hball)).circleIntegrable hr.le
  exact ⟨hi, circleAverage_le_of_localSuperMean hvc.lowerSemicontinuousOn hlocal hr hball hi⟩

/-- A continuous distributional supersolution extends across a closed
countable set. -/
theorem laplacianLE_zero_of_countable_removal {U K : Set ℂ} {v : ℂ → ℝ}
    (hU : IsOpen U) (hKc : IsClosed K) (hK : K.Countable)
    (hvc : ContinuousOn v U) (hv : LaplacianLE v 0 (U \ K)) : LaplacianLE v 0 U := by
  have hs := superharmonicOfLaplacianLEStep_holds _ _ (hU.sdiff hKc)
    (hvc.mono sdiff_subset) hv
  exact laplacianLEOfSuperharmonicStep_holds U v hU hvc
    (isSuperharmonicOn_of_countable_removal hU hKc hK hvc hs)

/-- Removal also holds for a measure-valued weak Laplacian when the measure
has a continuous potential. -/
theorem laplacianLE_of_countable_removal {μ : Measure ℂ}
    (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ} (hU : IsOpen U)
    (hKc : IsClosed K) (hK : K.Countable) {w q : ℂ → ℝ}
    (hwc : ContinuousOn w U) (hqc : ContinuousOn q U)
    (hq : HasLaplacian q 0 μ U) (hw : LaplacianLE w μ (U \ K)) :
    LaplacianLE w μ U := by
  have hp := (laplacianLE_iff_add_potential hμ (hq.mono_domain sdiff_subset)).mp hw
  exact (laplacianLE_iff_add_potential hμ hq).mpr
    (laplacianLE_zero_of_countable_removal hU hKc hK (hwc.add hqc) hp)

/-- A supersolution on a bounded open domain minus a closed countable set extends to the whole domain. -/
theorem countable_punctured_supersolution_mem_domain
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) 
    (hKc : IsClosed K) (hK : K.Countable)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    {z : ℂ} {t : ℝ} (ht : 0 ≤ t) {w : ℂ → ℝ}
    (hw : w ∈ supersolutionsOn μ (U \ K) z t) : w ∈ supersolutionsOn μ U z t := by
  have hcl : closure (U \ K) = closure U :=
    closure_sdiff_countable_inter hU (hK.mono inter_subset_left)
  refine ⟨by simpa only [hcl] using hw.1, ?_, ?_⟩
  · exact laplacianLE_of_countable_removal hμ hU hKc hK
      (hw.1.mono (by rw [hcl]; exact subset_closure)) hqc hq hw.2.1
  · intro x hx hxz
    have hwx := hw.2.2 x (hcl ▸ hx) hxz
    have hG := Section6.greenFunction_le_of_subset (show U \ K ⊆ U from sdiff_subset) hUb z x
    nlinarith

/-- The original-domain infimum bounds the punctured-domain infimum from
below, away from the pole. -/
theorem leastSupersolutionOn_le_countable_punctured
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) 
    (hKc : IsClosed K) (hK : K.Countable)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    {z x : ℂ} {t : ℝ} (ht : 0 ≤ t) (hx : x ∈ closure U) (hxz : x ≠ z) :
    leastSupersolutionOn μ U z t x ≤ leastSupersolutionOn μ (U \ K) z t x := by
  apply le_csInf
  · exact ⟨_, ⟨0, zero_mem_supersolutionsOn (hUb.subset sdiff_subset) ht, rfl⟩⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact leastSupersolutionOn_le_of_mem
      (countable_punctured_supersolution_mem_domain hμ hU hUb hKc hK hqc hq ht hw) hx hxz


/-- The least supersolutions agree away from a closed countable deletion and
the pole, when the full-domain least supersolution is admissible. -/
theorem leastSupersolutionOn_countable_sdiff_eq
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ} {R t : ℝ} {z x : ℂ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUR : closure U ⊆ ball (0 : ℂ) R)
    (hKc : IsClosed K) (hK : K.Countable) (hz : z ∈ U \ K)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 ≤ t) (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hx : x ∈ U \ K) (hxz : x ≠ z) :
    leastSupersolutionOn μ (U \ K) z t x = leastSupersolutionOn μ U z t x := by
  exact le_antisymm
    (leastSupersolutionOn_countable_sdiff_le_supersolution hU hUb hUR hKc hK hz hx hxz hw)
    (leastSupersolutionOn_le_countable_punctured hμ hU hUb hKc hK hqc hq ht
      (subset_closure hx.1) hxz)

/-- Deleting a closed countable set removes exactly its points from the cluster. -/
theorem clusterOn_countable_sdiff_eq
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ} {R t : ℝ} {z : ℂ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUR : closure U ⊆ ball (0 : ℂ) R)
    (hKc : IsClosed K) (hK : K.Countable) (hz : z ∈ U \ K)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 ≤ t) (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t) :
    clusterOn μ (U \ K) z t = clusterOn μ U z t \ K := by
  apply Subset.antisymm
    (clusterOn_countable_sdiff_subset_clusterOn_sdiff hU hUb hUR hKc hK hz hw)
  rintro x ⟨⟨hx, hxz | hxpos⟩, hxK⟩
  · exact ⟨⟨hx, hxK⟩, Or.inl hxz⟩
  · refine ⟨⟨hx, hxK⟩, ?_⟩
    by_cases hxz : x = z
    · exact Or.inl hxz
    · right
      rw [greenFunction_sdiff_of_countable hU (subset_closure.trans hUR) hKc hK
        hz ⟨hx, hxK⟩ hxz,
        leastSupersolutionOn_countable_sdiff_eq hμ hU hUb hUR hKc hK hz hqc hq ht hw
          ⟨hx, hxK⟩ hxz]
      exact hxpos

/-- If the full-domain cluster is open, closed countable deletion preserves
its closure. -/
theorem closure_clusterOn_countable_sdiff_eq
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ} {R t : ℝ} {z : ℂ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUR : closure U ⊆ ball (0 : ℂ) R)
    (hKc : IsClosed K) (hK : K.Countable) (hz : z ∈ U \ K)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 ≤ t) (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hopen : IsOpen (clusterOn μ U z t)) :
    closure (clusterOn μ (U \ K) z t) = closure (clusterOn μ U z t) := by
  rw [clusterOn_countable_sdiff_eq hμ hU hUb hUR hKc hK hz hqc hq ht hw]
  exact closure_sdiff_countable_inter hopen (hK.mono inter_subset_left)

#print axioms leastSupersolutionOn_countable_sdiff_eq
#print axioms clusterOn_countable_sdiff_eq
#print axioms closure_clusterOn_countable_sdiff_eq
#print axioms leastSupersolutionOn_le_countable_punctured
#print axioms isSuperharmonicOn_of_countable_removal
#print axioms laplacianLE_zero_of_countable_removal
#print axioms isSubharmonicOn_ball_sdiff_le_of_countable
#print axioms clusterOn_countable_sdiff_subset_clusterOn_sdiff
#print axioms greenFunction_sdiff_of_countable
#print axioms supersolution_mem_sdiff_of_countable_interior_zero
#print axioms exists_harmonic_extension_of_countable
#print axioms harmonic_extension_unique_of_countable
#print axioms exists_capped_barrier_of_countable
#print axioms greenFunction_ball_sdiff_of_countable
#print axioms leastSupersolutionOn_countable_punctured_le_supersolution

end HarmonicBalls
