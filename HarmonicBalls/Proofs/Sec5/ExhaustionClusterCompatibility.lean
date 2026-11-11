import HarmonicBalls.Proofs.Sec5.GreenRegularExhaustion
import HarmonicBalls.Proofs.Sec5.ExhaustionHorizon
import HarmonicBalls.Proofs.Sec5.MinimumLaplacianGluing
import HarmonicBalls.Proofs.Sec5.CountableDiscCompatibility

/-! # Exhaustion comparison for regularized clusters

The Green-function and obstacle arguments use the potential-theoretic
infrastructure of Leonardo Bonanno.
-/

namespace HarmonicBalls

open Filter MeasureTheory Metric Set
open scoped Topology

/-- Any fixed finite sequence of Poisson modifications eventually agrees with
the sequence on the increasing union of open domains. -/
theorem eventually_sweep_eq_of_open_exhaustion
    (V : ℕ → Set ℂ) (hopen : ∀ n, IsOpen (V n)) (hmono : Monotone V)
    {U : Set ℂ} (hcover : (⋃ n, V n) = U) (f : ℂ → ℝ) (k : ℕ) :
    ∀ᶠ n in atTop, sweep (V n) f k = sweep U f k := by
  classical
  have hsub (n : ℕ) : V n ⊆ U := by
    rw [← hcover]
    exact subset_iUnion V n
  induction k with
  | zero => exact Eventually.of_forall fun _ => rfl
  | succ k ih =>
    by_cases hd : IsSweepDisc U (sweepCenter k) (sweepRadius k)
    · obtain ⟨N, hN⟩ := IsCompact.subset_monotone_open_iUnion
        (isCompact_closedBall _ _) hopen hmono (hcover ▸ hd.2)
      filter_upwards [ih, eventually_ge_atTop N] with n hn hNn
      have hd' : IsSweepDisc (V n) (sweepCenter k) (sweepRadius k) :=
        ⟨hd.1, hN.trans (hmono hNn)⟩
      rw [sweep_succ, sweep_succ, hn]
      funext y
      simp only [discSweep, hd, hd', true_and]
    · have hd' (n : ℕ) : ¬ IsSweepDisc (V n) (sweepCenter k) (sweepRadius k) :=
        fun hv => hd ⟨hv.1, hv.2.trans (hsub n)⟩
      filter_upwards [ih] with n hn
      rw [sweep_succ, sweep_succ, hn]
      funext y
      simp only [discSweep, hd, hd', false_and, ite_false]

/-- The greatest harmonic minorants produced by sweeping converge along an
increasing open exhaustion, at each point of the union. -/
theorem tendsto_sweep_limit_of_open_exhaustion
    (V : ℕ → Set ℂ) (hopen : ∀ n, IsOpen (V n)) (hmono : Monotone V)
    {U : Set ℂ} (hU : IsOpen U) (hcover : (⋃ n, V n) = U)
    {f h₀ : ℂ → ℝ} (hf : ContinuousOn f U) (hm : HasLocalSuperMean U f)
    (hh₀ : InnerProductSpace.HarmonicOnNhd h₀ U) (h₀f : ∀ x ∈ U, h₀ x ≤ f x)
    {x : ℂ} (hx : x ∈ U) :
    Tendsto (fun n => ⨅ k, sweep (V n) f k x) atTop
      (𝓝 (⨅ k, sweep U f k x)) := by
  have hsub (n : ℕ) : V n ⊆ U := by
    rw [← hcover]
    exact subset_iUnion V n
  obtain ⟨N, hN⟩ := mem_iUnion.mp (hcover ▸ hx)
  have hxev : ∀ᶠ n in atTop, x ∈ V n := by
    filter_upwards [eventually_ge_atTop N] with n hn
    exact hmono hn hN
  have hlimU := sweep_limit hU hf hm hh₀ h₀f
  have hlimV (n : ℕ) := sweep_limit (hopen n) (hf.mono (hsub n))
    (fun y hy => hm y (hsub n hy)) (hh₀.mono (hsub n))
    (fun y hy => h₀f y (hsub n hy))
  have hbdd (n : ℕ) (hxn : x ∈ V n) :
      BddBelow (range fun k => sweep (V n) f k x) := by
    refine ⟨h₀ x, ?_⟩
    rintro _ ⟨k, rfl⟩
    have h := sweep_mono (hopen n) ((InnerProductSpace.HarmonicOnNhd.continuousOn hh₀).mono (hsub n))
      (hf.mono (hsub n)) (fun y hy => h₀f y (hsub n hy)) k x hxn
    rwa [sweep_harmonic (hh₀.mono (hsub n))] at h
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [hxev] with n hxn
    exact ha.trans_le ((hlimV n).2.2.2 _ (hlimU.1.mono (hsub n))
      (fun y hy => hlimU.2.1 y (hsub n hy)) x hxn)
  · intro b hb
    have hev : ∀ᶠ k in atTop, sweep U f k x < b :=
      (hlimU.2.2.1 x hx).eventually (Iio_mem_nhds hb)
    obtain ⟨k, hk⟩ := hev.exists
    filter_upwards [hxev, eventually_sweep_eq_of_open_exhaustion V hopen hmono hcover f k]
      with n hxn heq
    have hle := ciInf_le (hbdd n hxn) k
    rw [heq] at hle
    exact hle.trans_lt hk

/-- Green functions converge to the Green function of an increasing union of
bounded open planar domains, at points away from the pole. -/
theorem tendsto_greenFunction_of_open_exhaustion
    (V : ℕ → Set ℂ) (hopen : ∀ n, IsOpen (V n)) (hmono : Monotone V)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hcover : (⋃ n, V n) = U) {z x : ℂ} (hz : z ∈ V 0)
    (hx : x ∈ U) (hxz : x ≠ z) :
    Tendsto (fun n => greenFunction (V n) z x) atTop (𝓝 (greenFunction U z x)) := by
  have hsub (n : ℕ) : V n ⊆ U := by
    rw [← hcover]
    exact subset_iUnion V n
  have hzU : z ∈ U := hsub 0 hz
  obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.mp (hopen 0) z hz
  let ε : ℝ := δ / 4
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hball : closedBall z (2 * ε) ⊆ V 0 :=
    (closedBall_subset_ball (by dsimp [ε]; linarith)).trans hδV
  obtain ⟨R, hR⟩ := hUb.subset_ball z
  have hminor := isHarmonicMinorant_const_newtonKernelEReal (hR.trans ball_subset_closedBall)
  have hreg := (isHarmonicMinorant_regularized_iff hε (hball.trans (hsub 0))).1 hminor
  have hlow : ∀ y ∈ U, -(2 * Real.pi)⁻¹ * Real.log R ≤ regularizedNewtonKernel ε z y := by
    intro y hy
    exact EReal.coe_le_coe_iff.mp (hreg.2 y hy)
  have hf : ContinuousOn (regularizedNewtonKernel ε z) U :=
    (continuous_regularizedNewtonKernel_right hε z).continuousOn
  have hm := hasLocalSuperMean_regularizedNewtonKernel hε z U
  have hconv := tendsto_sweep_limit_of_open_exhaustion V hopen hmono hU hcover
    hf hm hreg.1 hlow hx
  have hval {O : Set ℂ} (hO : IsOpen O) (hOU : O ⊆ U)
      (hballO : closedBall z (2 * ε) ⊆ O) (hzO : z ∈ O) (hxO : x ∈ O) :
      greenFunction O z x = newtonKernel z x -
        (⨅ k, sweep O (regularizedNewtonKernel ε z) k x) := by
    rw [greenFunction, ite_eq_left ⟨hzO, hxO, Ne.symm hxz⟩,
      greatestHarmonicMinorant_regularized hε hballO,
      greatestHarmonicMinorant_eq_of_sweep_limit hO (hf.mono hOU)
        (fun y hy => hm y (hOU hy)) (hreg.1.mono hOU)
        (fun y hy => hlow y (hOU hy)) x hxO, EReal.toReal_coe]
  obtain ⟨N, hN⟩ := mem_iUnion.mp (hcover ▸ hx)
  have hev : (fun n => greenFunction (V n) z x) =ᶠ[atTop]
      (fun n => newtonKernel z x - (⨅ k, sweep (V n) (regularizedNewtonKernel ε z) k x)) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    exact hval (hopen n) (hsub n) (hball.trans (hmono (Nat.zero_le n)))
      (hmono (Nat.zero_le n) hz) (hmono hn hN)
  rw [hval hU (Subset.refl U) (hball.trans (hsub 0)) hzU hx]
  exact (tendsto_const_nhds.sub hconv).congr' hev.symm

/-- Every cluster in a relatively compact regular exhaustion is contained in
 the cluster of the union, even if the union is not Green-regular. -/
theorem iUnion_clusterOn_subset_of_regular_exhaustion
    {μ : Measure ℂ} {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (V : ℕ → Set ℂ) (hopen : ∀ n, IsOpen (V n))
    (hsub : ∀ n, closure (V n) ⊆ U) {z : ℂ} (hz : ∀ n, z ∈ V n)
    {t : ℝ} (ht : 0 ≤ t)
    (hboundary : ∀ n y, y ∈ closure (V n) → y ∉ V n →
      Tendsto (greenFunction (V n) z) (𝓝[V n] y) (𝓝 0)) :
    (⋃ n, clusterOn μ (V n) z t) ⊆ clusterOn μ U z t := by
  intro x hx
  obtain ⟨n, hn⟩ := mem_iUnion.mp hx
  exact clusterOn_subset_of_compactly_contained_regular (hopen n) hU hUb
    (hsub n) (hz n) ht (hboundary n) hn

/-- A positive shift of a subdomain supersolution can be clipped at zero and
extended to the ambient domain. -/
theorem exists_shifted_clipped_supersolutionOn_extension
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {V U : Set ℂ} (hV : IsOpen V) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hVU : V ⊆ U) {z : ℂ} (hz : z ∈ V)
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 < ε)
    {q : ℂ → ℝ} (hqc : ContinuousOn q V) (hq : HasLaplacian q 0 μ V)
    {v : ℂ → ℝ} (hv : v ∈ supersolutionsOn μ V z t) :
    ∃ w ∈ supersolutionsOn μ U z t, EqOn w (fun x => min (v x + ε) 0) V := by
  let K : Set ℂ := closure V ∩ v ⁻¹' Iic (-ε / 2)
  let O : Set ℂ := Kᶜ
  have hK : IsClosed K := hv.1.preimage_isClosed_of_isClosed isClosed_closure isClosed_Iic
  have hO : IsOpen O := hK.isOpen_compl
  have hKV : K ⊆ V := by
    intro x hx
    by_contra hxV
    have hxz : x ≠ z := fun h => hxV (h ▸ hz)
    have hbound := hv.2.2 x hx.1 hxz
    rw [greenFunction_of_notMem_right hxV, mul_zero] at hbound
    have : v x ≤ -ε / 2 := hx.2
    linarith
  have hcover : closure U ⊆ V ∪ O := by
    intro x _
    by_cases hx : x ∈ V
    · exact Or.inl hx
    · exact Or.inr (fun hxK => hx (hKV hxK))
  have hshift : LaplacianLE (fun x => v x + ε) μ V := by
    have hh := hasLaplacian_zero_of_harmonicOnNhd hV (InnerProductSpace.harmonicOnNhd_const 1)
    simpa using hv.2.1.add_const_mul_of_hasLaplacian_zero hh ε
  have hc : ContinuousOn (fun x => min (v x + ε) 0) V :=
    fun x hx => (((hv.1.mono subset_closure) x hx).add continuousWithinAt_const).min
      continuousWithinAt_const
  have hl := hshift.min_zero_of_potential hμ hV
    ((hv.1.mono subset_closure).add continuousOn_const) hqc hq
  have hagree : EqOn (fun x => min (v x + ε) 0) (fun _ => 0) (V ∩ O) := by
    intro x hx
    apply min_eq_right
    have hxK : x ∉ K := hx.2
    have hx' : ¬ v x ≤ -ε / 2 := fun h => hxK ⟨subset_closure hx.1, h⟩
    linarith
  obtain ⟨w, hwc, hwL, hwV, hwO⟩ := LaplacianLE.glue_of_open_cover
    hU hV hO hVU hcover hc continuousOn_const hl (laplacianLE_zero μ U) hagree
  refine ⟨w, ⟨hwc, hwL, ?_⟩, hwV⟩
  intro x hx hxz
  by_cases hxV : x ∈ V
  · rw [hwV hxV]
    have hvx := hv.2.2 x (subset_closure hxV) hxz
    have hG := Section6.greenFunction_le_of_subset hVU hUb z x
    have hG0 := greenFunction_nonneg hUb z x
    apply le_min <;> nlinarith
  · have hxO : x ∈ O := fun hxK => hxV (hKV hxK)
    rw [hwO hxO]
    have hG0 := greenFunction_nonneg hUb z x
    change -t * greenFunction U z x ≤ 0
    nlinarith [mul_nonneg ht hG0]

/-- The ambient-domain least supersolution is bounded above by an admissible
subdomain least supersolution. No regularity of the ambient boundary is used. -/
theorem leastSupersolutionOn_le_of_subdomain_admissible
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {V U : Set ℂ} (hV : IsOpen V) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hVU : V ⊆ U) {z x : ℂ} (hz : z ∈ V)
    (hx : x ∈ V) (hxz : x ≠ z) {t : ℝ} (ht : 0 ≤ t)
    {q : ℂ → ℝ} (hqc : ContinuousOn q V) (hq : HasLaplacian q 0 μ V)
    (hv : leastSupersolutionOn μ V z t ∈ supersolutionsOn μ V z t) :
    leastSupersolutionOn μ U z t x ≤ leastSupersolutionOn μ V z t x := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨w, hw, hwV⟩ := exists_shifted_clipped_supersolutionOn_extension
    hμ hV hU hUb hVU hz ht hε hqc hq hv
  have hwle := leastSupersolutionOn_le_of_mem hw (subset_closure (hVU hx)) hxz
  rw [hwV hx] at hwle
  exact hwle.trans (min_le_left _ _)

/-- The least-supersolution comparison applies to nested regular subdomains
under the volume-growth hypothesis, including touching boundaries. -/
theorem leastSupersolutionOn_le_of_regular_subdomain
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hvol : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {V U : Set ℂ} (hV : IsOpen V) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hVU : V ⊆ U) {z x : ℂ} (hz : z ∈ V)
    (hx : x ∈ V) (hxz : x ≠ z) {t : ℝ} (ht : 0 < t)
    (hboundary : ∀ y ∈ closure V, y ∉ V →
      Tendsto (greenFunction V z) (𝓝[V] y) (𝓝 0)) :
    leastSupersolutionOn μ U z t x ≤ leastSupersolutionOn μ V z t x := by
  obtain ⟨r₀, hr₀⟩ := hUb.subset_ball (0 : ℂ)
  let r := max r₀ 1 + 1
  have hr : 0 < r := by dsimp [r]; linarith [le_max_right r₀ (1 : ℝ)]
  have hUr : U ⊆ ball (0 : ℂ) r :=
    hr₀.trans (ball_subset_ball (by dsimp [r]; linarith [le_max_left r₀ (1 : ℝ)]))
  have hv := leastSupersolutionOn_mem_of_bounded_greenRegular hμ hvol hV
    (hUb.subset hVU) hz ht hboundary
  exact leastSupersolutionOn_le_of_subdomain_admissible hμ hV hU hUb hVU hz hx hxz ht.le
    ((greenPotentialBallContinuousStep_holds μ hμ r βm βp hr (hvol r hr)).mono
      (hVU.trans (hUr.trans ball_subset_closedBall)))
    ((greenPotentialBallLaplacianStep_holds μ hμ r βm βp hr (hvol r hr)).mono_domain
      (hVU.trans hUr)) hv

/-- The odometer gap is nonnegative and bounded by the Green-function gap. -/
theorem odometerOn_gap_le_greenFunction_gap
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hvol : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {V U : Set ℂ} (hV : IsOpen V) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hVU : closure V ⊆ U) {z x : ℂ} (hz : z ∈ V)
    (hx : x ∈ V) (hxz : x ≠ z) {t : ℝ} (ht : 0 < t)
    (hboundary : ∀ y ∈ closure V, y ∉ V →
      Tendsto (greenFunction V z) (𝓝[V] y) (𝓝 0)) :
    0 ≤ (leastSupersolutionOn μ U z t x + t * greenFunction U z x) -
        (leastSupersolutionOn μ V z t x + t * greenFunction V z x) ∧
      (leastSupersolutionOn μ U z t x + t * greenFunction U z x) -
        (leastSupersolutionOn μ V z t x + t * greenFunction V z x) ≤
          t * (greenFunction U z x - greenFunction V z x) := by
  have h₁ := odometerOn_le_of_compactly_contained_regular (μ := μ)
    hV hU hUb hVU hz hx hxz ht.le hboundary
  have h₂ := leastSupersolutionOn_le_of_regular_subdomain hμ hvol hV hU hUb
    (subset_closure.trans hVU) hz hx hxz ht hboundary
  constructor <;> linarith

/-- The odometers converge pointwise along a relatively compact regular
exhaustion, without assuming admissibility on the limiting domain. -/
theorem tendsto_odometerOn_of_regular_exhaustion
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hvol : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (V : ℕ → Set ℂ) (hopen : ∀ n, IsOpen (V n)) (hmono : Monotone V)
    (hcover : (⋃ n, V n) = U) (hsub : ∀ n, closure (V n) ⊆ U)
    {z x : ℂ} (hz : ∀ n, z ∈ V n) (hx : x ∈ U) (hxz : x ≠ z)
    {t : ℝ} (ht : 0 < t)
    (hboundary : ∀ n y, y ∈ closure (V n) → y ∉ V n →
      Tendsto (greenFunction (V n) z) (𝓝[V n] y) (𝓝 0)) :
    Tendsto (fun n => leastSupersolutionOn μ (V n) z t x + t * greenFunction (V n) z x)
      atTop (𝓝 (leastSupersolutionOn μ U z t x + t * greenFunction U z x)) := by
  let a := leastSupersolutionOn μ U z t x + t * greenFunction U z x
  have hg := tendsto_greenFunction_of_open_exhaustion V hopen hmono hU hUb hcover (hz 0) hx hxz
  have hlower : Tendsto (fun n => a - t * (greenFunction U z x - greenFunction (V n) z x))
      atTop (𝓝 a) := by
    have h : Tendsto (fun n => a - t * (greenFunction U z x - greenFunction (V n) z x))
        atTop (𝓝 (a - t * (greenFunction U z x - greenFunction U z x))) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.mul (tendsto_const_nhds.sub hg))
    simpa using h
  obtain ⟨N, hN⟩ := mem_iUnion.mp (hcover ▸ hx)
  have hb : ∀ᶠ n in atTop,
      a - t * (greenFunction U z x - greenFunction (V n) z x) ≤
          leastSupersolutionOn μ (V n) z t x + t * greenFunction (V n) z x ∧
      leastSupersolutionOn μ (V n) z t x + t * greenFunction (V n) z x ≤ a := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have h := odometerOn_gap_le_greenFunction_gap hμ hvol (hopen n) hU hUb (hsub n)
      (hz n) (hmono hn hN) hxz ht (hboundary n)
    dsimp [a]
    constructor <;> linarith [h.1, h.2]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower tendsto_const_nhds
    (hb.mono fun _ h => h.1) (hb.mono fun _ h => h.2)

/-- The cluster of the union is the increasing union of the clusters of its
relatively compact regular exhaustion. -/
theorem iUnion_clusterOn_eq_of_regular_exhaustion
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hvol : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (V : ℕ → Set ℂ) (hopen : ∀ n, IsOpen (V n)) (hmono : Monotone V)
    (hcover : (⋃ n, V n) = U) (hsub : ∀ n, closure (V n) ⊆ U)
    {z : ℂ} (hz : ∀ n, z ∈ V n) {t : ℝ} (ht : 0 < t)
    (hboundary : ∀ n y, y ∈ closure (V n) → y ∉ V n →
      Tendsto (greenFunction (V n) z) (𝓝[V n] y) (𝓝 0)) :
    (⋃ n, clusterOn μ (V n) z t) = clusterOn μ U z t := by
  apply Set.Subset.antisymm (iUnion_clusterOn_subset_of_regular_exhaustion hU hUb V hopen hsub hz ht.le hboundary)
  intro x hx
  rcases hx with ⟨hxU, hxbranch⟩
  by_cases hxz : x = z
  · subst x
    exact mem_iUnion.mpr ⟨0, hz 0, Or.inl rfl⟩
  · have hxpos := hxbranch.resolve_left hxz
    have hv := tendsto_odometerOn_of_regular_exhaustion hμ hvol hU hUb V hopen hmono
      hcover hsub hz hxU hxz ht hboundary
    have hp : 0 < leastSupersolutionOn μ U z t x + t * greenFunction U z x := by linarith
    have hev := hv.eventually (Ioi_mem_nhds hp)
    obtain ⟨N, hN⟩ := mem_iUnion.mp (hcover ▸ hxU)
    obtain ⟨n, hn, hnpos⟩ := (hev.and (eventually_ge_atTop N)).exists
    apply mem_iUnion.mpr
    refine ⟨n, hmono hnpos hN, Or.inr ?_⟩
    linarith

/-- If a regularized cluster is compactly contained in the union of an
increasing regular exhaustion, the closures of the exhausting-domain clusters
are eventually exactly its closure. -/
theorem eventually_closure_clusterOn_eq_regularized_of_exhaustion
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hvol : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {U : Set ℂ} (hUb : Bornology.IsBounded U)
    (V : ℕ → Set ℂ) (hopen : ∀ n, IsOpen (V n)) (hmono : Monotone V)
    (hcover : (⋃ n, V n) = U) (hsub : ∀ n, closure (V n) ⊆ U)
    {z : ℂ} (hz : ∀ n, z ∈ V n) {t : ℝ} (ht : 0 < t)
    (hboundary : ∀ n y, y ∈ closure (V n) → y ∉ V n →
      Tendsto (greenFunction (V n) z) (𝓝[V n] y) (𝓝 0))
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hcl : closure (Λ t) ⊆ U) :
    ∀ᶠ n in atTop, closure (Λ t) = closure (clusterOn μ (V n) z t) := by
  have hcompact : IsCompact (closure (Λ t)) :=
    isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure, (hΛ.1.isBounded t ht).closure⟩
  obtain ⟨N, hN⟩ := HarmonicBalls.IsCompact.subset_monotone_open_iUnion hcompact hopen hmono (hcover ▸ hcl)
  filter_upwards [eventually_ge_atTop N] with n hn
  exact regularizedFamily_closure_eq_clusterOn_of_boundary_of_volumeGrowth
    hμ hvol (hopen n) (hUb.subset (subset_closure.trans (hsub n)))
    (hz n) ht (hboundary n) hΛ (hN.trans (hmono hn))

/-- A compactly contained disc cluster gives equality of the corresponding
odometers on a Green-regular subdomain, away from the pole. -/
theorem odometerOn_eq_disc_of_compact_disc_cluster
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {V : Set ℂ} (hV : IsOpen V)
    {r βm βp : ℝ} (hr : 0 < r) (hvol : VolumeGrowth μ r βm βp)
    (hsub : V ⊆ ball (0 : ℂ) r) {z x : ℂ} (hz : z ∈ V) (hx : x ∈ V)
    (hxz : x ≠ z) {t : ℝ} (ht : 0 < t)
    (hboundary : ∀ y ∈ closure V, y ∉ V →
      Tendsto (greenFunction V z) (𝓝[V] y) (𝓝 0))
    (hcl : closure (cluster μ r z t) ⊆ V) :
    leastSupersolutionOn μ V z t x + t * greenFunction V z x =
      leastSupersolution μ r z t x + t * greenFunction (ball 0 r) z x := by
  obtain ⟨h, hc, hh, hG⟩ :=
    exists_continuousOn_green_difference_of_boundary_limits hV hsub hz hboundary
  have hd := (leastSupersolution_mem_of_general obstacleLeastSuperharmonicMajorantGeneral_holds
    obstacleCompatibilityShiftStep_holds hμ hr hvol (hsub hz) ht).2.2
  have hf := shifted_supersolutionOn_of_green_difference hV hsub hd hc hh hG
  have hupper := leastSupersolutionOn_le_of_mem hf (subset_closure hx) hxz
  have hlower : leastSupersolution μ r z t x + (-t) * h x ≤
      leastSupersolutionOn μ V z t x := by
    unfold leastSupersolutionOn
    apply le_csInf
    · exact ⟨_, ⟨_, hf, rfl⟩⟩
    · rintro _ ⟨v, hv, rfl⟩
      obtain ⟨w, hw, hwle⟩ := exists_disc_supersolution_le_shift_of_compact_cluster
        hμ hV hr hsub hz
        ((greenPotentialBallContinuousStep_holds μ hμ r βm βp hr hvol).mono
          (hsub.trans ball_subset_closedBall))
        ((greenPotentialBallLaplacianStep_holds μ hμ r βm βp hr hvol).mono_domain hsub)
        hc hh hG hd hcl hv
      have hwlower := leastSupersolution_le hw (ball_subset_closedBall (hsub hx)) hxz
      have hwupper := hwle x hx
      linarith
  have hgreen := hG x (subset_closure hx) hxz
  nlinarith

/-- If the regularized cluster is compactly contained in the exhausted
domain, the clusters of the regular domains eventually equal the cluster
in any disc containing that domain. -/
theorem eventually_clusterOn_eq_disc_of_regularized_compact_containment
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hvol : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {U : Set ℂ}
    (V : ℕ → Set ℂ) (hopen : ∀ n, IsOpen (V n)) (hmono : Monotone V)
    (hcover : (⋃ n, V n) = U) (hsub : ∀ n, closure (V n) ⊆ U)
    {z : ℂ} (hz : ∀ n, z ∈ V n) {t : ℝ} (ht : 0 < t)
    (hboundary : ∀ n y, y ∈ closure (V n) → y ∉ V n →
      Tendsto (greenFunction (V n) z) (𝓝[V n] y) (𝓝 0))
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hcl : closure (Λ t) ⊆ U) {r : ℝ} (hr : 0 < r)
    (hUr : U ⊆ ball (0 : ℂ) r) :
    (∀ᶠ n in atTop, clusterOn μ (V n) z t = cluster μ r z t) ∧
      (⋃ n, clusterOn μ (V n) z t) = cluster μ r z t := by
  have hzU : z ∈ U := hsub 0 (subset_closure (hz 0))
  have hrepr := hΛ.2.2 t ht r hr (hcl.trans hUr) r le_rfl
  have hcluster : closure (Λ t) = closure (cluster μ r z t) := by
    rw [hrepr, closure_regularizedCluster_eq_of_isOpen
      (isOpen_cluster_of_volumeGrowth hμ hvol ht r hr (hUr hzU))]
  have hcompact : IsCompact (closure (Λ t)) :=
    isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure, (hΛ.1.isBounded t ht).closure⟩
  obtain ⟨N, hN⟩ := HarmonicBalls.IsCompact.subset_monotone_open_iUnion
    hcompact hopen hmono (hcover ▸ hcl)
  have hevent : ∀ᶠ n in atTop, clusterOn μ (V n) z t = cluster μ r z t := by
    filter_upwards [eventually_ge_atTop N] with n hn
    exact clusterOn_eq_cluster_of_compact_disc_cluster_of_volumeGrowth
      hμ (hopen n) hr (hvol r hr) (subset_closure.trans ((hsub n).trans hUr))
      (hz n) ht (hboundary n) (hcluster ▸ hN.trans (hmono hn))
  refine ⟨hevent, ?_⟩
  obtain ⟨M, hM⟩ := eventually_atTop.mp hevent
  apply subset_antisymm
  · intro x hx
    obtain ⟨n, hxn⟩ := mem_iUnion.mp hx
    have hbounded : Bornology.IsBounded (V (max n M)) :=
      Metric.isBounded_ball.subset (subset_closure.trans ((hsub (max n M)).trans hUr))
    have hle := clusterOn_subset_of_nested_regular (μ := μ) (hopen n) (hopen (max n M))
      hbounded (hmono (le_max_left n M)) (hz n) ht.le (hboundary n) (hboundary (max n M))
    rw [hM (max n M) (le_max_right n M)] at hle
    exact hle hxn
  · intro x hx
    exact mem_iUnion.mpr ⟨M, (hM M le_rfl).symm ▸ hx⟩

/-- Under regularized compact containment, exhausting-domain odometer values
eventually equal the enclosing-disc odometer at each point away from the pole. -/
theorem eventually_odometerOn_eq_disc_of_regularized_compact_containment
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hvol : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {U : Set ℂ} (V : ℕ → Set ℂ) (hopen : ∀ n, IsOpen (V n)) (hmono : Monotone V)
    (hcover : (⋃ n, V n) = U) (hsub : ∀ n, closure (V n) ⊆ U)
    {z x : ℂ} (hz : ∀ n, z ∈ V n) (hx : x ∈ U) (hxz : x ≠ z)
    {t : ℝ} (ht : 0 < t)
    (hboundary : ∀ n y, y ∈ closure (V n) → y ∉ V n →
      Tendsto (greenFunction (V n) z) (𝓝[V n] y) (𝓝 0))
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hcl : closure (Λ t) ⊆ U) {r : ℝ} (hr : 0 < r)
    (hUr : U ⊆ ball (0 : ℂ) r) :
    ∀ᶠ n in atTop,
      leastSupersolutionOn μ (V n) z t x + t * greenFunction (V n) z x =
        leastSupersolution μ r z t x + t * greenFunction (ball 0 r) z x := by
  have hzU : z ∈ U := hsub 0 (subset_closure (hz 0))
  have hrepr := hΛ.2.2 t ht r hr (hcl.trans hUr) r le_rfl
  have hcluster : closure (Λ t) = closure (cluster μ r z t) := by
    rw [hrepr, closure_regularizedCluster_eq_of_isOpen
      (isOpen_cluster_of_volumeGrowth hμ hvol ht r hr (hUr hzU))]
  have hcompact : IsCompact (closure (Λ t)) :=
    isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure, (hΛ.1.isBounded t ht).closure⟩
  obtain ⟨N, hN⟩ := HarmonicBalls.IsCompact.subset_monotone_open_iUnion
    hcompact hopen hmono (hcover ▸ hcl)
  obtain ⟨M, hM⟩ := mem_iUnion.mp (hcover ▸ hx)
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop M] with n hn hm
  exact odometerOn_eq_disc_of_compact_disc_cluster hμ (hopen n) hr (hvol r hr)
    (subset_closure.trans ((hsub n).trans hUr)) (hz n) (hmono hm hM) hxz ht
    (hboundary n) (hcluster ▸ hN.trans (hmono hn))

/-- Under regularized compact containment, stabilization to the disc odometer
holds simultaneously on each compact set away from the pole. -/
theorem eventually_eqOn_odometerOn_disc_of_regularized_compact_containment
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hvol : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {U K : Set ℂ} {z : ℂ} (hK : IsCompact K) (hKU : K ⊆ U) (hzK : z ∉ K)
    (V : ℕ → Set ℂ) (hopen : ∀ n, IsOpen (V n)) (hmono : Monotone V)
    (hcover : (⋃ n, V n) = U) (hsub : ∀ n, closure (V n) ⊆ U)
    (hz : ∀ n, z ∈ V n) {t : ℝ} (ht : 0 < t)
    (hboundary : ∀ n y, y ∈ closure (V n) → y ∉ V n →
      Tendsto (greenFunction (V n) z) (𝓝[V n] y) (𝓝 0))
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hcl : closure (Λ t) ⊆ U) {r : ℝ} (hr : 0 < r)
    (hUr : U ⊆ ball (0 : ℂ) r) :
    ∀ᶠ n in atTop, EqOn
      (fun x => leastSupersolutionOn μ (V n) z t x + t * greenFunction (V n) z x)
      (fun x => leastSupersolution μ r z t x + t * greenFunction (ball 0 r) z x) K := by
  have hzU : z ∈ U := hsub 0 (subset_closure (hz 0))
  have hrepr := hΛ.2.2 t ht r hr (hcl.trans hUr) r le_rfl
  have hcluster : closure (Λ t) = closure (cluster μ r z t) := by
    rw [hrepr, closure_regularizedCluster_eq_of_isOpen
      (isOpen_cluster_of_volumeGrowth hμ hvol ht r hr (hUr hzU))]
  have hcompact : IsCompact (closure (Λ t)) :=
    isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure, (hΛ.1.isBounded t ht).closure⟩
  obtain ⟨N, hN⟩ := HarmonicBalls.IsCompact.subset_monotone_open_iUnion
    hcompact hopen hmono (hcover ▸ hcl)
  obtain ⟨M, hM⟩ := HarmonicBalls.IsCompact.subset_monotone_open_iUnion
    hK hopen hmono (hcover ▸ hKU)
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop M] with n hn hm
  intro x hx
  exact odometerOn_eq_disc_of_compact_disc_cluster hμ (hopen n) hr (hvol r hr)
    (subset_closure.trans ((hsub n).trans hUr)) (hz n) (hmono hm (hM hx))
    (fun h => hzK (h ▸ hx)) ht (hboundary n) (hcluster ▸ hN.trans (hmono hn))

/-- For a relatively countable deletion from a disc, regularized compact
containment makes the exhaustion odometers eventually equal the deleted-domain
odometer at every point away from the pole. -/
theorem eventually_odometerOn_eq_countable_deleted_disc
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hvol : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {R : ℝ} (hR : 0 < R) (K : Set ℂ)
    (hD : IsOpen (ball (0 : ℂ) R \ K)) (hK : (K ∩ ball (0 : ℂ) R).Countable)
    (V : ℕ → Set ℂ) (hopen : ∀ n, IsOpen (V n)) (hmono : Monotone V)
    (hcover : (⋃ n, V n) = ball (0 : ℂ) R \ K)
    (hsub : ∀ n, closure (V n) ⊆ ball (0 : ℂ) R \ K)
    {z x : ℂ} (hz : ∀ n, z ∈ V n) (hx : x ∈ ball (0 : ℂ) R \ K) (hxz : x ≠ z)
    {t : ℝ} (ht : 0 < t)
    (hboundary : ∀ n y, y ∈ closure (V n) → y ∉ V n →
      Tendsto (greenFunction (V n) z) (𝓝[V n] y) (𝓝 0))
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hcl : closure (Λ t) ⊆ ball (0 : ℂ) R \ K) :
    ∀ᶠ n in atTop,
      leastSupersolutionOn μ (V n) z t x + t * greenFunction (V n) z x =
        leastSupersolutionOn μ (ball (0 : ℂ) R \ K) z t x +
          t * greenFunction (ball (0 : ℂ) R \ K) z x := by
  have hzD : z ∈ ball (0 : ℂ) R \ K := hsub 0 (subset_closure (hz 0))
  have hcontain : closure (ball (0 : ℂ) R) ⊆ ball (0 : ℂ) (R + 1) :=
    (closure_minimal ball_subset_closedBall isClosed_closedBall).trans
      (closedBall_subset_ball (by linarith))
  let L := closure (ball (0 : ℂ) R ∩ K)
  have hDL : ball (0 : ℂ) R \ L = ball (0 : ℂ) R \ K :=
    sdiff_closure_inter_eq_of_isOpen_sdiff hD
  have hL : (L ∩ ball (0 : ℂ) R).Countable := by
    dsimp [L]
    simpa only [closure_inter_eq_inter_of_isOpen_sdiff hD] using hK
  have hd := (leastSupersolution_mem_of_general obstacleLeastSuperharmonicMajorantGeneral_holds
    obstacleCompatibilityShiftStep_holds hμ hR (hvol R hR) hzD.1 ht).2.2
  have heq : leastSupersolutionOn μ (ball (0 : ℂ) R) z t = leastSupersolution μ R z t := by
    funext y
    simp only [leastSupersolutionOn, leastSupersolution, supersolutionsOn_ball μ hR.ne']
  have hd' : leastSupersolutionOn μ (ball (0 : ℂ) R) z t ∈
      supersolutionsOn μ (ball (0 : ℂ) R) z t := by
    rw [heq, supersolutionsOn_ball μ hR.ne']
    exact hd
  have hv := leastSupersolutionOn_sdiff_eq_of_local_countable hμ isOpen_ball isBounded_ball
    hcontain isClosed_closure hL
    ((greenPotentialBallContinuousStep_holds μ hμ R βm βp hR (hvol R hR)).mono
      ball_subset_closedBall)
    (greenPotentialBallLaplacianStep_holds μ hμ R βm βp hR (hvol R hR)) ht.le
    (show z ∈ ball (0 : ℂ) R \ L from by rwa [hDL]) hd'
    (show x ∈ ball (0 : ℂ) R \ L from by rwa [hDL]) hxz
  have hg := greenFunction_sdiff_of_local_countable isOpen_ball
    (subset_closure.trans hcontain) isClosed_closure hL
    (show z ∈ ball (0 : ℂ) R \ L from by rwa [hDL])
    (show x ∈ ball (0 : ℂ) R \ L from by rwa [hDL]) hxz
  rw [hDL, heq] at hv
  rw [hDL] at hg
  simpa only [hv, hg] using
    (eventually_odometerOn_eq_disc_of_regularized_compact_containment hμ hvol V hopen hmono
      hcover hsub hz hx hxz ht hboundary hΛ hcl hR sdiff_subset)

/-- Either compact-containment alternative gives eventual equality with the
deleted-domain odometer after a relatively countable deletion from a disc. -/
theorem eventually_odometerOn_eq_countable_deleted_disc_of_compact_containment
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hvol : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {R : ℝ} (hR : 0 < R) (K : Set ℂ)
    (hD : IsOpen (ball (0 : ℂ) R \ K)) (hK : (K ∩ ball (0 : ℂ) R).Countable)
    (V : ℕ → Set ℂ) (hopen : ∀ n, IsOpen (V n)) (hmono : Monotone V)
    (hcover : (⋃ n, V n) = ball (0 : ℂ) R \ K)
    (hsub : ∀ n, closure (V n) ⊆ ball (0 : ℂ) R \ K)
    {z x : ℂ} (hz : ∀ n, z ∈ V n) (hx : x ∈ ball (0 : ℂ) R \ K) (hxz : x ≠ z)
    {t : ℝ} (ht : 0 < t)
    (hboundary : ∀ n y, y ∈ closure (V n) → y ∉ V n →
      Tendsto (greenFunction (V n) z) (𝓝[V n] y) (𝓝 0))
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hcl : closure (Λ t) ⊆ ball (0 : ℂ) R \ K ∨
      closure (clusterOn μ (ball (0 : ℂ) R \ K) z t) ⊆ ball (0 : ℂ) R \ K) :
    ∀ᶠ n in atTop,
      leastSupersolutionOn μ (V n) z t x + t * greenFunction (V n) z x =
        leastSupersolutionOn μ (ball (0 : ℂ) R \ K) z t x +
          t * greenFunction (ball (0 : ℂ) R \ K) z x := by
  have hzD : z ∈ ball (0 : ℂ) R \ K := hsub 0 (subset_closure (hz 0))
  have heq := regularizedFamily_strongCompatibility_relative_countable_disc
    hμ hvol hR K hD hK hzD ht hΛ hcl
  have hΛcl : closure (Λ t) ⊆ ball (0 : ℂ) R \ K := by
    rcases hcl with h | h
    · exact h
    · rw [heq]
      exact h
  exact eventually_odometerOn_eq_countable_deleted_disc hμ hvol hR K hD hK V hopen
    hmono hcover hsub hz hx hxz ht hboundary hΛ hΛcl

/-- Under the regularized-family compact-containment alternative, its closure
is contained in the limiting-domain cluster closure. -/
theorem regularized_closure_subset_clusterOn_of_regular_exhaustion
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hvol : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (V : ℕ → Set ℂ) (hopen : ∀ n, IsOpen (V n)) (hmono : Monotone V)
    (hcover : (⋃ n, V n) = U) (hsub : ∀ n, closure (V n) ⊆ U)
    {z : ℂ} (hz : ∀ n, z ∈ V n) {t : ℝ} (ht : 0 < t)
    (hboundary : ∀ n y, y ∈ closure (V n) → y ∉ V n →
      Tendsto (greenFunction (V n) z) (𝓝[V n] y) (𝓝 0))
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hcl : closure (Λ t) ⊆ U) :
    closure (Λ t) ⊆ closure (clusterOn μ U z t) := by
  obtain ⟨n, hn⟩ := (eventually_closure_clusterOn_eq_regularized_of_exhaustion
    hμ hvol hUb V hopen hmono hcover hsub hz ht hboundary hΛ hcl).exists
  rw [hn]
  exact closure_mono (clusterOn_subset_of_compactly_contained_regular
    (hopen n) hU hUb (hsub n) (hz n) ht.le (hboundary n))

/-- If the limiting-domain cluster is compactly contained, the exhausting
clusters eventually stabilize to the cluster of any fixed enclosing disc. -/
theorem eventually_clusterOn_eq_enclosing_disc_of_compact_containment
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hvol : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (V : ℕ → Set ℂ) (hopen : ∀ n, IsOpen (V n)) (hmono : Monotone V)
    (hcover : (⋃ n, V n) = U) (hsub : ∀ n, closure (V n) ⊆ U)
    {z : ℂ} (hz : ∀ n, z ∈ V n) {t : ℝ} (ht : 0 < t)
    (hboundary : ∀ n y, y ∈ closure (V n) → y ∉ V n →
      Tendsto (greenFunction (V n) z) (𝓝[V n] y) (𝓝 0))
    (hcl : closure (clusterOn μ U z t) ⊆ U)
    {r : ℝ} (hr : U ⊆ ball (0 : ℂ) r) :
    ∀ᶠ n in atTop, clusterOn μ (V n) z t = cluster μ r z t := by
  have hclusterb : Bornology.IsBounded (clusterOn μ U z t) :=
    hUb.subset (fun _ hx => hx.1)
  have hcompact : IsCompact (closure (clusterOn μ U z t)) :=
    isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure, hclusterb.closure⟩
  obtain ⟨N, hN⟩ := HarmonicBalls.IsCompact.subset_monotone_open_iUnion
    hcompact hopen hmono (hcover ▸ hcl)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hVb : Bornology.IsBounded (V n) :=
    hUb.subset (subset_closure.trans (hsub n))
  have hv := leastSupersolutionOn_mem_of_bounded_greenRegular
    hμ hvol (hopen n) hVb (hz n) ht (hboundary n)
  have hsmall : closure (clusterOn μ (V n) z t) ⊆ V n :=
    (closure_mono (clusterOn_subset_of_compactly_contained_regular
      (hopen n) hU hUb (hsub n) (hz n) ht.le (hboundary n))).trans
      (hN.trans (hmono hn))
  exact clusterOn_eq_cluster_of_compact_containment (hopen n)
    (subset_closure.trans ((hsub n).trans hr)) (hz n) ht hv hsmall

/-- Compact containment of the limiting-domain cluster also makes each
exhaustion odometer eventually equal the enclosing-disc odometer off the pole. -/
theorem eventually_odometerOn_eq_disc_of_clusterOn_compact_containment
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hvol : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (V : ℕ → Set ℂ) (hopen : ∀ n, IsOpen (V n)) (hmono : Monotone V)
    (hcover : (⋃ n, V n) = U) (hsub : ∀ n, closure (V n) ⊆ U)
    {z x : ℂ} (hz : ∀ n, z ∈ V n) (hx : x ∈ U) (hxz : x ≠ z)
    {t : ℝ} (ht : 0 < t)
    (hboundary : ∀ n y, y ∈ closure (V n) → y ∉ V n →
      Tendsto (greenFunction (V n) z) (𝓝[V n] y) (𝓝 0))
    (hcl : closure (clusterOn μ U z t) ⊆ U)
    {r : ℝ} (hr : 0 < r) (hUr : U ⊆ ball (0 : ℂ) r) :
    ∀ᶠ n in atTop,
      leastSupersolutionOn μ (V n) z t x + t * greenFunction (V n) z x =
        leastSupersolution μ r z t x + t * greenFunction (ball 0 r) z x := by
  have hclusterb : Bornology.IsBounded (clusterOn μ U z t) :=
    hUb.subset (fun _ hx' => hx'.1)
  have hcompact : IsCompact (closure (clusterOn μ U z t)) :=
    isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure, hclusterb.closure⟩
  obtain ⟨N, hN⟩ := HarmonicBalls.IsCompact.subset_monotone_open_iUnion
    hcompact hopen hmono (hcover ▸ hcl)
  obtain ⟨M, hM⟩ := mem_iUnion.mp (hcover ▸ hx)
  have hevent := eventually_clusterOn_eq_enclosing_disc_of_compact_containment
    hμ hvol hU hUb V hopen hmono hcover hsub hz ht hboundary hcl hUr
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop M, hevent] with n hn hm heq
  have hsmall : closure (cluster μ r z t) ⊆ V n := by
    rw [← heq]
    exact (closure_mono (clusterOn_subset_of_compactly_contained_regular
      (hopen n) hU hUb (hsub n) (hz n) ht.le (hboundary n))).trans
      (hN.trans (hmono hn))
  exact odometerOn_eq_disc_of_compact_disc_cluster hμ (hopen n) hr (hvol r hr)
    (subset_closure.trans ((hsub n).trans hUr)) (hz n) (hmono hm hM) hxz ht
    (hboundary n) hsmall

/-- For a relatively countable deletion from a disc, compact containment of
its cluster makes the exhaustion clusters eventually equal it as sets. -/
theorem eventually_clusterOn_eq_countable_deleted_disc_of_compact_containment
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hvol : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {R : ℝ} (hR : 0 < R) {z : ℂ} (K : Set ℂ)
    (hD : IsOpen (ball (0 : ℂ) R \ K)) (hK : (K ∩ ball (0 : ℂ) R).Countable)
    (V : ℕ → Set ℂ) (hopen : ∀ n, IsOpen (V n)) (hmono : Monotone V)
    (hcover : (⋃ n, V n) = ball (0 : ℂ) R \ K)
    (hsub : ∀ n, closure (V n) ⊆ ball (0 : ℂ) R \ K)
    (hz : ∀ n, z ∈ V n) {t : ℝ} (ht : 0 < t)
    (hboundary : ∀ n y, y ∈ closure (V n) → y ∉ V n →
      Tendsto (greenFunction (V n) z) (𝓝[V n] y) (𝓝 0))
    (hcl : closure (clusterOn μ (ball (0 : ℂ) R \ K) z t) ⊆
      ball (0 : ℂ) R \ K) :
    ∀ᶠ n in atTop, clusterOn μ (V n) z t =
      clusterOn μ (ball (0 : ℂ) R \ K) z t := by
  have hzU := hsub 0 (subset_closure (hz 0))
  have hclosure := closure_clusterOn_relative_countable_disc_eq hμ hR (hvol R hR) K hD hK hzU ht
  have hdisj : Disjoint (cluster μ R z t) K := by
    apply disjoint_left.mpr
    intro x hx hKx
    have hxU := hcl (hclosure.symm ▸ subset_closure hx)
    exact hxU.2 hKx
  have heq : clusterOn μ (ball (0 : ℂ) R \ K) z t = cluster μ R z t := by
    rw [clusterOn_relative_countable_disc_eq_sdiff hμ hR (hvol R hR) K hD hK hzU ht]
    exact sdiff_eq_left.mpr hdisj
  have hstable := eventually_clusterOn_eq_enclosing_disc_of_compact_containment
    hμ hvol hD (isBounded_ball.subset sdiff_subset)
    V hopen hmono hcover hsub hz ht hboundary hcl sdiff_subset
  filter_upwards [hstable] with n hn
  exact hn.trans heq.symm


/-- For a punctured disc, compact containment of the limiting cluster makes
regular exhaustion clusters eventually equal that cluster as sets. The proof
does not require the punctured-domain infimum to be admissible. -/
theorem eventually_clusterOn_eq_punctured_disc_of_compact_containment
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hvol : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {R : ℝ} (hR : 0 < R) {z a : ℂ}
    (V : ℕ → Set ℂ) (hopen : ∀ n, IsOpen (V n)) (hmono : Monotone V)
    (hcover : (⋃ n, V n) = ball (0 : ℂ) R \ {a})
    (hsub : ∀ n, closure (V n) ⊆ ball (0 : ℂ) R \ {a})
    (hz : ∀ n, z ∈ V n) {t : ℝ} (ht : 0 < t)
    (hboundary : ∀ n y, y ∈ closure (V n) → y ∉ V n →
      Tendsto (greenFunction (V n) z) (𝓝[V n] y) (𝓝 0))
    (hcl : closure (clusterOn μ (ball (0 : ℂ) R \ {a}) z t) ⊆
      ball (0 : ℂ) R \ {a}) :
    ∀ᶠ n in atTop, clusterOn μ (V n) z t =
      clusterOn μ (ball (0 : ℂ) R \ {a}) z t := by
  exact eventually_clusterOn_eq_countable_deleted_disc_of_compact_containment
    hμ hvol hR {a} (isOpen_ball.sdiff isClosed_singleton)
    (Set.Countable.mono inter_subset_left (Set.countable_singleton a))
    V hopen hmono hcover hsub hz ht hboundary hcl

/-- Eventual stabilization of closures commutes with an increasing union. -/
theorem closure_iUnion_eq_of_eventually_closure_eq
    (A : ℕ → Set ℂ) (hmono : Monotone A) {C : Set ℂ}
    (hC : ∀ᶠ n in atTop, closure (A n) = C) :
    closure (⋃ n, A n) = C := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hC
  apply Set.Subset.antisymm
  · apply closure_minimal _ (hN N le_rfl ▸ isClosed_closure)
    intro x hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    have hm := hN (max n N) (le_max_right _ _)
    rw [← hm]
    exact subset_closure (hmono (le_max_left _ _) hn)
  · rw [← hN N le_rfl]
    exact closure_mono (subset_iUnion A N)

/-- Both compact-containment alternatives imply strong compatibility, provided
the indicated regular exhaustion is available. -/
theorem regularizedFamily_closure_eq_clusterOn_of_regular_exhaustion
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hvol : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (V : ℕ → Set ℂ) (hopen : ∀ n, IsOpen (V n)) (hmono : Monotone V)
    (hcover : (⋃ n, V n) = U) (hsub : ∀ n, closure (V n) ⊆ U)
    {z : ℂ} (hz : ∀ n, z ∈ V n) {t : ℝ} (ht : 0 < t)
    (hboundary : ∀ n y, y ∈ closure (V n) → y ∉ V n →
      Tendsto (greenFunction (V n) z) (𝓝[V n] y) (𝓝 0))
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hcl : closure (Λ t) ⊆ U ∨ closure (clusterOn μ U z t) ⊆ U) :
    closure (Λ t) = closure (clusterOn μ U z t) := by
  have hclusters : Monotone (fun n => clusterOn μ (V n) z t) := by
    intro n m hnm
    exact clusterOn_subset_of_nested_regular (hopen n) (hopen m)
      (hUb.subset (subset_closure.trans (hsub m))) (hmono hnm) (hz n) ht.le
      (hboundary n) (hboundary m)
  have hev : ∀ᶠ n in atTop, closure (clusterOn μ (V n) z t) = closure (Λ t) := by
    rcases hcl with hΛcl | hUcl
    · exact (eventually_closure_clusterOn_eq_regularized_of_exhaustion
        hμ hvol hUb V hopen hmono hcover hsub hz ht hboundary hΛ hΛcl).mono
        (fun _ h => h.symm)
    · obtain ⟨r₁, hr₁⟩ := hUb.subset_ball (0 : ℂ)
      obtain ⟨r₂, hr₂⟩ := ((hΛ.1.isBounded t ht).closure).subset_ball (0 : ℂ)
      let r := max 1 (max r₁ r₂) + 1
      have hr : 0 < r := by dsimp [r]; linarith [le_max_left (1 : ℝ) (max r₁ r₂)]
      have hr₁r : r₁ ≤ r := by dsimp [r]; linarith [(le_max_left r₁ r₂).trans (le_max_right (1 : ℝ) (max r₁ r₂))]
      have hr₂r : r₂ ≤ r := by dsimp [r]; linarith [(le_max_right r₁ r₂).trans (le_max_right (1 : ℝ) (max r₁ r₂))]
      have hUr : U ⊆ ball (0 : ℂ) r := hr₁.trans (ball_subset_ball hr₁r)
      have hΛr : closure (Λ t) ⊆ ball (0 : ℂ) r := hr₂.trans (ball_subset_ball hr₂r)
      have hrepr := hΛ.2.2 t ht r hr hΛr r le_rfl
      have hzU : z ∈ U := hsub 0 (subset_closure (hz 0))
      have heq : closure (Λ t) = closure (cluster μ r z t) := by
        rw [hrepr, closure_regularizedCluster_eq_of_isOpen
          (isOpen_cluster_of_volumeGrowth hμ hvol ht r hr (hUr hzU))]
      filter_upwards [eventually_clusterOn_eq_enclosing_disc_of_compact_containment
        hμ hvol hU hUb V hopen hmono hcover hsub hz ht hboundary hUcl hUr] with n hn
      rw [hn, ← heq]
  rw [← iUnion_clusterOn_eq_of_regular_exhaustion hμ hvol hU hUb V hopen hmono
    hcover hsub hz ht hboundary]
  exact (closure_iUnion_eq_of_eventually_closure_eq _ hclusters hev).symm



end HarmonicBalls
