import HarmonicBalls.Proofs.Sec5.ContactMassContinuity
import HarmonicBalls.Proofs.Sec5.BoundaryContinuityCompactness
import HarmonicBalls.Proofs.Sec7.ClusterContinuity

/-!
# Local exclusion at boundary contact

A good annulus away from the current cluster excludes new limit points inside
its inner ball when later cluster increments have vanishing measure.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Section6
open scoped Pointwise

/-- A Harnack barrier whose annulus misses the current set excludes points in
its inner ball from the intersection of the future closures. -/
theorem not_mem_iInter_closure_of_harnack_barrier
    (μ : Measure ℂ) (A : Set ℂ) (B : ℕ → Set ℂ) (w : ℂ) (ρ α : ℝ)
    (hdis : Disjoint (annulus w (ρ / 2) ρ) A)
    (hpositive : 0 < ENNReal.ofReal α * μ (annulus w (ρ / 2) ρ))
    (hmass : ∀ n, μ (B n \ A) ≤ ENNReal.ofReal (dyadicScale n))
    (hharnack : ∀ n,
      μ (B n ∩ annulus w (ρ / 2) ρ) ≤ ENNReal.ofReal α * μ (annulus w (ρ / 2) ρ) →
      B n ∩ ball w (ρ / 2) = ∅) :
    Disjoint (⋂ n, closure (B n)) (ball w (ρ / 2)) := by
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (dyadicScale n)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal
      (tendsto_dyadicScale_nhdsGT.mono_right nhdsWithin_le_nhds)
  obtain ⟨n, hn⟩ := (hlim.eventually (Iio_mem_nhds hpositive)).exists
  have hsmall : μ (B n ∩ annulus w (ρ / 2) ρ) ≤
      ENNReal.ofReal α * μ (annulus w (ρ / 2) ρ) := by
    calc
      _ ≤ μ (B n \ A) := measure_mono (by
        intro x hx
        exact ⟨hx.1, fun hxA => Set.disjoint_left.mp hdis hx.2 hxA⟩)
      _ ≤ ENNReal.ofReal (dyadicScale n) := hmass n
      _ ≤ _ := hn.le
  have hempty := hharnack n hsmall
  have hsub : B n ⊆ (ball w (ρ / 2))ᶜ := by
    intro x hx hxball
    exact (eq_empty_iff_forall_notMem.mp hempty) x ⟨hx, hxball⟩
  apply Set.disjoint_left.mpr
  intro x hx hxball
  exact (closure_minimal hsub isOpen_ball.isClosed_compl (Set.mem_iInter.mp hx n)) hxball

/-- Eventually good prevalence grids provide arbitrarily local barriers at
any nonzero point outside the closure of the current set. -/
theorem exists_good_annulus_around_point
    (A : Set ℂ) (x : ℂ) (hx : x ∈ ball (0 : ℂ) 1) (hx0 : x ≠ 0)
    (hxA : x ∉ closure A) (N : ℕ) (P : ℝ → ℂ → Prop)
    (hgood : ∀ᶠ n : ℕ in atTop, ∀ w ∈ prevalenceGrid (dyadicScale n),
      ∃ ρ ∈ Icc (dyadicScale n) (Real.sqrt (dyadicScale n)), P ρ w) :
    ∃ n w ρ, N ≤ n ∧ w ∈ prevalenceGrid (dyadicScale n) ∧
      ρ ∈ Icc (dyadicScale n) (Real.sqrt (dyadicScale n)) ∧ ρ < 1 ∧ P ρ w ∧
      x ∈ ball w (ρ / 2) ∧ closedBall w ρ ⊆ ball 0 1 \ A := by
  have hV : IsOpen (ball (0 : ℂ) 1 \ closure A) := isOpen_ball.sdiff isClosed_closure
  obtain ⟨d, hd, hdsub⟩ := Metric.isOpen_iff.mp hV x ⟨hx, hxA⟩
  let q : ℝ := min (min (d / 4) (dist x 0 / 40)) (1 / 4)
  have hq : 0 < q := by dsimp [q]; exact lt_min (lt_min (by positivity)
    (div_pos (dist_pos.mpr hx0) (by norm_num))) (by norm_num)
  have hqd : q ≤ d / 4 := (min_le_left _ _).trans (min_le_left _ _)
  have hqx : q ≤ dist x 0 / 40 := (min_le_left _ _).trans (min_le_right _ _)
  have hq1 : q ≤ 1 / 4 := min_le_right _ _
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hgood
  obtain ⟨N₂, hN₂⟩ := exists_pow_lt_of_lt_one (sq_pos_of_pos hq)
    (by norm_num : (2 : ℝ)⁻¹ < 1)
  let n := max N (max N₁ N₂)
  have hn : N ≤ n := le_max_left _ _
  have hn1 : N₁ ≤ n := (le_max_left N₁ N₂).trans (le_max_right _ _)
  have hn2 : N₂ ≤ n := (le_max_right N₁ N₂).trans (le_max_right _ _)
  have hs : 0 < dyadicScale n := dyadicScale_pos n
  have hs2 : dyadicScale n < q ^ 2 := by
    calc
      dyadicScale n ≤ dyadicScale N₂ := by
        dsimp [dyadicScale]
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hn2
      _ < q ^ 2 := hN₂
  have hsroot : Real.sqrt (dyadicScale n) < q := (Real.sqrt_lt hs.le hq.le).2 hs2
  have hsq : dyadicScale n < q := by nlinarith
  have hxunit : dist x 0 < 1 := mem_ball.mp hx
  obtain ⟨w, hw, hwx⟩ := exists_prevalenceGrid_dist_lt hs hxunit (by linarith)
  obtain ⟨ρ, hρ, hP⟩ := hN₁ n hn1 w hw
  have hρpos : 0 < ρ := lt_of_lt_of_le hs hρ.1
  have hρq : ρ < q := lt_of_le_of_lt hρ.2 hsroot
  refine ⟨n, w, ρ, hn, hw, hρ, by linarith, hP, ?_, ?_⟩
  · rw [mem_ball]
    linarith [hρ.1]
  · intro y hy
    have hyw : dist y w ≤ ρ := mem_closedBall.mp hy
    have hyx : dist y x < d := by
      have hh := dist_triangle y w x
      rw [dist_comm w x] at hh
      linarith
    have hyV := hdsub (mem_ball.mpr hyx)
    exact ⟨hyV.1, fun hyA => hyV.2 (subset_closure hyA)⟩

/-- Good grid annuli and a volume lower bound rule out new interior limit
points away from the origin when the mass of the increment vanishes. -/
theorem iInter_future_closure_inter_ball_subset_closure_union_origin
    (μ : Measure ℂ) (A : Set ℂ) (B : ℕ → Set ℂ) (α β : ℝ) (hα : 0 < α)
    (P : ℝ → ℂ → Prop)
    (hgood : ∀ᶠ n : ℕ in atTop,
      (∀ x ∈ ball (0 : ℂ) 1,
        ENNReal.ofReal ((dyadicScale n / 8) ^ β) ≤ μ (ball x (dyadicScale n / 8))) ∧
      (∀ w ∈ prevalenceGrid (dyadicScale n),
        ∃ ρ ∈ Icc (dyadicScale n) (Real.sqrt (dyadicScale n)), P ρ w))
    (hmass : ∀ n, μ (B n \ A) ≤ ENNReal.ofReal (dyadicScale n))
    (hharnack : ∀ n w ρ, ρ ∈ Ioo (0 : ℝ) 1 → P ρ w →
      closedBall w ρ ⊆ ball 0 1 \ A →
      μ (B n ∩ annulus w (ρ / 2) ρ) ≤ ENNReal.ofReal α * μ (annulus w (ρ / 2) ρ) →
      B n ∩ ball w (ρ / 2) = ∅) :
    (⋂ n, closure (B n)) ∩ ball 0 1 ⊆ closure A ∪ {0} := by
  intro x hx
  by_cases hxA : x ∈ closure A
  · exact Or.inl hxA
  by_cases hx0 : x = 0
  · exact Or.inr (by simpa using hx0)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hgood
  have hscales : ∀ᶠ n : ℕ in atTop, ∀ w ∈ prevalenceGrid (dyadicScale n),
      ∃ ρ ∈ Icc (dyadicScale n) (Real.sqrt (dyadicScale n)), P ρ w :=
    hgood.mono fun _ h => h.2
  obtain ⟨k, w, ρ, hk, hw, hρ, hρ1, hP, hxinner, hdomain⟩ :=
    exists_good_annulus_around_point A x hx.2 hx0 hxA N P hscales
  have hs : 0 < dyadicScale k := dyadicScale_pos k
  have hρpos : 0 < ρ := lt_of_lt_of_le hs hρ.1
  have hvol := (hN k hk).1
  have hlower : ENNReal.ofReal ((dyadicScale k / 8) ^ β) ≤ μ (annulus w (ρ / 2) ρ) :=
    lower_mass_half_annulus_of_ball_volume μ hs hvol hρ.1 (hdomain.trans sdiff_subset)
  have hpositive : 0 < ENNReal.ofReal α * μ (annulus w (ρ / 2) ρ) := by
    apply ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hα).ne'
    exact (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos (by positivity) β)) hlower).ne'
  have hdis : Disjoint (annulus w (ρ / 2) ρ) A := by
    apply Set.disjoint_left.mpr
    intro y hy hyA
    exact (hdomain (ball_subset_closedBall hy.1)).2 hyA
  have h := not_mem_iInter_closure_of_harnack_barrier μ A B w ρ α hdis hpositive hmass
    (fun n => hharnack n w ρ ⟨hρpos, hρ1⟩ hP hdomain)
  exact False.elim ((Set.disjoint_left.mp h) hx.1 hxinner)

/-- For decreasing closed preconnected sets containing the current set, the
origin cannot be an isolated new interior point of the intersection. -/
theorem iInter_inter_ball_subset_closure_of_subset_union_origin
    (A : Set ℂ) (F : ℕ → Set ℂ) (z : ℂ) (hz : z ∈ A)
    (hclosed : ∀ n, IsClosed (F n)) (hanti : Antitone F)
    (hconnected : ∀ n, IsPreconnected (F n)) (hAF : ∀ n, A ⊆ F n)
    (hsub : (⋂ n, F n) ∩ ball 0 1 ⊆ closure A ∪ {0}) :
    (⋂ n, F n) ∩ ball 0 1 ⊆ closure A := by
  intro x hx
  rcases hsub hx with hxA | hx0
  · exact hxA
  have hx0' : x = 0 := by simpa using hx0
  subst x
  by_contra h0
  have hV : IsOpen (ball (0 : ℂ) 1 \ closure A) := isOpen_ball.sdiff isClosed_closure
  have h0V : (0 : ℂ) ∈ ball (0 : ℂ) 1 \ closure A := ⟨by simp, h0⟩
  obtain ⟨d, hd, hdsub⟩ := Metric.isOpen_iff.mp hV 0 h0V
  let q : ℝ := d / 2
  have hq : 0 < q := by dsimp [q]; positivity
  have hqd : q < d := by dsimp [q]; linarith
  have hdis : Disjoint (sphere (0 : ℂ) q) (⋂ n, F n) := by
    apply Set.disjoint_left.mpr
    intro y hy hyF
    have hydist : dist y 0 = q := mem_sphere.mp hy
    have hyV := hdsub (mem_ball.mpr (by linarith))
    rcases hsub ⟨hyF, hyV.1⟩ with hyA | hy0
    · exact hyV.2 hyA
    · have hyzero : y = 0 := by simpa using hy0
      subst y
      simp only [dist_self] at hydist
      linarith
  obtain ⟨n, hn⟩ := (isCompact_sphere (0 : ℂ) q).elim_directed_family_closed F hclosed hdis
    hanti.directed_ge
  have hzdist : d ≤ dist z 0 := by
    by_contra h
    have hzV := hdsub (mem_ball.mpr (lt_of_not_ge h))
    exact hzV.2 (subset_closure hz)
  have h0F : (0 : ℂ) ∈ F n := Set.mem_iInter.mp hx.1 n
  have hzF : z ∈ F n := hAF n hz
  have hbetween : q ∈ Icc (dist (0 : ℂ) 0) (dist z 0) :=
    ⟨by simpa using hq.le, by linarith⟩
  obtain ⟨y, hyF, hyq⟩ := (hconnected n).intermediate_value (f := fun y : ℂ => dist y 0)
    h0F hzF (continuous_id.dist continuous_const).continuousOn hbetween
  change dist y 0 = q at hyq
  exact Set.disjoint_left.mp hn (mem_sphere.mpr hyq) hyF

universe u

/-- At a time approached by compactly contained clusters, future closures
cannot acquire an interior point other than the origin outside the present
closure. The estimate holds simultaneously for all centres and such times. -/
theorem ae_future_closure_inter_ball_subset_closure_union_origin_of_steps
    (hvolume : LiouvilleVolumeGrowthStmt.{u})
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h34 : ClusterConservationOfMassStmt.{u}) (h61 : HarnackTypeEstimateStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u}) (h82 : TypicalPointManyGoodScalesStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα₀ : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      (∀ s ∈ Ioo (0 : ℝ) t, closure (cluster (μ ω) 1 z s) ⊆ ball 0 1) →
      (⋂ n : ℕ, closure (cluster (μ ω) 1 z (t + dyadicScale n))) ∩ ball 0 1 ⊆
        closure (cluster (μ ω) 1 z t) ∪ {0} := by
  obtain ⟨c, hc, h61⟩ := h61
  obtain ⟨α, hα, h61⟩ := h61 γ hγ hγ2
  obtain ⟨E, hE, hcount⟩ := h61 α₀ hα₀ Ω P hC hcirc μ hGFF hμ
  let v : ℝ := min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀))
  have hv : 0 < v := by
    dsimp [v]
    exact lt_min (by positivity) (mul_pos hγ (sub_pos.mpr hα₀))
  let βplus : ℝ := v / 2
  have hβplus : 0 < βplus := by dsimp [βplus]; positivity
  have hβplus' : βplus < v := by dsimp [βplus]; linarith
  let β : ℝ := max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) + 1
  have hβ : max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) < β := by dsimp [β]; linarith
  have hvol0 := (hvolume γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ βplus β
    hβplus hβplus' hβ).1
  have hvol : PolyHighProb P (fun s => {ω | ∀ x ∈ ball (0 : ℂ) 1,
      ENNReal.ofReal (s ^ β) ≤ μ ω (ball x s)}) := by
    apply hvol0.mono
    intro s ω hω x hx
    exact (hω x hx).1
  have hdyadic := ((hvol.comp_mul (c := (1 : ℝ) / 8) (by norm_num)).inter hcount).ae_eventually_dyadic
  filter_upwards [hdyadic,
    ae_cluster_contact_mass_and_increment_of_steps h32 h33 h34 h611 h82
      γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hgood hmass
  have hgood' : ∀ᶠ n : ℕ in atTop,
      (∀ x ∈ ball (0 : ℂ) 1,
        ENNReal.ofReal ((dyadicScale n / 8) ^ β) ≤ μ ω (ball x (dyadicScale n / 8))) ∧
      (∀ w ∈ prevalenceGrid (dyadicScale n),
        ∃ ρ ∈ Icc (dyadicScale n) (Real.sqrt (dyadicScale n)), ω ∈ E ρ w) := by
    filter_upwards [hgood, eventually_ge_atTop 1] with n hn hn1
    have hs : 0 < ((2 : ℝ)⁻¹) ^ n := by positivity
    have hs1 : ((2 : ℝ)⁻¹) ^ n < 1 := by
      have hp := pow_le_pow_of_le_one (show (0 : ℝ) ≤ (2 : ℝ)⁻¹ by norm_num)
        (show (2 : ℝ)⁻¹ ≤ 1 by norm_num) hn1
      norm_num at hp ⊢
      linarith
    refine ⟨?_, ?_⟩
    · simpa only [dyadicScale, mem_ofPred_eq, one_div, div_eq_mul_inv, one_mul, mul_comm] using hn.1
    · simpa only [dyadicScale] using exists_good_scale_of_prevalence_count hc hs hs1 hn.2
  intro t ht z hz hcompact
  apply iInter_future_closure_inter_ball_subset_closure_union_origin
    (μ ω) (cluster (μ ω) 1 z t) (fun n => cluster (μ ω) 1 z (t + dyadicScale n))
    α β hα (fun ρ w => ω ∈ E ρ w) hgood'
  · intro n
    simpa using (hmass t ht z hz hcompact).2 (t + dyadicScale n)
      (le_add_of_nonneg_right (dyadicScale_pos n).le)
  · intro n w ρ hρ hEρ hdomain hsmall
    apply hE ω ρ hρ w hEρ z hz (t + dyadicScale n)
      (add_pos ht (dyadicScale_pos n)) _ hsmall
    intro y hy
    refine ⟨(hdomain hy).1, ?_⟩
    intro hyz
    have hyz' : y = z := by simpa using hyz
    exact (hdomain hy).2 (hyz'.symm ▸ self_mem_cluster (μ := μ ω) (t := t) hz)

/-- At a time approached by compactly contained clusters, the future-closure
intersection has no new points inside the disc. -/
theorem ae_future_closure_inter_ball_subset_closure_of_steps
    (hvolume : LiouvilleVolumeGrowthStmt.{u})
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h34 : ClusterConservationOfMassStmt.{u}) (h61 : HarnackTypeEstimateStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u}) (h82 : TypicalPointManyGoodScalesStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα₀ : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      (∀ s ∈ Ioo (0 : ℝ) t, closure (cluster (μ ω) 1 z s) ⊆ ball 0 1) →
      (⋂ n : ℕ, closure (cluster (μ ω) 1 z (t + dyadicScale n))) ∩ ball 0 1 ⊆
        closure (cluster (μ ω) 1 z t) := by
  filter_upwards [h32 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    h33 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_future_closure_inter_ball_subset_closure_union_origin_of_steps
      hvolume h32 h33 h34 h61 h611 h82 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ]
    with ω hconnected hmono hsub
  intro t ht z hz hcompact
  apply iInter_inter_ball_subset_closure_of_subset_union_origin (cluster (μ ω) 1 z t)
    (fun n => closure (cluster (μ ω) 1 z (t + dyadicScale n))) z (self_mem_cluster hz)
  · exact fun _ => isClosed_closure
  · intro i j hij
    apply closure_mono
    have hscale : dyadicScale j ≤ dyadicScale i := by
      dsimp [dyadicScale]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hij
    exact hmono _ _ 1 (add_pos ht (dyadicScale_pos j)) (by linarith)
      zero_lt_one z hz
  · intro n
    exact (hconnected (t + dyadicScale n) 1 (add_pos ht (dyadicScale_pos n))
      zero_lt_one z hz).2.1.isPreconnected.closure
  · intro n x hx
    exact subset_closure (hmono t (t + dyadicScale n) 1 ht
      (le_add_of_nonneg_right (dyadicScale_pos n).le) zero_lt_one z hz hx)
  · exact hsub t ht z hz hcompact

/-- At a first-contact time, right continuity follows once the future
closures acquire no new points on the unit circle. -/
theorem ae_cluster_right_continuity_at_contact_of_sphere_inclusion
    (hvolume : LiouvilleVolumeGrowthStmt.{u})
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h34 : ClusterConservationOfMassStmt.{u}) (h61 : HarnackTypeEstimateStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u}) (h82 : TypicalPointManyGoodScalesStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα₀ : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      (∀ s ∈ Ioo (0 : ℝ) t, closure (cluster (μ ω) 1 z s) ⊆ ball 0 1) →
      ((⋂ n : ℕ, closure (cluster (μ ω) 1 z (t + dyadicScale n))) ∩ sphere 0 1 ⊆
        closure (cluster (μ ω) 1 z t)) →
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
        closure (cluster (μ ω) 1 z s) ⊆ cluster (μ ω) 1 z t + ball (0 : ℂ) ε := by
  filter_upwards [h33 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_future_closure_inter_ball_subset_closure_of_steps
      hvolume h32 h33 h34 h61 h611 h82 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ]
    with ω hmono hinterior
  intro t ht z hz hcompact hsphere
  apply (cluster_closure_dyadic_iInter_subset_iff_right_continuous ht
    (fun s s' hs hss' => hmono s s' 1 hs hss' zero_lt_one z hz)).1
  intro x hx
  have hx' : x ∈ ⋂ n : ℕ, closure (cluster (μ ω) 1 z (t + dyadicScale n)) := by
    simpa only [dyadicScale] using hx
  by_cases hxball : x ∈ ball (0 : ℂ) 1
  · exact hinterior t ht z hz hcompact ⟨hx', hxball⟩
  · have hxclosed : x ∈ closedBall (0 : ℂ) 1 :=
      closure_minimal (cluster_subset_ball.trans ball_subset_closedBall) isClosed_closedBall
        (Set.mem_iInter.mp hx' 0)
    have hxdist : dist x 0 = 1 := by
      have hle := mem_closedBall.mp hxclosed
      have hge : 1 ≤ dist x 0 := le_of_not_gt (by simpa only [mem_ball] using hxball)
      exact le_antisymm hle hge
    exact hsphere ⟨hx', mem_sphere.mpr hxdist⟩

end HarmonicBalls
