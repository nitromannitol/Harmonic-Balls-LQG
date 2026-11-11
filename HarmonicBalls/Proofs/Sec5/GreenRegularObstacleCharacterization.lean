import HarmonicBalls.Proofs.Sec5.GreenRegularDomainAdmissibility
import HarmonicBalls.Proofs.Sec5.GeneralDomainClusterOpen
import HarmonicBalls.Proofs.Sec5.GeneralDomainNoncontactHarmonicity

/-! # Green-regular obstacle characterization

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Laplacian
open scoped Topology

/-- A continuous candidate has an open noncontact set, including its pole. -/
theorem isOpen_candidate_noncontact
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t)
    (w : ℂ → ℝ) (hw : ContinuousOn w (closure U)) :
    IsOpen {x ∈ U | x = z ∨ -t * greenFunction U z x < w x} := by
  obtain ⟨R, hUR⟩ := hUb.subset_ball (0 : ℂ)
  obtain ⟨h, hh, hG⟩ := exists_harmonicOnNhd_greenFunction_difference hU hUb hUR hz
  have hvcont : ∀ x ∈ U, ContinuousAt (w) x := by
    intro x hx
    exact hw.continuousAt (mem_of_superset (hU.mem_nhds hx) subset_closure)
  rw [isOpen_iff_mem_nhds]
  intro x hx
  by_cases hxz : x = z
  · subst x
    have hvnear : ∀ᶠ y in 𝓝 z,
        w z - 1 < w y :=
      (hvcont z hz).eventually (Ioi_mem_nhds (by linarith))
    have hhnear : ∀ᶠ y in 𝓝 z, h z - 1 < h y :=
      ((hh z hz).1.continuousAt).eventually (Ioi_mem_nhds (by linarith))
    have hnear : ∀ᶠ y in 𝓝[≠] z,
        (1 - w z - t * (h z - 1)) / t <
          greenFunction (ball (0 : ℂ) R) z y :=
      (tendsto_greenFunction_ball_pole (hUR hz)).eventually (eventually_gt_atTop _)
    rw [eventually_nhdsWithin_iff] at hnear
    filter_upwards [hU.mem_nhds hz, hvnear, hhnear, hnear] with y hy hyv hyh hyG
    refine ⟨hy, ?_⟩
    by_cases hyz : y = z
    · exact Or.inl hyz
    · right
      have hineq := (div_lt_iff₀ ht).mp (hyG hyz)
      have heq := hG y hy hyz
      nlinarith
  · have hGcont : ContinuousAt (greenFunction U z) x := by
      have hc := ((hh x hx.1).1.continuousAt).add
        ((continuousOn_greenFunction_ball (hUR hz)).continuousAt
          (isOpen_compl_singleton.mem_nhds hxz))
      apply hc.congr_of_eventuallyEq
      filter_upwards [hU.mem_nhds hx.1, isOpen_compl_singleton.mem_nhds hxz] with y hy hyz
      have heq := hG y hy hyz
      change greenFunction U z y = h y + greenFunction (ball 0 R) z y
      linarith
    have hlt : -t * greenFunction U z x < w x :=
      hx.2.resolve_left hxz
    filter_upwards [hU.mem_nhds hx.1,
      (hGcont.const_mul (-t)).eventually_lt (hvcont x hx.1) hlt] with y hy hlt'
    exact ⟨hy, Or.inr hlt'⟩


/-- Comparison on a bounded domain when the larger function has the prescribed
Laplacian wherever it is strictly larger. -/
theorem eqOn_of_obstacle_comparison {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {μ : Measure ℂ} {w v : ℂ → ℝ}
    (hwc : ContinuousOn w (closure U)) (hvc : ContinuousOn v (closure U))
    (hv : LaplacianLE v μ U)
    (hw : HasLaplacian w μ 0 {x ∈ U | v x < w x})
    (hboundary : ∀ x ∈ closure U, x ∉ U → w x = v x)
    (hle : ∀ x ∈ U, v x ≤ w x) : EqOn w v (closure U) := by
  let W := {x ∈ U | v x < w x}
  have hdc : ContinuousOn (fun x => w x - v x) (closure U) := hwc.sub hvc
  have hWo : IsOpen W := by
    convert (hdc.mono subset_closure).isOpen_inter_preimage hU (isOpen_Ioi : IsOpen (Ioi (0 : ℝ))) using 1
    ext x
    simp only [W, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ioi, sub_pos]
  have hcl : closure W ⊆ closure U := closure_mono (fun _ hx => hx.1)
  have hleW := hv.mono_set (show W ⊆ U from fun _ hx => hx.1)
  have hdiff : LaplacianLE (fun x => v x - w x) 0 W := by
    refine ⟨hleW.1.sub hw.1, ?_⟩
    intro φ hφ hφ0 _
    obtain ⟨hi, _, he⟩ := hw.2 φ hφ
    have hvφ := hleW.2 φ hφ hφ0 hi
    have heq : (fun x => (v x - w x) * Δ φ x) =
        (fun x => v x * Δ φ x - w x * Δ φ x) := by
      funext x
      ring
    rw [heq, integral_sub (integrable_mul_laplacian_of_test hleW.1 hφ)
      (integrable_mul_laplacian_of_test hw.1 hφ)]
    rw [integral_zero_measure, sub_zero] at he
    simp only [integral_zero_measure]
    linarith
  have hs := superharmonicOfLaplacianLEStep_holds W (fun x => v x - w x) hWo
    ((hvc.sub hwc).mono (subset_closure.trans hcl)) hdiff
  have hempty : W = ∅ := by
    apply eq_empty_of_pos_of_subMean (f := fun x => w x - v x)
      (hUb.subset (fun _ hx => hx.1)) (hdc.mono hcl)
    · intro x hx
      exact sub_pos.mpr hx.2
    · intro x hx
      have hxcl := hcl (frontier_subset_closure hx)
      by_cases hxU : x ∈ U
      · have hxW : x ∉ W := by
          rw [hWo.frontier_eq] at hx
          exact hx.2
        exact sub_nonpos.mpr (le_of_not_gt (fun h => hxW ⟨hxU, h⟩))
      · exact sub_nonpos.mpr (hboundary x hxcl hxU).le
    · intro x hx
      obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hWo x hx
      have hsub' : closedBall x (r / 2) ⊆ W :=
        (closedBall_subset_ball (half_lt_self hr)).trans hsub
      refine ⟨r / 2, half_pos hr, hsub', ?_⟩
      have hm := (hs.2 x hx (r / 2) (half_pos hr) hsub').2
      have heq : (fun x => w x - v x) = -(fun x => v x - w x) := by
        funext x
        simp only [Pi.neg_apply]
        ring
      have hm' := neg_le_neg hm
      rw [← circleAverage_neg_fun, ← heq] at hm'
      simpa only [Pi.neg_apply, neg_sub] using hm'
  intro x hx
  by_cases hxU : x ∈ U
  · have hn : ¬ v x < w x := by
      intro h
      have : x ∈ W := ⟨hxU, h⟩
      simp [hempty] at this
    exact le_antisymm (le_of_not_gt hn) (hle x hxU)
  · exact hboundary x hx hxU

/-- A Green-regular candidate with the obstacle PDE on its noncontact set
coincides with the actual least supersolution on the closed domain. -/
theorem candidate_eqOn_leastSupersolutionOn
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t)
    (hregular : ∀ y ∈ closure U, y ∉ U →
      Tendsto (greenFunction U z) (𝓝[U] y) (𝓝 0))
    {w : ℂ → ℝ} (hw : w ∈ supersolutionsOn μ U z t)
    (hwboundary : ∀ x ∈ closure U, x ∉ U → w x = 0)
    (hwlap : HasLaplacian w μ 0 {x ∈ U | x = z ∨
      -t * greenFunction U z x < w x}) :
    EqOn w (leastSupersolutionOn μ U z t) (closure U) := by
  let v := leastSupersolutionOn μ U z t
  have hUb := isBounded_ball.subset hsub
  have hv : v ∈ supersolutionsOn μ U z t :=
    leastSupersolutionOn_mem_of_greenRegular hμ hR hV hU hsub hz ht hregular
  apply eqOn_of_obstacle_comparison hU hUb hw.1 hv.1 hv.2.1
  · apply hwlap.mono_domain
    intro x hx
    refine ⟨hx.1, ?_⟩
    by_cases hxz : x = z
    · exact Or.inl hxz
    · exact Or.inr (lt_of_le_of_lt (hv.2.2 x (subset_closure hx.1) hxz) hx.2)
  · intro x hx hxU
    have hxz : x ≠ z := by
      intro he
      subst x
      exact hxU hz
    change w x = leastSupersolutionOn μ U z t x
    rw [hwboundary x hx hxU,
      leastSupersolutionOn_eq_zero_of_boundary hUb ht.le hx hxU hxz]
  · intro x hx
    exact leastSupersolutionOn_le_of_mem_interior hμ hR hV hU hsub hz hx hw

/-- The candidate's noncontact set is the cluster of the infimum. -/
theorem candidate_noncontact_eq_clusterOn
    {μ : Measure ℂ} {U : Set ℂ} {z : ℂ} {t : ℝ} {w : ℂ → ℝ}
    (heq : EqOn w (leastSupersolutionOn μ U z t) (closure U)) :
    {x ∈ U | x = z ∨ -t * greenFunction U z x < w x} = clusterOn μ U z t := by
  ext x
  simp only [clusterOn, mem_ofPred_eq]
  constructor <;> intro hx <;> refine ⟨hx.1, ?_⟩
  · simpa only [heq (subset_closure hx.1)] using hx.2
  · simpa only [heq (subset_closure hx.1)] using hx.2

/-- Two candidates satisfying the same obstacle PDE agree on the closure. -/
theorem candidate_uniqueness
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t)
    (hregular : ∀ y ∈ closure U, y ∉ U →
      Tendsto (greenFunction U z) (𝓝[U] y) (𝓝 0))
    {w v : ℂ → ℝ} (hw : w ∈ supersolutionsOn μ U z t)
    (hv : v ∈ supersolutionsOn μ U z t)
    (hwb : ∀ x ∈ closure U, x ∉ U → w x = 0)
    (hvb : ∀ x ∈ closure U, x ∉ U → v x = 0)
    (hwlap : HasLaplacian w μ 0 {x ∈ U | x = z ∨
      -t * greenFunction U z x < w x})
    (hvlap : HasLaplacian v μ 0 {x ∈ U | x = z ∨
      -t * greenFunction U z x < v x}) : EqOn w v (closure U) := by
  exact (candidate_eqOn_leastSupersolutionOn hμ hR hV hU hsub hz ht hregular hw hwb hwlap).trans
    (candidate_eqOn_leastSupersolutionOn hμ hR hV hU hsub hz ht hregular hv hvb hvlap).symm

end HarmonicBalls
