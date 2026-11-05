import HarmonicBalls.Proofs.Sec5.ComponentSupersolutionExtension
import HarmonicBalls.Proofs.Sec5.PuncturePotentialShift

/-! # Clipping supersolutions on a connected component -/

namespace HarmonicBalls

open MeasureTheory Metric Set

/-- The minimum of two continuous superharmonic functions is superharmonic. -/
theorem isSuperharmonicOn_min_continuous {U : Set ℂ} {f g : ℂ → ℝ}
    (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (hfs : IsSuperharmonicOn U f) (hgs : IsSuperharmonicOn U g) :
    IsSuperharmonicOn U (fun x => min (f x) (g x)) := by
  have hc : ContinuousOn (fun x => min (f x) (g x)) U := fun x hx => (hf x hx).min (hg x hx)
  refine ⟨hc.lowerSemicontinuousOn, fun x hx r hr hsub => ?_⟩
  have hi : CircleIntegrable (fun y => min (f y) (g y)) x r :=
    (hc.mono (sphere_subset_closedBall.trans hsub)).circleIntegrable hr.le
  have hfi := (hfs.2 x hx r hr hsub).1
  have hgi := (hgs.2 x hx r hr hsub).1
  refine ⟨hi, le_min ?_ ?_⟩
  · exact (Real.circleAverage_mono hi hfi fun _ _ => min_le_left _ _).trans
      (hfs.2 x hx r hr hsub).2
  · exact (Real.circleAverage_mono hi hgi fun _ _ => min_le_right _ _).trans
      (hgs.2 x hx r hr hsub).2

/-- A continuous supersolution can be clipped above by zero when the measure
has a continuous potential on the domain. -/
theorem LaplacianLE.min_zero_of_potential {μ : Measure ℂ}
    (hμ : IsLocallyFiniteMeasure μ) {U : Set ℂ} (hU : IsOpen U)
    {w q : ℂ → ℝ} (hwc : ContinuousOn w U) (hqc : ContinuousOn q U)
    (hq : HasLaplacian q 0 μ U) (hw : LaplacianLE w μ U) :
    LaplacianLE (fun x => min (w x) 0) μ U := by
  have hwq := (laplacianLE_iff_add_potential hμ hq).mp hw
  have hq0 := (laplacianLE_iff_add_potential hμ hq).mp (laplacianLE_zero μ U)
  have h1 := superharmonicOfLaplacianLEStep_holds U (fun x => w x + q x) hU
    (hwc.add hqc) hwq
  have h2 : IsSuperharmonicOn U q := by
    apply superharmonicOfLaplacianLEStep_holds U q hU hqc
    simpa using hq0
  have hs := isSuperharmonicOn_min_continuous (hwc.add hqc) hqc h1 h2
  have hc : ContinuousOn (fun x => min (w x + q x) (q x)) U :=
    fun x hx => ((hwc x hx).add (hqc x hx)).min (hqc x hx)
  have hl := laplacianLEOfSuperharmonicStep_holds U _ hU hc hs
  apply (laplacianLE_iff_add_potential hμ hq).mpr
  have he : (fun x => min (w x) 0 + q x) =
      (fun x => min (w x + q x) (q x)) := by
    funext x
    simpa only [zero_add] using (min_add_add_right (w x) 0 (q x)).symm
  rw [he]
  exact hl

/-- Clipping a component supersolution at zero lets it extend by zero to the
whole domain, even when the component's least supersolution is inadmissible. -/
theorem exists_clipped_component_supersolution_extension
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 ≤ t)
    {q : ℂ → ℝ} (hqc : ContinuousOn q (connectedComponentIn U z))
    (hq : HasLaplacian q 0 μ (connectedComponentIn U z))
    {v : ℂ → ℝ} (hv : v ∈ supersolutionsOn μ (connectedComponentIn U z) z t) :
    ∃ w ∈ supersolutionsOn μ U z t,
      EqOn w (fun x => min (v x) 0) (connectedComponentIn U z) := by
  classical
  let V := connectedComponentIn U z
  let W := U \ V
  let v₀ : ℂ → ℝ := fun x => min (v x) 0
  let w : ℂ → ℝ := fun x => if x ∈ V then v₀ x else 0
  have hV : IsOpen V := hU.connectedComponentIn
  have hW : IsOpen W := IsOpen.sdiff_connectedComponentIn hU z
  have hsub : V ⊆ U := connectedComponentIn_subset U z
  have hzV : z ∈ V := mem_connectedComponentIn hz
  have hv₀c : ContinuousOn v₀ (closure V) :=
    fun x hx => (hv.1 x hx).min continuousWithinAt_const
  have hzero : ∀ x ∈ frontier V, v₀ x = 0 := by
    intro x hx
    have hxnot : x ∉ V := by
      have hi : x ∉ interior V := hx.2
      simpa [hV.interior_eq] using hi
    have hxz : x ≠ z := fun e => hxnot (e ▸ hzV)
    have h := hv.2.2 x hx.1 hxz
    rw [greenFunction_of_notMem_right hxnot, mul_zero] at h
    exact min_eq_right (by simpa using h)
  have hcont : ContinuousOn w (closure U) := by
    dsimp only [w]
    apply ContinuousOn.if
    · intro x hx
      exact hzero x hx.2
    · exact hv₀c.mono inter_subset_right
    · exact continuousOn_const
  have hLV : LaplacianLE w μ V := by
    apply (hv.2.1.min_zero_of_potential hμ hV (hv.1.mono subset_closure) hqc hq).congr_eqOn hV.measurableSet
    intro x hx
    change x ∈ V at hx
    simp [w, hx, v₀]
  have hLW : LaplacianLE w μ W := by
    apply (laplacianLE_zero μ W).congr_eqOn hW.measurableSet
    intro x hx
    simp [w, hx.2]
  have hsplit : V ∪ W = U := union_sdiff_cancel hsub
  have hL : LaplacianLE w μ U := hsplit ▸ LaplacianLE.union hV hW hLV hLW
  refine ⟨w, ⟨hcont, hL, ?_⟩, ?_⟩
  · intro x hx hxz
    by_cases hxV : x ∈ V
    · rw [greenFunction_eq_connectedComponentIn_all hU hUb hz]
      have hvx := hv.2.2 x (subset_closure hxV) hxz
      have hg := greenFunction_nonneg (hUb.subset hsub) z x
      simp only [w, hxV, ↓reduceIte, v₀]
      exact le_min hvx (by simpa only [neg_mul] using neg_nonpos.mpr (mul_nonneg ht hg))
    · have hG := greenFunction_eq_zero_of_not_mem_connectedComponentIn hU hUb hz hxV
      simp [w, hxV, hG]
  · intro x hx
    change x ∈ V at hx
    simp [w, hx, v₀]

/-- The full-domain infimum is bounded above by the pole-component infimum
at every non-pole point of that component. -/
theorem leastSupersolutionOn_le_connectedComponentIn
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 ≤ t)
    {q : ℂ → ℝ} (hqc : ContinuousOn q (connectedComponentIn U z))
    (hq : HasLaplacian q 0 μ (connectedComponentIn U z))
    {x : ℂ} (hx : x ∈ connectedComponentIn U z) (hxz : x ≠ z) :
    leastSupersolutionOn μ U z t x ≤
      leastSupersolutionOn μ (connectedComponentIn U z) z t x := by
  apply le_csInf
  · exact ⟨_, ⟨0, zero_mem_supersolutionsOn (hUb.subset (connectedComponentIn_subset U z)) ht, rfl⟩⟩
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨w, hw, heq⟩ := exists_clipped_component_supersolution_extension
      hμ hU hUb hz ht hqc hq hv
    calc
      leastSupersolutionOn μ U z t x ≤ w x :=
        leastSupersolutionOn_le_of_mem hw (subset_closure (connectedComponentIn_subset U z hx)) hxz
      _ = min (v x) 0 := heq hx
      _ ≤ v x := min_le_left _ _

/-- A bounded open domain and the component containing the pole have the
same cluster when the component admits a continuous measure potential. -/
theorem clusterOn_eq_connectedComponentIn_of_potential
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 ≤ t)
    {q : ℂ → ℝ} (hqc : ContinuousOn q (connectedComponentIn U z))
    (hq : HasLaplacian q 0 μ (connectedComponentIn U z)) :
    clusterOn μ U z t = clusterOn μ (connectedComponentIn U z) z t := by
  apply subset_antisymm
  · intro x hx
    have hxV := clusterOn_subset_connectedComponentIn hU hUb hz ht hx
    refine ⟨hxV, ?_⟩
    by_cases hxz : x = z
    · exact Or.inl hxz
    · right
      rw [← greenFunction_eq_connectedComponentIn_all hU hUb hz]
      exact (hx.2.resolve_left hxz).trans_le
        (leastSupersolutionOn_le_connectedComponentIn hμ hU hUb hz ht hqc hq hxV hxz)
  · exact clusterOn_connectedComponentIn_subset hU hUb hz ht

/-- The comparison of the least supersolutions is an equality away from the
pole within its component. -/
theorem leastSupersolutionOn_eq_connectedComponentIn
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 ≤ t)
    {q : ℂ → ℝ} (hqc : ContinuousOn q (connectedComponentIn U z))
    (hq : HasLaplacian q 0 μ (connectedComponentIn U z))
    {x : ℂ} (hx : x ∈ connectedComponentIn U z) (hxz : x ≠ z) :
    leastSupersolutionOn μ U z t x =
      leastSupersolutionOn μ (connectedComponentIn U z) z t x := by
  apply le_antisymm
  · exact leastSupersolutionOn_le_connectedComponentIn hμ hU hUb hz ht hqc hq hx hxz
  · apply le_csInf
    · exact ⟨_, ⟨0, zero_mem_supersolutionsOn hUb ht, rfl⟩⟩
    · rintro _ ⟨w, hw, rfl⟩
      exact leastSupersolutionOn_le_of_mem
        (supersolutionsOn_subset_connectedComponentIn hU hUb hz hw) (subset_closure hx) hxz

/-- All-scale volume growth supplies the required potential on any bounded
open pole component, so adjoining other components does not change the cluster. -/
theorem clusterOn_eq_connectedComponentIn_of_volumeGrowth
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hgrowth : ∀ R : ℝ, 0 < R → VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 ≤ t) :
    clusterOn μ U z t = clusterOn μ (connectedComponentIn U z) z t := by
  obtain ⟨R, hUR⟩ := hUb.subset_ball (0 : ℂ)
  have hR : 0 < R := lt_of_le_of_lt (dist_nonneg) (mem_ball.mp (hUR hz))
  have hsub : connectedComponentIn U z ⊆ ball (0 : ℂ) R :=
    (connectedComponentIn_subset U z).trans hUR
  exact clusterOn_eq_connectedComponentIn_of_potential hμ hU hUb hz ht
    ((greenPotentialBallContinuousStep_holds μ hμ R βm βp hR (hgrowth R hR)).mono
      (hsub.trans ball_subset_closedBall))
    ((greenPotentialBallLaplacianStep_holds μ hμ R βm βp hR (hgrowth R hR)).mono_domain hsub)

#print axioms LaplacianLE.min_zero_of_potential
#print axioms exists_clipped_component_supersolution_extension
#print axioms leastSupersolutionOn_le_connectedComponentIn
#print axioms clusterOn_eq_connectedComponentIn_of_potential
#print axioms leastSupersolutionOn_eq_connectedComponentIn
#print axioms clusterOn_eq_connectedComponentIn_of_volumeGrowth

end HarmonicBalls
