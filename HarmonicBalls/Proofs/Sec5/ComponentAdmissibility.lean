import HarmonicBalls.Proofs.Sec5.ComponentSupersolutionExtension

/-! # Admissibility on the pole component -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped Topology

open Classical in
/-- The zero extension of the admissible component least supersolution is a
supersolution on the original domain. -/
theorem zeroExtend_component_leastSupersolutionOn_mem
    {μ : Measure ℂ} {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 ≤ t)
    (hv : leastSupersolutionOn μ (connectedComponentIn U z) z t ∈
      supersolutionsOn μ (connectedComponentIn U z) z t) :
    (fun x => if x ∈ connectedComponentIn U z then
      leastSupersolutionOn μ (connectedComponentIn U z) z t x else 0) ∈
      supersolutionsOn μ U z t := by
  classical
  let V := connectedComponentIn U z
  let W := U \ V
  let v := leastSupersolutionOn μ V z t
  let w : ℂ → ℝ := fun x => if x ∈ V then v x else 0
  change w ∈ supersolutionsOn μ U z t
  have hV : IsOpen V := hU.connectedComponentIn
  have hW : IsOpen W := IsOpen.sdiff_connectedComponentIn hU z
  have hsub : V ⊆ U := connectedComponentIn_subset U z
  have hzV : z ∈ V := mem_connectedComponentIn hz
  have hzero : ∀ x ∈ frontier V, v x = 0 := by
    intro x hx
    have hxnot : x ∉ V := by
      have hi : x ∉ interior V := hx.2
      simpa [hV.interior_eq] using hi
    exact leastSupersolutionOn_eq_zero_of_boundary (hUb.subset hsub) ht hx.1 hxnot
      (fun e => hxnot (e ▸ hzV))
  have hcont : ContinuousOn w (closure U) := by
    dsimp only [w]
    apply ContinuousOn.if
    · intro x hx
      exact hzero x hx.2
    · exact hv.1.mono inter_subset_right
    · exact continuousOn_const
  have hLV : LaplacianLE w μ V := by
    apply hv.2.1.congr_eqOn hV.measurableSet
    intro x hx
    change x ∈ V at hx
    change v x = w x
    simp [w, hx]
  have hLW : LaplacianLE w μ W := by
    apply (laplacianLE_zero μ W).congr_eqOn hW.measurableSet
    intro x hx
    simp [w, hx.2]
  have hsplit : V ∪ W = U := union_sdiff_cancel hsub
  refine ⟨hcont, hsplit ▸ LaplacianLE.union hV hW hLV hLW, ?_⟩
  intro x hx hxz
  by_cases hxV : x ∈ V
  · rw [greenFunction_eq_connectedComponentIn_all hU hUb hz]
    simpa [w, hxV] using hv.2.2 x (subset_closure hxV) hxz
  · have hG := greenFunction_eq_zero_of_not_mem_connectedComponentIn hU hUb hz hxV
    simp [w, hxV, hG]

/-- The least component supersolution is below every global competitor also
at the pole, by continuity and comparison at the nearby non-pole points. -/
theorem component_leastSupersolutionOn_le_at_pole
    {μ : Measure ℂ} {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {z : ℂ} (hz : z ∈ U) {t : ℝ}
    (hv : leastSupersolutionOn μ (connectedComponentIn U z) z t ∈
      supersolutionsOn μ (connectedComponentIn U z) z t)
    {w : ℂ → ℝ} (hw : w ∈ supersolutionsOn μ U z t) :
    leastSupersolutionOn μ (connectedComponentIn U z) z t z ≤ w z := by
  have hzV : z ∈ connectedComponentIn U z := mem_connectedComponentIn hz
  have hV : IsOpen (connectedComponentIn U z) := hU.connectedComponentIn
  have hvcont := hv.1.continuousAt (mem_of_superset (hV.mem_nhds hzV) subset_closure)
  have hwcont := hw.1.continuousAt (mem_of_superset (hU.mem_nhds hz) subset_closure)
  apply le_of_tendsto_of_tendsto (b := 𝓝[≠] z)
    (hvcont.tendsto.mono_left nhdsWithin_le_nhds)
    (hwcont.tendsto.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (hV.mem_nhds hzV)] with x hxz hxV
  exact leastSupersolutionOn_le_of_mem
    (supersolutionsOn_subset_connectedComponentIn hU hUb hz hw)
    (subset_closure hxV) (by simpa using hxz)

open Classical in
/-- On the closure of the domain, the least supersolution is the zero
extension of the least supersolution on the pole component. -/
theorem leastSupersolutionOn_eq_zeroExtend_component
    {μ : Measure ℂ} {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 ≤ t)
    (hv : leastSupersolutionOn μ (connectedComponentIn U z) z t ∈
      supersolutionsOn μ (connectedComponentIn U z) z t) :
    EqOn (leastSupersolutionOn μ U z t)
      (fun x => if x ∈ connectedComponentIn U z then
        leastSupersolutionOn μ (connectedComponentIn U z) z t x else 0) (closure U) := by
  classical
  intro x hx
  have hzV : z ∈ connectedComponentIn U z := mem_connectedComponentIn hz
  have hw := zeroExtend_component_leastSupersolutionOn_mem hU hUb hz ht hv
  by_cases hxV : x ∈ connectedComponentIn U z
  · simp only [hxV, ↓reduceIte]
    apply le_antisymm
    · by_cases hxz : x = z
      · subst x
        have hbdd : BddBelow ((fun w : ℂ → ℝ => w z) '' supersolutionsOn μ U z t) :=
          ⟨leastSupersolutionOn μ (connectedComponentIn U z) z t z, by
            rintro _ ⟨w, hw', rfl⟩
            exact component_leastSupersolutionOn_le_at_pole hU hUb hz hv hw'⟩
        have h := csInf_le hbdd ⟨_, hw, rfl⟩
        simpa [leastSupersolutionOn, hzV] using h
      · have h := leastSupersolutionOn_le_of_mem hw hx hxz
        simpa [hxV] using h
    · apply le_csInf
      · exact ⟨_, ⟨0, zero_mem_supersolutionsOn hUb ht, rfl⟩⟩
      · rintro _ ⟨w, hw', rfl⟩
        by_cases hxz : x = z
        · subst x
          exact component_leastSupersolutionOn_le_at_pole hU hUb hz hv hw'
        · exact leastSupersolutionOn_le_of_mem
            (supersolutionsOn_subset_connectedComponentIn hU hUb hz hw')
            (subset_closure hxV) hxz
  · simp only [hxV, ↓reduceIte]
    have hxz : x ≠ z := fun e => hxV (e ▸ hzV)
    have hG := greenFunction_eq_zero_of_not_mem_connectedComponentIn hU hUb hz hxV
    apply le_antisymm
    · exact leastSupersolutionOn_le_of_mem (zero_mem_supersolutionsOn hUb ht) hx hxz
    · have h := le_csInf (show ((fun w : ℂ → ℝ => w x) '' supersolutionsOn μ U z t).Nonempty from
          ⟨_, ⟨0, zero_mem_supersolutionsOn hUb ht, rfl⟩⟩)
          (show ∀ a ∈ (fun w : ℂ → ℝ => w x) '' supersolutionsOn μ U z t, 0 ≤ a from by
            rintro _ ⟨w, hw', rfl⟩
            simpa [hG] using hw'.2.2 x hx hxz)
      exact h

/-- Admissibility of the least supersolution transfers from the pole
component to the entire bounded open domain. -/
theorem leastSupersolutionOn_mem_of_component_mem
    {μ : Measure ℂ} {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 ≤ t)
    (hv : leastSupersolutionOn μ (connectedComponentIn U z) z t ∈
      supersolutionsOn μ (connectedComponentIn U z) z t) :
    leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t := by
  classical
  have hw := zeroExtend_component_leastSupersolutionOn_mem hU hUb hz ht hv
  have heq := leastSupersolutionOn_eq_zeroExtend_component hU hUb hz ht hv
  refine ⟨hw.1.congr heq, hw.2.1.congr_eqOn hU.measurableSet ?_, ?_⟩
  · exact (heq.mono subset_closure).symm
  · intro x hx hxz
    rw [heq hx]
    exact hw.2.2 x hx hxz

/-- A disc pole component yields an admissible least supersolution on the
whole domain under the disc volume-growth condition. -/
theorem leastSupersolutionOn_mem_of_connectedComponentIn_eq_ball
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {R βm βp t : ℝ} {z : ℂ} (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    (hz : z ∈ U) (hcomp : connectedComponentIn U z = ball (0 : ℂ) R) (ht : 0 < t) :
    leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t := by
  have hzR : z ∈ ball (0 : ℂ) R := hcomp ▸ mem_connectedComponentIn hz
  have hv := (leastSupersolution_mem_of_general obstacleLeastSuperharmonicMajorantGeneral_holds
    obstacleCompatibilityShiftStep_holds hμ hR hV hzR ht).2.2
  have heq : leastSupersolutionOn μ (ball (0 : ℂ) R) z t = leastSupersolution μ R z t := by
    funext x
    simp only [leastSupersolutionOn, leastSupersolution, supersolutionsOn_ball μ hR.ne']
  have hv' : leastSupersolutionOn μ (ball (0 : ℂ) R) z t ∈
      supersolutionsOn μ (ball (0 : ℂ) R) z t := by
    rw [heq, supersolutionsOn_ball μ hR.ne']
    exact hv
  exact leastSupersolutionOn_mem_of_component_mem hU hUb hz ht.le (hcomp.symm ▸ hv')

/-- A relatively closed countable deletion from a domain with a disc pole
component removes exactly its points from the disc cluster. -/
theorem clusterOn_sdiff_of_connectedComponentIn_eq_ball
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hV : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {U K : Set ℂ} {R S t : ℝ} {z : ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUS : closure U ⊆ ball (0 : ℂ) S)
    (hD : IsOpen (U \ K)) (hK : (K ∩ U).Countable)
    (hR : 0 < R) (hz : z ∈ U \ K)
    (hcomp : connectedComponentIn U z = ball (0 : ℂ) R) (ht : 0 < t) :
    clusterOn μ (U \ K) z t = cluster μ R z t \ K := by
  have hS : 0 < S := lt_of_le_of_lt (dist_nonneg : 0 ≤ dist z (0 : ℂ))
    (mem_ball.mp (hUS (subset_closure hz.1)))
  have hq := greenPotentialBallLaplacianStep_holds μ hμ S βm βp hS (hV S hS)
  have hqc := greenPotentialBallContinuousStep_holds μ hμ S βm βp hS (hV S hS)
  have hsub : U ⊆ ball (0 : ℂ) S := subset_closure.trans hUS
  have hw := leastSupersolutionOn_mem_of_connectedComponentIn_eq_ball
    hμ hU hUb hR (hV R hR) hz.1 hcomp ht
  rw [clusterOn_sdiff_of_relative_countable hμ hU hUb hUS hD hK
    (hqc.mono (hsub.trans ball_subset_closedBall)) (hq.mono_domain hsub) ht.le hz hw,
    clusterOn_eq_disc_of_connectedComponentIn_eq_ball hμ hU hUb hR (hV R hR) hz.1 hcomp ht]

/-- Strong compatibility survives a relatively closed countable deletion
when the original pole component is a disc. -/
theorem regularizedFamily_strongCompatibility_sdiff_of_connectedComponentIn_eq_ball
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hV : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {U K : Set ℂ} {R S t : ℝ} {z : ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUS : closure U ⊆ ball (0 : ℂ) S)
    (hD : IsOpen (U \ K)) (hK : (K ∩ U).Countable)
    (hR : 0 < R) (hz : z ∈ U \ K)
    (hcomp : connectedComponentIn U z = ball (0 : ℂ) R) (ht : 0 < t)
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hcl : closure (Λ t) ⊆ U \ K ∨
      closure (clusterOn μ (U \ K) z t) ⊆ U \ K) :
    closure (Λ t) = closure (clusterOn μ (U \ K) z t) := by
  have hsub : ball (0 : ℂ) R ⊆ U := hcomp ▸ connectedComponentIn_subset U z
  have hzR : z ∈ ball (0 : ℂ) R := hcomp ▸ mem_connectedComponentIn hz.1
  have hDR : IsOpen (ball (0 : ℂ) R \ K) := by
    have heq : ball (0 : ℂ) R \ K = (U \ K) ∩ ball 0 R := by
      ext x
      simp only [Set.mem_sdiff, mem_inter_iff]
      constructor
      · rintro ⟨hx, hk⟩
        exact ⟨⟨hsub hx, hk⟩, hx⟩
      · rintro ⟨⟨_, hk⟩, hx⟩
        exact ⟨hx, hk⟩
    rw [heq]
    exact hD.inter isOpen_ball
  have hKR : (K ∩ ball (0 : ℂ) R).Countable := hK.mono (inter_subset_inter_right K hsub)
  have hzRK : z ∈ ball (0 : ℂ) R \ K := ⟨hzR, hz.2⟩
  have hc := clusterOn_sdiff_of_connectedComponentIn_eq_ball hμ hV hU hUb hUS hD hK hR hz hcomp ht
  have hd := clusterOn_relative_countable_disc_eq_sdiff hμ hR (hV R hR) K hDR hKR hzRK ht
  have heq : clusterOn μ (U \ K) z t = clusterOn μ (ball (0 : ℂ) R \ K) z t := hc.trans hd.symm
  have hclosure : closure (clusterOn μ (U \ K) z t) = closure (cluster μ R z t) := by
    rw [heq, closure_clusterOn_relative_countable_disc_eq hμ hR (hV R hR) K hDR hKR hzRK ht]
  have hconnected : IsConnected (cluster μ R z t) := by
    rw [(obstacleCompatibilityShiftStep_holds μ hμ R βm βp hR (hV R hR) z hzR t ht).2.2.1]
    exact (obstacleNonCoincidenceHarmonicGeneral_holds μ hμ R βm βp hR (hV R hR) z hzR t ht).2.1
  have hcl' : closure (Λ t) ⊆ ball (0 : ℂ) R \ K ∨
      closure (clusterOn μ (ball (0 : ℂ) R \ K) z t) ⊆ ball 0 R \ K := by
    rcases hcl with hcl | hcl
    · left
      have hcompcl : closure (Λ t) ⊆ connectedComponentIn U z :=
        (hΛ.1.isConnected t ht).isPreconnected.closure.subset_connectedComponentIn
          (subset_closure (hΛ.1.mem t ht)) (hcl.trans sdiff_subset)
      intro x hx
      exact ⟨hcomp ▸ hcompcl hx, (hcl hx).2⟩
    · right
      have hcompcl : closure (cluster μ R z t) ⊆ connectedComponentIn U z :=
        hconnected.isPreconnected.closure.subset_connectedComponentIn
          (subset_closure ⟨hzR, Or.inl rfl⟩) (by simpa only [hclosure] using hcl.trans sdiff_subset)
      intro x hx
      have hx' : x ∈ closure (clusterOn μ (U \ K) z t) := by simpa only [heq] using hx
      exact ⟨hcomp ▸ hcompcl (hclosure ▸ hx'), (hcl hx').2⟩
  have h := regularizedFamily_strongCompatibility_relative_countable_disc hμ hV hR K hDR hKR hzRK ht hΛ hcl'
  simpa only [heq] using h

#print axioms regularizedFamily_strongCompatibility_sdiff_of_connectedComponentIn_eq_ball

#print axioms leastSupersolutionOn_mem_of_connectedComponentIn_eq_ball
#print axioms clusterOn_sdiff_of_connectedComponentIn_eq_ball

#print axioms leastSupersolutionOn_eq_zeroExtend_component
#print axioms leastSupersolutionOn_mem_of_component_mem

#print axioms zeroExtend_component_leastSupersolutionOn_mem
#print axioms component_leastSupersolutionOn_le_at_pole

end HarmonicBalls
