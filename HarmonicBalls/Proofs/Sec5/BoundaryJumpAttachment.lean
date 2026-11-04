import HarmonicBalls.Proofs.Sec5.InteriorTimeContinuity
import HarmonicBalls.Proofs.Sec5.RightContinuousEnvelope
import HarmonicBalls.Proofs.Sec10.DirectedContinuumIntersection
import HarmonicBalls.Proofs.Sec10.CompactComponentSeparation

/-! # Attachment of boundary jumps

Every component of a possible boundary jump accumulates at the previous
cluster. These results do not exclude boundary jumps.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open scoped Pointwise ENNReal MeasureTheory

/-- Every component of the complement of a closed set in a compact continuum
accumulates at that closed set, provided the continuum meets it. -/
theorem closure_component_sdiff_meets_closed
    {K A : Set ℂ} (hKc : IsCompact K) (hK : IsConnected K) (hA : IsClosed A)
    (hKA : (K ∩ A).Nonempty) {x : ℂ} (hx : x ∈ K \ A) :
    (closure (connectedComponentIn (K \ A) x) ∩ A).Nonempty := by
  have hout : (K \ Aᶜ).Nonempty := by
    obtain ⟨y, hyK, hyA⟩ := hKA
    exact ⟨y, hyK, by simpa using hyA⟩
  obtain ⟨y, hycomp, _, hyA⟩ :=
    IsConnected.closure_component_inter_open_meets_compl hK hKc hA.isOpen_compl hout hx
  exact ⟨y, hycomp, by simpa using hyA⟩

/-- A connected set has one-dimensional Hausdorff measure at least the
separation between any point of the set and any point of its closure. -/
theorem ofReal_dist_le_hausdorffMeasure_one_of_closure
    {C : Set ℂ} (hC : IsPreconnected C) {x y : ℂ} (hx : x ∈ C) (hy : y ∈ closure C) :
    ENNReal.ofReal (dist x y) ≤ μH[1] C := by
  have hinterval : Ioo (0 : ℝ) (dist x y) ⊆ (fun w : ℂ => dist w x) '' C := by
    intro q hq
    obtain ⟨z, hzC, hzy⟩ := Metric.mem_closure_iff.mp hy
      ((dist x y - q) / 2) (by have := hq.2; linarith)
    have hqz : q ≤ dist z x := by
      have htri := dist_triangle x z y
      rw [dist_comm x z] at htri
      rw [dist_comm y z] at hzy
      have := hq.2
      linarith
    have hbetween : q ∈ Icc (dist x x) (dist z x) := ⟨by simpa using hq.1.le, hqz⟩
    obtain ⟨w, hwC, hwq⟩ := hC.intermediate_value (f := fun w : ℂ => dist w x)
      hx hzC (continuous_id.dist continuous_const).continuousOn hbetween
    exact ⟨w, hwC, hwq⟩
  have hlip : LipschitzWith 1 (fun w : ℂ => dist w x) :=
    LipschitzWith.of_le_add (fun w v => by simpa [add_comm] using dist_triangle w v x)
  have hmeasure := hlip.hausdorffMeasure_image_le (d := 1) (by norm_num) C
  have hintervalmeasure : μH[1] (Ioo (0 : ℝ) (dist x y)) ≤
      μH[1] ((fun w : ℂ => dist w x) '' C) := measure_mono hinterval
  rw [MeasureTheory.hausdorffMeasure_real, Real.volume_Ioo] at hintervalmeasure
  rw [MeasureTheory.hausdorffMeasure_real] at hmeasure
  simpa using hintervalmeasure.trans hmeasure

/-- A decreasing sequence of compact connected sets has a compact connected
intersection; each component of its new part attaches to the original set. -/
theorem closure_component_iInter_sdiff_meets_closed
    (F : ℕ → Set ℂ) (A : Set ℂ) (hF : ∀ n, IsCompact (F n))
    (hconn : ∀ n, IsConnected (F n)) (hanti : Antitone F) (hA : IsClosed A)
    (hAF : ∀ n, A ⊆ F n) (hAne : A.Nonempty) {x : ℂ}
    (hx : x ∈ (⋂ n, F n) \ A) :
    (closure (connectedComponentIn ((⋂ n, F n) \ A) x) ∩ A).Nonempty := by
  have hc : IsConnected (⋂ n, F n) :=
    isConnected_iInter_of_directed_compact F hF hconn hanti.directed_ge
  have hk : IsCompact (⋂ n, F n) := (hF 0).of_isClosed_subset
    (isClosed_iInter fun n => (hF n).isClosed) (iInter_subset F 0)
  apply closure_component_sdiff_meets_closed hk hc hA
  · obtain ⟨z, hz⟩ := hAne
    exact ⟨z, mem_iInter.mpr (fun n => hAF n hz), hz⟩
  · exact hx

/-- Every component of a boundary-only jump accumulates at a previously
contacted point of the unit circle. -/
theorem boundary_jump_component_attaches
    {F : ℝ → Set ℂ} {t : ℝ} {z : ℂ} (ht : 0 < t) (hz : z ∈ F t)
    (hmono : ∀ s s', 0 < s → s ≤ s' → F s ⊆ F s')
    (hbound : ∀ s, 0 < s → F s ⊆ ball (0 : ℂ) 1)
    (hconn : ∀ s, 0 < s → IsConnected (F s))
    (hinter : rightClosedEnvelope F t ∩ ball 0 1 ⊆ closure (F t))
    {x : ℂ} (hx : x ∈ rightClosedEnvelope F t \ closure (F t)) :
    (closure (connectedComponentIn (rightClosedEnvelope F t \ closure (F t)) x) ∩
      (closure (F t) ∩ sphere (0 : ℂ) 1)).Nonempty := by
  let G : ℕ → Set ℂ := fun n => closure (F (t + (2 : ℝ)⁻¹ ^ n))
  have hcompact (n : ℕ) : IsCompact (G n) :=
    (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset isClosed_closure
      (closure_minimal ((hbound _ (by positivity)).trans ball_subset_closedBall) isClosed_closedBall)
  have hconnected (n : ℕ) : IsConnected (G n) := (hconn _ (by positivity)).closure
  have hanti : Antitone G := by
    intro i j hij
    apply closure_mono
    apply hmono _ _ (by positivity)
    exact add_le_add le_rfl (pow_le_pow_of_le_one (by norm_num) (by norm_num) hij)
  have hsub (n : ℕ) : closure (F t) ⊆ G n :=
    closure_mono (hmono t _ ht (le_add_of_nonneg_right (by positivity)))
  have hnew : (rightClosedEnvelope F t \ closure (F t)) ⊆ sphere (0 : ℂ) 1 := by
    intro y hy
    have hclosed : y ∈ closedBall (0 : ℂ) 1 :=
      (closure_minimal ((hbound _ (by positivity)).trans ball_subset_closedBall) isClosed_closedBall)
        (mem_iInter.mp hy.1 0)
    have hnot : y ∉ ball (0 : ℂ) 1 := fun hyb => hy.2 (hinter ⟨hy.1, hyb⟩)
    apply mem_sphere.mpr
    exact le_antisymm (mem_closedBall.mp hclosed)
      (le_of_not_gt (by simpa only [mem_ball] using hnot))
  obtain ⟨y, hycomp, hyold⟩ := closure_component_iInter_sdiff_meets_closed
    G (closure (F t)) hcompact hconnected hanti isClosed_closure hsub
    ⟨z, subset_closure hz⟩ hx
  have hycircle : y ∈ sphere (0 : ℂ) 1 :=
    closure_minimal ((connectedComponentIn_subset _ x).trans hnew) isClosed_sphere hycomp
  exact ⟨y, hycomp, hyold, hycircle⟩

universe u

/-- Almost surely, for every centre and positive time, each component of a
possible new unit-circle portion attaches to the earlier circle contact set. -/
theorem ae_boundary_jump_component_attaches
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hvolume : LiouvilleVolumeGrowthStmt.{u})
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h34 : ClusterConservationOfMassStmt.{u}) (h61 : HarnackTypeEstimateStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u}) (h82 : TypicalPointManyGoodScalesStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα₀ : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      ∀ x ∈ rightClosedEnvelope (fun s => cluster (μ ω) 1 z s) t \ closure (cluster (μ ω) 1 z t),
        (closure (connectedComponentIn
          (rightClosedEnvelope (fun s => cluster (μ ω) 1 z s) t \ closure (cluster (μ ω) 1 z t)) x) ∩
          (closure (cluster (μ ω) 1 z t) ∩ sphere (0 : ℂ) 1)).Nonempty := by
  filter_upwards [h32 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    h33 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_future_closure_inter_ball_subset_closure hI2 hvolume h32 h33 h34 h61 h611 h82
      γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hopen hmono hinter
  intro t ht z hz x hx
  apply boundary_jump_component_attaches ht (self_mem_cluster hz)
    (fun s s' hs hss' => hmono s s' 1 hs hss' zero_lt_one z hz)
    (fun _ _ => cluster_subset_ball)
    (fun s hs => (hopen s 1 hs zero_lt_one z hz).2.1)
  · simpa only [rightClosedEnvelope, dyadicScale] using hinter t ht z hz
  · exact hx

/-- Each component of a possible boundary jump has positive
one-dimensional Hausdorff measure. -/
theorem ae_boundary_jump_component_has_positive_length
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hvolume : LiouvilleVolumeGrowthStmt.{u})
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h34 : ClusterConservationOfMassStmt.{u}) (h61 : HarnackTypeEstimateStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u}) (h82 : TypicalPointManyGoodScalesStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα₀ : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      ∀ x ∈ rightClosedEnvelope (fun s => cluster (μ ω) 1 z s) t \ closure (cluster (μ ω) 1 z t),
        0 < μH[1] (connectedComponentIn
          (rightClosedEnvelope (fun s => cluster (μ ω) 1 z s) t \ closure (cluster (μ ω) 1 z t)) x) := by
  filter_upwards [ae_boundary_jump_component_attaches hI2 hvolume h32 h33 h34 h61 h611 h82
    γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hattach
  intro t ht z hz x hx
  obtain ⟨y, hycomp, hyold, _⟩ := hattach t ht z hz x hx
  have hxy : x ≠ y := fun heq => hx.2 (heq ▸ hyold)
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (dist_pos.mpr hxy))
    (ofReal_dist_le_hausdorffMeasure_one_of_closure isPreconnected_connectedComponentIn
      (mem_connectedComponentIn hx) hycomp)

#print axioms ae_boundary_jump_component_has_positive_length
#print axioms ofReal_dist_le_hausdorffMeasure_one_of_closure
#print axioms boundary_jump_component_attaches
#print axioms ae_boundary_jump_component_attaches
#print axioms closure_component_sdiff_meets_closed
#print axioms closure_component_iInter_sdiff_meets_closed

end HarmonicBalls
