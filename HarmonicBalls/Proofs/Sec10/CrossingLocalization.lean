import HarmonicBalls.Proofs.Sec10.CrossingMassCount
import HarmonicBalls.Proofs.Sec3.OpenLaplacian
import HarmonicBalls.Draft.Section6

/-!
# Localization of the crossing count

A crossing component in a larger ball contains a component of the cluster in
a smaller, possibly displaced ball. An interior point supplied by closure
contact lets the Harnack-type estimate apply to the smaller component.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Topology
open Section6
open scoped ENNReal

universe u

/-- A component in a smaller open set is contained in the component of a
larger set containing the same point. -/
theorem connectedComponentIn_mono_of_mem {X : Type*} [TopologicalSpace X]
    {F G : Set X} {x y : X} (hFG : F ⊆ G) (hxF : x ∈ F)
    (hxy : x ∈ connectedComponentIn G y) :
    connectedComponentIn F x ⊆ connectedComponentIn G y := by
  have hxeq := connectedComponentIn_eq hxy
  rw [hxeq]
  exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
    (mem_connectedComponentIn hxF) ((connectedComponentIn_subset F x).trans hFG)

/-- A Harnack-type estimate in a smaller, displaced ball bounds the number
of crossing components in a larger ball. -/
theorem encard_crossingComponents_of_local_mass_or_avoids
    (μ : Measure ℂ) (Λ A : Set ℂ) (hΛ : IsOpen Λ) (hA : MeasurableSet A)
    (hAfin : μ A ≠ ∞) {α : ℝ} (hα : 0 < α)
    (w x₀ : ℂ) (r R q ρ : ℝ) (hqr : q ≤ ρ)
    (hinner : sphere w r ⊆ ball x₀ q) (houter : ball x₀ ρ ⊆ ball w R)
    (hcomponent : ∀ C ∈ connectedComponentsIn (Λ ∩ ball x₀ ρ),
      μ (C ∩ A) ≤ ENNReal.ofReal α * μ A → C ∩ closedBall x₀ q = ∅) :
    (crossingComponents (Λ ∩ ball w R) w r R).encard ≤ ⌈1 / α⌉₊ := by
  apply encard_crossingComponents_le_ceil_inv μ Λ A hΛ hA hAfin hα w r R
  intro C hC
  obtain ⟨x, hxcl, hxsphere⟩ := hC.2.1
  have hxball : x ∈ ball x₀ q := hinner hxsphere
  obtain ⟨y, hyball, hyC⟩ := mem_closure_iff.mp hxcl _ isOpen_ball hxball
  obtain ⟨p, hp, hpC⟩ := hC.1
  have hyF : y ∈ Λ ∩ ball x₀ ρ := by
    refine ⟨(connectedComponentIn_subset (Λ ∩ ball w R) p (hpC ▸ hyC)).1, ?_⟩
    exact ball_subset_ball hqr hyball
  let D := connectedComponentIn (Λ ∩ ball x₀ ρ) y
  have hD : D ∈ connectedComponentsIn (Λ ∩ ball x₀ ρ) := ⟨y, hyF, rfl⟩
  have hDC : D ⊆ C := by
    rw [← hpC]
    exact connectedComponentIn_mono_of_mem
      (inter_subset_inter_right Λ houter) hyF (hpC ▸ hyC)
  have hmassD : ENNReal.ofReal α * μ A < μ (D ∩ A) := by
    apply lt_of_not_ge
    intro hsmall
    have hyD : y ∈ D := mem_connectedComponentIn hyF
    have hy : y ∈ D ∩ closedBall x₀ q := ⟨hyD, ball_subset_closedBall hyball⟩
    rw [hcomponent D hD hsmall] at hy
    exact hy
  exact hmassD.trans_le (measure_mono (inter_subset_inter_left A hDC))

/-- The radius comparison in Lemma 10.1: a good ball whose centre is within
`ρ / 6` of `w` controls crossings of the concentric annulus with radii
`ρ / 3` and `2ρ` around `w`. -/
theorem encard_crossingComponents_of_nearby_harnack
    (μ : Measure ℂ) (Λ : Set ℂ) (hΛ : IsOpen Λ)
    {α : ℝ} (hα : 0 < α) (w x₀ : ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hnear : dist w x₀ < ρ / 6)
    (hAfin : μ (annulus x₀ (ρ / 2) ρ) ≠ ∞)
    (hcomponent : ∀ C ∈ connectedComponentsIn (Λ ∩ ball x₀ ρ),
      μ (C ∩ annulus x₀ (ρ / 2) ρ) ≤
        ENNReal.ofReal α * μ (annulus x₀ (ρ / 2) ρ) →
      C ∩ closedBall x₀ (ρ / 2) = ∅) :
    (crossingComponents (Λ ∩ ball w (2 * ρ)) w (ρ / 3) (2 * ρ)).encard ≤
      ⌈1 / α⌉₊ := by
  apply encard_crossingComponents_of_local_mass_or_avoids μ Λ
    (annulus x₀ (ρ / 2) ρ) hΛ ?_ hAfin hα w x₀ (ρ / 3) (2 * ρ) (ρ / 2) ρ
    (by linarith) ?_ ?_ hcomponent
  · exact (isOpen_ball.sdiff isClosed_closedBall).measurableSet
  · intro x hx
    have hxw : dist x w = ρ / 3 := mem_sphere.mp hx
    have htriangle := dist_triangle x w x₀
    apply mem_ball.mpr
    linarith
  · intro x hx
    have hxx₀ : dist x x₀ < ρ := mem_ball.mp hx
    have htriangle := dist_triangle x x₀ w
    have hnear' : dist x₀ w < ρ / 6 := by simpa [dist_comm] using hnear
    apply mem_ball.mpr
    linarith

/-- The displaced good ball is contained in the unit disc and avoids the pole
when its double-radius ball about `w` has the corresponding margins. -/
theorem closedBall_subset_unit_sdiff_pole_of_nearby
    (w x₀ z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) (hnear : dist w x₀ < ρ / 6)
    (hboundary : dist w 0 + 2 * ρ < 1) (hpole : 2 * ρ < dist z w) :
    closedBall x₀ ρ ⊆ ball 0 1 \ {z} := by
  intro y hy
  have hyx : dist y x₀ ≤ ρ := mem_closedBall.mp hy
  have hnear' : dist x₀ w < ρ / 6 := by simpa [dist_comm] using hnear
  have hyw : dist y w < 2 * ρ := by
    have := dist_triangle y x₀ w
    linarith
  refine ⟨mem_ball.mpr ?_, ?_⟩
  · have := dist_triangle y w (0 : ℂ)
    linarith
  · intro hyz
    have : y = z := mem_singleton_iff.mp hyz
    subst y
    linarith

/-- Proposition 6.2 controls displaced crossings on its good events, at
scales whose double-radius balls stay inside the domain and avoid the pole.
The good events retain the prevalence stated in Proposition 6.2. -/
theorem localizedCrossingCount_of_harnack
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h6 : HarnackTypeComponentStmt.{u}) :
    ∃ c : ℝ, 0 < c ∧ ∀ γ : ℝ, 0 < γ → γ < 2 →
    ∃ α : ℝ, 0 < α ∧ ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∃ E : ℝ → ℂ → Set Ω,
      PolyHighProb P (fun ε => {ω | ∀ x₀ ∈ prevalenceGrid ε,
        c * Real.log (ε ^ (-(1 / 2 : ℝ))) ≤
          ({ρ : ℝ | ρ ∈ Icc ε (Real.sqrt ε) ∧ (∃ n : ℕ, ρ = (8 : ℝ)⁻¹ ^ n) ∧
            ω ∈ E ρ x₀}.ncard : ℝ)}) ∧
      ∀ᵐ ω ∂P, ∀ ρ ∈ Ioo (0 : ℝ) 1, ∀ x₀, ω ∈ E ρ x₀ →
        ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t → ∀ w : ℂ,
        dist w x₀ < ρ / 6 → dist w 0 + 2 * ρ < 1 → 2 * ρ < dist z w →
        (crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ)) w (ρ / 3)
          (2 * ρ)).encard ≤ ⌈1 / α⌉₊ := by
  obtain ⟨c, hc, h6⟩ := h6
  refine ⟨c, hc, ?_⟩
  intro γ hγ hγ2
  obtain ⟨α, hα, h6⟩ := h6 γ hγ hγ2
  refine ⟨α, hα, ?_⟩
  intro α₀ hα₀ Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨E, hgood, hprev⟩ := h6 α₀ hα₀ Ω P hC hcirc μ hGFF hμ
  refine ⟨E, hprev, ?_⟩
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα₀ hGFF hμ
  filter_upwards [hV, clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hV hopen
  let : IsLocallyFiniteMeasure (μ ω) := hV.1
  intro ρ hρ x₀ hE z hz t ht w hnear hboundary hpole
  apply encard_crossingComponents_of_nearby_harnack (μ ω) (cluster (μ ω) 1 z t)
    (hopen t 1 ht zero_lt_one z hz).1 hα w x₀ hρ.1 hnear
  · exact ne_top_of_le_ne_top (measure_ball_lt_top (μ := μ ω)).ne (measure_mono sdiff_subset)
  · exact hgood ω ρ hρ x₀ hE z hz t ht
      (closedBall_subset_unit_sdiff_pole_of_nearby w x₀ z hρ.1 hnear hboundary hpole)

end HarmonicBalls
