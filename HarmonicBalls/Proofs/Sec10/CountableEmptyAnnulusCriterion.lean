import HarmonicBalls.Proofs.Sec10.CountableCrossingNoHoles

/-! # Countable empty-annulus criterion for holes

A countable family of tests detects exactly the failure of connectedness of
closed-cluster complements. The stochastic reduction still requires the
explicit frontier-nullity inputs used for persistence of holes in time.
-/

namespace HarmonicBalls

open Set Metric Topology MeasureTheory Filter

/-- On empty fixed-ratio annuli at centres in `D`, the complement of the
exterior component has no crossing component. -/
def EmptyAnnulusCrossingTest (G D : Set ℂ) : Prop :=
  ∀ w ∈ D, ∀ n : ℕ,
    let r : ℝ := 1 / ((n : ℝ) + 1)
    closure (annulus w r (2 * r)) ⊆ ball 0 1 →
    Disjoint (closure G) (annulus w r (2 * r)) →
    crossingComponents
      ((connectedComponentIn (closure G)ᶜ (2 : ℂ))ᶜ ∩ annulus w r (2 * r)) w r (2 * r) = ∅

/-- A bounded closed-set complement is connected precisely when its exterior
component passes all empty-annulus tests at centres in a dense set. -/
theorem isConnected_compl_closure_iff_emptyAnnulusCrossingTest
    {G D : Set ℂ} (hG : closure G ⊆ closedBall 0 1) (hD : Dense D) :
    IsConnected (closure G)ᶜ ↔ EmptyAnnulusCrossingTest G D := by
  let U := connectedComponentIn (closure G)ᶜ (2 : ℂ)
  have hp : (2 : ℂ) ∈ (closedBall (0 : ℂ) 1)ᶜ := by
    norm_num [mem_closedBall, dist_eq_norm]
  have hpG : (2 : ℂ) ∈ (closure G)ᶜ := (compl_subset_compl.mpr hG) hp
  have hU : U ∈ connectedComponentsIn (closure G)ᶜ := ⟨2, hpG, rfl⟩
  constructor
  · intro hc w hw n
    dsimp only
    intro hcl hdis
    have hUeq : U = (closure G)ᶜ := by
      apply Subset.antisymm (connectedComponentIn_subset _ _)
      exact hc.isPreconnected.subset_connectedComponentIn hpG Subset.rfl
    have hempty : Uᶜ ∩ annulus w (1 / ((n : ℝ) + 1))
        (2 * (1 / ((n : ℝ) + 1))) = ∅ := by
      rw [hUeq, compl_compl]
      exact disjoint_iff_inter_eq_empty.mp hdis
    rw [hempty]
    simp [crossingComponents, connectedComponentsIn]
  · intro htest
    by_contra hn
    obtain ⟨V, hV, hb⟩ :=
      (not_isConnected_compl_iff_exists_bounded_component zero_lt_one hG hp).mp hn
    have hVo : IsOpen V := by
      obtain ⟨v, hv, rfl⟩ := hV
      exact isClosed_closure.isOpen_compl.connectedComponentIn
    have hVne : V.Nonempty := by
      obtain ⟨v, hv, rfl⟩ := hV
      exact ⟨v, mem_connectedComponentIn hv⟩
    obtain ⟨w, hwV, hwD⟩ := hD.inter_open_nonempty V hVo hVne
    have hVsub : V ⊆ (closure G)ᶜ := by
      obtain ⟨v, hv, rfl⟩ := hV
      exact connectedComponentIn_subset _ _
    have hVball : V ⊆ ball (0 : ℂ) 1 :=
      bounded_complement_component_subset_unit_ball isClosed_closure hG hV hb
    have hUV : Disjoint U V := by
      apply connectedComponentsIn_pairwise_disjoint _ hU hV
      intro heq
      have hbU : Bornology.IsBounded U := by rw [heq]; exact hb
      exact not_isBounded_exterior_component zero_lt_one hG hp hbU
    have hGV : Disjoint G V := by
      apply disjoint_left.mpr
      intro x hx hxV
      exact hVsub hxV (subset_closure hx)
    obtain ⟨δ, hδ, hδcross⟩ := complementary_hole_fixed_ratio_all_small hGV hUV hVo
      ⟨hwV, hVball hwV⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
    let r : ℝ := 1 / ((n : ℝ) + 1)
    have hr : 0 < r := by dsimp [r]; positivity
    have hrδ : r < δ := by simpa [r] using hn
    obtain ⟨hcl, hcross, _, _⟩ := hδcross r hr hrδ
    have hdis : Disjoint (closure G) (annulus w r (2 * r)) := by
      apply disjoint_left.mpr
      intro x hx hxann
      exact hVsub (hcl (subset_closure hxann)).1 hx
    have ht := htest w hwD n (hcl.trans inter_subset_right) hdis
    rw [hcross] at ht
    exact singleton_ne_empty _ ht

universe u

/-- Under volume growth and the explicit frontier-nullity inputs, the
countably many tests at rational times characterize connected cluster
complements at all positive times for each pole. -/
theorem ae_cluster_compl_connected_iff_rational_emptyAnnulus_tests
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u})
    {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (D : Set ℂ) (hDdense : Dense D) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1,
      (∀ t : ℝ, 0 < t → IsConnected (closure (cluster (μ ω) 1 z t))ᶜ) ↔
      (∀ q : ℚ, 0 < (q : ℝ) → EmptyAnnulusCrossingTest (cluster (μ ω) 1 z q) D) := by
  filter_upwards [ae_cluster_no_holes_iff_no_rational_holes hI2 h611 h82
    γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ] with ω htime
  intro z hz
  have hcl : ∀ t : ℝ, closure (cluster (μ ω) 1 z t) ⊆ closedBall 0 1 := by
    intro t
    exact closure_minimal (cluster_subset_ball.trans ball_subset_closedBall) isClosed_closedBall
  have hp : (2 : ℂ) ∈ (closedBall (0 : ℂ) 1)ᶜ := by
    norm_num [mem_closedBall, dist_eq_norm]
  constructor
  · intro hc q hq
    exact (isConnected_compl_closure_iff_emptyAnnulusCrossingTest (hcl q) hDdense).mp (hc q hq)
  · intro htest t ht
    have hrat : ∀ q : ℚ, 0 < (q : ℝ) → ∀ U ∈ connectedComponentsIn
        (closure (cluster (μ ω) 1 z q))ᶜ, ¬ Bornology.IsBounded U := by
      intro q hq U hU hb
      have hc := (isConnected_compl_closure_iff_emptyAnnulusCrossingTest (hcl q) hDdense).mpr
        (htest q hq)
      exact ((not_isConnected_compl_iff_exists_bounded_component zero_lt_one (hcl q) hp).mpr
        ⟨U, hU, hb⟩) hc
    have hnone := (htime z hz).2 hrat
    by_contra hn
    obtain ⟨U, hU, hb⟩ :=
      (not_isConnected_compl_iff_exists_bounded_component zero_lt_one (hcl t) hp).mp hn
    exact hnone t ht U hU hb

/-- For a fixed pole and a countable dense set of centres, the all-times
no-hole event holds almost surely exactly when every individual rational-time,
reciprocal-radius empty-annulus test holds almost surely. -/
theorem ae_cluster_compl_connected_iff_individual_emptyAnnulus_tests
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u})
    {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1)
    (D : Set ℂ) (hDcount : D.Countable) (hDdense : Dense D) :
    (∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → IsConnected (closure (cluster (μ ω) 1 z t))ᶜ) ↔
    (∀ (q : ℚ) (w : D) (n : ℕ), 0 < (q : ℝ) → ∀ᵐ ω ∂P,
      let G := cluster (μ ω) 1 z q
      let r : ℝ := 1 / ((n : ℝ) + 1)
      closure (annulus (w : ℂ) r (2 * r)) ⊆ ball 0 1 →
      Disjoint (closure G) (annulus (w : ℂ) r (2 * r)) →
      crossingComponents
        ((connectedComponentIn (closure G)ᶜ (2 : ℂ))ᶜ ∩ annulus (w : ℂ) r (2 * r))
        (w : ℂ) r (2 * r) = ∅) := by
  let : Countable D := hDcount.to_subtype
  have hevent := ae_cluster_compl_connected_iff_rational_emptyAnnulus_tests hI2 h611 h82
    hγ hγ2 hα P hC hcirc μ hGFF hμ D hDdense
  constructor
  · intro hall q w n hq
    filter_upwards [hall, hevent] with ω hω heq
    exact (heq z hz).mp hω q hq w w.property n
  · intro htest
    have hall : ∀ᵐ ω ∂P, ∀ (q : ℚ) (w : D) (n : ℕ), 0 < (q : ℝ) →
        let G := cluster (μ ω) 1 z q
        let r : ℝ := 1 / ((n : ℝ) + 1)
        closure (annulus (w : ℂ) r (2 * r)) ⊆ ball 0 1 →
        Disjoint (closure G) (annulus (w : ℂ) r (2 * r)) →
        crossingComponents
          ((connectedComponentIn (closure G)ᶜ (2 : ℂ))ᶜ ∩ annulus (w : ℂ) r (2 * r))
          (w : ℂ) r (2 * r) = ∅ := by
      apply ae_all_iff.mpr
      intro q
      apply ae_all_iff.mpr
      intro w
      apply ae_all_iff.mpr
      intro n
      by_cases hq : 0 < (q : ℝ)
      · filter_upwards [htest q w n hq] with ω hω _
        exact hω
      · exact Filter.Eventually.of_forall fun _ h => (hq h).elim
    filter_upwards [hall, hevent] with ω hω heq
    apply (heq z hz).mpr
    intro q hq w hw n
    exact hω q ⟨w, hw⟩ n hq

end HarmonicBalls
