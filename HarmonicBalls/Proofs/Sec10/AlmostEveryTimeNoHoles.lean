import HarmonicBalls.Proofs.Sec10.VolumeGrowthHoleCriteria

/-! # Almost-every-time reduction for absence of holes

Right persistence allows deterministic times from any dense set to detect
holes. In particular, a time-almost-everywhere family of almost-sure
statements suffices, without a joint measurability assumption.
-/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter Topology

universe u

/-- Volume growth and typical scales make any dense set of positive times
sufficient to detect every bounded complementary component, simultaneously
for all poles. -/
theorem ae_cluster_no_holes_iff_no_holes_on_dense_times
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u})
    {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (T : Set ℝ) (hT : Dense T) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1,
      (∀ t : ℝ, 0 < t → ∀ U ∈ connectedComponentsIn
        (closure (cluster (μ ω) 1 z t))ᶜ, ¬ Bornology.IsBounded U) ↔
      (∀ t ∈ T, 0 < t → ∀ U ∈ connectedComponentsIn
        (closure (cluster (μ ω) 1 z t))ᶜ, ¬ Bornology.IsBounded U) := by
  filter_upwards [ae_cluster_hole_persists_of_volumeGrowth_typicalScales hI2 h82
    γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ] with ω hpersist
  intro z hz
  constructor
  · intro h t _ ht U hU
    exact h t ht U hU
  · intro h t ht U hU hb
    obtain ⟨δ, hδ, hp⟩ := hpersist t ht z hz U hU hb
    obtain ⟨s, hs, hsT⟩ := hT.inter_open_nonempty (Ioo t (t + δ))
      isOpen_Ioo (nonempty_Ioo.mpr (lt_add_of_pos_right t hδ))
    obtain ⟨V, hV, hVb, _⟩ := hp s ⟨hs.1.le, hs.2.le⟩
    exact h s hsT (ht.trans hs.1) V hV hVb

/-- For any set of poles, almost-sure absence of holes at almost every
positive deterministic time is equivalent to almost-sure absence at every
positive time. The time-wise assertion is uniform over the chosen poles.
No joint measurability of the hole event is needed. -/
theorem ae_cluster_no_holes_all_times_iff_ae_deterministic_time
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u})
    {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (Z : Set ℂ) (hZ : Z ⊆ ball (0 : ℂ) 1) :
    (∀ᵐ ω ∂P, ∀ z ∈ Z, ∀ t : ℝ, 0 < t → ∀ U ∈ connectedComponentsIn
      (closure (cluster (μ ω) 1 z t))ᶜ, ¬ Bornology.IsBounded U) ↔
    (∀ᵐ t ∂(volume : Measure ℝ), 0 < t → ∀ᵐ ω ∂P, ∀ z ∈ Z,
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
        ¬ Bornology.IsBounded U) := by
  constructor
  · intro hall
    exact Eventually.of_forall fun t ht => hall.mono fun ω hω z hz => hω z hz t ht
  · intro htime
    let S : Set ℝ := {t | 0 < t → ∀ᵐ ω ∂P, ∀ z ∈ Z,
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
        ¬ Bornology.IsBounded U}
    have hS : Dense S := Measure.dense_of_ae htime
    obtain ⟨T, hTS, hcount, hdense⟩ := hS.exists_countable_dense_subset
    let : Countable T := hcount.to_subtype
    have hall : ∀ᵐ ω ∂P, ∀ t : T, 0 < (t : ℝ) → ∀ z ∈ Z,
        ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
          ¬ Bornology.IsBounded U := by
      apply ae_all_iff.mpr
      intro t
      by_cases ht : 0 < (t : ℝ)
      · filter_upwards [(hTS t.property) ht] with ω hω _
        exact hω
      · exact Eventually.of_forall fun _ h => (ht h).elim
    filter_upwards [hall, ae_cluster_no_holes_iff_no_holes_on_dense_times hI2 h82
      hγ hγ2 hα P hC hcirc μ hGFF hμ T hdense] with ω hω heq
    intro z hz
    apply (heq z (hZ hz)).2
    intro t htT ht U hU
    exact hω ⟨t, htT⟩ ht z hz U hU


/-- The same almost-every-time criterion expressed as connectedness of closed
cluster complements. The premise is uniform over `Z`, which may be a singleton
or the whole unit disk. -/
theorem ae_cluster_compl_connected_all_times_iff_ae_deterministic_time
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u})
    {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (Z : Set ℂ) (hZ : Z ⊆ ball (0 : ℂ) 1) :
    (∀ᵐ ω ∂P, ∀ z ∈ Z, ∀ t : ℝ, 0 < t →
      IsConnected (closure (cluster (μ ω) 1 z t))ᶜ) ↔
    (∀ᵐ t ∂(volume : Measure ℝ), 0 < t → ∀ᵐ ω ∂P, ∀ z ∈ Z,
      IsConnected (closure (cluster (μ ω) 1 z t))ᶜ) := by
  have hchar (ω : Ω) (z : ℂ) (t : ℝ) :
      IsConnected (closure (cluster (μ ω) 1 z t))ᶜ ↔
      (∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
        ¬ Bornology.IsBounded U) := by
    have hcl : closure (cluster (μ ω) 1 z t) ⊆ closedBall 0 1 :=
      closure_minimal (cluster_subset_ball.trans ball_subset_closedBall) isClosed_closedBall
    have hp : (2 : ℂ) ∈ (closedBall (0 : ℂ) 1)ᶜ := by
      norm_num [mem_closedBall, dist_eq_norm]
    have h := not_isConnected_compl_iff_exists_bounded_component zero_lt_one hcl hp
    constructor
    · intro hc U hU hb
      exact (h.mpr ⟨U, hU, hb⟩) hc
    · intro hn
      by_contra hc
      obtain ⟨U, hU, hb⟩ := h.mp hc
      exact hn U hU hb
  have hmain := ae_cluster_no_holes_all_times_iff_ae_deterministic_time hI2 h82
    hγ hγ2 hα P hC hcirc μ hGFF hμ Z hZ
  constructor
  · intro hall
    have hn := hmain.mp (hall.mono fun ω hω z hz t ht => (hchar ω z t).mp (hω z hz t ht))
    filter_upwards [hn] with t ht htpos
    filter_upwards [ht htpos] with ω hω z hz
    exact (hchar ω z t).mpr (hω z hz)
  · intro htime
    have hn : ∀ᵐ t ∂(volume : Measure ℝ), 0 < t → ∀ᵐ ω ∂P, ∀ z ∈ Z,
        ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
          ¬ Bornology.IsBounded U := by
      filter_upwards [htime] with t ht htpos
      filter_upwards [ht htpos] with ω hω z hz
      exact (hchar ω z t).mp (hω z hz)
    filter_upwards [hmain.mpr hn] with ω hω z hz t ht
    exact (hchar ω z t).mpr (hω z hz t ht)

end HarmonicBalls
