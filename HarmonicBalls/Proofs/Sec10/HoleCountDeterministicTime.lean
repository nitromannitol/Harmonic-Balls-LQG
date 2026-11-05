import HarmonicBalls.Proofs.Sec10.FiniteHoleCounts
import HarmonicBalls.Proofs.Sec10.RationalTimeHoles

/-! # Hole-count bounds from almost every deterministic time -/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter Topology

universe u

/-- Under I2 and the typical-scale estimate, a bound on the number of bounded
holes at a dense set of times is equivalent to the same bound at every positive
time. This includes clusters whose closure meets the disc boundary. -/
theorem ae_cluster_hole_count_bound_iff_dense_times
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u})
    {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (T : Set ℝ) (hT : Dense T) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ n : ℕ,
      (∀ t : ℝ, 0 < t → ∀ F : Finset (Set ℂ),
        (∀ U ∈ F, U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ ∧
          Bornology.IsBounded U) → F.card ≤ n) ↔
      (∀ t ∈ T, 0 < t → ∀ F : Finset (Set ℂ),
        (∀ U ∈ F, U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ ∧
          Bornology.IsBounded U) → F.card ≤ n) := by
  classical
  filter_upwards [ae_finite_cluster_holes_inject_at_boundary_contact hI2
    (Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hI2) h82
    γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ] with ω hpersist
  intro z hz n
  constructor
  · intro h t _ ht F hF
    exact h t ht F hF
  · intro h t ht F hF
    obtain ⟨δ, hδ, hp⟩ := hpersist t ht z hz F hF
    obtain ⟨s, hs, hsT⟩ := hT.inter_open_nonempty (Ioo t (t + δ))
      isOpen_Ioo (nonempty_Ioo.mpr (lt_add_of_pos_right t hδ))
    obtain ⟨V, hVinj, hV⟩ := hp s ⟨hs.1.le, hs.2.le⟩
    have hbound := h s hsT (ht.trans hs.1) (F.attach.image V) (by
      intro U hU
      obtain ⟨W, _, rfl⟩ := Finset.mem_image.mp hU
      exact ⟨(hV W).1, (hV W).2.1⟩)
    simpa [Finset.card_image_of_injective _ hVinj] using hbound

/-- A uniform-in-pole finite hole-count bound almost surely at almost every
deterministic time is equivalent to the bound at all positive times almost
surely. No joint measurability in time and sample is assumed. -/
theorem ae_cluster_hole_count_bound_all_times_iff_ae_deterministic_time
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u})
    {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (Z : Set ℂ) (hZ : Z ⊆ ball (0 : ℂ) 1) (n : ℕ) :
    (∀ᵐ ω ∂P, ∀ z ∈ Z, ∀ t : ℝ, 0 < t → ∀ F : Finset (Set ℂ),
      (∀ U ∈ F, U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ ∧
        Bornology.IsBounded U) → F.card ≤ n) ↔
    (∀ᵐ t ∂(volume : Measure ℝ), 0 < t → ∀ᵐ ω ∂P, ∀ z ∈ Z,
      ∀ F : Finset (Set ℂ),
        (∀ U ∈ F, U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ ∧
          Bornology.IsBounded U) → F.card ≤ n) := by
  classical
  constructor
  · intro hall
    exact Eventually.of_forall fun t ht => hall.mono fun ω hω z hz => hω z hz t ht
  · intro htime
    let S : Set ℝ := {t | 0 < t → ∀ᵐ ω ∂P, ∀ z ∈ Z,
      ∀ F : Finset (Set ℂ),
        (∀ U ∈ F, U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ ∧
          Bornology.IsBounded U) → F.card ≤ n}
    have hS : Dense S := Measure.dense_of_ae htime
    obtain ⟨T, hTS, hcount, hdense⟩ := hS.exists_countable_dense_subset
    let : Countable T := hcount.to_subtype
    have hall : ∀ᵐ ω ∂P, ∀ t : T, 0 < (t : ℝ) → ∀ z ∈ Z,
        ∀ F : Finset (Set ℂ),
          (∀ U ∈ F, U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ ∧
            Bornology.IsBounded U) → F.card ≤ n := by
      apply ae_all_iff.mpr
      intro t
      by_cases ht : 0 < (t : ℝ)
      · filter_upwards [(hTS t.property) ht] with ω hω _
        exact hω
      · exact Filter.Eventually.of_forall fun _ h => (ht h).elim
    filter_upwards [hall, ae_cluster_hole_count_bound_iff_dense_times hI2 h82
      hγ hγ2 hα P hC hcirc μ hGFF hμ T hdense] with ω hω heq
    intro z hz
    apply (heq z (hZ hz) n).2
    intro t htT ht F hF
    exact hω ⟨t, htT⟩ ht z hz F hF

end HarmonicBalls
