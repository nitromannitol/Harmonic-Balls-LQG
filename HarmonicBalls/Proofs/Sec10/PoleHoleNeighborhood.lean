import HarmonicBalls.Proofs.Sec10.PoleHoleStability
import HarmonicBalls.Proofs.Sec10.VolumeGrowthHoleCriteria
import Mathlib.Topology.Sequences

/-! # Neighborhood persistence of holes under pole motion

The sequential compact-barrier result gives an entire neighborhood of poles
with bounded complementary components. Consequently any dense set of poles
detects a hole satisfying the compact-barrier hypothesis.
-/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter Topology

/-- In a Fréchet-Urysohn space, a property that eventually holds along
every sequence converging to a point holds in a neighborhood of that point. -/
theorem eventually_nhds_of_seq_eventually
    {X : Type*} [TopologicalSpace X] [FrechetUrysohnSpace X]
    {x : X} {p : X → Prop}
    (h : ∀ s : ℕ → X, Tendsto s atTop (𝓝 x) → ∀ᶠ n in atTop, p (s n)) :
    ∀ᶠ y in 𝓝 x, p y := by
  by_contra hn
  have hx : x ∈ closure {y | ¬ p y} := by
    apply mem_closure_iff_nhds.mpr
    intro V hV
    by_contra hne
    apply hn
    filter_upwards [hV] with y hy
    by_contra hyp
    exact hne ⟨y, hy, hyp⟩
  obtain ⟨s, hs, hlim⟩ := mem_closure_iff_seq_limit.mp hx
  obtain ⟨n, hn⟩ := (h s hlim).exists
  exact hs n hn

universe u

/-- A compact pole-avoiding barrier with positive exterior mass forces a
bounded hole for every pole in some neighborhood. The barrier remains an
explicit geometric hypothesis. -/
theorem ae_bounded_hole_near_centre_of_compact_barrier
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u})
    {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z : ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ K W U : Set ℂ, IsCompact K → K ⊆ cluster (μ ω) 1 z t →
      (z : ℂ) ∉ K → W ∈ connectedComponentsIn Kᶜ → Bornology.IsBounded W →
      U ⊆ W → U ⊆ ball 0 1 → U ⊆ (cluster (μ ω) 1 z t)ᶜ → μ ω U ≠ 0 →
      ∀ᶠ w : ball (0 : ℂ) 1 in 𝓝 z,
        ∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 w t))ᶜ,
        Bornology.IsBounded V ∧ (V ∩ U).Nonempty := by
  filter_upwards [ae_bounded_hole_persists_of_compact_barrier_under_centre_motion
    hI2 h82 hγ hγ2 hα P hC hcirc μ hGFF hμ] with ω hω
  intro t ht z hcompact K W U hK hKsub hzK hW hWb hUW hUball hUout hUpos
  apply eventually_nhds_of_seq_eventually
  intro zs hzs
  exact hω t ht z hcompact K W U hK hKsub hzK hW hWb hUW hUball hUout hUpos zs hzs

/-- Each dense set of poles detects every compact-barrier hole at the same
time, on the same probability-one event. -/
theorem ae_dense_centres_detect_compact_barrier_holes
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u})
    {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z : ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ K W U : Set ℂ, IsCompact K → K ⊆ cluster (μ ω) 1 z t →
      (z : ℂ) ∉ K → W ∈ connectedComponentsIn Kᶜ → Bornology.IsBounded W →
      U ⊆ W → U ⊆ ball 0 1 → U ⊆ (cluster (μ ω) 1 z t)ᶜ → μ ω U ≠ 0 →
      ∀ D : Set (ball (0 : ℂ) 1), Dense D →
      ∃ w ∈ D, ∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 w t))ᶜ,
        Bornology.IsBounded V ∧ (V ∩ U).Nonempty := by
  filter_upwards [ae_bounded_hole_near_centre_of_compact_barrier
    hI2 h82 hγ hγ2 hα P hC hcirc μ hGFF hμ] with ω hω
  intro t ht z hcompact K W U hK hKsub hzK hW hWb hUW hUball hUout hUpos D hD
  have hnear := hω t ht z hcompact K W U hK hKsub hzK hW hWb hUW hUball hUout hUpos
  obtain ⟨w, hw, hwD⟩ := mem_closure_iff_nhds.mp (hD z) _ hnear
  exact ⟨w, hwD, hw⟩

/-- A compact-barrier hole is detected at a dense pole and a later rational
time. The rational-time hole need not meet the original exterior set. -/
theorem ae_dense_centres_rational_times_detect_compact_barrier_holes
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u})
    {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z : ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ K W U : Set ℂ, IsCompact K → K ⊆ cluster (μ ω) 1 z t →
      (z : ℂ) ∉ K → W ∈ connectedComponentsIn Kᶜ → Bornology.IsBounded W →
      U ⊆ W → U ⊆ ball 0 1 → U ⊆ (cluster (μ ω) 1 z t)ᶜ → μ ω U ≠ 0 →
      ∀ D : Set (ball (0 : ℂ) 1), Dense D → ∃ w ∈ D, ∃ q : ℚ, t < (q : ℝ) ∧
        ∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 w q))ᶜ,
          Bornology.IsBounded V := by
  filter_upwards [ae_dense_centres_detect_compact_barrier_holes
      hI2 h82 hγ hγ2 hα P hC hcirc μ hGFF hμ,
    ae_cluster_hole_persists_of_volumeGrowth_typicalScales hI2 h82
      γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ] with ω hdense hpersist
  intro t ht z hcompact K W U hK hKsub hzK hW hWb hUW hUball hUout hUpos D hD
  obtain ⟨w, hwD, V, hV, hVb, _⟩ :=
    hdense t ht z hcompact K W U hK hKsub hzK hW hWb hUW hUball hUout hUpos D hD
  obtain ⟨δ, hδ, hp⟩ := hpersist t ht w w.property V hV hVb
  obtain ⟨q, hqt, hqδ⟩ := exists_rat_btwn (lt_add_of_pos_right t hδ)
  obtain ⟨V', hV', hVb', _⟩ := hp q ⟨hqt.le, hqδ.le⟩
  exact ⟨w, hwD, q, hqt, V', hV', hVb'⟩

end HarmonicBalls
