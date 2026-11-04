import HarmonicBalls.Proofs.Sec10.PoleHoleNeighborhood

/-! # Countable tests for compact-barrier holes

Full support supplies the positive mass required in the pole-stability
argument. Countable dense poles and rational times then reduce the exclusion
of compact-barrier holes to pointwise almost-sure exclusions.
-/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter Topology

universe u

/-- A nonempty open set trapped by a compact barrier detects a hole at a
dense pole and a later rational time. -/
theorem ae_dense_centres_rational_times_detect_open_barrier_holes
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
      IsOpen U → U.Nonempty → U ⊆ W → U ⊆ ball 0 1 →
      U ⊆ (cluster (μ ω) 1 z t)ᶜ →
      ∀ D : Set (ball (0 : ℂ) 1), Dense D → ∃ w ∈ D, ∃ q : ℚ, t < (q : ℝ) ∧
        ∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 w q))ᶜ,
          Bornology.IsBounded V := by
  filter_upwards [ae_dense_centres_rational_times_detect_compact_barrier_holes
      hI2 h82 hγ hγ2 hα P hC hcirc μ hGFF hμ,
    lqgMeasureFullSupportStmt_of_volumeGrowth hI2 γ α₀ hγ hγ2 hα
      Ω P hC hcirc μ hGFF hμ] with ω hdetect hfull
  intro t ht z hcompact K W U hK hKsub hzK hW hWb hUopen hUne hUW hUball hUout D hD
  exact hdetect t ht z hcompact K W U hK hKsub hzK hW hWb hUW hUball hUout
    (hfull U hUopen hUne).ne' D hD

/-- If bounded holes are almost surely absent at each pole of a countable
dense set and each positive rational time, then almost surely no compactly
contained cluster has a compact pole-avoiding barrier trapping a nonempty
open exterior set. The pointwise no-hole assertions remain hypotheses. -/
theorem ae_no_open_barrier_holes_of_countable_pole_tests
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u})
    {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (D : Set (ball (0 : ℂ) 1)) (hDcount : D.Countable) (hDdense : Dense D)
    (htests : ∀ w : D, ∀ q : ℚ, 0 < (q : ℝ) → ∀ᵐ ω ∂P,
      ∀ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 (w : ball (0 : ℂ) 1) q))ᶜ,
        ¬ Bornology.IsBounded V) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z : ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ K W U : Set ℂ, IsCompact K → K ⊆ cluster (μ ω) 1 z t →
      (z : ℂ) ∉ K → W ∈ connectedComponentsIn Kᶜ → Bornology.IsBounded W →
      IsOpen U → U.Nonempty → U ⊆ W → U ⊆ ball 0 1 →
      U ⊆ (cluster (μ ω) 1 z t)ᶜ → False := by
  let : Countable D := hDcount.to_subtype
  have hall : ∀ᵐ ω ∂P, ∀ w : D, ∀ q : ℚ, 0 < (q : ℝ) →
      ∀ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 (w : ball (0 : ℂ) 1) q))ᶜ,
        ¬ Bornology.IsBounded V := by
    apply ae_all_iff.mpr
    intro w
    apply ae_all_iff.mpr
    intro q
    by_cases hq : 0 < (q : ℝ)
    · filter_upwards [htests w q hq] with ω hω _
      exact hω
    · exact Eventually.of_forall fun _ h => (hq h).elim
  filter_upwards [hall, ae_dense_centres_rational_times_detect_open_barrier_holes
    hI2 h82 hγ hγ2 hα P hC hcirc μ hGFF hμ] with ω hall hdetect
  intro t ht z hcompact K W U hK hKsub hzK hW hWb hUopen hUne hUW hUball hUout
  obtain ⟨w, hwD, q, hq, V, hV, hVb⟩ :=
    hdetect t ht z hcompact K W U hK hKsub hzK hW hWb hUopen hUne hUW hUball hUout
      D hDdense
  exact hall ⟨w, hwD⟩ q (ht.trans hq) V hV hVb

/-- Under the countable pole tests, a bounded complementary component cannot
be enclosed by a compact pole-avoiding subset of the cluster. -/
theorem ae_bounded_holes_not_enclosed_of_countable_pole_tests
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u})
    {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (D : Set (ball (0 : ℂ) 1)) (hDcount : D.Countable) (hDdense : Dense D)
    (htests : ∀ w : D, ∀ q : ℚ, 0 < (q : ℝ) → ∀ᵐ ω ∂P,
      ∀ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 (w : ball (0 : ℂ) 1) q))ᶜ,
        ¬ Bornology.IsBounded V) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z : ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ H ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      Bornology.IsBounded H → ∀ K W : Set ℂ, IsCompact K →
      K ⊆ cluster (μ ω) 1 z t → (z : ℂ) ∉ K →
      W ∈ connectedComponentsIn Kᶜ → Bornology.IsBounded W → H ⊆ W → False := by
  filter_upwards [ae_no_open_barrier_holes_of_countable_pole_tests
    hI2 h82 hγ hγ2 hα P hC hcirc μ hGFF hμ D hDcount hDdense htests] with ω hno
  intro t ht z hcompact H hH hHb K W hK hKsub hzK hW hWb hHW
  have hopen : IsOpen H := by
    obtain ⟨x, hx, hxH⟩ := hH
    rw [← hxH]
    exact isClosed_closure.isOpen_compl.connectedComponentIn
  have hnon : H.Nonempty := by
    obtain ⟨x, hx, hxH⟩ := hH
    exact ⟨x, hxH ▸ mem_connectedComponentIn hx⟩
  have hHout : H ⊆ (cluster (μ ω) 1 z t)ᶜ := by
    obtain ⟨x, hx, hxH⟩ := hH
    exact (hxH ▸ connectedComponentIn_subset _ x).trans (compl_subset_compl.mpr subset_closure)
  have hHball : H ⊆ ball (0 : ℂ) 1 :=
    bounded_complement_component_subset_unit_ball isClosed_closure
      (hcompact.trans ball_subset_closedBall) hH hHb
  exact hno t ht z hcompact K W H hK hKsub hzK hW hWb hopen hnon hHW hHball hHout

end HarmonicBalls
