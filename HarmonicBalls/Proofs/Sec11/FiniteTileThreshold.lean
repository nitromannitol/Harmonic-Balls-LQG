import HarmonicBalls.Proofs.Sec11.MassDiameterCoreThreshold
import HarmonicBalls.Proofs.Sec11.ConditionalPositiveIntersection

/-! # Simultaneous deterministic thresholds on finitely many tiles -/

namespace HarmonicBalls
open MeasureTheory Set Filter
open scoped ENNReal

/-- Any positive-probability seed contains a positive-probability subevent
on which finitely many compact tiles have a common finite internal-distance
bound. No measurability of the seed or the threshold events is needed. -/
theorem exists_positive_measure_finite_tiles_internal_distance_bound
    {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (P : Measure Ω) (D : Ω → ℂ → ℂ → ℝ) (I : Finset ι)
    (H J : ι → Set ℂ) (hH : ∀ i ∈ I, IsCompact (H i))
    (hJ : ∀ i ∈ I, IsOpen (J i)) (hconn : ∀ i ∈ I, IsConnected (J i))
    (hHJ : ∀ i ∈ I, H i ⊆ J i)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (A : Set Ω) (hA : 0 < P A) :
    ∃ m : ℕ, 0 < P {ω | ω ∈ A ∧ ∀ i ∈ I, ∀ x ∈ H i, ∀ y ∈ H i,
      internalMetric (D ω) (J i) x y < (m : ℝ≥0∞)} := by
  induction I using Finset.induction_on generalizing A with
  | empty =>
      refine ⟨0, ?_⟩
      simpa using hA
  | @insert i I hi ih =>
      have hHi : IsCompact (H i) := hH i (Finset.mem_insert_self i I)
      have hJi : IsOpen (J i) := hJ i (Finset.mem_insert_self i I)
      have hci : IsConnected (J i) := hconn i (Finset.mem_insert_self i I)
      have hsubi : H i ⊆ J i := hHJ i (Finset.mem_insert_self i I)
      obtain ⟨m, hm⟩ := ih (fun j hj => hH j (Finset.mem_insert_of_mem hj))
        (fun j hj => hJ j (Finset.mem_insert_of_mem hj))
        (fun j hj => hconn j (Finset.mem_insert_of_mem hj))
        (fun j hj => hHJ j (Finset.mem_insert_of_mem hj)) A hA
      let B : Set Ω := {ω | ω ∈ A ∧ ∀ j ∈ I, ∀ x ∈ H j, ∀ y ∈ H j,
        internalMetric (D ω) (J j) x y < (m : ℝ≥0∞)}
      obtain ⟨n, hn⟩ := exists_positive_measure_core_internal_distance_bound P B D
        hHi hJi hci hsubi hm hmetric
      refine ⟨max m n, hn.trans_le (measure_mono ?_)⟩
      intro ω hω
      refine ⟨hω.1.1, ?_⟩
      intro j hj x hx y hy
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact (hω.2 x hx y hy).trans_le (by exact_mod_cast le_max_right m n)
      · exact (hω.1.2 j hj x hx y hy).trans_le (by exact_mod_cast le_max_left m n)


/-- If a measurable mass event has positive conditional probability, then
every positive outside event contains a positive-probability seed with that
mass event and one finite bound for all tiles. The bound may depend on the
outside event. -/
theorem exists_positive_conditional_mass_finite_tile_seed
    {Ω ι : Type*} [m₀ : MeasurableSpace Ω] [DecidableEq ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (m : MeasurableSpace Ω) (hm : m ≤ m₀)
    (D : Ω → ℂ → ℂ → ℝ) (I : Finset ι)
    (H J : ι → Set ℂ) (hH : ∀ i ∈ I, IsCompact (H i))
    (hJ : ∀ i ∈ I, IsOpen (J i)) (hconn : ∀ i ∈ I, IsConnected (J i))
    (hHJ : ∀ i ∈ I, H i ⊆ J i)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (G F : Set Ω) (hG : @MeasurableSet Ω m₀ G) (hF : MeasurableSet[m] F)
    (hFp : 0 < P F)
    (hcond : ∀ᵐ ω ∂P, 0 < (P[G.indicator (fun _ => (1 : ℝ)) | m]) ω) :
    ∃ n : ℕ, 0 < P {ω | ω ∈ F ∧ ω ∈ G ∧ ∀ i ∈ I, ∀ x ∈ H i, ∀ y ∈ H i,
      internalMetric (D ω) (J i) x y < (n : ℝ≥0∞)} := by
  have hp : 0 < P (F ∩ G) := measure_inter_pos_of_condExp_indicator_pos P m hm hF hG hFp hcond
  obtain ⟨n, hn⟩ := @exists_positive_measure_finite_tiles_internal_distance_bound
    Ω ι m₀ ‹DecidableEq ι› P D I H J hH hJ hconn hHJ hmetric (F ∩ G) hp
  refine ⟨n, ?_⟩
  simpa only [mem_inter_iff, and_assoc] using hn

end HarmonicBalls
