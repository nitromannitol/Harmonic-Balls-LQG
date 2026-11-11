import HarmonicBalls.Steps.Sec11.PinchDiameterFiniteness
import HarmonicBalls.Steps.Sec11.PinchThresholdSelection

/-! # Deterministic core threshold for the mass-diameter construction -/

namespace HarmonicBalls
open MeasureTheory Set Filter
open scoped ENNReal

/-- A compact core inside a connected open neighborhood has a deterministic
finite internal-distance bound on a positive-mass part of any positive-mass
event. The event need not be measurable. -/
theorem exists_positive_measure_core_internal_distance_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω)
    (D : Ω → ℂ → ℂ → ℝ) {C O : Set ℂ}
    (hC : IsCompact C) (hO : IsOpen O) (hconn : IsConnected O) (hCO : C ⊆ O)
    (hA : 0 < P A) (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω)) :
    ∃ m : ℕ, 0 < P {ω | ω ∈ A ∧ ∀ x ∈ C, ∀ y ∈ C,
      internalMetric (D ω) O x y < (m : ℝ≥0∞)} := by
  let G : Set Ω := {ω | IsEuclideanLengthMetric (D ω)}
  have heq : A =ᵐ[P] A ∩ G := by
    filter_upwards [hmetric] with ω hω
    simp only [mem_inter_iff, G, mem_ofPred_eq, hω, and_true]
  have hAG : 0 < P (A ∩ G) := by rwa [← measure_congr heq]
  let g : Ω → ℝ≥0∞ := fun ω =>
    ⨆ x ∈ C, ⨆ y ∈ C, internalMetric (D ω) O x y
  have hfin : ∀ ω ∈ A ∩ G, (1 : ℝ≥0∞) ≠ 0 ∧ g ω ≠ ∞ := by
    intro ω hω
    have hm : IsEuclideanLengthMetric (D ω) := hω.2
    have hn : ∀ x y, 0 ≤ D ω x y := by
      intro x y
      have h := hm.triangle x y x
      rw [hm.self_eq_zero, hm.symm y x] at h
      linarith
    exact ⟨one_ne_zero, (hm.iSup_pair_internalMetric_lt_top_of_isCompact hn hO hconn hC hCO).ne⟩
  obtain ⟨n, m, hn, hp⟩ :=
    exists_positive_measure_uniform_thresholds P (A ∩ G) (fun _ => 1) g hAG hfin
  refine ⟨m, hp.trans_le (measure_mono ?_)⟩
  intro ω hω
  refine ⟨hω.1.1, ?_⟩
  intro x hx y hy
  have hle : internalMetric (D ω) O x y ≤ g ω := by
    dsimp [g]
    exact le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le y
      (le_iSup_of_le hy le_rfl)))
  exact hle.trans_lt hω.2.2

end HarmonicBalls
