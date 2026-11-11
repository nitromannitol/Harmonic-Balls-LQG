import HarmonicBalls.Proofs.Sec8.BufferedRootedLocalEvents

/-! # Eventual local events at buffered sampled roots

The buffered regions increase as their radii shrink. Thus a countable family
of origin-inserted almost-sure events transfers at all sufficiently small
scales at almost every sampled root. This development uses Leonardo Bonanno's
whole-plane GFF formalization.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal

/-- The interior and exterior buffered regions increase as the buffer shrinks. -/
theorem bufferedRoots_mono : Monotone bufferedRoots := by
  intro n m hnm z hz
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hden : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hnm 1
  have hle : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
    one_div_le_one_div_of_le hpos hden
  rcases hz with hin | hout
  · left
    change ‖z‖ + 1 / ((m : ℝ) + 1) < 1
    change ‖z‖ + 1 / ((n : ℝ) + 1) < 1 at hin
    linarith
  · right
    change 1 + 1 / ((m : ℝ) + 1) < ‖z‖
    change 1 + 1 / ((n : ℝ) + 1) < ‖z‖ at hout
    linarith

/-- Under a rooted-law comparison and an absolutely continuous reference root
measure, the origin-inserted events hold at every sufficiently small scale
for almost every sampled root. -/
theorem IsWholePlaneGFF.ae_ae_eventually_buffered_local_events
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (μ : Ω → Measure ℂ)
    (hμ : AEMeasurable μ P) (A : Set ℂ) (hA : MeasurableSet A)
    (hfin : ∀ᵐ ω ∂P, μ ω A ≠ ∞) (ρ : Measure ℂ) [SFinite ρ]
    (hρ : ρ ≪ volume) (γ : ℝ)
    (hrooted : (P.bind fun ω => ((μ ω).restrict A).map
      (fun z => (Section6.pairingProc hC ω, z))) ≪
      shiftedRootReferenceLaw ρ P (fun p => fun φ : LQGMetric.TestC0 =>
        hC p.2 φ.1 + ∫ x, φ.1 x *
          (-γ * Real.log ‖x - p.1‖ + γ * Real.log (max ‖x‖ 1))))
    (E : ∀ n : ℕ, Set (Section6.LocalTest (ball 0 (1 / (2 * ((n : ℝ) + 1)))) → ℝ))
    (hE : ∀ n, MeasurableSet (E n))
    (hfixed : ∀ n, ∀ᵐ ω ∂P,
      (fun φ : Section6.LocalTest (ball 0 (1 / (2 * ((n : ℝ) + 1)))) =>
        hC ω φ.1.1 + ∫ x, φ.1.1 x * (-γ * Real.log ‖x‖)) ∈ E n) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, z ∈ A → ∀ᶠ n in atTop,
      z ∈ bufferedRoots n ∧
      recenteredDistributionObservation (ball 0 (1 / (2 * ((n : ℝ) + 1))))
        (Section6.pairingProc hC ω, z) ∈ E n := by
  filter_upwards [hh.ae_ae_buffered_local_events μ hμ A hA hfin ρ γ hrooted E hE hfixed,
    hh.ae_ae_buffered_root_cover μ hμ A hA hfin ρ hρ γ hrooted] with ω hev hcov
  filter_upwards [hev, hcov] with z hz hc hzA
  have hsome : ∃ n, z ∈ bufferedRoots n := by
    rcases hc hzA with ⟨n, hn⟩ | ⟨n, hn⟩
    · exact ⟨n, Or.inl hn⟩
    · exact ⟨n, Or.inr hn⟩
  obtain ⟨N, hN⟩ := hsome
  filter_upwards [eventually_ge_atTop N] with n hn
  have hzn := bufferedRoots_mono hn hN
  exact ⟨hzn, hz hzA n hzn⟩

end HarmonicBalls
