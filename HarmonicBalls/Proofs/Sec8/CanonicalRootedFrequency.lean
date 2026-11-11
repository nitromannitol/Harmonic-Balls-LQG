import HarmonicBalls.Proofs.Sec8.CanonicalPhaseCertificate
import HarmonicBalls.Proofs.Sec8.SingularFieldFrequencyCertificate

/-! # Frequency certificates for the canonical field at rooted points

The distribution reconstruction and imported frequency arguments use
Leonardo Bonanno's LatticeProb formalization.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

namespace HarmonicBalls

/-- The measurable frequency certificate on raw pairings can be evaluated on
any distribution-valued version, simultaneously for every possible root. -/
theorem IsWholePlaneGFF.exists_canonical_global_field_frequency_certificate
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α β : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {ν : Ω → Measure ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hν : IsLQGMeasureOfField P γ α hcirc ν)
    (H : Ω → LQGMetric.DistC)
    (hversion : ∀ φ : LQGMetric.TestC0,
      (fun ω => H ω φ.1) =ᵐ[P] (fun ω => hC ω φ.1))
    (hmass : ∀ᵐ ω ∂P, ν ω (ball 0 1) ≠ 0)
    (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ) (ha : 0 < a) :
    ∃ E : Set (LQGMetric.DistC × ℂ), MeasurableSet E ∧
      ∀ᵐ ω ∂P, ∀ᵐ z ∂ν ω,
        ((H ω, z) ∈ E ↔ ∀ᶠ K : ℕ in atTop, (1 - ζ) * (K : ℝ) ≤
          (veryGoodComparableScaleCount (ν ω) β z N₀ a b C₁m C₁p C₂m C₂p C₃ m K : ℝ)) := by
  obtain ⟨E₀, hE₀, hEae⟩ := hh.exists_global_field_frequency_certificate hν hmass
    N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ ha
  let R : LQGMetric.DistC → RawMeanZeroTest → ℝ := fun h φ => h (meanZeroTestEquiv.symm φ).1
  have hR : Measurable R := measurable_pi_iff.mpr fun φ =>
    LQGMetric.measurable_distOn_apply (meanZeroTestEquiv.symm φ).1
  let E : Set (LQGMetric.DistC × ℂ) := (fun p => (R p.1, p.2)) ⁻¹' E₀
  have hxy : ∀ φ : RawMeanZeroTest,
      (fun ω => R (H ω) φ) =ᵐ[P] (fun ω => hC ω φ.1) := by
    intro φ
    filter_upwards [hversion (meanZeroTestEquiv.symm φ)] with ω hω
    change H ω (meanZeroTestEquiv.symm φ).1 = hC ω φ.1 at hω
    exact hω
  let E' : Set (ℂ × (RawMeanZeroTest → ℝ)) := Prod.swap ⁻¹' E₀
  have hE' : MeasurableSet E' := hE₀.preimage measurable_swap
  have heq := ae_forall_mem_iff_of_coordinatewise_ae_eq hxy E' hE'
  refine ⟨E, hE₀.preimage ((hR.comp measurable_fst).prodMk measurable_snd), ?_⟩
  filter_upwards [heq, hEae] with ω hω hfreq
  filter_upwards [hfreq] with z hz
  exact (hω z).trans hz

/-- A fixed-root estimate for the canonical certificate implies the global
frequency estimate whenever the displayed canonical rooted-law comparisons
hold on an expanding ball cover. -/
theorem IsWholePlaneGFF.exists_canonical_global_frequency_of_root_reference
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} {γ α β : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {ν : Ω → Measure ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hν : IsLQGMeasureOfField P γ α hcirc ν)
    (H : Ω → LQGMetric.DistC) (hH : Measurable H)
    (hversion : ∀ φ : LQGMetric.TestC0,
      (fun ω => H ω φ.1) =ᵐ[P] (fun ω => hC ω φ.1))
    (hmass : ∀ᵐ ω ∂P, ν ω (ball 0 1) ≠ 0)
    (ρ : ℕ → Measure ℂ) (Q : Measure Ξ) [SFinite Q]
    (shift : ℕ → ℂ × Ξ → LQGMetric.DistC) (hshift : ∀ n, Measurable (shift n))
    (R : ℕ → ℂ → Measure LQGMetric.DistC)
    (hrooted : ∀ n : ℕ, (P.bind fun ω => ((ν ω).restrict (ball 0 ((n : ℝ) + 1))).map
      (fun z => (H ω, z))) ≪ shiftedRootReferenceLaw (ρ n) Q (shift n))
    (hac : ∀ n, ∀ᵐ z ∂ρ n, Q.map (fun ω => shift n (z, ω)) ≪ R n z)
    (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ) (ha : 0 < a) :
    ∃ E : Set (LQGMetric.DistC × ℂ), MeasurableSet E ∧
      ((∀ n, ∀ᵐ z ∂ρ n, ∀ᵐ f ∂(R n z), (f, z) ∈ E) →
        ∀ᵐ ω ∂P, ∀ᵐ z ∂ν ω, ∀ᶠ K : ℕ in atTop,
          (1 - ζ) * (K : ℝ) ≤
            (veryGoodComparableScaleCount (ν ω) β z N₀ a b C₁m C₁p C₂m C₂p C₃ m K : ℝ)) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  have hfin : ∀ n : ℕ, ∀ᵐ ω ∂P, ν ω (ball 0 ((n : ℝ) + 1)) ≠ ∞ := by
    intro n
    filter_upwards [hν] with ω hω
    let : IsLocallyFiniteMeasure (ν ω) := hω.isLocallyFiniteMeasure
    exact measure_ball_ne_top
  have hcover : ∀ z : ℂ, ∃ n : ℕ, z ∈ ball 0 ((n : ℝ) + 1) := by
    intro z
    obtain ⟨n, hn⟩ := exists_nat_gt (dist z (0 : ℂ))
    exact ⟨n, mem_ball.mpr (by linarith)⟩
  obtain ⟨E, hE, hcert⟩ := hh.exists_canonical_global_field_frequency_certificate
    hν H hversion hmass N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ ha
  refine ⟨E, hE, fun hfixed => ?_⟩
  have ht := ae_ae_of_observed_root_reference_cover P ν (hh.aemeasurable_lqgMeasure hν)
    H hH (fun n => ball 0 ((n : ℝ) + 1)) (fun _ => measurableSet_ball) hcover hfin
    ρ Q shift hshift R (p := fun x => x ∈ E) hE hrooted hac hfixed
  filter_upwards [ht, hcert] with ω hω hc
  filter_upwards [hω, hc] with z hz hcz
  exact hcz.mp hz

end HarmonicBalls
