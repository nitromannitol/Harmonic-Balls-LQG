import HarmonicBalls.Proofs.Sec8.VeryGoodLocality
import HarmonicBalls.Proofs.Sec6.Localization
import HarmonicBalls.Proofs.Sec8.SingularTypicalPointTransfer

/-! # Good-scale frequency for comparable measures

Local comparability transfers the two measure-dependent events in the block
count with explicit constants. The imported Section 8 development uses
Leonardo Bonanno's whole-plane GFF formalization.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

/-- Local comparability transfers the annulus-ball mass comparison with its
threshold divided by four. -/
theorem annulusBallComparison_of_comparable
    {μ ν : Measure ℂ} {z : ℂ} {n : ℕ} {m : ℝ} {c : ℝ≥0∞}
    (h : Section6.IsComparableOn μ ν (ball z (2 * dyadicScale n)) c)
    (hv : AnnulusBallComparison ν n z m) : AnnulusBallComparison μ n z (m / 4) := by
  have hball : ball z (dyadicScale n) ⊆ ball z (2 * dyadicScale n) :=
    ball_subset_ball (by have := dyadicScale_pos n; linarith)
  have hann : annulus z (dyadicScale (n + 1)) (dyadicScale n) ⊆
      ball z (2 * dyadicScale n) := sdiff_subset.trans hball
  change ENNReal.ofReal (m / 4) * μ (ball z (dyadicScale n)) ≤
    μ (annulus z (dyadicScale (n + 1)) (dyadicScale n))
  calc
    _ ≤ ENNReal.ofReal (m / 4) * (4 * c * ν (ball z (dyadicScale n))) := by
      gcongr
      exact h.apply_le hball
    _ = c * (ENNReal.ofReal m * ν (ball z (dyadicScale n))) := by
      rw [← Section6.ofReal_div_four_mul_four m]
      ring
    _ ≤ c * ν (annulus z (dyadicScale (n + 1)) (dyadicScale n)) := by
      gcongr
      exact hv
    _ ≤ μ (annulus z (dyadicScale (n + 1)) (dyadicScale n)) := h.le_apply hann

/-- Comparable measures on a fixed neighborhood transfer both good-scale
conditions at all sufficiently fine dyadic scales. -/
theorem eventually_veryGoodComparable_of_comparable
    {μ ν : Measure ℂ} {z : ℂ} {R : ℝ} {c : ℝ≥0∞}
    (hR : 0 < R) (h : Section6.IsComparableOn μ ν (ball z R) c)
    {β : ℝ} {N₀ : ℕ} (hN₀ : 5 ≤ N₀) {a b C₁m C₁p C₂m C₂p C₃ m : ℝ} :
    ∃ K : ℕ, ∀ n, K ≤ n →
      (IsVeryGoodAnnulus ν β (dyadicScale n) z N₀ a b C₁m C₁p C₂m C₂p C₃ ∧
        AnnulusBallComparison ν n z m) →
      (IsVeryGoodAnnulus μ β (dyadicScale n) z N₀ (a / 4) b
        (C₁m / 4) (4 * C₁p) (C₂m / 4) (4 * C₂p) C₃ ∧
        AnnulusBallComparison μ n z (m / 4)) := by
  obtain ⟨K, hK⟩ := eventually_ball_six_dyadic_subset z hR
  refine ⟨K, ?_⟩
  intro n hn hv
  have hsub : ball z (2 * dyadicScale n) ⊆ ball z R :=
    (ball_subset_ball (by have := dyadicScale_pos n; linarith)).trans (hK n hn)
  exact ⟨Section6.isVeryGoodAnnulus_of_comparable (h.mono hsub) (dyadicScale_pos n) hN₀ hv.1,
    annulusBallComparison_of_comparable (h.mono hsub) hv.2⟩

/-- Local comparability preserves lower block-frequency bounds after the
explicit adjustment of the thresholds. -/
theorem veryGoodComparable_blockFrequency_of_comparable
    {μ ν : Measure ℂ} {z : ℂ} {R : ℝ} {c : ℝ≥0∞}
    (hR : 0 < R) (h : Section6.IsComparableOn μ ν (ball z R) c)
    {β : ℝ} {N₀ : ℕ} (hN₀ : 5 ≤ N₀) {a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ}
    (hv : ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
      (veryGoodComparableScaleCount ν β z N₀ a b C₁m C₁p C₂m C₂p C₃ m N : ℝ)) :
    ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
      (veryGoodComparableScaleCount μ β z N₀ (a / 4) b (C₁m / 4) (4 * C₁p)
        (C₂m / 4) (4 * C₂p) C₃ (m / 4) N : ℝ) := by
  obtain ⟨K, hK⟩ := eventually_veryGoodComparable_of_comparable hR h hN₀
  filter_upwards [hv, eventually_ge_atTop K] with N hN hKN
  apply hN.trans
  norm_cast
  apply Set.ncard_le_ncard
  · intro n hn
    refine ⟨hn.1, hK n (le_trans hKN (le_trans (Nat.le_succ N) hn.1.1)) ⟨hn.2.1, hn.2.2⟩⟩
  · exact (Set.finite_Icc (N + 1) (2 * N)).subset (by intro n hn; exact hn.1)

/-- Away from the origin the singular Weyl weight is uniformly comparable
to a constant in some positive-radius neighborhood. -/
theorem exists_comparableOn_ball_of_singular_weight
    {μ ν : Measure ℂ} {z : ℂ} {e : ℝ} (hz : z ≠ 0)
    (hweight : μ.restrict {0}ᶜ =
      (ν.withDensity fun x => ENNReal.ofReal (‖x‖ ^ e)).restrict {0}ᶜ) :
    ∃ R : ℝ, 0 < R ∧ ∃ c : ℝ≥0∞, Section6.IsComparableOn μ ν (ball z R) c := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  let f : ℝ → ℝ := fun R => |e| * (4 * R / ‖z‖)
  have hf : ContinuousAt f 0 := by
    dsimp [f]
    fun_prop
  have hlim : Tendsto f (𝓝 0) (𝓝 0) := by
    simpa [f] using hf.tendsto
  have hflat : ∀ᶠ R in 𝓝[>] (0 : ℝ), f R ≤ Real.log 2 :=
    nhdsWithin_le_nhds (hlim.eventually (eventually_le_nhds (Real.log_pos one_lt_two)))
  have hsmall : ∀ᶠ R in 𝓝[>] (0 : ℝ), R < ‖z‖ / 2 :=
    nhdsWithin_le_nhds (eventually_lt_nhds (by positivity))
  have hpos : ∀ᶠ R in 𝓝[>] (0 : ℝ), 0 < R := self_mem_nhdsWithin
  obtain ⟨R, hR, hfR, hRsmall⟩ := (hpos.and (hflat.and hsmall)).exists
  refine ⟨R, hR, ENNReal.ofReal (‖z‖ ^ e) / 2, ?_⟩
  apply Section6.isComparableOn_ball_of_weight hR (by linarith) ?_ hweight
  exact hfR

/-- At any nonzero center, a singular Weyl weight transfers good-scale block
frequency after an explicit, center-independent adjustment of constants. -/
theorem veryGoodComparable_blockFrequency_of_singular_weight
    {μ ν : Measure ℂ} {z : ℂ} {e : ℝ} (hz : z ≠ 0)
    (hweight : μ.restrict {0}ᶜ =
      (ν.withDensity fun x => ENNReal.ofReal (‖x‖ ^ e)).restrict {0}ᶜ)
    {β : ℝ} {N₀ : ℕ} (hN₀ : 5 ≤ N₀) {a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ}
    (hv : ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
      (veryGoodComparableScaleCount ν β z N₀ a b C₁m C₁p C₂m C₂p C₃ m N : ℝ)) :
    ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
      (veryGoodComparableScaleCount μ β z N₀ (a / 4) b (C₁m / 4) (4 * C₁p)
        (C₂m / 4) (4 * C₂p) C₃ (m / 4) N : ℝ) := by
  obtain ⟨R, hR, c, hc⟩ := exists_comparableOn_ball_of_singular_weight hz hweight
  exact veryGoodComparable_blockFrequency_of_comparable hR hc hN₀ hv

universe u

/-- A regular-measure typical-point frequency bound transfers to the singular
measure of the same field, with explicit adjusted annulus thresholds. -/
theorem IsWholePlaneGFF.ae_ae_singular_blockFrequency_of_regular
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α β : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ ν : Ω → Measure ℂ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hν : IsLQGMeasureOfField P γ 0 hcirc ν)
    {N₀ : ℕ} (hN₀ : 5 ≤ N₀) {a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ}
    (hv : ∀ᵐ ω ∂P, ∀ᵐ z ∂ν ω, ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
      (veryGoodComparableScaleCount (ν ω) β z N₀ a b C₁m C₁p C₂m C₂p C₃ m N : ℝ)) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
      (veryGoodComparableScaleCount (μ ω) β z N₀ (a / 4) b (C₁m / 4) (4 * C₁p)
        (C₂m / 4) (4 * C₂p) C₃ (m / 4) N : ℝ) := by
  have hdom := hGFF.ae_singular_absolutelyContinuous_of_volumeGrowth
    hgrowth hγ hγ2 hα hμ hν
  have hnon := Section6.lqgMeasureNonatomic_of_volumeGrowth hgrowth P γ α hC hcirc
    hGFF hγ hγ2 hα μ hμ
  filter_upwards [hdom, hnon, hGFF.ae_singular_weight_of_existing_regular_measure hμ hν, hv]
    with ω hdomω hnonω hweightω hvω
  have hz : ∀ᵐ z ∂μ ω, z ≠ 0 := by
    simpa [ae_iff] using hnonω 0
  filter_upwards [hdomω.ae_le hvω, hz] with z hvz hz
  exact veryGoodComparable_blockFrequency_of_singular_weight hz hweightω hN₀ hvz

#print axioms annulusBallComparison_of_comparable
#print axioms eventually_veryGoodComparable_of_comparable
#print axioms veryGoodComparable_blockFrequency_of_comparable
#print axioms exists_comparableOn_ball_of_singular_weight
#print axioms veryGoodComparable_blockFrequency_of_singular_weight
#print axioms IsWholePlaneGFF.ae_ae_singular_blockFrequency_of_regular

end HarmonicBalls
