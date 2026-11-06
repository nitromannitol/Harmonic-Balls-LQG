import HarmonicBalls.Proofs.Sec6.MassTypicalDyadicPrevalence
import HarmonicBalls.Proofs.Sec6.RootedGoodAnnulusContinuity

/-! # Nearby-centre counts at weighted LQG roots

The countable-centre iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal

universe u

/-- For every weighted root measure, the fixed-threshold dyadic count bound
holds throughout a root-dependent neighbourhood after relaxing the thresholds.
The neighbourhood may also depend on the scale and dyadic window. -/
theorem exists_ae_all_weightedMass_eventually_nearby_dyadic_goodAnnuli_count
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {b : ℝ} (hb : 0 < b) (β : ℝ) (hβ : β ∈ Ioo (0 : ℝ) 1)
    (s : ℕ → ℝ) (hs : ∀ i, 0 < s i) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ᵐ ω ∂P, ∀ wgt : ℂ → ℝ≥0∞,
      ∀ᵐ z ∂((μ ω).withDensity wgt).restrict (ball 0 1), ∀ i, ∀ᶠ n : ℕ in atTop,
      ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℂ, dist w z < δ →
        (β / 16) * Real.logb 7 ((dyadicScale n) ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc (dyadicScale n) ((dyadicScale n) ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
          IsGoodAnnulus (μ ω) (s i * r) w (a / 2) (b + 2)}.ncard : ℝ) := by
  have hQ : 0 < lqgQ γ := by unfold lqgQ; positivity
  have hfull := lqgMeasureFullSupportStmt_of_volumeGrowth hgrowth γ 0 hγ hγ2 hQ
    Ω P hC hcirc μ h hμ
  have hcont := ae_lqg_ae_nearby_goodAnnuli_count_lower_bound hgrowth hγ hγ2 hQ h hμ
  obtain ⟨a, ha, ht⟩ := exists_ae_lqg_mass_eventually_dyadic_goodAnnuli_count_all_scales
    hgrowth hγ hγ2 h hμ hb β hβ s hs
  refine ⟨a, ha, ?_⟩
  filter_upwards [hfull, hcont, ht] with ω hfull hcont ht
  have hc' := (ae_mono (Measure.restrict_le_self (s := ball (0 : ℂ) 1) (μ := μ ω))) hcont
  intro wgt
  apply ((withDensity_absolutelyContinuous (μ ω) wgt).restrict (ball 0 1)).ae_le
  filter_upwards [hc', ht] with z hcz htz i
  filter_upwards [htz i] with n hn
  let S : Set ℝ := {r | r ∈ Icc (dyadicScale n) ((dyadicScale n) ^ (3 / 4 : ℝ)) ∧
    ∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k}
  have hS : S.Finite := by
    refine finite_of_geometric (q := (7 : ℝ)⁻¹) (A := 1) (lo := dyadicScale n)
      (by norm_num) (by norm_num) (dyadicScale_pos n) ?_
    intro r hr
    exact ⟨hr.1.1, by obtain ⟨k, hk⟩ := hr.2; exact ⟨k, by simpa using hk⟩⟩
  let T : Set ℝ := (fun r : ℝ => s i * r) '' S
  have hT : T.Finite := hS.image _
  obtain ⟨δ, hδ, hnear⟩ := hcz T hT (show 0 ≤ a / 2 by linarith [ha.1])
    (show a / 2 < a by linarith [ha.1]) (show 0 ≤ b + 1 by linarith)
    (show b + 1 < b + 2 by linarith) (by
      intro r hr _
      obtain ⟨t, ht, rfl⟩ := hr
      have htpos : 0 < t := (dyadicScale_pos n).trans_le ht.1.1
      exact ⟨mul_pos (hs i) htpos, annulus_three_five_pos_of_fullSupport (μ ω) hfull z
        (mul_pos (hs i) htpos)⟩)
  refine ⟨δ, hδ, ?_⟩
  intro w hw
  have hcompare := hnear w hw
  have hinj : Function.Injective (fun r : ℝ => s i * r) :=
    fun x y hxy => mul_left_cancel₀ (ne_of_gt (hs i)) hxy
  have hsource : {r ∈ T | IsGoodAnnulus (μ ω) r z a (b + 1)} =
      (fun r : ℝ => s i * r) '' {r ∈ S | IsGoodAnnulus (μ ω) (s i * r) z a (b + 1)} := by
    ext r
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hg⟩
      exact ⟨t, ⟨ht, hg⟩, rfl⟩
    · rintro ⟨t, ⟨ht, hg⟩, rfl⟩
      exact ⟨⟨t, ht, rfl⟩, hg⟩
  have htarget : {r ∈ T | IsGoodAnnulus (μ ω) r w (a / 2) (b + 2)} =
      (fun r : ℝ => s i * r) '' {r ∈ S | IsGoodAnnulus (μ ω) (s i * r) w (a / 2) (b + 2)} := by
    ext r
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hg⟩
      exact ⟨t, ⟨ht, hg⟩, rfl⟩
    · rintro ⟨t, ⟨ht, hg⟩, rfl⟩
      exact ⟨⟨t, ht, rfl⟩, hg⟩
  rw [hsource, htarget, Set.ncard_image_of_injective _ hinj,
    Set.ncard_image_of_injective _ hinj] at hcompare
  have hcompare' : ({r ∈ S | IsGoodAnnulus (μ ω) (s i * r) z a (b + 1)}.ncard : ℝ) ≤
      ({r ∈ S | IsGoodAnnulus (μ ω) (s i * r) w (a / 2) (b + 2)}.ncard : ℝ) := by
    exact_mod_cast hcompare
  exact hn.trans (by simpa only [S, mem_ofPred_eq, and_assoc] using hcompare')

end HarmonicBalls.Section6
