import HarmonicBalls.Proofs.Sec6.UniformFixedCentreCover
import HarmonicBalls.Proofs.Sec6.CriterionThreeLocalComparison
import HarmonicBalls.Proofs.Sec6.LQGWeylScaling

/-! # Nearby-centre counts under a singular Weyl weight

The whole-plane probability estimate uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal

universe u

/-- At fine scales the annuli tested at nearby centres lie in the size annulus. -/
theorem nearby_goodAnnulus_subset_size_annulus {s r : ℝ} {x z d : ℂ} {n : ℕ}
    (hs : 0 < s) (hn : 10 ≤ n)
    (hd : dist 0 d < 2 * (dyadicScale (2 * n) * s / 100))
    (hz : z ∈ annulus (x + d) (s / 2) s)
    (hr : r ≤ Real.sqrt (dyadicScale n) * s) :
    annulus z (3 * r) (5 * r) ⊆ annulus x (s / 4) (2 * s) := by
  have hsq : Real.sqrt (dyadicScale n) ≤ 1 / 25 := by
    rw [Real.sqrt_le_left (by norm_num)]
    unfold dyadicScale
    calc (2 : ℝ)⁻¹ ^ n ≤ (2 : ℝ)⁻¹ ^ 10 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
      _ ≤ (1 / 25) ^ 2 := by norm_num
  have hdyad : dyadicScale (2 * n) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hd' : dist (x + d) x < s / 50 := by
    have heq : dist (x + d) x = dist 0 d := by simp [dist_eq_norm]
    rw [heq]
    nlinarith
  have hr' : r ≤ s / 25 := by
    have h := mul_le_mul_of_nonneg_right hsq hs.le
    linarith
  intro w hw
  have hzout : dist z (x + d) < s := hz.1
  have hzin : s / 2 < dist z (x + d) := lt_of_not_ge hz.2
  have hwz : dist w z < 5 * r := hw.1
  have ht₁ := dist_triangle w z x
  have ht₂ := dist_triangle z (x + d) x
  have ht₃ := dist_triangle z w x
  have ht₄ := dist_triangle z x (x + d)
  have heq₁ : dist z w = dist w z := dist_comm _ _
  have heq₂ : dist x (x + d) = dist (x + d) x := dist_comm _ _
  change dist w x < 2 * s ∧ ¬ dist w x ≤ s / 4
  constructor <;> linarith

/-- Local comparison transfers all nearby-centre counts at once. -/
theorem nearbyCentrePhaseCounts_of_comparableWith
    {μ ν : Measure ℂ} {s : ℝ} {x : ℂ} {N : ℕ} {a b C t : ℝ}
    {F : ℕ → Finset ℂ} {c : ℝ≥0∞}
    (hs : 0 < s) (hN : 10 ≤ N) (ht : 0 < t)
    (h : IsComparableOnWith μ ν (annulus x (s / 4) (2 * s)) c (ENNReal.ofReal t))
    (hc : HasNearbyCentrePhaseCounts ν s x N a b C F) :
    HasNearbyCentrePhaseCounts μ s x N (a / t) b C F := by
  intro n hn q hq v hv d hd z hz hlat
  refine (hc n hn q hq v hv d hd z hz hlat).trans ?_
  norm_cast
  refine Set.ncard_le_ncard (fun r hr => ⟨hr.1, hr.2.1, ?_⟩) ?_
  · have hsub := nearby_goodAnnulus_subset_size_annulus hs (hN.trans hn) hd hz hr.1.2
    exact isGoodAnnulus_of_measure_comparison h.scale_ne_zero h.scale_ne_top ht
      (fun A hA => h.le_apply (hA.trans hsub)) (h.apply_le hsub) hr.2.2
  · refine finite_of_geometric (q := (7 : ℝ)⁻¹) (A := s) (lo := dyadicScale n * s)
      (by norm_num) (by norm_num) (mul_pos (dyadicScale_pos n) hs) fun r hr => ⟨hr.1.1, ?_⟩
    obtain ⟨k, -, hk⟩ := hr.2.1
    exact ⟨k, hk⟩

/-- The simultaneous nearby-centre counts transfer through the singular
Weyl weight on a separated size annulus. -/
theorem nearbyCentrePhaseCounts_of_singular_weight
    {μ ν : Measure ℂ} {s e : ℝ} {x : ℂ} {N : ℕ} {a b C : ℝ}
    {F : ℕ → Finset ℂ} (hs : 0 < s) (hN : 10 ≤ N)
    (hd : s / 100 ≤ infDist (0 : ℂ) (annulus x (s / 4) (2 * s)))
    (hμ : μ.restrict {0}ᶜ =
      (ν.withDensity fun x => ENNReal.ofReal (‖x‖ ^ e)).restrict {0}ᶜ)
    (hc : HasNearbyCentrePhaseCounts ν s x N a b C F) :
    HasNearbyCentrePhaseCounts μ s x N (a / (((401 : ℝ) ^ |e|) ^ 2)) b C F := by
  obtain ⟨c, hcomp⟩ := isComparableOnWith_size_annulus_of_weight hs hd hμ
  exact nearbyCentrePhaseCounts_of_comparableWith hs hN
    (sq_pos_of_pos (Real.rpow_pos_of_pos (by norm_num) _)) hcomp hc

/-- The nearby-centre source counts have a uniform probability bound for a
singular measure, on separated size annuli. The zero-strength existence input
is staged pending source review. -/
theorem exists_universal_singular_nearbyCentre_phaseCounts_probability
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2)
    {Ω₀ : Type u} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀}
    {hC₀ : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ω₀ → ℝ → ℂ → ℝ} {μ₀ : Ω₀ → Measure ℂ}
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hμ₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ μ₀)
    {b : ℝ} (hb : 0 < b) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α hcirc μ →
      LQGMeasureExistence P γ 0 hC hcirc →
    ∀ (s : ℝ), 0 < s → ∀ (x : ℂ),
      s / 100 ≤ infDist (0 : ℂ) (annulus x (s / 4) (2 * s)) →
    ∀ (F : ℕ → Finset ℂ), (∀ n, (F n).card ≤ 2 ^ (3 * n)) →
      (∀ n, (F n).Nonempty) →
      P {ω | ¬ HasNearbyCentrePhaseCounts (μ ω) s x N
        (a / (((401 : ℝ) ^ |-(γ * α)|) ^ 2)) b (1 / 32) F} ≤ δ := by
  obtain ⟨a, ha, N₀, hN₀, hcounts⟩ :=
    exists_universal_nearbyCentre_phaseCounts_probability hgrowth hγ hγ₂ h₀ hμ₀ hb hδ
  refine ⟨a, ha, max 10 N₀, le_max_left _ _, ?_⟩
  intro N hN Ω _ P hC hcirc μ hgff hμ hE0 s hs x hd F hFcard hF
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨ν, hν⟩ := hE0 hgff hγ hγ₂ hQ
  have hW := lqgMeasureWeylScaling Ω P γ 0 hC hcirc
  have hweight : ∀ᵐ ω ∂P, (μ ω).restrict {0}ᶜ =
      ((ν ω).withDensity fun x => ENNReal.ofReal (‖x‖ ^ (-(γ * α)))).restrict {0}ᶜ := by
    have h1 : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) (μ ω) := hμ
    filter_upwards [h1, hW hgff hγ hγ₂ hQ ν hν] with ω hω1 hω2
    exact restrict_compl_zero_eq_withDensity hω1 hω2
  apply (measure_mono_ae ?_).trans
    (hcounts N ((le_max_right 10 N₀).trans hN) Ω P hC hcirc ν hgff hν s hs x F hFcard hF)
  filter_upwards [hweight] with ω hω hbad
  intro hgood
  exact hbad (nearbyCentrePhaseCounts_of_singular_weight hs
    ((le_max_left 10 N₀).trans hN) hd hω hgood)

/-- For an arbitrary field-dependent phase, the singular criterion failure is
bounded by the displacement-stability failure plus an arbitrarily small error. -/
theorem exists_universal_singular_phaseCriterion_probability_le_stability_failure
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2)
    {Ω₀ : Type u} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀}
    {hC₀ : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ω₀ → ℝ → ℂ → ℝ} {μ₀ : Ω₀ → Measure ℂ}
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hμ₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ μ₀)
    {b : ℝ} (hb : 0 < b) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α hcirc μ →
      LQGMeasureExistence P γ 0 hC hcirc →
    ∀ (s : ℝ), 0 < s → ∀ (x : ℂ),
      s / 100 ≤ infDist (0 : ℂ) (annulus x (s / 4) (2 * s)) →
    ∀ (a' b' : ℝ) (phase : Ω → ℕ → ℂ),
      P {ω | ¬ PhaseVeryGoodCriterionThree (μ ω) s x N a' b' (1 / 32) (phase ω)} ≤
        δ + P {ω | ¬ HasNearbyGoodAnnulusTransfer (μ ω) s x N
          (a / (((401 : ℝ) ^ |-(γ * α)|) ^ 2)) b a' b'} := by
  obtain ⟨a, ha, N₀, hN₀, hbound⟩ :=
    exists_universal_singular_nearbyCentre_phaseCounts_probability hgrowth hγ hγ₂ h₀ hμ₀ hb hδ
  refine ⟨a, ha, N₀, hN₀, ?_⟩
  intro N hN Ω _ P hC hcirc μ hgff hμ hE0 s hs x hd a' b' phase
  obtain ⟨F, hcard, hcover⟩ := exists_dyadic_phase_displacement hs
  have hF : ∀ n, (F n).Nonempty := by
    intro n
    obtain ⟨q, hq, _⟩ := hcover n 0
    exact ⟨q, hq⟩
  calc
    _ ≤ P {ω | ¬ HasNearbyCentrePhaseCounts (μ ω) s x N
          (a / (((401 : ℝ) ^ |-(γ * α)|) ^ 2)) b (1 / 32) F} +
        P {ω | ¬ HasNearbyGoodAnnulusTransfer (μ ω) s x N
          (a / (((401 : ℝ) ^ |-(γ * α)|) ^ 2)) b a' b'} :=
      measure_bad_phaseCriterion_le_nearby_failures P μ hs x N _ b a' b' (1 / 32) F hcover phase
    _ ≤ _ := add_le_add (hbound N hN Ω P hC hcirc μ hgff hμ hE0 s hs x hd F hcard hF) le_rfl

end HarmonicBalls.Section6
