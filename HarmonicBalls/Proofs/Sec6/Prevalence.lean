import HarmonicBalls.Steps.Sec6.Prevalence
import HarmonicBalls.Proofs.Sec6.Localization
import HarmonicBalls.Proofs.Sec2.PolyHighProb
import HarmonicBalls.Proofs.Sec2.SingularWeight

/-!
# Lemmas 6.3 and 6.6 in the printed `α₀`-uniform order

Assembly of docs/campaign/cex/AlphaUniformity.md §6.2-6.3 (operator E31). Fix `α₀ < Q` and let `μ₀` be the γ-LQG
measure of `h^ℂ` on the same probability space (`LQGMeasureExistence` at `α₀ = 0`). By the Weyl identity
(`SingularWeightStep`), a.s. `μ_h = |x|^{-γα₀} μ₀` on `ℂ \ {0}`. For a grid point `z`, `|z| ≥ 10√ε`, and a radius
`r ≤ ε^{3/4}`, the weight is flat (within a factor 2 of its value at the centre) on `B_{5r}(z)` once
`2|γα₀| ε^{1/4} ≤ log 2` (S-Flat, `grid_flat`, `rpow_norm_flat`), so `E_r(z; a, b)[μ₀] ⊆ E_r(z; a/4, b)[μ_h]`
(S-Transfer); likewise for `Ē_ρ(x₀)` on `B_{2ρ}(x₀)`. The radii of the `α₀ = 0` sub-range steps then count for
`μ_h`. The `α₀`-dependent threshold on `ε` is absorbed by `PolyHighProb` (`mono_of_eventually`). Constants:
Lemma 6.3 with `a := a₀/4`, `c := c₀`; Lemma 6.6 with `a := a₀/4`, `C₁⁻/4, 4C₁⁺, C₂⁻/4, 4C₂⁺`, the same `C₃`,
`N₁ := max N₁ 5` and `c := c₀`; all chosen before `α₀`, as printed.

* `manyGoodAnnuliStmt_of_subRange`, `manyVeryGoodAnnuliStmt_of_subRange`: from the sub-range steps,
  `LQGMeasureExistence` (α₀ = 0) and `SingularWeightStep`;
* `manyGoodAnnuliStmt_of_literature`, `manyVeryGoodAnnuliStmt_of_literature`: the same with `SingularWeightStep`
  from Weyl scaling (`singularWeightStep_of_weyl`, Fact 2.1 III).
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

open Section6

universe u

namespace Section6

/-- Flatness at the grid: for `|z| ≥ 10√ε`, `ε ≤ 1` and `R ≤ 5 ε^{3/4}`: `2R ≤ |z|` and `4R/|z| ≤ 2 ε^{1/4}`. -/
theorem grid_flat {ε R : ℝ} {z : ℂ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hz : 10 * Real.sqrt ε ≤ ‖z‖)
    (hR : R ≤ 5 * ε ^ (3 / 4 : ℝ)) : 2 * R ≤ ‖z‖ ∧ 4 * R / ‖z‖ ≤ 2 * ε ^ (1 / 4 : ℝ) := by
  have h1 : ε ^ (3 / 4 : ℝ) = ε ^ (1 / 4 : ℝ) * Real.sqrt ε := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hε0]; norm_num
  have h4 : 0 ≤ ε ^ (1 / 4 : ℝ) := Real.rpow_nonneg hε0.le _
  have h4' : ε ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one hε0.le hε1 (by norm_num)
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε0
  have hz0 : 0 < ‖z‖ := by linarith
  have h2 : ε ^ (3 / 4 : ℝ) ≤ Real.sqrt ε := by rw [h1]; nlinarith
  refine ⟨by linarith, ?_⟩
  rw [div_le_iff₀ hz0]
  nlinarith [mul_le_mul_of_nonneg_left hz h4]

theorem norm_ge_of_mem_prevalenceGrid {ε : ℝ} {z : ℂ} (hz : z ∈ prevalenceGrid ε) :
    10 * Real.sqrt ε ≤ ‖z‖ :=
  not_lt.1 fun h => hz.1.2 (mem_ball_zero_iff.2 h)

/-- `c₀ log_B ε^{-1/2} ≤ c₀ log_B ε^{-1}` for `ε ∈ (0, 1]`, `B > 1`. -/
theorem logb_neg_half_le {B c₀ ε : ℝ} (hB : 1 < B) (hc₀ : 0 < c₀) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    c₀ * Real.logb B (ε ^ (-(1 / 2 : ℝ))) ≤ c₀ * Real.logb B (ε ^ (-1 : ℝ)) := by
  rw [Real.logb_rpow_eq_mul_logb_of_pos hε0, Real.logb_rpow_eq_mul_logb_of_pos hε0]
  have := Real.logb_nonpos hB hε0.le hε1
  nlinarith

/-- The eventual smallness of `ε` used by the localization. -/
theorem eventually_small (e : ℝ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 ∧ |e| * (2 * ε ^ (1 / 4 : ℝ)) ≤ Real.log 2 := by
  have hc : ContinuousAt (fun ε : ℝ => ε ^ (1 / 4 : ℝ)) 0 :=
    Real.continuousAt_rpow_const _ _ (Or.inr (by norm_num))
  have ht : Tendsto (fun ε : ℝ => |e| * (2 * ε ^ (1 / 4 : ℝ))) (𝓝 0) (𝓝 0) := by
    have := (hc.tendsto.const_mul 2).const_mul |e|
    simpa [Real.zero_rpow (by norm_num : (1 / 4 : ℝ) ≠ 0)] using this
  exact nhdsWithin_le_nhds ((eventually_lt_nhds one_pos).and
    (ht.eventually (eventually_le_nhds (Real.log_pos one_lt_two))))

/-- The Weyl identity makes `μ_h` and `μ₀` comparable on `B_R(z)` for grid points and `R ≤ 5 ε^{3/4}`. -/
theorem isComparableOn_grid {μ μ₀ : Measure ℂ} {e ε R : ℝ} {z : ℂ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (he : |e| * (2 * ε ^ (1 / 4 : ℝ)) ≤ Real.log 2)
    (hμ : μ.restrict {0}ᶜ = (μ₀.withDensity fun x => ENNReal.ofReal (‖x‖ ^ e)).restrict {0}ᶜ)
    (hz : z ∈ prevalenceGrid ε) (hR : 0 < R) (hR' : R ≤ 5 * ε ^ (3 / 4 : ℝ)) :
    IsComparableOn μ μ₀ (ball z R) (ENNReal.ofReal (‖z‖ ^ e) / 2) := by
  obtain ⟨h1, h2⟩ := grid_flat hε0 hε1.le (norm_ge_of_mem_prevalenceGrid hz) hR'
  exact isComparableOn_ball_of_weight hR h1
    ((mul_le_mul_of_nonneg_left h2 (abs_nonneg e)).trans he) hμ

end Section6

/-- **Lemma 6.3** in the printed order (`a = a(b, γ)`, universal `c`), from step S-SubRange, the existence of `μ₀`
and the Weyl identity. -/
theorem manyGoodAnnuliStmt_of_subRange (hsub : GoodAnnuliSubRangeStep.{u})
    (hex : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
    (hsw : SingularWeightStep.{u}) : ManyGoodAnnuliStmt.{u} := by
  obtain ⟨c₀, hc₀, hsub⟩ := hsub
  refine ⟨c₀, hc₀, fun γ hγ hγ2 b hb => ?_⟩
  obtain ⟨a, ha, hsub⟩ := hsub γ hγ hγ2 b hb
  refine ⟨a / 4, ⟨by linarith [ha.1], by linarith [ha.2]⟩, fun α₀ hα₀ Ω _ P hC hcirc μ hGFF hμ => ?_⟩
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨μ₀, hμ₀⟩ := hex Ω P γ hC hcirc hGFF hγ hγ2 hQ
  have hW := hsw γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ μ₀ hGFF hμ hμ₀
  refine ((hsub Ω P hC hcirc μ₀ hGFF hμ₀).inter_ae hW).mono_of_eventually ?_
  filter_upwards [eventually_small (-(γ * α₀)), self_mem_nhdsWithin] with ε hε hε0
  rintro ω ⟨hω, hωW⟩ z hz
  refine ((logb_neg_half_le (by norm_num) hc₀ hε0 hε.1.le).trans (hω z hz)).trans ?_
  norm_cast
  refine Set.ncard_le_ncard (fun r hr => ⟨⟨hr.1.1, ?_⟩, hr.2.1, ?_⟩) ?_
  · calc r ≤ ε ^ (3 / 4 : ℝ) := hr.1.2
      _ ≤ Real.sqrt ε := by
          rw [Real.sqrt_eq_rpow]
          exact Real.rpow_le_rpow_of_exponent_ge hε0 hε.1.le (by norm_num)
  · have hr0 : 0 < r := hε0.trans_le hr.1.1
    exact isGoodAnnulus_of_comparable
      (isComparableOn_grid hε0 hε.1 hε.2 hωW hz (by positivity) (by linarith [hr.1.2])) sdiff_subset
      hr.2.2
  · refine finite_of_geometric (q := (7 : ℝ)⁻¹) (A := 1) (lo := ε) (by norm_num) (by norm_num) hε0
      fun r hr => ⟨hr.1.1, ?_⟩
    obtain ⟨n, hn⟩ := hr.2.1
    exact ⟨n, by rw [hn, one_mul]⟩

/-- **Lemma 6.6** in the printed order (`a = a(b, γ)`, universal `c, C₃`, `C₁^±, C₂^±` depending on `a, γ`,
`N₁ = N₁(b, γ)`), from step S-SubRange, the existence of `μ₀` and the Weyl identity. -/
theorem manyVeryGoodAnnuliStmt_of_subRange (hsub : VeryGoodAnnuliSubRangeStep.{u})
    (hex : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
    (hsw : SingularWeightStep.{u}) : ManyVeryGoodAnnuliStmt.{u} := by
  obtain ⟨c₀, C₃, hc₀, hC₃, hsub⟩ := hsub
  refine ⟨c₀, C₃, hc₀, hC₃, fun γ hγ hγ2 β hβ b hb => ?_⟩
  obtain ⟨a, ha, C₁m, C₁p, C₂m, C₂p, h1m, h1p, h2m, h2p, N₁, -, hsub⟩ := hsub γ hγ hγ2 β hβ b hb
  refine ⟨a / 4, ⟨by linarith [ha.1], by linarith [ha.2]⟩, C₁m / 4, 4 * C₁p, C₂m / 4, 4 * C₂p,
    by positivity, by positivity, by positivity, by positivity, max N₁ 5, le_max_of_le_right (by norm_num),
    fun N₀ hN₀ α₀ hα₀ Ω _ P hC hcirc μ hGFF hμ => ?_⟩
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨μ₀, hμ₀⟩ := hex Ω P γ hC hcirc hGFF hγ hγ2 hQ
  have hW := hsw γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ μ₀ hGFF hμ hμ₀
  have hN₀5 : 5 ≤ N₀ := (le_max_right _ _).trans hN₀
  refine ((hsub N₀ ((le_max_left _ _).trans hN₀) Ω P hC hcirc μ₀ hGFF hμ₀).inter_ae hW).mono_of_eventually ?_
  filter_upwards [eventually_small (-(γ * α₀)), self_mem_nhdsWithin] with ε hε hε0
  rintro ω ⟨hω, hωW⟩ x₀ hx₀
  refine ((logb_neg_half_le (by norm_num) hc₀ hε0 hε.1.le).trans (hω x₀ hx₀)).trans ?_
  norm_cast
  refine Set.ncard_le_ncard (fun ρ hρ => ⟨⟨hρ.1.1, ?_⟩, hρ.2.1, ?_⟩) ?_
  · calc ρ ≤ ε ^ (3 / 4 : ℝ) := hρ.1.2
      _ ≤ Real.sqrt ε := by
          rw [Real.sqrt_eq_rpow]
          exact Real.rpow_le_rpow_of_exponent_ge hε0 hε.1.le (by norm_num)
  · have hρ0 : 0 < ρ := hε0.trans_le hρ.1.1
    exact isVeryGoodAnnulus_of_comparable
      (isComparableOn_grid hε0 hε.1 hε.2 hωW hx₀ (by positivity) (by linarith [hρ.1.2])) hρ0 hN₀5
      hρ.2.2
  · refine finite_of_geometric (q := (8 : ℝ)⁻¹) (A := 1) (lo := ε) (by norm_num) (by norm_num) hε0
      fun ρ hρ => ⟨hρ.1.1, ?_⟩
    obtain ⟨n, hn⟩ := hρ.2.1
    exact ⟨n, by rw [hn, one_mul]⟩

/-- Lemma 6.3 from step S-SubRange and the staged literature inputs `LQGMeasureExistence` (α₀ = 0) and
`LQGMeasureWeylScaling` (Fact 2.1 III, α₀ = 0). -/
theorem manyGoodAnnuliStmt_of_literature (hsub : GoodAnnuliSubRangeStep.{u})
    (hex : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc) : ManyGoodAnnuliStmt.{u} :=
  manyGoodAnnuliStmt_of_subRange hsub hex (singularWeightStep_of_weyl hW)

/-- Lemma 6.6 from step S-SubRange and the staged literature inputs `LQGMeasureExistence` (α₀ = 0) and
`LQGMeasureWeylScaling` (Fact 2.1 III, α₀ = 0). -/
theorem manyVeryGoodAnnuliStmt_of_literature (hsub : VeryGoodAnnuliSubRangeStep.{u})
    (hex : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc) : ManyVeryGoodAnnuliStmt.{u} :=
  manyVeryGoodAnnuliStmt_of_subRange hsub hex (singularWeightStep_of_weyl hW)

end HarmonicBalls
