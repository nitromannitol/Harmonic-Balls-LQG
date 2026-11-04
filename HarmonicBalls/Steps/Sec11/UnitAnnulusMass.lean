import HarmonicBalls.Steps.Sec11.AnnulusDilation

/-!
# The unit-disk annulus mass estimate for the comparison chain

Lemma 6.8 applied to the entire cluster inside the outer annulus yields the
mass-to-odometer estimate used in Lemma 11.6.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Section6

universe u

/-- The special case of Lemma 6.8 used in the Lemma 11.6 comparison chain. -/
theorem unit_annulus_mass_bound_of_lemma68 (h68 : AnnulusMassBoundByOdometerStmt.{u}) :
    ∃ C : ℝ, 0 < C ∧
      ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
      ∀ᵐ ω ∂P, ∀ p ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t → ∀ r : ℝ, 0 < r → ∀ z : ℂ,
        annulus z ((1 / 2) * r) (4 * r) ⊆ ball 0 1 \ {p} →
        μ ω (annulus z r (2 * r) ∩ cluster (μ ω) 1 p t) ≤
          ENNReal.ofReal C * ⨆ x ∈ annulus z ((1 / 2) * r) (4 * r), odometerExt (μ ω) p t x := by
  obtain ⟨C, hCpos, hC⟩ := h68 (1 / 2) 1 2 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C, hCpos, ?_⟩
  intro γ α₀ hγ hγ2 hα Ω _ P hfield hcirc μ hGFF hμ
  filter_upwards [hC γ α₀ hγ hγ2 hα Ω P hfield hcirc μ hGFF hμ] with ω hω
  intro p hp t ht r hr z hA
  have hinner : annulus z r (2 * r) ⊆ annulus z ((1 / 2) * r) (4 * r) := by
    intro x hx
    simp only [annulus, Set.mem_sdiff, mem_ball, mem_closedBall, not_le] at hx ⊢
    constructor <;> linarith [hx.1, hx.2]
  have hset : annulus z r (2 * r) ∩ (annulus z ((1 / 2) * r) (4 * r) ∩
      cluster (μ ω) 1 p t) = annulus z r (2 * r) ∩ cluster (μ ω) 1 p t := by
    ext x
    constructor
    · exact fun hx => ⟨hx.1, hx.2.2⟩
    · exact fun hx => ⟨hx.1, hinner hx.1, hx.2⟩
  have hpnot : p ∉ annulus z ((1 / 2) * r) (4 * r) := by
    intro hpA
    exact (hA hpA).2 rfl
  have hb := hω p hp t ht r hr z (hA.trans sdiff_subset) hpnot
    (annulus z ((1 / 2) * r) (4 * r) ∩ cluster (μ ω) 1 p t) subset_rfl
    (fun x _ => connectedComponentIn_subset _ x)
  simp only [one_mul, hset] at hb
  have hs : (⨆ x ∈ annulus z ((1 / 2) * r) (4 * r) ∩ cluster (μ ω) 1 p t,
      odometerExt (μ ω) p t x) ≤
      ⨆ x ∈ annulus z ((1 / 2) * r) (4 * r), odometerExt (μ ω) p t x := by
    refine iSup_le fun x => iSup_le fun hx => ?_
    exact le_iSup_of_le x (le_iSup_of_le hx.1 le_rfl)
  exact hb.trans (mul_le_mul_right hs _)

end HarmonicBalls
