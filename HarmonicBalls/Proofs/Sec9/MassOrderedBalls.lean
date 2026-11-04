import HarmonicBalls.Proofs.Sec9.GlobalBallUniqueness
import HarmonicBalls.Proofs.Sec3.Basic

/-! # Mass ordering of subharmonic balls

The monotonicity of clusters and the weak uniqueness sandwich order the
closures of subharmonic balls with a common centre by their mass.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

universe u

/-- Weak uniqueness and volume growth order bounded subharmonic balls by mass
at the level of closures and regularizations. If the larger ball is regular
open, the smaller ball is contained in it. -/
theorem ae_bounded_subharmonicBall_order_of_weak_uniqueness
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hweak : SubharmonicBallUniquenessWeakStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (A B : Set ℂ) (z : ℂ), Bornology.IsBounded A → Bornology.IsBounded B →
      IsSubharmonicBall (μ ω) A z → IsSubharmonicBall (μ ω) B z → μ ω A ≤ μ ω B →
      A ⊆ interior (closure B) ∧ closure A ⊆ closure B ∧
        interior (closure A) ⊆ interior (closure B) ∧ (IsRegularOpen B → A ⊆ B) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_subharmonicBall_sandwich_of_weak_uniqueness hI2 hweak
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ]
      with ω hcompare hmono
  intro A B z hAb hBb hA hB hmass
  obtain ⟨r, hr⟩ := hAb.closure.subset_ball (0 : ℂ)
  obtain ⟨s, hs⟩ := hBb.closure.subset_ball (0 : ℂ)
  let R := max r s + 1
  have hrR : r ≤ R := by dsimp [R]; linarith [le_max_left r s]
  have hsR : s ≤ R := by dsimp [R]; linarith [le_max_right r s]
  have hAcl : closure A ⊆ ball (0 : ℂ) R := hr.trans (ball_subset_ball hrR)
  have hBcl : closure B ⊆ ball (0 : ℂ) R := hs.trans (ball_subset_ball hsR)
  have hz : z ∈ ball (0 : ℂ) R := hAcl (subset_closure hA.2.1)
  have hR : 0 < R := pos_of_mem_ball hz
  let t : ℝ := (μ ω A).toReal
  let s : ℝ := (μ ω B).toReal
  have hfinA : μ ω A ≠ ⊤ := ne_of_lt hA.2.2.2.1
  have hfinB : μ ω B ≠ ⊤ := ne_of_lt hB.2.2.2.1
  have ht : 0 < t := ENNReal.toReal_pos hA.2.2.1.ne' hfinA
  have hs : 0 < s := ENNReal.toReal_pos hB.2.2.1.ne' hfinB
  have hts : t ≤ s := ENNReal.toReal_mono hfinB hmass
  have hmassA : μ ω A = ENNReal.ofReal t := (ENNReal.ofReal_toReal hfinA).symm
  have hmassB : μ ω B = ENNReal.ofReal s := (ENNReal.ofReal_toReal hfinB).symm
  obtain ⟨_, hAC, _⟩ := hcompare A z t R ht hR hz hAcl hA hmassA
  obtain ⟨hCB, _, _⟩ := hcompare B z s R hs hR hz hBcl hB hmassB
  have hcluster := hmono t s R ht hts hR z hz
  have hAB : A ⊆ interior (closure B) :=
    hAC.trans (interior_mono (closure_mono (hcluster.trans hCB)))
  have hcl : closure A ⊆ closure B :=
    closure_minimal (hAB.trans interior_subset) isClosed_closure
  refine ⟨hAB, hcl, interior_mono hcl, ?_⟩
  intro hBreg
  rw [← hBreg]
  exact hAB

/-- In the unit disc, I2 and the typical-scale estimate order subharmonic
balls almost everywhere by mass, without scaling hypotheses. -/
theorem ae_subharmonicBall_order_inside_unit_disc
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (A B : Set ℂ) (z : ℂ),
      closure A ⊆ ball 0 1 → closure B ⊆ ball 0 1 →
      IsSubharmonicBall (μ ω) A z → IsSubharmonicBall (μ ω) B z → μ ω A ≤ μ ω B →
      A ⊆ interior (closure B) ∧ closure A ⊆ closure B ∧
        μ ω (A \ B) = 0 ∧ (IsRegularOpen B → A ⊆ B) ∧
        (μ ω A < μ ω B → IsRegularOpen B → A ⊂ B) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_subharmonicBall_sandwich_inside_unit_disc_of_volumeGrowth hI2 h82
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    ae_subharmonicBall_restrict_eq_inside_unit_disc hI2 h82
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hcompare hmono hnull
  intro A B z hAcl hBcl hA hB hmass
  have hz : z ∈ ball (0 : ℂ) 1 := hAcl (subset_closure hA.2.1)
  let t : ℝ := (μ ω A).toReal
  let s : ℝ := (μ ω B).toReal
  have hfinA : μ ω A ≠ ⊤ := ne_of_lt hA.2.2.2.1
  have hfinB : μ ω B ≠ ⊤ := ne_of_lt hB.2.2.2.1
  have ht : 0 < t := ENNReal.toReal_pos hA.2.2.1.ne' hfinA
  have hs : 0 < s := ENNReal.toReal_pos hB.2.2.1.ne' hfinB
  have hts : t ≤ s := ENNReal.toReal_mono hfinB hmass
  have hmassA : μ ω A = ENNReal.ofReal t := (ENNReal.ofReal_toReal hfinA).symm
  have hmassB : μ ω B = ENNReal.ofReal s := (ENNReal.ofReal_toReal hfinB).symm
  obtain ⟨_, hAC, _⟩ := hcompare A z t 1 ht zero_lt_one hz hAcl hAcl hA hmassA
  obtain ⟨hCB, _, _⟩ := hcompare B z s 1 hs zero_lt_one hz hBcl hBcl hB hmassB
  have hcluster := hmono t s 1 ht hts zero_lt_one z hz
  have hAB : A ⊆ interior (closure B) :=
    hAC.trans (interior_mono (closure_mono (hcluster.trans hCB)))
  have hcl : closure A ⊆ closure B :=
    closure_minimal (hAB.trans interior_subset) isClosed_closure
  have hfront : μ ω (frontier B) = 0 := (hnull B B z hBcl hBcl hB hB rfl).1
  have hdiff : A \ B ⊆ frontier B := by
    rw [hB.1.frontier_eq]
    intro x hx
    exact ⟨interior_subset (hAB hx.1), hx.2⟩
  have hregular : IsRegularOpen B → A ⊆ B := by
    intro hreg
    rw [← hreg]
    exact hAB
  refine ⟨hAB, hcl, measure_mono_null hdiff hfront, hregular, ?_⟩
  intro hlt hreg
  apply ssubset_iff_subset_ne.mpr
  refine ⟨hregular hreg, ?_⟩
  intro heq
  exact (ne_of_lt hlt) (congrArg (μ ω) heq)

end HarmonicBalls
