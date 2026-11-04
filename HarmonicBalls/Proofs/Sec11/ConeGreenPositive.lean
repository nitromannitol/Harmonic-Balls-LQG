import HarmonicBalls.Proofs.Sec11.ConeLocalFinite
import HarmonicBalls.Proofs.Sec4.GreenAwayFromPole
import HarmonicBalls.Proofs.Potential.GreenPositivity

/-! # Positivity of annular Green potentials -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- A full-support measure has positive annular Green-potential supremum
on every nonempty open annulus. -/
theorem annulusGreenPotentialSup_pos_of_fullSupport
    (μ : Measure ℂ) (z : ℂ) (a b : ℝ)
    (hfull : ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ U)
    (hne : (annulus z a b).Nonempty) :
    0 < annulusGreenPotentialSup μ z a b := by
  obtain ⟨x, hx⟩ := hne
  have hopen : IsOpen (annulus z a b) := isOpen_ball.sdiff isClosed_closedBall
  obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp hopen x hx
  let ε := δ / 4
  have hε : 0 < ε := by dsimp [ε]; positivity
  let f : ℂ → ℝ≥0∞ := fun y => if y = x then ∞ else
    ENNReal.ofReal (greenFunction (ball z b) x y)
  have hf : Measurable f := by
    dsimp [f]
    exact Measurable.ite (measurableSet_singleton x)
      measurable_const ((measurable_greenFunction isOpen_ball x).ennreal_ofReal)
  have hball : ball x ε ⊆ Function.support f ∩ annulus z a b := by
    intro y hy
    have hyδ : y ∈ ball x δ := ball_subset_ball (by dsimp [ε]; linarith) hy
    refine ⟨?_, hδsub hyδ⟩
    change f y ≠ 0
    by_cases hyx : y = x
    · simp [f, hyx]
    · have hsub : closedBall y ε ⊆ ball z b := by
        apply Set.Subset.trans _ (fun w hw => (hδsub hw).1)
        apply closedBall_subset_ball'
        have hdist : dist y x < ε := hy
        dsimp [ε] at *
        linarith
      have hdist : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hyx))
      have hsmall : ‖x - y‖ < ε := by simpa [dist_eq_norm, norm_sub_rev] using hy
      have hp := greenFunction_pos (isBounded_ball (x := z) (r := b)) hε hsub hdist hsmall
      simpa [f, hyx] using (ENNReal.ofReal_pos.mpr hp).ne'
  have hμ : 0 < μ (Function.support f ∩ annulus z a b) :=
    lt_of_lt_of_le (hfull (ball x ε) isOpen_ball ⟨x, mem_ball_self hε⟩) (measure_mono hball)
  have hint : 0 < ∫⁻ y in annulus z a b, f y ∂μ := (setLIntegral_pos_iff hf).2 hμ
  exact lt_of_lt_of_le hint (le_iSup_of_le x (le_iSup_of_le hx le_rfl))

/-- The annulus used in the cone-mass event is nonempty at positive scales. -/
theorem coneMass_annulus_nonempty (z : ℂ) {r : ℝ} (hr : 0 < r) :
    (annulus z (3 * r) (6 * r)).Nonempty := by
  refine ⟨z + ((4 * r : ℝ) : ℂ), ?_⟩
  have hdist : dist (z + ((4 * r : ℝ) : ℂ)) z = 4 * r := by
    simp [dist_eq_norm, hr.le]
  change dist (z + ((4 * r : ℝ) : ℂ)) z < 6 * r ∧
    ¬ dist (z + ((4 * r : ℝ) : ℂ)) z ≤ 3 * r
  rw [hdist]
  constructor <;> linarith

/-- Full support supplies the positivity required in the deterministic cone
contradiction; the cone-mass event supplies finiteness. -/
theorem not_satisfiesConeCondition_of_frequently_coneMass_fullSupport
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] (Λ : Set ℂ) (z : ℂ)
    (C : ℝ) (hC : 0 < C) (hz : z ≠ 0)
    (hfull : ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ U)
    (hscales : ∀ Q : Set ℂ, IsCone Q → ∃ᶠ n : ℕ in atTop,
      coneMassEvent μ Q (2 * C) ((2 : ℝ)⁻¹ ^ n) z)
    (hbound : ∀ r : ℝ, 0 < r → (0 : ℂ) ∉ closedBall z (10 * r) →
      (annulus z (4 * r) (5 * r) ∩ Λᶜ).Nonempty →
      μ (annulus z r (2 * r) ∩ Λ) ≤
        ENNReal.ofReal C * annulusGreenPotentialSup μ z (3 * r) (6 * r)) :
    ¬ SatisfiesConeCondition Λ z := by
  apply not_satisfiesConeCondition_of_frequently_coneMass_locallyFinite
    μ Λ z C hC hz hscales ?_ hbound
  intro r hr
  exact annulusGreenPotentialSup_pos_of_fullSupport μ z (3 * r) (6 * r) hfull
    (coneMass_annulus_nonempty z hr)

end HarmonicBalls
