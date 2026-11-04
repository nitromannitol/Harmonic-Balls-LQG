import HarmonicBalls.Proofs.Sec6.PotentialRatioMeasurable
import HarmonicBalls.Proofs.Potential.GreenPositivity

/-!
# Positivity of potential ratios

The fine-support argument uses the ratio of a Green potential's minimum on a compact
circle to its supremum on an annulus. This file isolates the deterministic compactness
and boundedness argument; it does not establish these properties of the Green potential.
-/

namespace HarmonicBalls.Section6

open MeasureTheory
open scoped ENNReal

/-- A continuous, strictly positive function on a nonempty compact space has positive
infimum. If another function has a positive value and is bounded above, the ratio of
this infimum to its supremum is a positive real number. -/
theorem potential_extrema_ratio_pos
    {S T : Type*} [TopologicalSpace S] [CompactSpace S] [Nonempty S]
    (qS : S → ℝ) (qT : T → ℝ) (hSc : Continuous qS)
    (hSp : ∀ s, 0 < qS s) (M : ℝ) (hTb : ∀ t, qT t ≤ M)
    (t₀ : T) (hTp : 0 < qT t₀) :
    0 < ((⨅ s, ENNReal.ofReal (qS s)) / (⨆ t, ENNReal.ofReal (qT t))).toReal := by
  obtain ⟨c, hc, hbound⟩ := isCompact_univ.exists_forall_le' hSc.continuousOn
    (fun s _ => hSp s)
  have hApos : 0 < ⨅ s, ENNReal.ofReal (qS s) :=
    (ENNReal.ofReal_pos.2 hc).trans_le
      (le_iInf fun s => ENNReal.ofReal_le_ofReal (hbound s (Set.mem_univ s)))
  have hAtop : (⨅ s, ENNReal.ofReal (qS s)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (iInf_le _ (Classical.choice ‹Nonempty S›))
  have hBpos : 0 < ⨆ t, ENNReal.ofReal (qT t) :=
    (ENNReal.ofReal_pos.2 hTp).trans_le (le_iSup (fun t => ENNReal.ofReal (qT t)) t₀)
  have hBtop : (⨆ t, ENNReal.ofReal (qT t)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (iSup_le fun t => ENNReal.ofReal_le_ofReal (hTb t))
  exact ENNReal.toReal_pos (ENNReal.div_pos hApos.ne' hBtop).ne'
    (ENNReal.div_ne_top hAtop hBpos.ne')

/-- An integrable Green kernel that is positive off its pole has positive potential
when the domain has positive mass and the pole carries no atom. -/
theorem greenPotential_pos_of_pos_off_diagonal
    {O : Set ℂ} (hO : Bornology.IsBounded O) (μ : Measure ℂ) (x : ℂ)
    (hμx : μ {x} = 0) (hμO : 0 < μ O)
    (hint : Integrable (greenFunction O x) μ)
    (hpos : ∀ y ∈ O, y ≠ x → 0 < greenFunction O x y) :
    0 < greenPotential O μ x := by
  apply (integral_pos_iff_support_of_nonneg (greenFunction_nonneg hO x) hint).2
  have hsub : O \ {x} ⊆ Function.support (greenFunction O x) := by
    intro y hy
    exact ne_of_gt (hpos y hy.1 (by simpa using hy.2))
  have hmass : 0 < μ (O \ {x}) := by
    rwa [measure_sdiff_null hμx]
  exact hmass.trans_le (measure_mono hsub)

/-- A Green potential is positive at every point of a bounded open domain if the
measure has positive mass on open balls, has no atom at that point, and the Green
kernel is integrable. Only positivity near the pole is needed. -/
theorem greenPotential_pos_of_ball_mass
    {O : Set ℂ} (hO : Bornology.IsBounded O) (hopen : IsOpen O)
    (μ : Measure ℂ) (x : ℂ) (hx : x ∈ O) (hμx : μ {x} = 0)
    (hμball : ∀ r > 0, 0 < μ (Metric.ball x r))
    (hint : Integrable (greenFunction O x) μ) :
    0 < greenPotential O μ x := by
  obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.mp hopen x hx
  have hr : 0 < ε / 3 := by positivity
  have hsub : Metric.ball x (ε / 3) \ {x} ⊆ Function.support (greenFunction O x) := by
    intro y hy
    have hyx : y ≠ x := by simpa using hy.2
    have hyd : dist y x < ε / 3 := hy.1
    have hclosed : Metric.closedBall y (ε / 3) ⊆ O := by
      apply Set.Subset.trans _ hεO
      apply Metric.closedBall_subset_ball'
      linarith
    have hnorm : ‖x - y‖ < ε / 3 := by
      rw [← dist_eq_norm, dist_comm]
      exact hyd
    exact (greenFunction_pos hO hr hclosed
      (norm_pos_iff.mpr (sub_ne_zero.mpr hyx.symm)) hnorm).ne'
  apply (integral_pos_iff_support_of_nonneg (greenFunction_nonneg hO x) hint).2
  have hmass : 0 < μ (Metric.ball x (ε / 3) \ {x}) := by
    rw [measure_sdiff_null hμx]
    exact hμball _ hr
  exact hmass.trans_le (measure_mono hsub)

end HarmonicBalls.Section6
