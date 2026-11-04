import HarmonicBalls.Proofs.Sec6.PotentialRatioMeasurable

/-!
# Positivity of potential ratios

The fine-support argument uses the ratio of a Green potential's minimum on a compact
circle to its supremum on an annulus. This file isolates the deterministic compactness
and boundedness argument; it does not establish these properties of the Green potential.
-/

namespace HarmonicBalls.Section6

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

end HarmonicBalls.Section6
