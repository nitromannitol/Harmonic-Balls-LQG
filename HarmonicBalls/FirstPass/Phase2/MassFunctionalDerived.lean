import HarmonicBalls.FirstPass.Frozen.S11d
import HarmonicBalls.FirstPass.S11at.Producers

/-!
# Derivation of `LQGMassFunctionalMeasurableFrozen` (phase 2, worker z6)

Written argument: `notes/fp-gaps/CHATGPT-hb-distribution-frozen.md`, section 2. The decoder is built from a
countable dense family of circle averages, read off the raw distribution through the explicit annular approximants
`circleApprox` (`FirstPass/S11at/Producers.lean`). The envelope below replaces the Borel reconstruction of the
continuous circle-average process; the vague limit is replaced by lower limits of integrals of compactly supported
continuous functions.

This part: the deterministic envelope lemma. If the pairings of `T` with the approximants at the dense points `q m`
converge to `H (q m)`, where `H` is continuous at `p`, then the envelope of `T` at `p` equals `H p`.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open FirstPassS11atProducers

namespace HarmonicBalls.MassFunctionalDerived

/-- The code of a raw distribution `T` at the dense point `q m`: the limit superior of the pairings of `T` with the
annular approximants `circleApprox` of the circle average at `q m`. -/
noncomputable def codeAt {q : ℕ → ℝ × ℂ} (hq : ∀ m, 0 < (q m).1) (m : ℕ) (T : (ℂ → ℝ) → ℝ) : EReal :=
  limsup (fun j => ((T (circleApprox (hq m) (q m).2 j) : ℝ) : EReal)) atTop

/-- The envelope of the code of `T` at `p`: the infimum over the radii `1/(k+1)` of the supremum of the codes at the
dense points within that radius of `p`. -/
noncomputable def envelope {q : ℕ → ℝ × ℂ} (hq : ∀ m, 0 < (q m).1) (T : (ℂ → ℝ) → ℝ) (p : ℝ × ℂ) : EReal :=
  ⨅ k : ℕ, ⨆ m : ℕ, if dist (q m) p < 1 / ((k : ℝ) + 1) then codeAt hq m T else ⊥

/-- The supremum over the dense points within radius `1/(k+1)` of `p` of the values `H (q m)`. -/
noncomputable def ballSup (q : ℕ → ℝ × ℂ) (H : ℝ × ℂ → ℝ) (p : ℝ × ℂ) (k : ℕ) : EReal :=
  ⨆ m : ℕ, if dist (q m) p < 1 / ((k : ℝ) + 1) then ((H (q m) : ℝ) : EReal) else ⊥

theorem ballSup_anti (q : ℕ → ℝ × ℂ) (H : ℝ × ℂ → ℝ) (p : ℝ × ℂ) {k K : ℕ} (hkK : k ≤ K) :
    ballSup q H p K ≤ ballSup q H p k := by
  refine iSup_mono fun m => ?_
  by_cases hK : dist (q m) p < 1 / ((K : ℝ) + 1)
  · have hk : dist (q m) p < 1 / ((k : ℝ) + 1) := by
      refine lt_of_lt_of_le hK (one_div_le_one_div_of_le (by positivity) ?_)
      have : (k : ℝ) ≤ K := by exact_mod_cast hkK
      linarith
    simp only [hK, hk, ↓reduceIte, le_refl]
  · simp only [hK, ↓reduceIte, bot_le]

/-- The envelope of `T` at `p` is the infimum of the ball suprema of the limit values `H`. -/
theorem envelope_eq_iInf {q : ℕ → ℝ × ℂ} (hq : ∀ m, 0 < (q m).1) {H : ℝ × ℂ → ℝ} {T : (ℂ → ℝ) → ℝ}
    (hconv : ∀ m, Tendsto (fun j => T (circleApprox (hq m) (q m).2 j)) atTop (𝓝 (H (q m)))) (p : ℝ × ℂ) :
    envelope hq T p = ⨅ k : ℕ, ballSup q H p k := by
  have hcode : ∀ m, codeAt hq m T = ((H (q m) : ℝ) : EReal) := fun m =>
    Tendsto.limsup_eq (EReal.tendsto_coe.2 (hconv m))
  unfold envelope ballSup
  simp only [hcode]

/-- Envelope lemma. Let `H` be continuous at `p`, and let the pairings of `T` with the approximants at each dense
point `q m` converge to `H (q m)`. Then the envelope of `T` at `p` is `H p`. -/
theorem envelope_eq_of_tendsto {q : ℕ → ℝ × ℂ} (hq : ∀ m, 0 < (q m).1)
    (hdense : ∀ p : ℝ × ℂ, 0 < p.1 → ∀ δ > 0, ∃ m, dist (q m) p < δ)
    {H : ℝ × ℂ → ℝ} {p : ℝ × ℂ} (hp : 0 < p.1) (hcont : ContinuousAt H p) {T : (ℂ → ℝ) → ℝ}
    (hconv : ∀ m, Tendsto (fun j => T (circleApprox (hq m) (q m).2 j)) atTop (𝓝 (H (q m)))) :
    envelope hq T p = ((H p : ℝ) : EReal) := by
  rw [envelope_eq_iInf hq hconv p]
  refine le_antisymm ?_ ?_
  · -- upper bound: every ball supremum is at most `H p + ε` for large radius index
    have hup : ∀ ε > 0, (⨅ k : ℕ, ballSup q H p k) ≤ ((H p + ε : ℝ) : EReal) := by
      intro ε hε
      obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.1 hcont ε hε
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
      refine (iInf_le _ k).trans (iSup_le fun m => ?_)
      by_cases hm : dist (q m) p < 1 / ((k : ℝ) + 1)
      · simp only [hm, ↓reduceIte]
        have h1 : dist (q m) p < δ := lt_trans hm hk
        have h2 := hball h1
        rw [Real.dist_eq] at h2
        exact EReal.coe_le_coe_iff.2 (by linarith [le_abs_self (H (q m) - H p)])
      · simp only [hm, ↓reduceIte, bot_le]
    have ht : Tendsto (fun c : ℝ => H p + c) (𝓝[>] 0) (𝓝 (H p)) := by
      have := ((continuous_const.add continuous_id : Continuous fun c : ℝ => H p + c).tendsto' (0 : ℝ) (H p) (by simp))
      exact this.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto (EReal.tendsto_coe.2 ht) ?_
    exact eventually_nhdsWithin_of_forall fun ε hε => hup ε hε
  · -- lower bound: every ball supremum is at least `H p - ε` for all large indices
    have hlow : ∀ ε > 0, ((H p - ε : ℝ) : EReal) ≤ (⨅ k : ℕ, ballSup q H p k) := by
      intro ε hε
      obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.1 hcont ε hε
      obtain ⟨k0, hk0⟩ := exists_nat_one_div_lt hδ
      refine le_iInf fun k => ?_
      set K := max k k0 with hKdef
      have hKk : k ≤ K := le_max_left k k0
      have hKk0 : k0 ≤ K := le_max_right k k0
      have hpos : 0 < min δ (1 / ((K : ℝ) + 1)) := lt_min hδ (by positivity)
      obtain ⟨m, hm⟩ := hdense p hp _ hpos
      have hm1 : dist (q m) p < 1 / ((K : ℝ) + 1) := lt_of_lt_of_le hm (min_le_right _ _)
      have hm2 : dist (q m) p < δ := lt_of_lt_of_le hm (min_le_left _ _)
      have hval : ((H p - ε : ℝ) : EReal) ≤ ((H (q m) : ℝ) : EReal) := by
        apply EReal.coe_le_coe_iff.2
        have h2 := hball hm2
        rw [Real.dist_eq] at h2
        linarith [neg_abs_le (H (q m) - H p)]
      have hbK : ((H p - ε : ℝ) : EReal) ≤ ballSup q H p K := by
        refine hval.trans (le_iSup_of_le m ?_)
        simp only [hm1, ↓reduceIte, le_refl]
      exact le_trans hbK (ballSup_anti q H p hKk)
    have ht : Tendsto (fun c : ℝ => H p - c) (𝓝[>] 0) (𝓝 (H p)) := by
      have := ((continuous_const.sub continuous_id : Continuous fun c : ℝ => H p - c).tendsto' (0 : ℝ) (H p) (by simp))
      exact this.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto (EReal.tendsto_coe.2 ht) ?_
    exact eventually_nhdsWithin_of_forall fun ε hε => hlow ε hε

end HarmonicBalls.MassFunctionalDerived
