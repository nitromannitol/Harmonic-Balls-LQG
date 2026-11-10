import HarmonicBalls.Steps.Sec11.WeylLocalCurveLength
import HarmonicBalls.Steps.Sec11.MetricArcLength

/-!
# Weyl-shift estimates for the first event `E₁` (fp-S11m, owner z4)

Route: `notes/fp-gaps/CHATGPT-z4-11-12-local-certificate.md` section 6.2; paper `lem:E1`
(`paper/lqg_harmonic_ball-corrected.tex`, lines 3661-3700). Deterministic facts about `weylScaling D ξ f` for a
length metric `D` (`IsEuclideanLengthMetric D`) and a weight `f`:

* `weylScaling_ge_frontier` (first exit, paper: "the first-exit observation gives `L_new = b_Q L`"): if `f ≥ c` on
  `closure Q`, then for `u ∈ closure Q` and every `v ∈ frontier Q`,
  `e^{ξ c} · ⨅ w ∈ ∂Q, D u w ≤ weylScaling D ξ f u v`. Only the lower bound is used by `E₁`.
* `weylScaling_le_const` (paper: "the root bump multiplies all lengths in `Ω` by at most `b`"): if `f ≤ c` everywhere
  and `ξ ≥ 0`, then `weylScaling D ξ f u v ≤ e^{ξ c} · D u v`.

No probability and no measurability here. The internal-metric (`internalMetric`) versions needed for `a₀` and `A`
are separate steps (see the notes).
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace HarmonicBalls.S11m.WeylShiftE1

/-- First-exit lower bound for the Weyl scaling (paper `lem:E1`, `L_new = b_Q L`, lower half). -/
theorem weylScaling_ge_frontier {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {ξ c : ℝ} (hξ : 0 ≤ ξ)
    {f : ℂ → ℝ} {Q : Set ℂ} (hfc : ∀ z ∈ closure Q, c ≤ f z) {u v : ℂ} (hu : u ∈ closure Q)
    (hv : v ∈ frontier Q) :
    ENNReal.ofReal (Real.exp (ξ * c)) * ⨅ w ∈ frontier Q, ENNReal.ofReal (D u w) ≤
      weylScaling D ξ f u v := by
  unfold weylScaling
  refine le_iInf fun T => le_iInf fun p => le_iInf fun hp => le_iInf fun h0 => le_iInf fun hT => ?_
  obtain ⟨hT0, hcont, -⟩ := id hp
  -- first hitting time of the frontier
  set S : Set ℝ := Icc 0 T ∩ p ⁻¹' frontier Q with hS
  have hSc : IsClosed S := hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_frontier
  have hTS : T ∈ S := ⟨⟨hT0, le_rfl⟩, by show p T ∈ frontier Q; rw [hT]; exact hv⟩
  have hbdd : BddBelow S := ⟨0, fun t ht => ht.1.1⟩
  set t₀ := sInf S with ht₀
  have ht₀S : t₀ ∈ S := hSc.csInf_mem ⟨T, hTS⟩ hbdd
  have ht₀le : ∀ t ∈ S, t₀ ≤ t := fun t ht => csInf_le hbdd ht
  have ht₀I : t₀ ∈ Icc 0 T := ht₀S.1
  have hpt₀ : p t₀ ∈ frontier Q := ht₀S.2
  -- p maps [0, t₀] into closure Q
  have hcl : ∀ t ∈ Icc 0 t₀, p t ∈ closure Q := by
    intro t ht
    rcases eq_or_lt_of_le ht.2 with h | h
    · rw [h]; exact frontier_subset_closure hpt₀
    · have hu_int : u ∈ interior Q := by
        by_contra hnot
        have h0S : (0 : ℝ) ∈ S := ⟨⟨le_rfl, hT0⟩, by show p 0 ∈ frontier Q; rw [h0]; exact ⟨hu, hnot⟩⟩
        have := ht₀le 0 h0S
        linarith [ht.1]
      have hsub : p '' Icc 0 t ⊆ interior Q ∪ (closure Q)ᶜ := by
        rintro _ ⟨s, hs, rfl⟩
        by_cases hpf : p s ∈ frontier Q
        · exfalso
          have := ht₀le s ⟨⟨hs.1, by linarith [hs.2, ht.2, ht₀I.2]⟩, hpf⟩
          linarith [hs.2, ht.2]
        · by_cases hc : p s ∈ closure Q
          · left
            by_contra h'
            exact hpf ⟨hc, h'⟩
          · right; exact hc
      have hpc : IsPreconnected (p '' Icc 0 t) :=
        isPreconnected_Icc.image p (hcont.mono (Icc_subset_Icc le_rfl (ht.2.trans ht₀I.2)))
      have hdisj : Disjoint (interior Q) (closure Q)ᶜ :=
        Set.disjoint_left.2 fun x hx hx' => hx' (subset_closure (interior_subset hx))
      have hmem : (p '' Icc 0 t ∩ interior Q).Nonempty :=
        ⟨u, ⟨0, ⟨le_rfl, ht.1⟩, h0⟩, hu_int⟩
      have hall : p '' Icc 0 t ⊆ interior Q :=
        hpc.subset_left_of_subset_union isOpen_interior isClosed_closure.isOpen_compl hdisj hsub hmem
      exact subset_closure (interior_subset (hall ⟨t, ⟨ht.1, le_rfl⟩, rfl⟩))
  -- the integral over [0, T] dominates the integral over [0, t₀]
  have hint : ∫⁻ _ in Icc 0 t₀, ENNReal.ofReal (Real.exp (ξ * c)) ≤
      ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * f (p t))) := by
    calc ∫⁻ _ in Icc 0 t₀, ENNReal.ofReal (Real.exp (ξ * c))
        ≤ ∫⁻ t in Icc 0 t₀, ENNReal.ofReal (Real.exp (ξ * f (p t))) := by
          apply setLIntegral_mono' measurableSet_Icc
          intro t ht
          apply ENNReal.ofReal_le_ofReal
          apply Real.exp_le_exp.2
          exact mul_le_mul_of_nonneg_left (hfc _ (hcl t ht)) hξ
      _ ≤ ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * f (p t))) :=
          lintegral_mono_set (Icc_subset_Icc le_rfl ht₀I.2)
  have hD0 : D u (p t₀) ≤ t₀ := by
    have := hD.dist_le_of_lengthParametrized hp (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT0⟩) ht₀I
    rwa [h0, sub_zero, abs_of_nonneg ht₀I.1] at this
  have hvol : ∫⁻ _ in Icc 0 t₀, ENNReal.ofReal (Real.exp (ξ * c)) =
      ENNReal.ofReal (Real.exp (ξ * c)) * ENNReal.ofReal t₀ := by
    rw [setLIntegral_const, Real.volume_Icc, sub_zero]
  calc ENNReal.ofReal (Real.exp (ξ * c)) * ⨅ w ∈ frontier Q, ENNReal.ofReal (D u w)
      ≤ ENNReal.ofReal (Real.exp (ξ * c)) * ENNReal.ofReal t₀ :=
        by
          gcongr
          exact (iInf₂_le (p t₀) hpt₀).trans (ENNReal.ofReal_le_ofReal hD0)
    _ = ∫⁻ _ in Icc 0 t₀, ENNReal.ofReal (Real.exp (ξ * c)) := hvol.symm
    _ ≤ _ := hint

/-- Upper bound for the Weyl scaling by a constant weight (paper `lem:E1`, `A_new ≤ b A`). -/
theorem weylScaling_le_const {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {ξ c : ℝ} (hξ : 0 ≤ ξ)
    {f : ℂ → ℝ} (hfc : ∀ z, f z ≤ c) (u v : ℂ) :
    weylScaling D ξ f u v ≤ ENNReal.ofReal (Real.exp (ξ * c)) * ENNReal.ofReal (D u v) := by
  rw [← hD.weylScaling_zero ξ u v]
  have ha0 : ENNReal.ofReal (Real.exp (ξ * c)) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  unfold weylScaling
  simp only [ENNReal.mul_iInf_of_ne ha0 ENNReal.ofReal_ne_top]
  refine iInf_mono fun T => iInf_mono fun p => iInf_mono fun hp => iInf_mono fun h0 => iInf_mono fun hT => ?_
  simp only [Pi.zero_apply, mul_zero, Real.exp_zero, ENNReal.ofReal_one]
  calc ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * f (p t)))
      ≤ ∫⁻ _ in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * c)) := by
        apply lintegral_mono
        intro t
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.2
        exact mul_le_mul_of_nonneg_left (hfc _) hξ
    _ = ENNReal.ofReal (Real.exp (ξ * c)) * ∫⁻ _ in Icc 0 T, (1 : ℝ≥0∞) := by
        rw [setLIntegral_const, setLIntegral_const, one_mul]

end HarmonicBalls.S11m.WeylShiftE1

end
