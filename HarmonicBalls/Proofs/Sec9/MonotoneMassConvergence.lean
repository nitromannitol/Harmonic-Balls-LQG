import HarmonicBalls.Proofs.Sec9.MassContinuity

/-! # Almost-everywhere convergence along monotone mass sequences

For a sequence ordered modulo null sets, convergence in symmetric-difference
measure implies almost-everywhere eventual agreement with the limit set.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open scoped symmDiff

/-- Increasing sets modulo null sets that lie in a limit set modulo null sets
and converge to it in symmetric-difference measure eventually agree with it
almost everywhere. -/
theorem ae_eventually_mem_iff_of_ae_monotone_and_tendsto_symmDiff
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (A : ℕ → Set X) (B : Set X)
    (hmono : ∀ n m, n ≤ m → μ (A n \ A m) = 0)
    (hsub : ∀ n, μ (A n \ B) = 0)
    (hlim : Tendsto (fun n => μ (A n ∆ B)) atTop (𝓝 0)) :
    ∀ᵐ x ∂μ, ∀ᶠ n in atTop, (x ∈ A n ↔ x ∈ B) := by
  have hbad : μ (B \ ⋃ n, A n) = 0 := by
    apply le_antisymm _ bot_le
    apply ge_of_tendsto hlim
    exact Eventually.of_forall fun n => measure_mono (by
      intro x hx
      have hn : x ∉ A n := by
        intro h
        exact hx.2 (mem_iUnion.2 ⟨n, h⟩)
      exact Or.inr ⟨hx.1, hn⟩)
  have hpair : ∀ᵐ x ∂μ, ∀ n m, n ≤ m → x ∈ A n → x ∈ A m := by
    apply ae_all_iff.2
    intro n
    apply ae_all_iff.2
    intro m
    by_cases hnm : n ≤ m
    · filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hmono n m hnm)] with x hx _ hxn
      by_contra hxm
      exact hx ⟨hxn, hxm⟩
    · exact Eventually.of_forall fun _ h _ => (hnm h).elim
  have htoB : ∀ᵐ x ∂μ, ∀ n, x ∈ A n → x ∈ B := by
    apply ae_all_iff.2
    intro n
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hsub n)] with x hx hxn
    by_contra hxB
    exact hx ⟨hxn, hxB⟩
  filter_upwards [hpair, htoB, measure_eq_zero_iff_ae_notMem.1 hbad] with x hp hs hb
  by_cases hxB : x ∈ B
  · have hxU : x ∈ ⋃ n, A n := by
      by_contra hxU
      exact hb ⟨hxB, hxU⟩
    obtain ⟨n, hn⟩ := mem_iUnion.1 hxU
    exact eventually_atTop.2 ⟨n, fun m hnm => ⟨fun _ => hxB, fun _ => hp n m hnm hn⟩⟩
  · exact Eventually.of_forall fun n => ⟨hs n, fun h => (hxB h).elim⟩

/-- The corresponding result for decreasing sets modulo null sets. -/
theorem ae_eventually_mem_iff_of_ae_antitone_and_tendsto_symmDiff
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (A : ℕ → Set X) (B : Set X)
    (hanti : ∀ n m, n ≤ m → μ (A m \ A n) = 0)
    (hsup : ∀ n, μ (B \ A n) = 0)
    (hlim : Tendsto (fun n => μ (A n ∆ B)) atTop (𝓝 0)) :
    ∀ᵐ x ∂μ, ∀ᶠ n in atTop, (x ∈ A n ↔ x ∈ B) := by
  have h := ae_eventually_mem_iff_of_ae_monotone_and_tendsto_symmDiff μ
    (fun n => (A n)ᶜ) Bᶜ (by
      intro n m hnm
      convert hanti n m hnm using 1
      congr 1
      ext x
      simp [and_comm]) (by
      intro n
      convert hsup n using 1
      congr 1
      ext x
      simp [and_comm]) (by
      convert hlim using 1
      ext n
      congr 1
      ext x
      simp only [mem_symmDiff, mem_compl_iff]
      tauto)
  filter_upwards [h] with x hx
  filter_upwards [hx] with n hn
  simpa only [mem_compl_iff, not_iff_not] using hn

universe u

/-- Almost surely, every mass-increasing sequence of same-centre subharmonic
balls compactly contained in the unit disc eventually agrees pointwise
almost everywhere with any such ball whose real mass is its limiting mass.
The exceptional null set may depend on the sequence and comparison ball. -/
theorem ae_subharmonicBall_eventually_mem_iff_of_monotone_mass_limit
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (A : ℕ → Set ℂ) (B : Set ℂ) (z : ℂ),
      (∀ n, closure (A n) ⊆ ball 0 1 ∧ IsSubharmonicBall (μ ω) (A n) z) →
      closure B ⊆ ball 0 1 → IsSubharmonicBall (μ ω) B z →
      Monotone (fun n => (μ ω (A n)).toReal) →
      Tendsto (fun n => (μ ω (A n)).toReal) atTop (𝓝 ((μ ω B).toReal)) →
      ∀ᵐ x ∂(μ ω), ∀ᶠ n in atTop, (x ∈ A n ↔ x ∈ B) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_subharmonicBall_order_inside_unit_disc hI2 h82
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    ae_subharmonicBall_measureReal_symmDiff_inside_unit_disc hI2 h82
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω horder hdist
  intro A B z hA hBcl hB hmono hlim
  have hfin (n : ℕ) : μ ω (A n) ≠ ⊤ := ne_of_lt (hA n).2.2.2.2.1
  have hBfin : μ ω B ≠ ⊤ := ne_of_lt hB.2.2.2.1
  have hreal : Tendsto (fun n => ((μ ω) (A n ∆ B)).toReal) atTop (𝓝 0) := by
    have habs : Tendsto (fun n => |(μ ω (A n)).toReal - (μ ω B).toReal|) atTop (𝓝 0) := by
      have hconst : Tendsto (fun _ : ℕ => (μ ω B).toReal) atTop (𝓝 (μ ω B).toReal) :=
        tendsto_const_nhds
      simpa using (hlim.sub hconst).abs
    apply habs.congr'
    exact Eventually.of_forall fun n => (hdist (A n) B z (hA n).1 hBcl (hA n).2 hB).symm
  have hdistlim : Tendsto (fun n => (μ ω) (A n ∆ B)) atTop (𝓝 0) := by
    have h := ENNReal.tendsto_ofReal hreal
    simpa only [ENNReal.ofReal_zero, ENNReal.ofReal_toReal
      (measure_symmDiff_ne_top (hfin _) hBfin)] using h
  apply ae_eventually_mem_iff_of_ae_monotone_and_tendsto_symmDiff (μ ω) A B
  · intro n m hnm
    have hle : μ ω (A n) ≤ μ ω (A m) :=
      (ENNReal.toReal_le_toReal (hfin n) (hfin m)).1 (hmono hnm)
    exact (horder (A n) (A m) z (hA n).1 (hA m).1 (hA n).2 (hA m).2 hle).2.2.1
  · intro n
    have hle : μ ω (A n) ≤ μ ω B :=
      (ENNReal.toReal_le_toReal (hfin n) hBfin).1 (hmono.ge_of_tendsto hlim n)
    exact (horder (A n) B z (hA n).1 hBcl (hA n).2 hB hle).2.2.1
  · exact hdistlim

/-- The same almost-everywhere convergence for mass-decreasing sequences. -/
theorem ae_subharmonicBall_eventually_mem_iff_of_antitone_mass_limit
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (A : ℕ → Set ℂ) (B : Set ℂ) (z : ℂ),
      (∀ n, closure (A n) ⊆ ball 0 1 ∧ IsSubharmonicBall (μ ω) (A n) z) →
      closure B ⊆ ball 0 1 → IsSubharmonicBall (μ ω) B z →
      Antitone (fun n => (μ ω (A n)).toReal) →
      Tendsto (fun n => (μ ω (A n)).toReal) atTop (𝓝 ((μ ω B).toReal)) →
      ∀ᵐ x ∂(μ ω), ∀ᶠ n in atTop, (x ∈ A n ↔ x ∈ B) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_subharmonicBall_order_inside_unit_disc hI2 h82
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    ae_subharmonicBall_measureReal_symmDiff_inside_unit_disc hI2 h82
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω horder hdist
  intro A B z hA hBcl hB hanti hlim
  have hfin (n : ℕ) : μ ω (A n) ≠ ⊤ := ne_of_lt (hA n).2.2.2.2.1
  have hBfin : μ ω B ≠ ⊤ := ne_of_lt hB.2.2.2.1
  have hreal : Tendsto (fun n => ((μ ω) (A n ∆ B)).toReal) atTop (𝓝 0) := by
    have habs : Tendsto (fun n => |(μ ω (A n)).toReal - (μ ω B).toReal|) atTop (𝓝 0) := by
      have hconst : Tendsto (fun _ : ℕ => (μ ω B).toReal) atTop (𝓝 (μ ω B).toReal) :=
        tendsto_const_nhds
      simpa using (hlim.sub hconst).abs
    apply habs.congr'
    exact Eventually.of_forall fun n => (hdist (A n) B z (hA n).1 hBcl (hA n).2 hB).symm
  have hdistlim : Tendsto (fun n => (μ ω) (A n ∆ B)) atTop (𝓝 0) := by
    have h := ENNReal.tendsto_ofReal hreal
    simpa only [ENNReal.ofReal_zero, ENNReal.ofReal_toReal
      (measure_symmDiff_ne_top (hfin _) hBfin)] using h
  apply ae_eventually_mem_iff_of_ae_antitone_and_tendsto_symmDiff (μ ω) A B
  · intro n m hnm
    have hle : μ ω (A m) ≤ μ ω (A n) :=
      (ENNReal.toReal_le_toReal (hfin m) (hfin n)).1 (hanti hnm)
    exact (horder (A m) (A n) z (hA m).1 (hA n).1 (hA m).2 (hA n).2 hle).2.2.1
  · intro n
    have hle : μ ω B ≤ μ ω (A n) :=
      (ENNReal.toReal_le_toReal hBfin (hfin n)).1 (hanti.le_of_tendsto hlim n)
    exact (horder B (A n) z hBcl (hA n).1 hB (hA n).2 hle).2.2.1
  · exact hdistlim

end HarmonicBalls
