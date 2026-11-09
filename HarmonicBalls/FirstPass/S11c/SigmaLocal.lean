import Mathlib

/-!
# First pass, Lemma 11.7: Dynkin extension of local measurability (fp-S11c, owner n1)

Generic measure theory used in the transfer step (CHATGPT-11-7-proof.md, sec 4; operator note 20:22, B2): if the
mass of every open subset `V ⊆ U` is almost surely equal to a `m`-measurable variable (for the local field σ-algebra
`m = σ(h|_U)`, input `LQGMeasureLocality`, Proposed/LQG.lean:83, Fact 2.1 II), then so is the mass of every Borel
subset of `U`. This is the π-λ (Dynkin) argument on the open sets: the class of Borel `t` with `μ(t ∩ U)` a.s.
`m`-measurable contains the open sets, is closed under complements in `U` (as `μ U < ∞` a.s.) and under countable
disjoint unions.
-/

open MeasureTheory Set
open scoped ENNReal

namespace HarmonicBalls.S11c

/-- Dynkin extension: from the open subsets of an open set `U` to the Borel subsets of `U`. -/
theorem exists_measurable_of_open_family {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω}
    (μ : Ω → Measure ℂ) {U : Set ℂ} (hU : IsOpen U)
    (hopen : ∀ V : Set ℂ, IsOpen V → V ⊆ U →
      ∃ Y : Ω → ℝ≥0∞, Measurable[m] Y ∧ ∀ᵐ ω ∂P, μ ω V = Y ω)
    (hfin : ∀ᵐ ω ∂P, μ ω U ≠ ∞) :
    ∀ B : Set ℂ, MeasurableSet B → B ⊆ U →
      ∃ Y : Ω → ℝ≥0∞, Measurable[m] Y ∧ ∀ᵐ ω ∂P, μ ω B = Y ω := by
  have key : ∀ t : Set ℂ, MeasurableSet t →
      ∃ Y : Ω → ℝ≥0∞, Measurable[m] Y ∧ ∀ᵐ ω ∂P, μ ω (t ∩ U) = Y ω := by
    intro t ht
    refine MeasurableSpace.induction_on_inter (C := fun t _ =>
      ∃ Y : Ω → ℝ≥0∞, Measurable[m] Y ∧ ∀ᵐ ω ∂P, μ ω (t ∩ U) = Y ω)
      (s := {s : Set ℂ | IsOpen s}) BorelSpace.measurable_eq isPiSystem_isOpen ?_ ?_ ?_ ?_ t ht
    · refine ⟨fun _ => 0, measurable_const, ae_of_all _ fun ω => ?_⟩
      simp
    · intro t' ht'
      obtain ⟨Y, hY, hYa⟩ := hopen (t' ∩ U) (IsOpen.inter ht' hU) Set.inter_subset_right
      exact ⟨Y, hY, hYa⟩
    · intro t' htm ih
      obtain ⟨Yt, hYt, hYta⟩ := ih
      obtain ⟨YU, hYU, hYUa⟩ := hopen U hU Set.Subset.rfl
      refine ⟨fun ω => YU ω - Yt ω, hYU.sub hYt, ?_⟩
      filter_upwards [hYta, hYUa, hfin] with ω h1 h2 h3
      have hset : t'ᶜ ∩ U = U \ (t' ∩ U) := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff]
        tauto
      have hfin' : μ ω (t' ∩ U) ≠ ∞ :=
        ne_top_of_le_ne_top h3 (measure_mono Set.inter_subset_right)
      rw [hset, measure_sdiff Set.inter_subset_right
        ((htm.inter hU.measurableSet).nullMeasurableSet) hfin', h2, h1]
    · intro f hdisj hfm ih
      choose Yf hYfm hYfa using ih
      refine ⟨fun ω => ∑' i, Yf i ω, Measurable.tsum hYfm, ?_⟩
      have hall : ∀ᵐ ω ∂P, ∀ i, μ ω (f i ∩ U) = Yf i ω := ae_all_iff.mpr hYfa
      filter_upwards [hall] with ω hω
      have hdisj' : Pairwise (Function.onFun Disjoint fun i => f i ∩ U) := fun i j hij =>
        Disjoint.mono Set.inter_subset_left Set.inter_subset_left (hdisj hij)
      rw [Set.iUnion_inter, measure_iUnion hdisj' fun i => (hfm i).inter hU.measurableSet]
      exact tsum_congr fun i => hω i
  intro B hB hBU
  obtain ⟨Y, hY, hYa⟩ := key B hB
  refine ⟨Y, hY, ?_⟩
  filter_upwards [hYa] with ω h
  rwa [Set.inter_eq_left.mpr hBU] at h

end HarmonicBalls.S11c
