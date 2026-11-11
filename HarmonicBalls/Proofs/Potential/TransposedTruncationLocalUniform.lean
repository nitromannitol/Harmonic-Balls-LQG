import HarmonicBalls.Proofs.Potential.SourceFreeTransposedMassBound
import HarmonicBalls.Proofs.Potential.TransposedChangedSourceObstruction

/-! # Local uniform source truncation

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
The source is the first Green function argument.
-/

namespace HarmonicBalls

open MeasureTheory Set Filter InnerProductSpace
open scoped Topology

/-- Increasing measurable truncations carrying a finite source converge uniformly on
compact subsets of a source-free open set. Both the truncated and full potentials
are harmonic there. -/
theorem transposed_green_source_truncation_local_uniform
    {V U L : Set ℂ} (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (hU : IsOpen U) (hL : IsCompact L) (hLU : L ⊆ U) (hUV : U ⊆ V)
    {ν : Measure ℂ} [IsFiniteMeasure ν] (hνV : ν Vᶜ = 0) (hνU : ν U = 0)
    (E : ℕ → Set ℂ) (hE : ∀ n, MeasurableSet (E n)) (hmono : Monotone E)
    (hcover : ν (⋃ n, E n)ᶜ = 0) :
    HarmonicOnNhd (fun x => ∫ y, greenFunction V y x ∂ν) U ∧
    (∀ n, HarmonicOnNhd (fun x => ∫ y in E n, greenFunction V y x ∂ν) U) ∧
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ x ∈ L,
      |(∫ y in E n, greenFunction V y x ∂ν) -
        (∫ y, greenFunction V y x ∂ν)| < ε := by
  have hnull (n : ℕ) (s : Set ℂ) (hs : ν s = 0) : (ν.restrict (E n)) s = 0 :=
    le_antisymm ((Measure.restrict_le_self s).trans_eq hs) bot_le
  have hresnull (n : ℕ) (s : Set ℂ) (hs : ν s = 0) :
      (ν.restrict (E n)ᶜ) s = 0 := le_antisymm ((Measure.restrict_le_self s).trans_eq hs) bot_le
  have hinter : ν (⋂ n, (E n)ᶜ) = 0 := by simpa only [← compl_iUnion] using hcover
  have hmass0 : Tendsto (fun n => ν (E n)ᶜ) atTop (𝓝 0) := by
    simpa only [hinter, Function.comp_def] using
      (tendsto_measure_iInter_atTop (μ := ν) (s := fun n => (E n)ᶜ)
        (fun n => (hE n).compl.nullMeasurableSet)
        (fun i j hij => compl_subset_compl.mpr (hmono hij))
        ⟨0, measure_ne_top ν _⟩)
  have hmass : Tendsto (fun n => ((ν.restrict (E n)ᶜ) univ).toReal) atTop (𝓝 0) := by
    simpa only [Measure.restrict_apply_univ, ENNReal.toReal_zero, Function.comp_def] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hmass0
  have hzero := uniform_zero_and_harmonic_transposed_green_of_mass_tendsto_zero
    hV hVb hU hL hLU hUV (fun n => ν.restrict (E n)ᶜ)
    (fun n => hresnull n _ hνV) (fun n => hresnull n _ hνU) hmass
  refine ⟨harmonicOnNhd_transposed_greenIntegral_of_finite_source hV hVb hνV hU hUV hνU,
    fun n => harmonicOnNhd_transposed_greenIntegral_of_finite_source hV hVb
      (hnull n _ hνV) hU hUV (hnull n _ hνU), ?_⟩
  intro ε hε
  filter_upwards [hzero.2 ε hε] with n hn x hx
  have hi := integrable_transposed_green_of_source_free hV hVb hνV hU hUV hνU (hLU hx)
  have heq : (∫ y, greenFunction V y x ∂ν) =
      (∫ y in E n, greenFunction V y x ∂ν) +
      (∫ y in (E n)ᶜ, greenFunction V y x ∂ν) := by
    calc
      _ = ∫ y, greenFunction V y x ∂(ν.restrict (E n) + ν.restrict (E n)ᶜ) := by
        rw [Measure.restrict_add_restrict_compl (hE n)]
      _ = _ := integral_add_measure (hi.mono_measure Measure.restrict_le_self)
        (hi.mono_measure Measure.restrict_le_self)
  rw [heq, sub_add_cancel_left, abs_neg]
  exact hn x hx


end HarmonicBalls
