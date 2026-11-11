import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Bases

/-!
# Countable dense replacements of infima and suprema

The rule of
Lemma 11.12 is a set of pairings, so each infimum or supremum over an uncountable set of points must be replaced by one
over a countable dense subset. A decoder returns only measurable functions of the pairing (no continuity clause), so the
replacement is exact only almost surely, where the true internal metric is continuous. This file gives the deterministic
replacement lemmas and the measurability of countable infima, suprema and limsups.

Deterministic; no probability and no inputs beyond the topology of `X`.
-/

namespace HarmonicBalls.S11m

open Set Filter Topology MeasureTheory
open scoped ENNReal

variable {X : Type*} [TopologicalSpace X]

/-- A countable subset of `T` which is dense in `T` (for a second countable `X`). -/
theorem exists_countable_dense_subset_of_secondCountable [SecondCountableTopology X] (T : Set X) :
    ∃ C : Set X, C ⊆ T ∧ C.Countable ∧ T ⊆ closure C := by
  obtain ⟨C, hCc, hCT, hTC⟩ := TopologicalSpace.exists_countable_dense_subset T
  exact ⟨C, hCT, hCc, hTC⟩

/-- **Countable dense replacement of an infimum** (deterministic). If `g` is continuous on `T` and `C ⊆ T` is dense in
`T`, then `⨅ t ∈ T, g t = ⨅ c ∈ C, g c`. -/
theorem iInf_mem_eq_iInf_mem_of_dense_continuousOn {T C : Set X} {g : X → ℝ≥0∞} (hg : ContinuousOn g T)
    (hCT : C ⊆ T) (hdense : T ⊆ closure C) : (⨅ t ∈ T, g t) = ⨅ c ∈ C, g c := by
  refine le_antisymm (le_iInf₂ fun c hc => iInf₂_le c (hCT hc)) (le_iInf₂ fun t ht => ?_)
  have hcont : Tendsto g (𝓝[C] t) (𝓝 (g t)) :=
    (hg t ht).mono_left (nhdsWithin_mono t hCT)
  have hev : ∀ᶠ c in 𝓝[C] t, (⨅ c' ∈ C, g c') ≤ g c :=
    eventually_nhdsWithin_of_forall fun c hc => iInf₂_le c hc
  have : (𝓝[C] t).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hdense ht)
  exact ge_of_tendsto hcont hev

/-- **Countable dense replacement of a supremum** (deterministic), the dual of the infimum version. -/
theorem iSup_mem_eq_iSup_mem_of_dense_continuousOn {T C : Set X} {g : X → ℝ≥0∞} (hg : ContinuousOn g T)
    (hCT : C ⊆ T) (hdense : T ⊆ closure C) : (⨆ t ∈ T, g t) = ⨆ c ∈ C, g c := by
  refine le_antisymm (iSup₂_le fun t ht => ?_) (iSup₂_le fun c hc => le_iSup₂_of_le c (hCT hc) le_rfl)
  have hcont : Tendsto g (𝓝[C] t) (𝓝 (g t)) :=
    (hg t ht).mono_left (nhdsWithin_mono t hCT)
  have hev : ∀ᶠ c in 𝓝[C] t, g c ≤ ⨆ c' ∈ C, g c' :=
    eventually_nhdsWithin_of_forall fun c hc => le_iSup₂ (f := fun c' (_ : c' ∈ C) => g c') c hc
  have : (𝓝[C] t).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hdense ht)
  exact le_of_tendsto hcont hev

omit [TopologicalSpace X] in
/-- A countable infimum of measurable `ℝ≥0∞`-valued functions over a countable set is measurable. -/
theorem measurable_biInf_of_countable {Ω : Type*} [MeasurableSpace Ω] {C : Set X} (hC : C.Countable)
    (F : X → Ω → ℝ≥0∞) (hF : ∀ c, Measurable (F c)) :
    Measurable fun ω => ⨅ c ∈ C, F c ω := by
  have := hC.to_subtype
  have h : (fun ω => ⨅ c ∈ C, F c ω) = fun ω => ⨅ c : C, F c ω := by
    funext ω
    simp only [iInf_subtype']
  rw [h]
  exact Measurable.iInf fun c : C => hF c

omit [TopologicalSpace X] in
/-- A countable supremum of measurable `ℝ≥0∞`-valued functions over a countable set is measurable. -/
theorem measurable_biSup_of_countable {Ω : Type*} [MeasurableSpace Ω] {C : Set X} (hC : C.Countable)
    (F : X → Ω → ℝ≥0∞) (hF : ∀ c, Measurable (F c)) :
    Measurable fun ω => ⨆ c ∈ C, F c ω := by
  have := hC.to_subtype
  have h : (fun ω => ⨆ c ∈ C, F c ω) = fun ω => ⨆ c : C, F c ω := by
    funext ω
    simp only [iSup_subtype']
  rw [h]
  exact Measurable.iSup fun c : C => hF c

/-- The `limsup` along `ℕ` of measurable `ℝ≥0∞`-valued functions is measurable (used for the root values
`lim_{s → 0} inf_{∂B_s}` along the sequence `s_n → 0`). -/
theorem measurable_limsup_nat {Ω : Type*} [MeasurableSpace Ω] (F : ℕ → Ω → ℝ≥0∞) (hF : ∀ n, Measurable (F n)) :
    Measurable fun ω => limsup (fun n => F n ω) atTop :=
  Measurable.limsup hF

end HarmonicBalls.S11m
