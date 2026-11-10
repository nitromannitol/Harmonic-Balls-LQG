import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Order.SymmDiff

/-!
# The σ-algebra of almost sure modifications of a sub-σ-algebra (fp-S11p, owner n4)

A null ideal `𝒩` on `Ω` (for a probability measure `P`: the sets of `P`-measure zero, `NullIdeal.ofMeasure P`). For a
sub-σ-algebra `F`, `nullSigma 𝒩 F` is the σ-algebra of sets that agree up to a negligible set with a set of `F`.
A `nullSigma`-measurable `ℝ≥0∞`-valued function agrees outside a negligible set with an `F`-measurable one.

Used to pass from the full field σ-algebra to the zero-mean exterior σ-algebra in `FirstPass/S11p.lean`: generator-wise
almost sure measurability gives measurability for `nullSigma`.

Instance hygiene: the lemmas about `F` take no ambient `MeasurableSpace Ω` instance; the approximation lemma takes its
σ-algebra explicitly as `M`.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set
open scoped ENNReal Topology symmDiff

/-- A null ideal: a predicate on sets closed under subsets and countable unions, containing `∅`. -/
structure NullIdeal (Ω : Type*) where
  Null : Set Ω → Prop
  null_empty : Null ∅
  null_mono : ∀ {s t : Set Ω}, s ⊆ t → Null t → Null s
  null_iUnion : ∀ {ι : Type} [Countable ι] (f : ι → Set Ω), (∀ i, Null (f i)) → Null (⋃ i, f i)

/-- The null ideal of a probability measure: sets of measure zero. -/
def NullIdeal.ofMeasure {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) : NullIdeal Ω where
  Null s := P s = 0
  null_empty := measure_empty
  null_mono h ht := measure_mono_null h ht
  null_iUnion _ hf := measure_iUnion_null hf

set_option linter.unusedVariables false in
/-- The null modification `F ∨ 𝒩` of a sub-σ-algebra `F`: sets `A` with `A ∆ C` negligible for some `C ∈ F`. -/
@[instance_reducible]
def nullSigma {Ω : Type*} (𝒩 : NullIdeal Ω) (F : MeasurableSpace Ω) : MeasurableSpace Ω where
  MeasurableSet' A := ∃ C, MeasurableSet[F] C ∧ 𝒩.Null (A ∆ C)
  measurableSet_empty := ⟨∅, MeasurableSet.empty, by simpa using 𝒩.null_empty⟩
  measurableSet_compl A := by
    rintro ⟨C, hC, h⟩
    exact ⟨Cᶜ, hC.compl, by rwa [compl_symmDiff_compl]⟩
  measurableSet_iUnion f hf := by
    choose C hCm hCn using hf
    have hsub : (⋃ n, f n) ∆ (⋃ n, C n) ⊆ ⋃ n, (f n ∆ C n) := by
      intro ω hω
      rcases Set.mem_symmDiff.1 hω with ⟨hA, hB⟩ | ⟨hB, hA⟩
      · obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hA
        exact Set.mem_iUnion.2 ⟨n, Set.mem_symmDiff.2 (Or.inl ⟨hn, fun hc => hB (Set.mem_iUnion.2 ⟨n, hc⟩)⟩)⟩
      · obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hB
        exact Set.mem_iUnion.2 ⟨n, Set.mem_symmDiff.2 (Or.inr ⟨hn, fun hf => hA (Set.mem_iUnion.2 ⟨n, hf⟩)⟩)⟩
    exact ⟨⋃ n, C n, MeasurableSet.iUnion hCm, 𝒩.null_mono hsub (𝒩.null_iUnion _ hCn)⟩

/-- A function that agrees outside a negligible set with an `F`-measurable one is `nullSigma`-measurable. -/
theorem measurable_nullSigma_of_ae_eq {Ω : Type*} {β : Type*} [MeasurableSpace β] {𝒩 : NullIdeal Ω}
    {F : MeasurableSpace Ω} {X Y : Ω → β} (hY : Measurable[F] Y) {N : Set Ω} (hN : 𝒩.Null N) (hXY : ∀ ω, ω ∉ N → X ω = Y ω) :
    Measurable[nullSigma 𝒩 F] X := by
  intro B hB
  have hsub : (X ⁻¹' B) ∆ (Y ⁻¹' B) ⊆ N := by
    intro ω hω
    by_contra hωN
    have heq := hXY ω hωN
    rw [Set.mem_symmDiff, Set.mem_preimage, Set.mem_preimage, heq] at hω
    tauto
  exact ⟨Y ⁻¹' B, hY hB, 𝒩.null_mono hsub hN⟩

/-- `F` is contained in its null modification. -/
theorem le_nullSigma {Ω : Type*} (𝒩 : NullIdeal Ω) (F : MeasurableSpace Ω) : F ≤ nullSigma 𝒩 F :=
  fun A hA => ⟨A, hA, by simpa using 𝒩.null_empty⟩

/-- Approximation (instance explicit): a measurable `ℝ≥0∞`-valued function is a pointwise limit of simple functions
with finitely many values and measurable fibres. -/
theorem exists_simple_approx {Ω : Type*} (M : MeasurableSpace Ω) {g : Ω → ℝ≥0∞} (hg : Measurable[M] g) :
    ∃ s : ℕ → Ω → ℝ≥0∞, ∃ T : ℕ → Finset ℝ≥0∞, (∀ n ω, s n ω ∈ T n) ∧
      (∀ n y, MeasurableSet[M] (s n ⁻¹' {y})) ∧ ∀ ω, Tendsto (fun n => s n ω) atTop (𝓝 (g ω)) := by
  refine ⟨fun n => ⇑(SimpleFunc.eapprox g n), fun n => (SimpleFunc.eapprox g n).range,
    fun n ω => SimpleFunc.mem_range_self _ ω, fun n y => SimpleFunc.measurableSet_fiber _ y, fun ω => ?_⟩
  have hmono : Monotone (fun n => SimpleFunc.eapprox g n ω) := fun m n h => SimpleFunc.monotone_eapprox g h ω
  have hsup : ⨆ n, SimpleFunc.eapprox g n ω = g ω := SimpleFunc.iSup_eapprox_apply hg ω
  have := tendsto_atTop_iSup hmono
  rw [hsup] at this
  exact this

/-- A `nullSigma 𝒩 F`-measurable `ℝ≥0∞`-valued function agrees outside a negligible set with an `F`-measurable one.
Proof: the approximations `s_n` have `nullSigma`-measurable fibres; replace each fibre `{s_n = y}` by an `F`-set `C n y`
agreeing with it outside a negligible set. The sums `∑_{y ∈ T n} 1_{C n y} · y` are `F`-measurable and equal `s_n`
outside a negligible set (the fibres are disjoint); `s_n → g` pointwise. -/
theorem exists_measurable_of_measurable_nullSigma {Ω : Type*} {𝒩 : NullIdeal Ω} {F : MeasurableSpace Ω}
    {g : Ω → ℝ≥0∞} (hg : Measurable[nullSigma 𝒩 F] g) :
    ∃ g' : Ω → ℝ≥0∞, Measurable[F] g' ∧ ∃ N : Set Ω, 𝒩.Null N ∧ ∀ ω, ω ∉ N → g ω = g' ω := by
  obtain ⟨s, T, hT, hfib, hlim⟩ := exists_simple_approx (nullSigma 𝒩 F) hg
  have hfibF : ∀ (n : ℕ) (y : ℝ≥0∞), ∃ C : Set Ω, MeasurableSet[F] C ∧ 𝒩.Null ((s n ⁻¹' {y}) ∆ C) :=
    fun n y => hfib n y
  choose C hCm hCn using hfibF
  have hmeas : ∀ n, Measurable[F] (fun ω => ∑ y ∈ T n, (C n y).indicator (fun _ => y) ω) :=
    fun n => Finset.measurable_sum _ fun y _ => measurable_const.indicator (hCm n y)
  -- for each `n`, a negligible set outside which the `F`-sum equals `s n`
  have hgood : ∀ n, ∃ N : Set Ω, 𝒩.Null N ∧ ∀ ω, ω ∉ N →
      ∑ y ∈ T n, (C n y).indicator (fun _ => y) ω = s n ω := by
    intro n
    refine ⟨⋃ y : T n, ((s n ⁻¹' {(y : ℝ≥0∞)}) ∆ C n y), 𝒩.null_iUnion _ fun y => hCn n y, fun ω hω => ?_⟩
    have hno : ∀ y ∈ T n, ω ∉ ((s n ⁻¹' {y}) ∆ C n y) := fun y hy h =>
      hω (Set.mem_iUnion.2 ⟨⟨y, hy⟩, h⟩)
    have hiff : ∀ y ∈ T n, (ω ∈ s n ⁻¹' {y} ↔ ω ∈ C n y) := fun y hy => by
      have := hno y hy
      rw [Set.mem_symmDiff] at this
      tauto
    have hy0 : s n ω ∈ T n := hT n ω
    rw [Finset.sum_eq_single (s n ω)]
    · have hωC : ω ∈ C n (s n ω) := (hiff _ hy0).1 rfl
      simp [Set.indicator_of_mem hωC]
    · intro y hy hne
      have hωC : ω ∉ C n y := fun hc => hne (by
        have hf := (hiff y hy).2 hc
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hf
        exact hf.symm)
      simp [Set.indicator_of_notMem hωC]
    · intro h
      exact absurd hy0 h
  choose N hNn hNe using hgood
  refine ⟨fun ω => limsup (fun n => ∑ y ∈ T n, (C n y).indicator (fun _ => y) ω) atTop,
    Measurable.limsup hmeas, ⋃ n, N n, 𝒩.null_iUnion _ hNn, fun ω hω => ?_⟩
  have hfun : (fun n => ∑ y ∈ T n, (C n y).indicator (fun _ => y) ω) = fun n => s n ω :=
    funext fun n => hNe n ω (fun h => hω (Set.mem_iUnion.2 ⟨n, h⟩))
  show g ω = limsup (fun n => ∑ y ∈ T n, (C n y).indicator (fun _ => y) ω) atTop
  rw [hfun]
  exact ((hlim ω).limsup_eq).symm

end HarmonicBalls
