import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-! # Transfer of laws through common local approximations

The limits under two field laws must arise from the same approximations.  This
condition gives a common measurable realization of the limits, simultaneously
for a countable family of observables.
-/

open MeasureTheory Filter
open scoped Topology

namespace HarmonicBalls

/-- Limits in measure of the same measurable real-valued approximations have
one common measurable representative under both field laws. -/
theorem exists_common_limit_of_tendstoInMeasure
    {E Ω Ξ : Type*} [MeasurableSpace E] [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) (Q : Measure Ξ) (X : Ω → E) (Y : Ξ → E)
    (f : ℕ → E → ℝ) (hf : ∀ n, Measurable (f n))
    (u : Ω → ℝ) (v : Ξ → ℝ)
    (hu : TendstoInMeasure P (fun n ω => f n (X ω)) atTop u)
    (hv : TendstoInMeasure Q (fun n ω => f n (Y ω)) atTop v) :
    ∃ F : E → ℝ, Measurable F ∧
      (fun ω => F (X ω)) =ᵐ[P] u ∧ (fun ω => F (Y ω)) =ᵐ[Q] v := by
  obtain ⟨s, hs, hsP⟩ := hu.exists_seq_tendsto_ae
  obtain ⟨t, ht, htQ⟩ := (hv.comp hs.tendsto_atTop).exists_seq_tendsto_ae
  let F : E → ℝ := fun x => limUnder atTop (fun n => f (s (t n)) x)
  have hF : Measurable F :=
    (StronglyMeasurable.limUnder (fun n => (hf (s (t n))).stronglyMeasurable)).measurable
  refine ⟨F, hF, ?_, ?_⟩
  · filter_upwards [hsP] with ω hω
    exact (hω.comp ht.tendsto_atTop).limUnder_eq
  · filter_upwards [htQ] with ω hω
    exact hω.limUnder_eq

/-- Countably many observables admit common representatives on the field
space, with the almost-sure equalities holding simultaneously. -/
theorem exists_common_countable_limits_of_tendstoInMeasure
    {E Ω Ξ ι : Type*} [MeasurableSpace E] [MeasurableSpace Ω] [MeasurableSpace Ξ]
    [Countable ι]
    (P : Measure Ω) (Q : Measure Ξ) (X : Ω → E) (Y : Ξ → E)
    (f : ι → ℕ → E → ℝ) (hf : ∀ i n, Measurable (f i n))
    (u : ι → Ω → ℝ) (v : ι → Ξ → ℝ)
    (hu : ∀ i, TendstoInMeasure P (fun n ω => f i n (X ω)) atTop (u i))
    (hv : ∀ i, TendstoInMeasure Q (fun n ω => f i n (Y ω)) atTop (v i)) :
    ∃ F : ι → E → ℝ, (∀ i, Measurable (F i)) ∧
      (∀ᵐ ω ∂P, ∀ i, F i (X ω) = u i ω) ∧
      (∀ᵐ ω ∂Q, ∀ i, F i (Y ω) = v i ω) := by
  choose F hFm hFP hFQ using fun i =>
    exists_common_limit_of_tendstoInMeasure P Q X Y (f i) (hf i) (u i) (v i) (hu i) (hv i)
  exact ⟨F, hFm, ae_all_iff.mpr hFP, ae_all_iff.mpr hFQ⟩

/-- The joint law of countably many common approximation limits inherits
absolute continuity from the two field laws. -/
theorem countable_limit_law_absolutelyContinuous
    {E Ω Ξ ι : Type*} [MeasurableSpace E] [MeasurableSpace Ω] [MeasurableSpace Ξ]
    [Countable ι]
    (P : Measure Ω) (Q : Measure Ξ) (X : Ω → E) (Y : Ξ → E)
    (hX : Measurable X) (hY : Measurable Y) (hdom : Q.map Y ≪ P.map X)
    (f : ι → ℕ → E → ℝ) (hf : ∀ i n, Measurable (f i n))
    (u : ι → Ω → ℝ) (v : ι → Ξ → ℝ)
    (hu : ∀ i, TendstoInMeasure P (fun n ω => f i n (X ω)) atTop (u i))
    (hv : ∀ i, TendstoInMeasure Q (fun n ω => f i n (Y ω)) atTop (v i)) :
    Q.map (fun ω i => v i ω) ≪ P.map (fun ω i => u i ω) := by
  obtain ⟨F, hFm, hFP, hFQ⟩ :=
    exists_common_countable_limits_of_tendstoInMeasure P Q X Y f hf u v hu hv
  have hF : Measurable (fun x i => F i x) := Measurable.of_eval hFm
  have hP : P.map (fun ω i => u i ω) = P.map ((fun x i => F i x) ∘ X) := by
    apply Measure.map_congr
    filter_upwards [hFP] with ω hω
    funext i
    exact (hω i).symm
  have hQ : Q.map (fun ω i => v i ω) = Q.map ((fun x i => F i x) ∘ Y) := by
    apply Measure.map_congr
    filter_upwards [hFQ] with ω hω
    funext i
    exact (hω i).symm
  rw [hQ, hP, ← Measure.map_map hF hY, ← Measure.map_map hF hX]
  exact hdom.map hF


/-- If a countable family of observables measurably embeds the object space,
common approximations transfer the law of the whole object. -/
theorem law_absolutelyContinuous_of_countable_approximations
    {E Ω Ξ ι Z : Type*} [MeasurableSpace E] [MeasurableSpace Ω] [MeasurableSpace Ξ]
    [MeasurableSpace Z] [Countable ι]
    (P : Measure Ω) (Q : Measure Ξ) (X : Ω → E) (Y : Ξ → E)
    (hX : Measurable X) (hY : Measurable Y) (hdom : Q.map Y ≪ P.map X)
    (U : Ω → Z) (V : Ξ → Z) (hU : Measurable U) (hV : Measurable V)
    (encode : Z → ι → ℝ) (hencode : MeasurableEmbedding encode)
    (f : ι → ℕ → E → ℝ) (hf : ∀ i n, Measurable (f i n))
    (hu : ∀ i, TendstoInMeasure P (fun n ω => f i n (X ω)) atTop
      (fun ω => encode (U ω) i))
    (hv : ∀ i, TendstoInMeasure Q (fun n ω => f i n (Y ω)) atTop
      (fun ω => encode (V ω) i)) :
    Q.map V ≪ P.map U := by
  have h := countable_limit_law_absolutelyContinuous P Q X Y hX hY hdom f hf
    (fun i ω => encode (U ω) i) (fun i ω => encode (V ω) i) hu hv
  change Q.map (encode ∘ V) ≪ P.map (encode ∘ U) at h
  rw [← Measure.map_map hencode.measurable hV, ← Measure.map_map hencode.measurable hU] at h
  refine Measure.AbsolutelyContinuous.mk ?_
  intro s hs hzero
  have hz : (P.map U).map encode (encode '' s) = 0 := by
    rw [hencode.map_apply, hencode.injective.preimage_image]
    exact hzero
  have hq := h hz
  rwa [hencode.map_apply, hencode.injective.preimage_image] at hq

end HarmonicBalls
