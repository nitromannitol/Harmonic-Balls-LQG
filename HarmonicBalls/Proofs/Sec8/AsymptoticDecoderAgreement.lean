import HarmonicBalls.Proofs.Sec8.CommonCanonicalRootedApproximation
import HarmonicBalls.Proofs.Sec8.JointNormalizedMassLaw

/-! # Asymptotic agreement of rooted mass decoders

The imported distribution-valued reconstruction uses Leonardo Bonanno's
LatticeProb formalization. The convergence of the difference below is an
explicit obligation; it is not implied by fixed-test equality.
-/

open MeasureTheory Filter Set Metric ProbabilityTheory
open scoped Topology

namespace HarmonicBalls

/-- A measurable sequence has the same limit in measure as a second sequence
if their difference converges to zero in measure. -/
theorem tendstoInMeasure_of_sub_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsFiniteMeasure Q]
    (f g : ℕ → Ω → ℝ) (v : Ω → ℝ)
    (hf : ∀ n, AEStronglyMeasurable (f n) Q)
    (hg : TendstoInMeasure Q g atTop v)
    (hd : TendstoInMeasure Q (fun n x => f n x - g n x) atTop (fun _ => 0)) :
    TendstoInMeasure Q f atTop v := by
  apply (exists_seq_tendstoInMeasure_atTop_iff hf).2
  intro s hs
  obtain ⟨t, ht, hgt⟩ := (hg.comp hs.tendsto_atTop).exists_seq_tendsto_ae
  obtain ⟨u, hu, hdu⟩ := ((hd.comp hs.tendsto_atTop).comp ht.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨t ∘ u, ht.comp hu, ?_⟩
  filter_upwards [hgt, hdu] with x hx hy
  have hg' := hx.comp hu.tendsto_atTop
  have h := hy.add hg'
  simpa only [Function.comp_apply, zero_add, sub_add_cancel] using h

/-- Separate reference and sampled-root decoders become a common decoder as
soon as their sampled normalized masses are asymptotically equal in measure.
This retains only the exact comparison still needed for each continuity set. -/
theorem common_mass_approximation_of_asymptotic_decoder_agreement
    {E F Ω Ξ ι : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ξ) (Q : Measure Ω) [IsFiniteMeasure Q]
    (X : Ξ → E) (Y : Ω → E) (Z : Ω → F) (hY : Measurable Y)
    (f : ι → ℕ → E → ℝ) (g : ι → ℕ → F → ℝ)
    (hf : ∀ i n, Measurable (f i n)) (u : ι → Ξ → ℝ) (v : ι → Ω → ℝ)
    (href : ∀ i, TendstoInMeasure P (fun n x => f i n (X x)) atTop (u i))
    (hroot : ∀ i, TendstoInMeasure Q (fun n x => g i n (Z x)) atTop (v i))
    (hclose : ∀ i, TendstoInMeasure Q
      (fun n x => f i n (Y x) - g i n (Z x)) atTop (fun _ => 0)) :
    (∀ i, TendstoInMeasure P (fun n x => f i n (X x)) atTop (u i)) ∧
    ∀ i, TendstoInMeasure Q (fun n x => f i n (Y x)) atTop (v i) := by
  refine ⟨href, ?_⟩
  intro i
  exact tendstoInMeasure_of_sub_tendsto_zero Q _ _ _
    (fun n => ((hf i n).comp hY).aestronglyMeasurable) (hroot i) (hclose i)

/-- Asymptotic agreement of two mass decoders and domination of the local
field law imply domination of the joint field and normalized-measure laws. -/
theorem joint_normalizedRestriction_law_ac_of_asymptotic_decoder_agreement
    {E F Ω Ξ : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ξ) (Q : Measure Ω) [IsFiniteMeasure Q]
    (X : Ξ → E) (Y : Ω → E) (Z : Ω → F)
    (hX : Measurable X) (hY : Measurable Y) (hdom : Q.map Y ≪ P.map X)
    (μ : Ξ → Measure ℂ) (ν : Ω → Measure ℂ) (hμ : Measurable μ) (hν : Measurable ν)
    (W : Set ℂ) (hW : MeasurableSet W)
    (S : Set (Set ℂ)) (hcount : S.Countable)
    (hgen : (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom S)
    (hpi : IsPiSystem S) (hsets : ∀ A ∈ S, MeasurableSet A) (huniv : univ ∈ S)
    (f : S → ℕ → E → ℝ) (g : S → ℕ → F → ℝ)
    (hf : ∀ A n, Measurable (f A n))
    (href : ∀ A, TendstoInMeasure P (fun n x => f A n (X x)) atTop
      (fun x => (normalizedRestriction (μ x) W A.val).toReal))
    (hroot : ∀ A, TendstoInMeasure Q (fun n x => g A n (Z x)) atTop
      (fun x => (normalizedRestriction (ν x) W A.val).toReal))
    (hclose : ∀ A, TendstoInMeasure Q
      (fun n x => f A n (Y x) - g A n (Z x)) atTop (fun _ => 0)) :
    Q.map (fun x => (Y x, normalizedRestriction (ν x) W)) ≪
      P.map (fun x => (X x, normalizedRestriction (μ x) W)) := by
  obtain ⟨hP, hQ⟩ := common_mass_approximation_of_asymptotic_decoder_agreement
    P Q X Y Z hY f g hf _ _ href hroot hclose
  exact joint_normalizedRestriction_law_absolutelyContinuous_of_common_approximations
    P Q X Y hX hY hdom μ ν hμ hν W hW S hcount hgen hpi hsets huniv f hf hP hQ

end HarmonicBalls
