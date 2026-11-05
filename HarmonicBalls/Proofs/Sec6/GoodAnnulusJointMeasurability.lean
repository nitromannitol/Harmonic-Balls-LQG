import HarmonicBalls.Proofs.Sec6.MeasurePushforwardJoint
import HarmonicBalls.Proofs.Sec8.GoodEventPointPolarity
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-! # Joint measurability of good annuli

A parameterized affine pullback reduces the good-annulus event to the unit
annulus at the origin.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter

/-- For a measurable locally finite measure family, the good-annulus event is
jointly measurable in a measurable centre and positive radius. -/
theorem measurableSet_isGoodAnnulus_joint
    {A : Type*} [MeasurableSpace A] {μ : A → Measure ℂ} {z : A → ℂ} {r : A → ℝ}
    (hμ : Measurable μ) (hfinite : ∀ x, IsLocallyFiniteMeasure (μ x))
    (hz : Measurable z) (hr : Measurable r) (hrpos : ∀ x, 0 < r x)
    {a : ℝ} (ha : 0 < a) (b : ℝ) :
    MeasurableSet {x : A | IsGoodAnnulus (μ x) (r x) (z x) a b} := by
  let ν : A → Measure ℂ := fun x => (μ x).map (fun y => (r x)⁻¹ • (y - z x))
  have hν : Measurable ν := measurable_map_of_locallyFinite hμ hfinite
    (f := fun p : A × ℂ => (r p.1)⁻¹ • (p.2 - z p.1)) (by fun_prop)
  have hu := measurableSet_isGoodAnnulus_of_pos 1 (by norm_num) 0 a b ha
  have heq : {x : A | IsGoodAnnulus (μ x) (r x) (z x) a b} =
      ν ⁻¹' {m : Measure ℂ | IsGoodAnnulus m 1 0 a b} := by
    ext x
    change IsGoodAnnulus (μ x) (r x) (z x) a b ↔ IsGoodAnnulus (ν x) 1 0 a b
    have hmap : ((μ x).map (fun y : ℂ => y + -z x)).map
        (fun y : ℂ => (r x)⁻¹ • y) = ν x := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    rw [← hmap, isGoodAnnulus_unit_normalize (μ x) (hrpos x) (z x) a b]
  rw [heq]
  exact hu.preimage hν


/-- The joint event is null measurable when the measure family is only
almost-everywhere measurable and locally finite. This applies under any rooted
law for which these properties hold. -/
theorem nullMeasurableSet_isGoodAnnulus_joint
    {A : Type*} [MeasurableSpace A] {P : Measure A}
    {μ : A → Measure ℂ} {z : A → ℂ} {r : A → ℝ}
    (hμ : AEMeasurable μ P) (hfinite : ∀ᵐ x ∂P, IsLocallyFiniteMeasure (μ x))
    (hz : Measurable z) (hr : Measurable r) (hrpos : ∀ x, 0 < r x)
    {a : ℝ} (ha : 0 < a) (b : ℝ) :
    NullMeasurableSet {x : A | IsGoodAnnulus (μ x) (r x) (z x) a b} P := by
  obtain ⟨ν, hν, hνfinite, heq⟩ := exists_measurable_locallyFinite_rep hμ hfinite
  have hgood := measurableSet_isGoodAnnulus_joint hν hνfinite hz hr hrpos ha b
  apply hgood.nullMeasurableSet.congr
  filter_upwards [heq] with x hx
  simp only [← hx]

/-- Null measurability transfers from the base field law to a rooted law
whose projection to the field is quasi-measure-preserving. -/
theorem nullMeasurableSet_isGoodAnnulus_of_quasiMeasurePreserving
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {Q : Measure A} {P : Measure B} {π : A → B}
    (hπ : Measure.QuasiMeasurePreserving π Q P)
    {μ : B → Measure ℂ} (hμ : AEMeasurable μ P)
    (hfinite : ∀ᵐ x ∂P, IsLocallyFiniteMeasure (μ x))
    {z : A → ℂ} {r : A → ℝ} (hz : Measurable z) (hr : Measurable r)
    (hrpos : ∀ x, 0 < r x) {a : ℝ} (ha : 0 < a) (b : ℝ) :
    NullMeasurableSet {x : A | IsGoodAnnulus (μ (π x)) (r x) (z x) a b} Q := by
  obtain ⟨ν, hν, hνfinite, heq⟩ := exists_measurable_locallyFinite_rep hμ hfinite
  have hgood := measurableSet_isGoodAnnulus_joint (hν.comp hπ.measurable)
    (fun x => hνfinite (π x)) hz hr hrpos ha b
  apply hgood.nullMeasurableSet.congr
  filter_upwards [hπ.ae_eq_comp heq] with x hx
  simp only [Function.comp_apply] at hx ⊢
  rw [← hx]

/-- Projection to the field is quasi-measure-preserving for a composition
product with a sampling kernel. -/
theorem quasiMeasurePreserving_fst_compProd
    {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    (P : Measure Ω) (κ : Kernel Ω Z) :
    Measure.QuasiMeasurePreserving Prod.fst (P ⊗ₘ κ) P := by
  refine ⟨measurable_fst, ?_⟩
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hsz
  rw [Measure.map_apply measurable_fst hs]
  have hae : ∀ᵐ ω ∂P, ω ∉ s := ae_iff.mpr (by simpa using hsz)
  have hroot := Measure.ae_compProd_of_ae_fst κ hs.compl hae
  change (P ⊗ₘ κ) {x : Ω × Z | x.1 ∈ s} = 0
  simpa only [not_not] using (ae_iff.mp hroot)

/-- Joint good-annulus events are null measurable under a rooted law
constructed as the composition product with a sampling kernel. -/
theorem nullMeasurableSet_isGoodAnnulus_compProd
    {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    (P : Measure Ω) (κ : Kernel Ω Z)
    {μ : Ω → Measure ℂ} (hμ : AEMeasurable μ P)
    (hfinite : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    {z : Ω × Z → ℂ} {r : Ω × Z → ℝ}
    (hz : Measurable z) (hr : Measurable r) (hrpos : ∀ x, 0 < r x)
    {a : ℝ} (ha : 0 < a) (b : ℝ) :
    NullMeasurableSet {x : Ω × Z | IsGoodAnnulus (μ x.1) (r x) (z x) a b}
      (P ⊗ₘ κ) :=
  nullMeasurableSet_isGoodAnnulus_of_quasiMeasurePreserving
    (quasiMeasurePreserving_fst_compProd P κ) hμ hfinite hz hr hrpos ha b

/-- The number of good annuli in a countable measurable family is measurable
jointly in the measure, centres and radii. -/
theorem measurable_goodAnnulus_count_joint
    {A : Type*} [MeasurableSpace A] {μ : A → Measure ℂ}
    (hμ : Measurable μ) (hfinite : ∀ x, IsLocallyFiniteMeasure (μ x))
    (z : ℕ → A → ℂ) (r : ℕ → A → ℝ)
    (hz : ∀ n, Measurable (z n)) (hr : ∀ n, Measurable (r n))
    (hrpos : ∀ n x, 0 < r n x) (S : Set ℕ)
    {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Measurable (fun x : A =>
      ({n : ℕ | n ∈ S ∧ IsGoodAnnulus (μ x) (r n x) (z n x) a b}.ncard : ℝ)) := by
  let T : A → Set ℕ := fun x => {n | n ∈ S ∧ IsGoodAnnulus (μ x) (r n x) (z n x) a b}
  have hT : Measurable T := by
    apply measurable_setOfPred.comp
    apply measurable_pi_iff.mpr
    intro n
    apply measurableSet_setOfPred.mp
    by_cases hn : n ∈ S
    · simp only [hn, true_and]
      exact measurableSet_isGoodAnnulus_joint hμ hfinite (hz n) (hr n) (hrpos n) ha b
    · simp only [hn, false_and, ofPred_false, MeasurableSet.empty]
  exact Measurable.of_discrete.comp (measurable_ncard.comp hT)

end HarmonicBalls.Section6
