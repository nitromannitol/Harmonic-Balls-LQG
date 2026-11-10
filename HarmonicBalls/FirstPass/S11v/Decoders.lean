import HarmonicBalls.FirstPass.S11n
import HarmonicBalls.FirstPass.S11s.Uniqueness

/-!
# Measurable-function principle for the canonical decoders (fp-S11v, operator note 01:44 UTC, §4)

Coordinatewise almost-sure equality `X ω i = Y ω i` (for every canonical index `i`, the index outside the
almost-sure quantifier) implies almost-sure equality of every measurable decoder output:
`K (X ω) = K (Y ω)` for a kernel `K` of measures on `ℂ` and `d (X ω) = d (Y ω)` for a Borel metric decoder `d`
(`notes/fp-gaps/CHATGPT-n1-hAff-hhom.md`, §4, "The measurable-function principle").

Proof. The sets `S` with `X ω ∈ S ↔ Y ω ∈ S` almost surely form a σ-algebra (`coordAeSigma`) containing the
coordinate cylinders, hence the product σ-algebra of `CanonSpace = CanonIdx → ℝ`. No measurability of `X` or `Y` is
used. A measurable map into a second countable T0 space is then a.s. equal along `X` and `Y` (countable basis). Measure
values `K L S` on a countable π-system generating the Borel sets of `ℂ` (`exists_countable_pi_system_complex`) determine
the measures `K L` (`measure_ext_of_complex_pi`). The metric values are compared on a countable dense set of `ℂ × ℂ`
and then by continuity.
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal

/-- The σ-algebra of sets `S ⊆ CanonSpace` with `X ω ∈ S ↔ Y ω ∈ S` almost surely. -/
@[instance_reducible]
def coordAeSigma {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X Y : Ω → S11n.CanonSpace) :
    MeasurableSpace S11n.CanonSpace where
  MeasurableSet' S := ∀ᵐ ω ∂P, (X ω ∈ S ↔ Y ω ∈ S)
  measurableSet_empty := ae_of_all _ fun ω => by simp
  measurableSet_compl S hS := hS.mono fun ω hω => not_congr hω
  measurableSet_iUnion f hf := by
    filter_upwards [ae_all_iff.2 hf] with ω hω
    simp only [mem_iUnion]
    exact exists_congr fun n => hω n

/-- Coordinatewise almost-sure equality gives almost-sure agreement on every measurable set of `CanonSpace`. -/
theorem coordAe_mem_iff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X Y : Ω → S11n.CanonSpace}
    (hXY : ∀ i : CanonIdx, (fun ω => X ω i) =ᵐ[P] (fun ω => Y ω i))
    {S : Set S11n.CanonSpace} (hS : MeasurableSet S) : ∀ᵐ ω ∂P, (X ω ∈ S ↔ Y ω ∈ S) := by
  have hle : (MeasurableSpace.pi : MeasurableSpace S11n.CanonSpace) ≤ coordAeSigma P X Y := by
    refine iSup_le fun i => ?_
    have hm : @Measurable S11n.CanonSpace ℝ (coordAeSigma P X Y) _ (fun x => x i) := by
      intro B _
      change ∀ᵐ ω ∂P, (X ω ∈ (fun x : S11n.CanonSpace => x i) ⁻¹' B ↔ Y ω ∈ (fun x : S11n.CanonSpace => x i) ⁻¹' B)
      filter_upwards [hXY i] with ω hω
      have hω' : X ω i = Y ω i := hω
      simp only [Set.mem_preimage, hω']
    exact hm.comap_le
  exact hle S hS

/-- **Measurable-function principle.** If `X` and `Y` agree coordinatewise almost surely and `F` is measurable into a
second countable T0 space, then `F (X ω) = F (Y ω)` almost surely. -/
theorem ae_eq_comp_of_coordwise {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X Y : Ω → S11n.CanonSpace}
    (hXY : ∀ i : CanonIdx, (fun ω => X ω i) =ᵐ[P] (fun ω => Y ω i))
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [T0Space E]
    {F : S11n.CanonSpace → E} (hF : Measurable F) : ∀ᵐ ω ∂P, F (X ω) = F (Y ω) := by
  obtain ⟨Bs, hBsc, -, hbas⟩ := TopologicalSpace.exists_countable_basis E
  have hU : ∀ᵐ ω ∂P, ∀ U ∈ Bs, (F (X ω) ∈ U ↔ F (Y ω) ∈ U) := by
    rw [ae_ball_iff hBsc]
    intro U hU
    exact coordAe_mem_iff hXY (hF (hbas.isOpen hU).measurableSet)
  filter_upwards [hU] with ω hω
  by_contra hne
  obtain ⟨V, hVo, hxor⟩ := exists_isOpen_xor_mem hne
  rcases hxor with ⟨hx, hy⟩ | ⟨hy, hx⟩
  · obtain ⟨B, hB, hxB, hBV⟩ := hbas.exists_subset_of_mem_open hx hVo
    exact hy (hBV ((hω B hB).1 hxB))
  · obtain ⟨B, hB, hyB, hBV⟩ := hbas.exists_subset_of_mem_open hy hVo
    exact hx (hBV ((hω B hB).2 hyB))

/-- Almost-sure equality of the measure decoder: `K (X ω) = K (Y ω)` almost surely. -/
theorem ae_kernel_eq_of_coordwise {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X Y : Ω → S11n.CanonSpace}
    (hXY : ∀ i : CanonIdx, (fun ω => X ω i) =ᵐ[P] (fun ω => Y ω i))
    (K : Kernel S11n.CanonSpace ℂ) (hKf : ∀ L, IsFiniteMeasureOnCompacts (K L)) :
    ∀ᵐ ω ∂P, K (X ω) = K (Y ω) := by
  obtain ⟨C, hCc, hpi, hgen, B, hBC, hcov, hcpt⟩ := exists_countable_pi_system_complex
  have hCm : ∀ S ∈ C, MeasurableSet S := fun S hS => by
    have hle : MeasurableSpace.generateFrom C ≤ (inferInstance : MeasurableSpace ℂ) := hgen.le
    exact hle _ (MeasurableSpace.measurableSet_generateFrom hS)
  have := hCc.to_subtype
  have hall : ∀ᵐ ω ∂P, ∀ S : C, K (X ω) S = K (Y ω) S := by
    refine ae_all_iff.2 fun S => ?_
    exact ae_eq_comp_of_coordwise hXY (F := fun L => K L S) (K.measurable_coe (hCm S S.2))
  filter_upwards [hall] with ω hω
  have := hKf (X ω)
  exact measure_ext_of_complex_pi C hpi hgen B hBC hcov hcpt (fun S hS => hω ⟨S, hS⟩)

/-- Almost-sure equality of the metric decoder: `d (X ω) = d (Y ω)` almost surely. -/
theorem ae_decoder_eq_of_coordwise {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X Y : Ω → S11n.CanonSpace}
    (hXY : ∀ i : CanonIdx, (fun ω => X ω i) =ᵐ[P] (fun ω => Y ω i))
    (d : S11n.CanonSpace → ContinuousMap (ℂ × ℂ) ℝ) (hd : Measurable d) :
    ∀ᵐ ω ∂P, d (X ω) = d (Y ω) := by
  obtain ⟨Q, hQc, hQd⟩ := TopologicalSpace.exists_countable_dense (ℂ × ℂ)
  have := hQc.to_subtype
  have hall : ∀ᵐ ω ∂P, ∀ q : Q, d (X ω) q = d (Y ω) q := by
    refine ae_all_iff.2 fun q => ?_
    exact ae_eq_comp_of_coordwise hXY (F := fun L => d L q)
      ((continuous_eval_const (q : ℂ × ℂ)).measurable.comp hd)
  filter_upwards [hall] with ω hω
  have hfun : ⇑(d (X ω)) = ⇑(d (Y ω)) :=
    Continuous.ext_on hQd (d (X ω)).continuous (d (Y ω)).continuous (fun q hq => hω ⟨q, hq⟩)
  exact ContinuousMap.ext fun x => congrFun hfun x

/-- **Decoder principle (operator note 01:44 UTC, §4).** If `X` and `Y` agree coordinatewise almost surely, then almost
surely the measure decoder `K` and the metric decoder `d` take the same values at `X ω` and `Y ω`. -/
theorem ae_decoders_eq_of_coordwise_ae_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Y : Ω → S11n.CanonSpace}
    (hXY : ∀ i : CanonIdx, (fun ω => X ω i) =ᵐ[P] (fun ω => Y ω i))
    (K : Kernel S11n.CanonSpace ℂ) (hKf : ∀ L, IsFiniteMeasureOnCompacts (K L))
    (d : S11n.CanonSpace → ContinuousMap (ℂ × ℂ) ℝ) (hd : Measurable d) :
    ∀ᵐ ω ∂P, K (X ω) = K (Y ω) ∧ d (X ω) = d (Y ω) := by
  filter_upwards [ae_kernel_eq_of_coordwise hXY K hKf, ae_decoder_eq_of_coordwise hXY d hd] with ω h1 h2
  exact ⟨h1, h2⟩

end HarmonicBalls
