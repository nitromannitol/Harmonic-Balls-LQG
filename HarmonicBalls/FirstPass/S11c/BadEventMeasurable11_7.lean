import HarmonicBalls.Draft.Section11
import HarmonicBalls.Steps.Sec11.PinchJointMeasure

/-!
# Lemma 11.7: joint measurability of the cone-mass event in the sample and the root

For an s-finite kernel `κ` from a measurable space `Ω` to measures on `ℂ` (the random measure `μ_ω`, or a decoded
version of it), the set `{(ω, z) | coneMassEvent (κ ω) Q M r z}` is measurable, for any measurable cone `Q`. This is the
measurability of the single local bad set once the random measure is a kernel.

Ingredients: `measurable_kernel_annulusGreenPotentialSup` (Steps/Sec11/PinchJointMeasure.lean:85, the extended Green
potential supremum over the annulus, jointly measurable in the sample and the centre), and the kernel section-mass lemma
proved here (Mathlib `Measurable.lintegral_kernel_prod_right'`). No sector algebra is needed: the annulus-and-cone set is
the section of a measurable set `G ⊆ ℂ × ℂ` at the root.
-/

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

namespace HarmonicBalls.S11c

/-- The mass of the section `{y | (z, y) ∈ G}` of a measurable set `G ⊆ ℂ × ℂ` under `κ ω` is jointly measurable in
`(ω, z)`. -/
theorem measurable_kernel_section_mass {Ω : Type*} [MeasurableSpace Ω] (κ : Kernel Ω ℂ) [IsSFiniteKernel κ]
    {G : Set (ℂ × ℂ)} (hG : MeasurableSet G) :
    Measurable (fun p : Ω × ℂ => κ p.1 {y | (p.2, y) ∈ G}) := by
  set f : (Ω × ℂ) × ℂ → ℝ≥0∞ := fun q => G.indicator (fun _ => (1 : ℝ≥0∞)) (q.1.2, q.2) with hf_def
  have hf : Measurable f :=
    (measurable_const.indicator hG).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have key := Measurable.lintegral_kernel_prod_right' (κ := κ.comap Prod.fst measurable_fst) hf
  convert key using 1
  funext p
  rw [Kernel.comap_apply]
  have hsec : MeasurableSet {y : ℂ | (p.2, y) ∈ G} :=
    hG.preimage (measurable_const.prodMk measurable_id)
  rw [← lintegral_indicator_one hsec]
  rfl

/-- The cone-mass event `coneMassEvent (κ ω) Q M r z` (Draft/Section11.lean:72) is a jointly measurable set in the sample
and the root, for an s-finite kernel `κ` and a measurable set `Q` (every cone of `IsCone` is measurable). -/
theorem measurableSet_coneMassEvent {Ω : Type*} [MeasurableSpace Ω] (κ : Kernel Ω ℂ) [IsSFiniteKernel κ]
    {Q : Set ℂ} (hQ : MeasurableSet Q) (M r : ℝ) :
    MeasurableSet {p : Ω × ℂ | coneMassEvent (κ p.1) Q M r p.2} := by
  set G : Set (ℂ × ℂ) := {q | q.2 ∈ annulus q.1 r (2 * r) ∧ q.2 - q.1 ∈ Q} with hGdef
  have hd : Measurable (fun q : ℂ × ℂ => dist q.2 q.1) :=
    (continuous_snd.dist continuous_fst).measurable
  have hann : MeasurableSet {q : ℂ × ℂ | q.2 ∈ annulus q.1 r (2 * r)} := by
    have heq : {q : ℂ × ℂ | q.2 ∈ annulus q.1 r (2 * r)} =
        {q | dist q.2 q.1 < 2 * r} ∩ {q | r < dist q.2 q.1} := by
      ext q
      simp [annulus, Metric.mem_ball, Metric.mem_closedBall, not_le]
    rw [heq]
    exact (measurableSet_lt hd measurable_const).inter (measurableSet_lt measurable_const hd)
  have hcone : MeasurableSet {q : ℂ × ℂ | q.2 - q.1 ∈ Q} :=
    hQ.preimage (measurable_snd.sub measurable_fst)
  have hG : MeasurableSet G := hann.inter hcone
  have hsec : ∀ z : ℂ, {y : ℂ | (z, y) ∈ G} = annulus z r (2 * r) ∩ coneAt Q z := by
    intro z
    ext y
    simp only [hGdef, mem_ofPred_eq, mem_inter_iff, coneAt, mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, y - z, h2, by ring⟩
    · rintro ⟨h1, x, hx, hxy⟩
      refine ⟨h1, ?_⟩
      rw [← hxy]
      simpa using hx
  have hset : {p : Ω × ℂ | coneMassEvent (κ p.1) Q M r p.2} =
      {p : Ω × ℂ | ENNReal.ofReal M * annulusGreenPotentialSup (κ p.1) p.2 (3 * r) (6 * r) ≤
        κ p.1 {y : ℂ | (p.2, y) ∈ G}} := by
    ext p
    simp only [mem_ofPred_eq, coneMassEvent, hsec]
  rw [hset]
  exact measurableSet_le ((measurable_kernel_annulusGreenPotentialSup κ (3 * r) (6 * r)).const_mul _)
    (measurable_kernel_section_mass κ hG)

end HarmonicBalls.S11c
