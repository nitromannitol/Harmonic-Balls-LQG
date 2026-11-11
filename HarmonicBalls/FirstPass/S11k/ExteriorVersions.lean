import HarmonicBalls.Steps.Sec11.CountableCoordinateObservables

/-!
# Exterior versions of field observables

Two measure-theoretic lemmas for the exterior versions of Lemma 11.16 ("every scalar full-exterior-field-measurable variable has an almost-surely equal version measurable for the raw
zero-mean exterior code", and the limit (17) `(h^α, φ) = lim_j (h^α, φ - m_φ ψ_j)` almost surely).

* `exists_measurable_version_of_coordinate_versions`: if each real coordinate `X · i` of a family has an `m`-measurable
  almost-sure version, then every observable measurable for `comap X` has an `m`-measurable almost-sure version. This is the
  Doob–Dynkin factorisation (`Measurable.exists_eq_measurable_comp`) combined with the countable-coordinate lemma
  `ae_eq_measurable_comp_of_coordinatewise_ae_eq` (`Steps/Sec11/CountableCoordinateObservables.lean`).
* `exists_measurable_limsup_version`: an almost surely convergent sequence of `m`-measurable real functions has an
  `m`-measurable almost-sure limit (the limit superior, `Measurable.limsup`).

Both lemmas are pure measure theory; no field input.
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- A measurable observable of a real-valued family has an `m`-measurable almost-sure version, provided each coordinate
of the family does. The coordinates `X · i` are the field pairings (or their exterior limits), and `m` is the zero-mean
exterior sigma-algebra. -/
theorem exists_measurable_version_of_coordinate_versions {ι : Type*} {P : Measure Ω} {m : MeasurableSpace Ω}
    (X : Ω → ι → ℝ)
    (hY : ∀ i, ∃ Y : Ω → ℝ, Measurable[m] Y ∧ ∀ᵐ ω ∂P, X ω i = Y ω)
    {E : Type*} [MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]
    [MeasurableSpace.CountablySeparated E]
    (G : Ω → E) (hG : Measurable[MeasurableSpace.comap X inferInstance] G) :
    ∃ G' : Ω → E, Measurable[m] G' ∧ ∀ᵐ ω ∂P, G' ω = G ω := by
  choose Y hYm hYae using hY
  obtain ⟨F, hF, hGF⟩ := hG.exists_eq_measurable_comp
  let Ŷ : Ω → ι → ℝ := fun ω i => Y i ω
  have hŶ : Measurable[m] Ŷ := measurable_pi_iff.2 fun i => hYm i
  refine ⟨F ∘ Ŷ, fun s hs => hŶ (hF hs), ?_⟩
  have hae := @ae_eq_measurable_comp_of_coordinatewise_ae_eq Ω ι E mΩ _ _ P (fun _ => ℝ) _ X Ŷ
    (fun i => hYae i) F hF
  filter_upwards [hae] with ω hω
  rw [Function.comp_apply, hGF]
  exact hω.symm

/-- An almost surely convergent sequence of `m`-measurable real functions has an `m`-measurable almost-sure limit: the
limit superior. This is the limit step (17) of the exterior versions. -/
theorem exists_measurable_limsup_version {P : Measure Ω} {m : MeasurableSpace Ω}
    (X : ℕ → Ω → ℝ) (hX : ∀ n, Measurable[m] (X n))
    (hconv : ∀ᵐ ω ∂P, ∃ L : ℝ, Tendsto (fun n => X n ω) atTop (𝓝 L)) :
    ∃ Y : Ω → ℝ, Measurable[m] Y ∧ ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω)) := by
  refine ⟨fun ω => limsup (fun n => X n ω) atTop, Measurable.limsup hX, ?_⟩
  filter_upwards [hconv] with ω hω
  obtain ⟨L, hL⟩ := hω
  have h := hL.limsup_eq
  show Tendsto (fun n => X n ω) atTop (𝓝 (limsup (fun n => X n ω) atTop))
  rw [h]
  exact hL


end HarmonicBalls
