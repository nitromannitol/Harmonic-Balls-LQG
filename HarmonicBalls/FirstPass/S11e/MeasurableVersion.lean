import Mathlib

/-!
# Measurable versions of random continuous metrics

Generic measure-theoretic fact used for Lemma 11.15 (paper `lemma:first-event-proof`, line 3277; certificate events
`Ẽ₁` of lines 3325-3357): a random function `D : Ω → ℂ × ℂ → ℝ` which is almost surely continuous and whose evaluation at
each single point is almost everywhere measurable has a version `D'` whose evaluations at every point are measurable, and
which agrees with `D` almost surely, at every point simultaneously.

Proof (countable representation). Fix a countable dense `S ⊆ ℂ × ℂ` and measurable versions `G s` of `D · s`, `s ∈ S`;
almost surely `G s ω = D ω s` for all `s ∈ S`. For `q ∈ ℂ × ℂ` choose a sequence `x_n ∈ S` with `x_n → q`, and put
`D' ω q = limsup_n G (x_n) ω`. This is measurable, and equals `D ω q` whenever `D ω` is continuous and `G = D` on `S`.
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology Set

/-- A measurable version, at every point, of an a.s. continuous random function whose point evaluations are a.e.
measurable; it agrees with `D` almost surely, at every point. -/
theorem exists_measurable_version_of_continuous
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D : Ω → ℂ × ℂ → ℝ)
    (hcont : ∀ᵐ ω ∂P, Continuous (D ω))
    (hae : ∀ q : ℂ × ℂ, AEMeasurable (fun ω => D ω q) P) :
    ∃ D' : Ω → ℂ × ℂ → ℝ, (∀ q, Measurable fun ω => D' ω q) ∧ ∀ᵐ ω ∂P, ∀ q, D' ω q = D ω q := by
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense (ℂ × ℂ)
  have : Countable S := hSc.to_subtype
  have hv : ∀ s : S, ∃ g : Ω → ℝ, Measurable g ∧ (fun ω => D ω s.1) =ᵐ[P] g :=
    fun s => ⟨(hae s.1).mk _, (hae s.1).measurable_mk, (hae s.1).ae_eq_mk⟩
  choose G hGm hGa using hv
  have hS : ∀ᵐ ω ∂P, ∀ s : S, G s ω = D ω s.1 :=
    ae_all_iff.2 fun s => (hGa s).mono fun ω h => h.symm
  have hdense : ∀ q : ℂ × ℂ, ∃ x : ℕ → S, Tendsto (fun n => (x n).1) atTop (𝓝 q) := by
    intro q
    have hq : q ∈ closure (S : Set (ℂ × ℂ)) := by
      rw [hSd.closure_eq]
      exact mem_univ q
    obtain ⟨x, hxS, hx⟩ := mem_closure_iff_seq_limit.mp hq
    exact ⟨fun n => ⟨x n, hxS n⟩, hx⟩
  choose seq hseq using hdense
  refine ⟨fun ω q => limsup (fun n => G (seq q n) ω) atTop, ?_, ?_⟩
  · intro q
    exact Measurable.limsup (fun n => hGm (seq q n))
  · filter_upwards [hcont, hS] with ω hωc hωS
    intro q
    have hlim : Tendsto (fun n => D ω (seq q n).1) atTop (𝓝 (D ω q)) :=
      (hωc.tendsto q).comp (hseq q)
    have heq : (fun n => G (seq q n) ω) = fun n => D ω (seq q n).1 :=
      funext fun n => hωS (seq q n)
    show limsup (fun n => G (seq q n) ω) atTop = D ω q
    rw [heq]
    exact hlim.limsup_eq

#print axioms exists_measurable_version_of_continuous

end HarmonicBalls
