import HarmonicBalls.Defs.LQGMetric

/-!
# Measurability of a pointwise identity set

Generic measure theory for the Cameron-Martin transfer of the metric identity (step (d) of the rooted identity (20),
`ae_mem_addFunPairing_of_ae_mem` in CMShift.lean needs a measurable set of
distributions). The identity of (18) and (20) is required for all endpoints `p ∈ V × V`, an uncountable family.
If both sides are continuous in the endpoint for the distributions in a measurable set `S`, the set of distributions
where they agree at every endpoint is measurable (on `S`): it equals the intersection over a countable dense set of
endpoints. The continuity is only assumed on `S`, since the metric side need not be continuous off `S`.
-/

namespace HarmonicBalls

open MeasureTheory Set

/-- Two families `F T x`, `G T x` of `ℝ≥0∞`-values, measurable in `T` for each endpoint `x`, and continuous in `x` for
each `T ∈ S` with `S` measurable: the set of `T` such that `T ∈ S` implies `F T = G T` on the whole space is measurable. -/
theorem measurableSet_forall_eq_of_continuous {Ψ : Type*} [MeasurableSpace Ψ] {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.SeparableSpace X] (S : Set Ψ) (hS : MeasurableSet S) (F G : Ψ → X → ENNReal)
    (hF : ∀ T ∈ S, Continuous (F T)) (hG : ∀ T ∈ S, Continuous (G T))
    (hFm : ∀ x, Measurable fun T => F T x) (hGm : ∀ x, Measurable fun T => G T x) :
    MeasurableSet {T | T ∈ S → ∀ x, F T x = G T x} := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense X
  have hcore : MeasurableSet (⋂ x ∈ D, {T | F T x = G T x}) :=
    MeasurableSet.biInter hDc fun x _ => measurableSet_eq_fun (hFm x) (hGm x)
  have hset : {T | T ∈ S → ∀ x, F T x = G T x} = Sᶜ ∪ ⋂ x ∈ D, {T | F T x = G T x} := by
    ext T
    constructor
    · intro h
      have h0 : T ∈ S → ∀ x, F T x = G T x := h
      by_cases hT : T ∈ S
      · refine Or.inr ?_
        simp only [mem_iInter]
        intro x _
        exact h0 hT x
      · exact Or.inl hT
    · intro h
      have h1 : T ∈ S → ∀ x, F T x = G T x := by
        intro hTS
        rcases h with hT | hI
        · exact absurd hTS hT
        · have h' : ∀ x ∈ D, F T x = G T x := fun x hx => mem_iInter₂.1 hI x hx
          have hfg : F T = G T := Continuous.ext_on hDd (hF T hTS) (hG T hTS) h'
          exact fun x => congrFun hfg x
      exact h1
  rw [hset]
  exact hS.compl.union hcore

/-- The identity required on a countable set `D` of endpoints is a measurable set of distributions, when each side is
measurable in the distribution for each endpoint. This is the form used for the Cameron-Martin transfer of the metric
identity: the countable set is dense in `V × V`, and the identity on all of `V × V` follows by continuity of both sides
(`Continuous.ext_on`). -/
theorem measurableSet_forall_mem_eq {Ψ : Type*} [MeasurableSpace Ψ] {X : Type*} [TopologicalSpace X] (D : Set X)
    (hD : D.Countable) (F G : Ψ → X → ENNReal) (hFm : ∀ x, Measurable fun T => F T x)
    (hGm : ∀ x, Measurable fun T => G T x) :
    MeasurableSet {T | ∀ x ∈ D, F T x = G T x} := by
  have hset : {T | ∀ x ∈ D, F T x = G T x} = ⋂ x ∈ D, {T | F T x = G T x} := by
    ext T
    constructor
    · intro h
      have h0 : ∀ x ∈ D, F T x = G T x := h
      exact mem_iInter₂.2 fun x hx => h0 x hx
    · intro h
      have h1 : ∀ x ∈ D, F T x = G T x := fun x hx => mem_iInter₂.1 h x hx
      exact h1
  rw [hset]
  exact MeasurableSet.biInter hD fun x _ => measurableSet_eq_fun (hFm x) (hGm x)

end HarmonicBalls
