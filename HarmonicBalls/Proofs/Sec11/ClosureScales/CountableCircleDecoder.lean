import Mathlib

/-!
# Countable circle-profile decoder

`J = {p : ℝ × ℂ // 0 < p.1}` is `(0,∞) × ℂ` with its inherited topology, and `C(J, ℝ)` carries the
compact-open topology (uniform convergence on compact sets) with its Borel σ-algebra. For a countable index
type `I` and `q : I → J` with dense range, the restriction map `Φ f = (f (q i))_{i ∈ I}` is continuous and
injective. The decoder inverts `Φ` on valid codes (the image of `Φ`) and returns `0` on invalid codes, as required.

Route. `C(J, ℝ)` is a Polish space: it is second countable (Mathlib's instance, from the local compactness and
second countability of `J`) and completely metrizable through its compact-convergence uniformity, which is
complete and countably generated (Mathlib's `ContinuousMap.compactConvergenceUniformSpace`). An injective
continuous map out of a Polish space is a measurable embedding (Lusin–Souslin; Mathlib's
`Continuous.measurableEmbedding`), so `Φ` is a measurable embedding and `Function.extend Φ id 0` is the
decoder. The written construction (uniform continuity on the boxes `K_m`, gluing of the local
extensions, limits of coded evaluations) is not formalized here, because the existence statement does not
need it. The hypotheses `(1,0) ∈ range q` and the compact-density condition on the boxes `K_m` (integers
`m ≥ 2`, indexed by `m : ℕ`) are kept as stated in the source; the proof uses only `DenseRange q`.
-/

noncomputable section

open Set Filter

namespace HarmonicBalls

/-- The index domain `J = (0,∞) × ℂ` of the circle profiles, as the subtype `{p : ℝ × ℂ // 0 < p.1}`
with its inherited topology. -/
abbrev CircleDomain : Type := {p : ℝ × ℂ // 0 < p.1}

/-- The compact box `K_m = [1/m, m] × closedBall 0 m` of `CircleDomain`, for an integer `m ≥ 2`. -/
def circleBox (m : ℕ) : Set CircleDomain :=
  {p | 1 / (m : ℝ) ≤ p.1.1 ∧ p.1.1 ≤ m ∧ ‖p.1.2‖ ≤ m}

/-- `J = (0,∞) × ℂ` is open in `ℝ × ℂ`, hence locally compact. -/
instance : LocallyCompactSpace CircleDomain :=
  IsOpen.locallyCompactSpace (s := {p : ℝ × ℂ | 0 < p.1}) (isOpen_lt continuous_const continuous_fst)

/-- `C(J, ℝ)` with the compact-open topology is a Polish space: second countable (from the local compactness
and second countability of `J`), and completely metrizable through its complete, countably generated
compact-convergence uniformity (whose topology is the compact-open topology by construction). -/
instance : PolishSpace C(CircleDomain, ℝ) where
  toSecondCountableTopology := inferInstance
  toIsCompletelyMetrizableSpace := TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable

/-- The restriction map `f ↦ (f (q i))_{i ∈ I}` from `C(J, ℝ)` to `I → ℝ` is continuous. -/
theorem continuous_circleRestrict {I : Type*} (q : I → CircleDomain) :
    Continuous (fun (f : C(CircleDomain, ℝ)) (i : I) => f (q i)) :=
  continuous_pi fun i => continuous_eval_const (q i)

/-- For a dense range `q`, the restriction map `f ↦ (f (q i))_{i ∈ I}` is injective: two continuous functions
on `J` that agree on the dense set `range q` are equal. -/
theorem injective_circleRestrict {I : Type*} {q : I → CircleDomain} (hq : DenseRange q) :
    Function.Injective (fun (f : C(CircleDomain, ℝ)) (i : I) => f (q i)) := by
  intro f g hfg
  have hfun : ⇑f = ⇑g := by
    refine Continuous.ext_on hq f.continuous g.continuous ?_
    rintro _ ⟨i, rfl⟩
    exact congrFun hfg i
  exact ContinuousMap.ext (congrFun hfun)

/-- **Existence of the countable circle-profile decoder**.

Let `I` be countable and `q : I → J` have dense range, with `(1,0)` in its range and the compact-density
condition `K_m ⊆ closure (range q ∩ K_m)` for every integer `m ≥ 2`. Then there is a Borel map
`decode : (I → ℝ) → C(J, ℝ)` which inverts the restriction `f ↦ (f (q i))_i` on valid codes, and returns
`0` on invalid codes. The hypotheses `_h_one` and `_h_box` are the source's conditions; the proof does not
use them, since `DenseRange q` alone gives the measurable embedding. -/
theorem exists_measurable_circle_decoder {I : Type*} [Countable I]
    (q : I → CircleDomain) (hq : DenseRange q)
    (_h_one : ∃ i, (q i).1 = ((1 : ℝ), (0 : ℂ)))
    (_h_box : ∀ m : ℕ, 2 ≤ m → circleBox m ⊆ closure (Set.range q ∩ circleBox m)) :
    ∃ decode : (I → ℝ) → C(CircleDomain, ℝ), Measurable decode ∧
      (∀ f : C(CircleDomain, ℝ), decode (fun i => f (q i)) = f) ∧
      (∀ a : I → ℝ, (¬ ∃ f : C(CircleDomain, ℝ), ∀ i, f (q i) = a i) → decode a = 0) := by
  have hme := (continuous_circleRestrict q).measurableEmbedding (injective_circleRestrict hq)
  refine ⟨Function.extend (fun (f : C(CircleDomain, ℝ)) (i : I) => f (q i)) id (fun _ => 0),
    hme.measurable_extend measurable_id measurable_const, fun f => ?_, fun a ha => ?_⟩
  · exact (injective_circleRestrict hq).extend_apply id _ f
  · refine Function.extend_apply' id _ a ?_
    rintro ⟨f, hf⟩
    exact ha ⟨f, fun i => congrFun hf i⟩

/-- The circle-profile decoder: on a valid code it returns the continuous function on
`J` with those values on `range q` (unique when `q` has dense range), and on an invalid code it returns `0`. -/
def circleDecoder {I : Type*} (q : I → CircleDomain) : (I → ℝ) → C(CircleDomain, ℝ) :=
  Function.extend (fun (f : C(CircleDomain, ℝ)) (i : I) => f (q i)) id (fun _ => 0)

/-- The decoder is Borel for countable `I` and dense `q`. -/
theorem circleDecoder_measurable {I : Type*} [Countable I] {q : I → CircleDomain} (hq : DenseRange q) :
    Measurable (circleDecoder q) :=
  ((continuous_circleRestrict q).measurableEmbedding (injective_circleRestrict hq)).measurable_extend
    measurable_id measurable_const

/-- Left inverse: decoding the restriction of `f` returns `f`. -/
theorem circleDecoder_restrict {I : Type*} {q : I → CircleDomain} (hq : DenseRange q)
    (f : C(CircleDomain, ℝ)) : circleDecoder q (fun i => f (q i)) = f :=
  (injective_circleRestrict hq).extend_apply id _ f

/-- Invalid codes are sent to `0`. -/
theorem circleDecoder_of_not_valid {I : Type*} (q : I → CircleDomain) (a : I → ℝ)
    (h : ¬ ∃ f : C(CircleDomain, ℝ), ∀ i, f (q i) = a i) : circleDecoder q a = 0 := by
  refine Function.extend_apply' id _ a ?_
  rintro ⟨f, hf⟩
  exact h ⟨f, fun i => congrFun hf i⟩

/-- Complete characterization of valid codes: `a` is the restriction of a continuous function on `J` if and
only if the decoded function `circleDecoder q a` reproduces `a` on `range q`. -/
theorem circleDecoder_valid_iff {I : Type*} {q : I → CircleDomain} (hq : DenseRange q) (a : I → ℝ) :
    (∃ f : C(CircleDomain, ℝ), ∀ i, f (q i) = a i) ↔ ∀ i, circleDecoder q a (q i) = a i := by
  constructor
  · rintro ⟨f, hf⟩
    have ha : a = fun i => f (q i) := funext fun i => (hf i).symm
    subst ha
    intro i
    rw [circleDecoder_restrict hq f]
  · intro h
    exact ⟨circleDecoder q a, h⟩

end HarmonicBalls
