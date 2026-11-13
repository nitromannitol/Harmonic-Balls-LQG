import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# The measurable event of the local-agreement argument (step 4 of the route for `hN2`)

The local-agreement route for `LocalMetricReplacementStmt` produces a measurable set `A` of local observations `o` of a
disk `D` on which the decoded function `d o : ℂ → ℂ → ℝ≥0∞` has three properties, each checked on a countable set `S`
of points (and countably many indices):

* `eventMetricAxioms`: `d o x x = 0`, `d o x y = d o y x` and the triangle inequality for `x, y, w ∈ S`;
* `eventChains`: the chain property on `S`: for `x, y ∈ S` and `ε ∈ ℚ>0` there is `n` such that for every `δ ∈ ℚ>0` there
  is a `δ`-fine chain from `x` to `y` through `S` inside `K n` whose `d o`-length is at most `d o x y + ε`;
* `eventLocalAgreement`: for each index `i` of a countable family and each admissible element `k` of a countable family
  of sets `T i k`, there is a rational `η > 0` such that `d o u v = F i o u v` for `u, v ∈ S ∩ T i k` with `‖u - v‖ < η`.

Each is a countable intersection and union of sets `{o | f o ≤ g o}` and `{o | f o = g o}` with `f, g` measurable, so the
event is measurable once every `o ↦ d o x y` and `o ↦ F i o u v` is (`measurableSet_eventA`). `extendDist` and
`measurable_extendDist` turn a measurable family of continuous functions on `Z ⊆ ℂ × ℂ` into such a family `d`.
-/

namespace HarmonicBalls

open MeasureTheory Set
open scoped ENNReal

namespace LocalAgreementEvent

variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurableSet_forall_mem {β : Type*} {S : Set β} (hS : S.Countable) {P : β → Ω → Prop}
    (h : ∀ x ∈ S, MeasurableSet {o | P x o}) : MeasurableSet {o | ∀ x ∈ S, P x o} := by
  have : {o | ∀ x ∈ S, P x o} = ⋂ x ∈ S, {o | P x o} := by ext o; simp
  rw [this]
  exact MeasurableSet.biInter hS h

theorem measurableSet_forall {ι : Type*} [Countable ι] {P : ι → Ω → Prop}
    (h : ∀ i, MeasurableSet {o | P i o}) : MeasurableSet {o | ∀ i, P i o} := by
  have : {o | ∀ i, P i o} = ⋂ i, {o | P i o} := by ext o; simp
  rw [this]
  exact MeasurableSet.iInter h

theorem measurableSet_exists {ι : Type*} [Countable ι] {P : ι → Ω → Prop}
    (h : ∀ i, MeasurableSet {o | P i o}) : MeasurableSet {o | ∃ i, P i o} := by
  have : {o | ∃ i, P i o} = ⋃ i, {o | P i o} := by ext o; simp
  rw [this]
  exact MeasurableSet.iUnion h

theorem measurableSet_imp_const (p : Prop) {Q : Ω → Prop} (h : p → MeasurableSet {o | Q o}) :
    MeasurableSet {o | p → Q o} := by
  by_cases hp : p
  · simpa [hp] using h hp
  · simp [hp]

theorem measurableSet_and_const (p : Prop) {Q : Ω → Prop} (h : p → MeasurableSet {o | Q o}) :
    MeasurableSet {o | p ∧ Q o} := by
  by_cases hp : p
  · simpa [hp] using h hp
  · simp [hp]

theorem measurableSet_eq_ennreal {f g : Ω → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    MeasurableSet {o | f o = g o} := by
  have : {o | f o = g o} = {o | f o ≤ g o} ∩ {o | g o ≤ f o} := by
    ext o; simp [le_antisymm_iff]
  rw [this]
  exact (measurableSet_le hf hg).inter (measurableSet_le hg hf)

end LocalAgreementEvent

open LocalAgreementEvent

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **A1.** Vanishing on the diagonal, symmetry and the triangle inequality of `d o` on `S`. -/
def eventMetricAxioms (S : Set ℂ) (d : Ω → ℂ → ℂ → ℝ≥0∞) : Set Ω :=
  {o | ∀ x ∈ S, d o x x = 0} ∩ {o | ∀ x ∈ S, ∀ y ∈ S, d o x y = d o y x} ∩
    {o | ∀ x ∈ S, ∀ y ∈ S, ∀ w ∈ S, d o x w ≤ d o x y + d o y w}

/-- **A2.** The chain property of `d o` on `S`, with the compact windows `K n`. -/
def eventChains (S : Set ℂ) (K : ℕ → Set ℂ) (d : Ω → ℂ → ℂ → ℝ≥0∞) : Set Ω :=
  {o | ∀ x ∈ S, ∀ y ∈ S, ∀ ε : ℚ, 0 < ε → ∃ n : ℕ, ∀ δ : ℚ, 0 < δ → ∃ N : ℕ, ∃ m : Fin (N + 1) → S,
      (m 0 : ℂ) = x ∧ (m (Fin.last N) : ℂ) = y ∧ (∀ i, (m i : ℂ) ∈ K n) ∧
      (∀ i : Fin N, ‖(m i.castSucc : ℂ) - (m i.succ : ℂ)‖ < δ) ∧
      ∑ i : Fin N, d o (m i.castSucc) (m i.succ) ≤ d o x y + ENNReal.ofReal ε}

/-- **A3.** Local agreement of `d o` with the family `F i o` on the sets `T i k` (`k` admissible for `i`), on `S`. -/
def eventLocalAgreement {ι κ : Type*} (S : Set ℂ) (adm : ι → κ → Prop) (T : ι → κ → Set ℂ)
    (d : Ω → ℂ → ℂ → ℝ≥0∞) (F : ι → Ω → ℂ → ℂ → ℝ≥0∞) : Set Ω :=
  {o | ∀ i k, adm i k → ∃ η : ℚ, 0 < η ∧ ∀ u ∈ S, ∀ v ∈ S, u ∈ T i k → v ∈ T i k → ‖u - v‖ < η →
      d o u v = F i o u v}

/-- The event `A = A1 ∩ A2 ∩ A3`. -/
def eventA {ι κ : Type*} (S : Set ℂ) (K : ℕ → Set ℂ) (adm : ι → κ → Prop) (T : ι → κ → Set ℂ)
    (d : Ω → ℂ → ℂ → ℝ≥0∞) (F : ι → Ω → ℂ → ℂ → ℝ≥0∞) : Set Ω :=
  eventMetricAxioms S d ∩ eventChains S K d ∩ eventLocalAgreement S adm T d F

theorem measurableSet_eventMetricAxioms {S : Set ℂ} (hS : S.Countable) {d : Ω → ℂ → ℂ → ℝ≥0∞}
    (hd : ∀ x y, Measurable fun o => d o x y) : MeasurableSet (eventMetricAxioms S d) := by
  refine ((?_ : MeasurableSet {o | ∀ x ∈ S, d o x x = 0}).inter ?_).inter ?_
  · exact measurableSet_forall_mem hS fun x _ => measurableSet_eq_ennreal (hd x x) measurable_const
  · exact measurableSet_forall_mem hS fun x _ => measurableSet_forall_mem hS fun y _ =>
      measurableSet_eq_ennreal (hd x y) (hd y x)
  · exact measurableSet_forall_mem hS fun x _ => measurableSet_forall_mem hS fun y _ =>
      measurableSet_forall_mem hS fun w _ => measurableSet_le (hd x w) ((hd x y).add (hd y w))

theorem measurableSet_eventChains {S : Set ℂ} (hS : S.Countable) (K : ℕ → Set ℂ)
    {d : Ω → ℂ → ℂ → ℝ≥0∞} (hd : ∀ x y, Measurable fun o => d o x y) :
    MeasurableSet (eventChains S K d) := by
  have : Countable S := hS.to_subtype
  unfold eventChains
  refine measurableSet_forall_mem hS fun x _ => measurableSet_forall_mem hS fun y _ =>
    measurableSet_forall fun ε => measurableSet_imp_const _ fun _ =>
    measurableSet_exists fun n => measurableSet_forall fun δ => measurableSet_imp_const _ fun _ =>
    measurableSet_exists fun N => measurableSet_exists fun m =>
    measurableSet_and_const _ fun _ => measurableSet_and_const _ fun _ =>
    measurableSet_and_const _ fun _ => measurableSet_and_const _ fun _ => ?_
  exact measurableSet_le (Finset.measurable_sum _ fun i _ => hd _ _) ((hd x y).add_const _)

theorem measurableSet_eventLocalAgreement {ι κ : Type*} [Countable ι] [Countable κ] {S : Set ℂ}
    (hS : S.Countable) (adm : ι → κ → Prop) (T : ι → κ → Set ℂ) {d : Ω → ℂ → ℂ → ℝ≥0∞}
    {F : ι → Ω → ℂ → ℂ → ℝ≥0∞} (hd : ∀ x y, Measurable fun o => d o x y)
    (hF : ∀ i u v, Measurable fun o => F i o u v) :
    MeasurableSet (eventLocalAgreement S adm T d F) := by
  unfold eventLocalAgreement
  refine measurableSet_forall fun i => measurableSet_forall fun k => measurableSet_imp_const _ fun _ =>
    measurableSet_exists fun η => measurableSet_and_const _ fun _ =>
    measurableSet_forall_mem hS fun u _ => measurableSet_forall_mem hS fun v _ =>
    measurableSet_imp_const _ fun _ => measurableSet_imp_const _ fun _ =>
    measurableSet_imp_const _ fun _ => measurableSet_eq_ennreal (hd u v) (hF i u v)

/-- **Step 4.** The event `A` is measurable as soon as the family `d` and the local families `F i` are measurable in the
observation pointwise, `S` is countable, and the indices are countable. -/
theorem measurableSet_eventA {ι κ : Type*} [Countable ι] [Countable κ] {S : Set ℂ} (hS : S.Countable)
    (K : ℕ → Set ℂ) (adm : ι → κ → Prop) (T : ι → κ → Set ℂ) {d : Ω → ℂ → ℂ → ℝ≥0∞}
    {F : ι → Ω → ℂ → ℂ → ℝ≥0∞} (hd : ∀ x y, Measurable fun o => d o x y)
    (hF : ∀ i u v, Measurable fun o => F i o u v) :
    MeasurableSet (eventA S K adm T d F) :=
  ((measurableSet_eventMetricAxioms hS hd).inter (measurableSet_eventChains hS K hd)).inter
    (measurableSet_eventLocalAgreement hS adm T hd hF)

open Classical in
/-- The function `ℂ → ℂ → ℝ` extended by `0` off `Z` from a continuous function on `Z ⊆ ℂ × ℂ`. -/
noncomputable def extendDist (Z : Set (ℂ × ℂ)) (M : C(Z, ℝ)) (x y : ℂ) : ℝ :=
  if h : (x, y) ∈ Z then M ⟨(x, y), h⟩ else 0

/-- A measurable family of continuous functions on `Z` gives a pointwise measurable family of extended functions. -/
theorem measurable_extendDist (Z : Set (ℂ × ℂ)) {M : Ω → C(Z, ℝ)} (hM : Measurable M) (x y : ℂ) :
    Measurable fun o => extendDist Z (M o) x y := by
  unfold extendDist
  by_cases h : (x, y) ∈ Z
  · simp only [h, ↓reduceDIte]
    exact (ContinuousMap.measurable_eval (⟨(x, y), h⟩ : Z)).comp hM
  · simp only [h, ↓reduceDIte]
    exact measurable_const

theorem measurable_ofReal_extendDist (Z : Set (ℂ × ℂ)) {M : Ω → C(Z, ℝ)} (hM : Measurable M) (x y : ℂ) :
    Measurable fun o => ENNReal.ofReal (extendDist Z (M o) x y) :=
  ENNReal.measurable_ofReal.comp (measurable_extendDist Z hM x y)

end HarmonicBalls
